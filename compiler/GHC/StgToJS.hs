module GHC.StgToJS
  ( stgToJS
  )
where

import GHC.StgToJS.CodeGen


-- Note [StgToJS design]
-- ~~~~~~~~~~~~~~~~~~~~~
--
-- StgToJS ("JS backend") is adapted from GHCJS [GHCJS2013].
--
-- Haskell to JavaScript
-- ~~~~~~~~~~~~~~~~~~~~~
-- StgToJS converts STG into a JavaScript AST (in GHC.JS) that has been adapted
-- from JMacro [JMacro].
--
-- Tail calls: translated code is tail call optimized through a trampoline,
-- since JavaScript implementations don't always support tail calls.
--
-- JavaScript ASTs are then optimized. A dataflow analysis is performed and then
-- dead code and redundant assignments are removed.
--
-- Primitives
-- ~~~~~~~~~~
-- Haskell primitives have to be represented as JavaScript values. This is done
-- as follows:
--
--  - Int#/Int32#     -> number in Int32 range
--  - Int16#          -> number in Int16 range
--  - Int8#           -> number in Int8 range
--  - Word#/Word32#   -> number in Word32 range
--  - Word16#         -> number in Word16 range
--  - Word8#          -> number in Word8 range
--
--  - Float#/Double#  -> both represented as Javascript Double (no Float!)
--
--  - Int64#          -> represented with two fields:
--                          high -> number in Int32 range
--                          low  -> number in Word32 range
--  - Word64#         -> represented with two fields: high, low
--                          high -> number in Word32 range
--                          low  -> number in Word32 range
--
--  - Addr#           -> represented with two fields: array (used as a namespace) and index
--  - StablePtr#      -> similar to Addr# with array fixed to h$stablePtrBuf
--
--  - JSVal#          -> any Javascript object (used to pass JS objects via FFI)
--
--  - TVar#, MVar#, etc. are represented with JS objects
--
-- Foreign JavaScript imports
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~
-- StgToJS supports inline JavaScript code. Example:
--
--    > foreign import javascript unsafe
--    >   "((x,y) => x + y)"
--    >   plus :: Int -> Int -> Int
--
-- Currently the JS backend only supports functions as JS imports.
--
-- In comparison, GHCJS supports JavaScript snippets with $1, $2... variables
-- as placeholders for the arguments. It requires a JavaScript parser that the
-- JS backend lacks. In GHCJS, the parser is inherited from JMacro and supports
-- local variable declarations, loops, etc. Local variables are converted to
-- hygienic names to avoid capture.
--
-- Primitives that are represented as multiple values (Int64#, Word64#, Addr#)
-- are passed to FFI functions with multiple arguments.
--
-- Interruptible convention: FFI imports with the "interruptible" calling
-- convention are passed an extra argument (usually named "$c") that is a
-- continuation function. The FFI function must call this function to return to
-- Haskell code.
--
-- Unboxed tuples: returning an unboxed tuple can be done with the predefined
-- macros RETURN_UBX_TUPn where n is the size of the tuples. Internally it uses
-- predefined "h$retN" global variables to pass additional values; the first
-- element of the tuple is returned normally.
--
-- Memory management
-- ~~~~~~~~~~~~~~~~~
-- Heap objects are represented as JavaScript values.
--
-- Most heap objects are represented generically as JavaScript "objects" (hash
-- maps). However, some Haskell heap objects can use use a more memory efficient
-- JavaScript representation: number, string... An example of a consequence of
-- this is that both Int# and Int are represented the same as a JavaScript
-- number. JavaScript introspection (e.g. typeof) is used to differentiate
-- heap object representations when necessary.
--
-- Generic representation: objects on the heap ("closures") are represented as
-- JavaScript objects with the following fields:
--
--  { f   -- (function) entry function + info table
--  , d1  -- two fields of payload
--  , d2
--  , m   -- GC mark
--  , cc  -- optional cost-center
--  }
--
-- Payload: payload only consists of two fields (d1, d2). When more than two
-- fields of payload are required, the second field is itself an object.
--    payload []         ==> { d1 = null, d2 = null                   }
--    payload [a]        ==> { d1 = a   , d2 = null                   }
--    payload [a,b]      ==> { d1 = a   , d2 = b                      }
--    payload [a,b,c]    ==> { d1 = a   , d2 = { d1 = b, d2 = c}      }
--    payload [a,b,c...] ==> { d1 = a   , d2 = { d1 = b, d2 = c, ...} }
--
-- Entry function/ info tables: JavaScript functions are JavaScript objects. If
-- "f" is a function, we can:
--    - call it, e.g. "f(arg0,arg1...)"
--    - get/set its fields, e.g. "f.xyz = abc"
-- This is used to implement the equivalent of tables-next-to-code in
-- JavaScript: every heap object has an entry function "f" that also contains
-- some metadata (info table) about the Haskell object:
--    { t     -- object type
--    , size  -- number of fields in the payload (-1 if variable layout)
--    , i     -- (array) fields layout (empty if variable layout)
--    , n     -- (string) object name for easier dubugging
--    , a     -- constructor tag / fun arity
--    , r     -- ??
--    , s     -- static references?
--    , m     -- GC mark?
--    }
--
-- Payloads for each kind of heap object:
--
-- THUNK =
--  { f  = returns the object reduced to WHNF
--  , m  = ?
--  , d1 = ?
--  , d2 = ?
--  }
--
-- FUN =
--  { f  = function itself
--  , m  = ?
--  , d1 = free variable 1
--  , d2 = free variable 2
--  }
--
-- There are two different kinds of partial application:
--  - pap_r   : pre-generated PAP that contains r registers
--  - pap_gen : generic PAP, contains any number of registers
--
-- PAP =
--  { f  = ?
--  , m  = ?
--  , d1 = function
--  , d2 =
--    { d1 & 0xff = number of args (PAP arity)
--    , d1 >> 8   = number of registers (r for h$pap_r)
--    , d2, d3... = args (r)
--    }
--  }
--
-- CON =
--  { f  = entry function of the datacon worker
--  , m  = 0
--  , d1 = first arg
--  , d2 = arity = 2: second arg
--         arity > 2: { d1, d2, ...} object with remaining args (starts with "d1 = x2"!)
--  }
--
-- BLACKHOLE =
--  { f  = h$blackhole
--  , m  = ?
--  , d1 = owning TSO
--  , d2 = waiters array
--  }
--
-- StackFrame closures are *not* represented as JS objects. Instead they are
-- "unpacked" in the stack, i.e. a stack frame occupies a few slots in the JS
-- array representing the stack ("h$stack").
--
-- When a shared thunk is entered, it is overriden with a black hole ("eager
-- blackholing") and an update frame is pushed on the stack.
--
-- Stack: the Haskell stack is implemented with a dynamically growing JavaScript
-- array ("h$stack").
--  TODO: does it shrink sometimes?
--  TODO: what are the elements of the stack? one JS object per stack frame?
--
--
-- Interaction with JavaScript's garbage collector
-- ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
-- Using JS objects to represent Haskell heap objects means that JS's GC does
-- most of the memory management work.
--
-- However, GHC extends Haskell with features that rely on GC layer violation
-- (weak references, finalizers, etc.). To support these features, a heap scan
-- is can be performed (using TSOs, StablePtr, etc. as roots) to mark reachable
-- objects. Scanning the heap is an expensive operation, but fortunately it
-- doesn't need to happen too often and it can be disabled.
--
-- TODO: importance of eager blackholing
--
-- Concurrency
-- ~~~~~~~~~~~
-- The scheduler is implemented in JS and runs in a single JavaScript thread
-- (similarly to the C RTS not using `-threaded`).
--
-- The scheduler relies on callbacks/continuations to interact with other JS
-- codes (user interface, etc.). In particular, safe foreign import can use "$c"
-- as a continuation function to return to Haskell code.
--
-- TODO: is this still true since 2013 or are we using more recent JS features now?
-- TODO: synchronous threads
--
--
-- REFERENCES
--  * [GHCJS2013] "Demo Proposal: GHCJS, Concurrent Haskell in the Browser", Luite Stegeman,
--    2013 (https://www.haskell.org/haskell-symposium/2013/ghcjs.pdf)
--  * [JMacro] https://hackage.haskell.org/package/jmacro
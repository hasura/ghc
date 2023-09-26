/* -----------------------------------------------------------------------------
 *
 * (c) The GHC Team, 2017-2021
 *
 * IPE API
 *
 * Do not #include this file directly: #include "Rts.h" instead.
 *
 * To understand the structure of the RTS headers, see the wiki:
 *   https://gitlab.haskell.org/ghc/ghc/wikis/commentary/source-tree/includes
 *
 * -------------------------------------------------------------------------- */

#pragma once

typedef struct InfoProv_ {
    const char *table_name;
    const char *closure_desc;
    const char *ty_desc;
    const char *label;
    const char *module;
    const char *src_file;
    const char *src_span;
} InfoProv;

typedef struct InfoProvEnt_ {
    // When TNTC is enabled this will point to the entry code
    // not the info table itself.
    const StgInfoTable *info;
    InfoProv prov;
} InfoProvEnt;


/*
 * On-disk representation
 */

/*
 * A byte offset into the string table.
 * We use offsets rather than pointers as:
 *
 *  a. they are smaller than pointers on 64-bit platforms
 *  b. they are easier on the linker since they do not need
 *     to be relocated
 */
typedef uint32_t StringIdx;

// This is the provenance representation that we emit to
// object code (see
// GHC.GHC.StgToCmm.InfoTableProv.emitIpeBufferListNode).
//
// The size of this must be a multiple of the word size
// to ensure correct packing.
typedef struct {
    StringIdx table_name;
    StringIdx closure_desc;
    StringIdx ty_desc;
    StringIdx label;
    StringIdx src_file;
    StringIdx src_span;
} IpeBufferEntry;

GHC_STATIC_ASSERT(sizeof(IpeBufferEntry) % (WORD_SIZE_IN_BITS / 8) == 0, "sizeof(IpeBufferEntry) must be a multiple of the word size");

typedef struct IpeBufferListNode_ {
    struct IpeBufferListNode_ *next;

    // Everything below is read-only and generated by the codegen

    // This flag should be treated as a boolean
    StgWord compressed;

    StgWord count;

    // When TNTC is enabled, these will point to the entry code
    // not the info table itself.
    StgInfoTable **tables;

    IpeBufferEntry *entries;
    StgWord entries_size; // decompressed size

    char *string_table;
    StgWord string_table_size; // decompressed size

    // Shared by all entries
    StringIdx module_name;
} IpeBufferListNode;

void registerInfoProvList(IpeBufferListNode *node);

// Returns true on success, initializes `out`.
bool lookupIPE(const StgInfoTable *info, InfoProvEnt *out);

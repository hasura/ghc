-- trac #2033: This was previously used to fail when the renamer
-- didn't check for a view
-- /pattern/ being used in an /expression/ context
--
-- But due to GHC proposal #281 all arrows in an expression context
-- are function arrow type now

module RnFail051 where

main :: IO ()
main = wrapper (_ -> putStrLn "_")

wrapper :: (String -> IO ()) -> IO ()
wrapper f = f ""

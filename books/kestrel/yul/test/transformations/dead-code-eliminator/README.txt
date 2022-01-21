These files were modified versions of the yulOpimizerTests that do
the preprocessing needed for our deadCodeEliminator checker to work.
The .expected files were created from the comments using
  awk -f ~/acl2/books/kestrel/yul/test/uncomment-expected.awk *.yul

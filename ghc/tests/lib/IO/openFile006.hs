-- !!! opening a file in WriteMode better truncate it

import IO

main = do
  h <- openFile "openFile006.out" AppendMode
  hPutStrLn h "hello, world"
  size <- hFileSize h
  print size
  hClose h
 
  h <- openFile "openFile006.out" WriteMode
  size <- hFileSize h
  print size

/*
  Module:    fac
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Lee Pike, Galois Connections, Inc. <leepike@galois.com>
*/

// Factorial

exports fac;

fac : B^32 -> B^8;

fac i = facs @@ i
  where {
    rec 
      idx : B^8^inf;
      idx = [0] ## [x + 1 | x <- idx];
    and 
      facs : B^8^inf;
      facs = [1] ## [x * y | x <- facs | y <- drops{1} idx];
  };




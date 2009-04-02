/*
  Module:    fibs
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Mark Shields, Galois Connections, Inc. <mbs@galois.com>
*/

// Fibonacci numbers

exports fib;

fib : B^32 -> B^8;

fib i = fibs @@ i
  where {
    rec 
      fibs : B^8^inf;
      fibs = [0, 1] ## [x + y | x <- drops{1} fibs | y <- fibs];
  };


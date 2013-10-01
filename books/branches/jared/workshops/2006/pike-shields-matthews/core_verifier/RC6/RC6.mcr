/*
  Module:    RC6
  Copyright: (c) 2005 Galois Connections, Inc.
  Author:    Mark Shields, Galois Connections, Inc. <mbs@galois.com>
*/

// RC6 key expansion

exports rc6exp;

A = 5;
Nk = 44;
C = max 1 ((A + 3) / 4);
V = 3 * max C Nk;
Rot = V - 3 * Nk;
Off = V - Nk;

rc6exp (key : B^8^A) : B^32^Nk = segments s Off >>> Rot
  where {                 
    rec (consts : B^32^inf) = [0xb7e15163] ## 
                              [x + 0x9e3779b9 | x <- consts];
    (inits : B^32^Nk) = takes consts; 
    (initl : B^32^C) = split (join key # zero);
    rec 
      (s : B^32^inf) = [ (x+a+b) <<< 3 
                           | x <- inits ## s 
                           | a <- [0{32}] ## s 
                           | b <- [0{32}] ## l 
                       ];
    and 
      (l : B^32^inf) = [ (x+a+b) <<< drop ((a+b) % 5)
                           | x <- initl ## l 
                           | a <- s 
                           | b <- [0{32}] ## l 
                       ];
  };


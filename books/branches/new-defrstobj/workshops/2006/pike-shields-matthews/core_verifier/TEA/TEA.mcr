/*
  Module:    TEA
  Copyright: (c) 2004 Galois Connections, Inc.
  Authors:   Mark Shields, Galois Connections, Inc. <mbs@galois.com>
*/

/* The Tiny Encryption Algorithm 
   (original version, without key schedule strengthening)

   See D.J. Wheeler and R.M. Needham "TEA, a tiny encryption algorithm",
   In B. Preneel, ed, Fast Saftware Encryption, Second International Workshop
   (LNCS 1008), pp 363-366, Springer-Verlag, 1995.
*/

exports code, decode;

// Number of rounds
N = 32;
// Word width
W = 32;

// Some types
Word = B^W;
Block = Word^2;
Key = Word^4;
Index = B^W;

// Magic constant
Delta = 0x9e3779b9;

code : (Block, Key) -> Block;
code ([y, z], [k0, k1, k2, k3]) = [ys @@ N, zs @@ N]
  where {
    rec
      sums : Word^inf;
      sums = [Delta] ## [ sum + Delta | sum <- sums ];
    and
      ys : Word^inf;
      ys = [y] ## [ y + ((z<<4)+k0 ^^ z+sum ^^ (z>>5)+k1)
                  | sum <- sums | y <- ys | z <- zs ];
    and
      zs : Word^inf;
      zs = [z] ## [ z + ((y<<4)+k2 ^^ y+sum ^^ (y>>5)+k3)
            	  | sum <- sums | y <- drops{1} ys | z  <- zs ];
  };

decode : (Block, Key) -> Block;
decode ([y, z], [k0, k1, k2, k3]) = [ys @@ N, zs @@ N]
  where {
    rec
      sums : Word^inf;
      sums = [Delta * N] ## [ sum - Delta | sum <- sums ];
    and
      ys : Word^inf;
      ys = [y] ## [ y - ((z<<4)+k0 ^^ z+sum ^^ (z>>5)+k1)
      	          | sum <- sums | y  <- ys | z <- drops{1} zs ];
    and
      zs : Word^inf;
      zs = [z] ## [ z - ((y<<4)+k2 ^^ y+sum ^^ (y>>5)+k3)
                  | sum <- sums | y <- ys | z <- zs ];
  };

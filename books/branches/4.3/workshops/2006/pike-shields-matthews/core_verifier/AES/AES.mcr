/*
  Module:    AES
  Copyright: (c) 2004 Galois Connections, Inc.
  Author:    Mark Shields, Galois Connections, Inc. <mbs@galois.com>
*/

/* The Advanced Encryption Standard (Rijndael) algorithm */

exports aes, sea;

// ----------------------------------------
// Constants and Types
// ----------------------------------------

Nb = 128 / 32;
Nk = 128 / 32;
Nr = max Nb Nk + 6; // NOTE: (Nr+1)*Nb must be < 256

Byte = B^8;
Key = Byte^(4*Nk);
Block = Byte^(Nb*4);
State = Byte^Nb^4;
KeySched = (State, State^(Nr-1), State);

// ----------------------------------------
// Matrix multiplication in Galois field 2
// ----------------------------------------

bitMmult : (B^8^8, B^8) -> B^8;
bitMmult (xss, ys) = [ parity (xs && ys) | xs <- xss ];

// ----------------------------------------
// Galois field B^8
// ----------------------------------------

// polynomial x
GUnit = 0b00000010;

// irreducible polynomial x^8 + x^4 + x^3 + x + 1
GIrred = 0b100011011;

gtimes : (Byte, Byte) -> Byte;
gtimes (x, y) = pmod (pmult x y) GIrred;

gpower : (Byte, Byte) -> Byte;
gpower (x, i) = ps @@ i
  where {
    rec
      ps : Byte^inf[8,?];
      ps = [1] ## [ gtimes (x, p) | p <- ps ];
  };

ginverse : Byte -> Byte;
ginverse x = if x == 0 then 0 else pinv GIrred x ;

// ----------------------------------------
// Matrix multiplication in Galois field B^8
// ----------------------------------------

byteSum : Byte^4 -> Byte;
byteSum xs = sums @@ Nb
  where {
    rec
      sums : Byte^inf;
      sums = [0] ## [ x ^^ y | x <- cycle xs | y <- sums ];
  };

byteDot : (Byte^4, Byte^4) -> Byte;
byteDot (as, bs) = byteSum [ gtimes (a, b) | a <- as | b <- bs ];

byteMmult : (Byte^4^4, Byte^4) -> Byte^4;
byteMmult (xss, ys) = [ byteDot (xs, ys) | xs <- xss ];

// ----------------------------------------
// S-boxes
// ----------------------------------------

affMat : Byte^8;
affMat = [ 0xf8 >>> i | i <- [0{3} .. 7] ];

invAffMat : Byte^8;
invAffMat = [ 0x52 >>> i | i <- [0{3} .. 7] ];

affine : Byte -> Byte;
affine xs = bitMmult (affMat, xs) ^^ 0x63;

invAffine : Byte -> Byte;
invAffine xs = bitMmult (invAffMat, xs ^^ 0x63);

sbox : Byte^256;
sbox = 
  if mcc_target == "aamp-deep" then
    /* Takes too long on AAMP model */
    zero
  else
    [ affine (ginverse x) | x <- [0{8} .. 255] ];

invSbox : Byte^256;
invSbox =
  if mcc_target == "aamp-deep" then
    /* Takes too long on AAMP model */
    zero
  else
    [ ginverse (invAffine x) | x <- [0{8} .. 255] ];

// ----------------------------------------
// Rounds
// ----------------------------------------

byteSub : State -> State;
byteSub state = [ [ sbox @ x | x <- row ] | row <- state ]; 

invByteSub : State -> State;
invByteSub state = [ [ invSbox @ x | x <- row ] | row <- state ];

shiftRow : State -> State;
shiftRow state = [ row <<< i | row <- state | i <- [ 0{2}..3 ] ];

invShiftRow : State -> State;
invShiftRow state = [ row >>> i | row <- state | i <- [ 0{2}..3 ] ];

polyMat : Byte^Nb -> State;
polyMat coeff = transpose [ coeff >>> i | i <- [0{2}..3] ];

cx : State;
cx = polyMat [ 0x02, 0x01, 0x01, 0x03 ]; 

dx : State;
dx = polyMat [ 0x0e, 0x09, 0x0d, 0x0b ];

mixColumn : State -> State; 
mixColumn state = transpose [ byteMmult (cx, col) | col <- transpose state ];

invMixColumn : State -> State;
invMixColumn state = transpose [ byteMmult (dx, col) | col <- transpose state ];

xorS : (State, State) -> State;
// xorS (xss, yss) = [ [ x ^^ y | x <- xs | y <- ys ] | xs <- xss | ys <- yss ];
xorS (x, y) = split (split (join (join x) ^^ join (join y)));

round : (State, State) -> State;
round (state, roundKey) = xorS (mixColumn (shiftRow (byteSub state)), roundKey);

finalRound : (State, State) -> State;
finalRound (state, roundKey) = xorS (shiftRow (byteSub state), roundKey);

invRound : (State, State) -> State;
invRound (state, roundKey) 
  = xorS (invMixColumn (invShiftRow (invByteSub state)), roundKey);

invFinalRound : (State, State) -> State;
invFinalRound (state, roundKey) 
  = xorS (invShiftRow (invByteSub state), roundKey);

rounds : (State, KeySched) -> State;
rounds (state, (initialKey, rndKeys, finalKey)) 
  = finalRound (rnds @@ (Nr - 1), finalKey)
  where { 
    rec
      rnds : State^inf;
      rnds = [xorS (state, initialKey)] ## [ round (state', key) 
                                           | state' <- rnds 
                                           | key <- cycle rndKeys ]; 
  }; 

invRounds : (State, KeySched) -> State;
invRounds (state, (initialKey, rndKeys, finalKey)) 
  = invFinalRound (rnds @@ (Nr - 1), initialKey)
  where { 
    invRndKeys : State^(Nr-1);
    invRndKeys = [ invMixColumn k | k <- reverse rndKeys ];
    rec
      rnds : State^inf;
      rnds = [xorS (state, finalKey)] ## [ invRound (state', key)
                                         | state' <- rnds
                                         | key <- cycle invRndKeys ];
  };

// ----------------------------------------
// Key Schedule
// ----------------------------------------

xorB4 : (Byte^4, Byte^4) -> Byte^4;
// xorB4 (xs, ys) = [ x ^^ y | x <- xs | y <- ys ];
xorB4 (x, y) = split (join x ^^ join y);

subByte : Byte^4 -> Byte^4;
subByte p = [ sbox @ x | x <- p ];

rcon : Byte -> Byte^4;
rcon i = [gpower (GUnit, i - 1), 0, 0, 0];

nextWord : (Byte, Byte^4, Byte^4) -> Byte^4;
nextWord (i, old, prev) = xorB4 (old, prev') 
  where {
    prev' : Byte^4;
    prev' = if i % Nk == 0 then
              xorB4 (subByte (prev <<< 1), rcon (i / Nk))
            else if (6{8} < Nk) /\ (i % Nk == 4) then
              subByte prev
            else 
              prev;
  };

keyExpansion : Key -> B^8^4^((Nr+1)*Nb);
keyExpansion key = takes w
  where {
    keyCols : B^8^4^Nk;
    keyCols = split key;
    rec
      w : B^8^4^inf[?,(Nr+1)*Nb];
      w = keyCols ## [ nextWord (i, old, prev)
                     | i <- cycle [Nk{8}..(Nr+1)*Nb-1]
                     | old <- w
                     | prev <- drops{Nk-1} w ];
  };

keySchedule : Key -> KeySched;
keySchedule key = (rKeys @ 0, segment rKeys 1, rKeys @ Nr)
  where {
    w : B^8^4^((Nr+1)*Nb);
    w = keyExpansion key;
    rKeys : B^8^Nb^4^(Nr+1);
    rKeys = [ transpose ws | ws <- split{Nb} w ];
  };

// ----------------------------------------
// Top-level
// ----------------------------------------

stripe : Block -> State;
stripe block = transpose (split block);

unstripe : State -> Block;
unstripe state = join (transpose state);

encrypt : (Block, KeySched) -> Block;
encrypt (pt, keySched) = unstripe (rounds (stripe pt, keySched));

decrypt : (Block, KeySched) -> Block;
decrypt (ct, keySched) = unstripe (invRounds (stripe ct, keySched));

// ----------------------------------------
// Entry points
// ----------------------------------------

aes : (Block, Key) -> Block;
aes (pt, key) = encrypt (pt, keySchedule key);

sea : (Block, Key) -> Block;
sea (ct, key) = decrypt (ct, keySchedule key);

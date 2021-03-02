// Simplified version with only 1 round (spec says 10 rounds)
include "../circom/blake2s/blake2s-1round.circom"

// Simplified from 500 bits to 20 bits:
component main = Blake2s(20,0);

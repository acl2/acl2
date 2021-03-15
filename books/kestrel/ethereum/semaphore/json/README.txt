The JSON files in this directory were created by

1. building Semaphore according to the documented procedure in
   https://semaphore.appliedzkp.org/quickstart.html

2. for each template instantiation that we analyzed, creating
   a simple circom main function that calls it, and compiling it

3. copying the json output file here.

For example, to create montgomeryadd.json,
we created a file "montgomeryadd.circom" with the contents
  include "../node_modules/circomlib/circuits/montgomery.circom"
  component main = MontgomeryAdd();
and we compiled it with
  npx circom montgomeryadd.circom -o montgomeryadd.json

--------------------------------

The JSON output files have been saved in this directory,
and the circom main wrapper files have been saved in
the main-wrappers subdirectory.

Some of the JSON output files are too large for github, so they have been compressed with gzip.

--------------------------------

For the circom compiler and the latest library files, see https://github.com/iden3/circom

The circom source files that were used to build Semaphore are available on Github
at the following permalinks:

https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/aliascheck.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/assert.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/babyjub.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/binsum.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/bitify.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/comparators.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/compconstant.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/eddsamimcsponge.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/escalarmulany.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/escalarmulfix.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/mimcsponge.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/montgomery.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/mux1.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/mux3.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/pedersen.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/pointbits.circom
https://github.com/kobigurk/circomlib/blob/4284dc1ef984a204db08864f5da530c97f9376ef/circuits/sha256/rotate.circom
https://github.com/appliedzkp/semaphore/blob/1e34d21f989550bb10c1a356e045770dfd4b0a6d/circuits/circom/blake2s/blake2s.circom
https://github.com/appliedzkp/semaphore/blob/1e34d21f989550bb10c1a356e045770dfd4b0a6d/circuits/circom/blake2s/uint32.circom
https://github.com/appliedzkp/semaphore/blob/1e34d21f989550bb10c1a356e045770dfd4b0a6d/circuits/circom/semaphore-base.circom
https://github.com/appliedzkp/semaphore/blob/1e34d21f989550bb10c1a356e045770dfd4b0a6d/circuits/circom/semaphore.circom

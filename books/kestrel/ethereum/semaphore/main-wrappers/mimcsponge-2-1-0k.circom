include "../node_modules/circomlib/circuits/mimcsponge.circom"

component main = MiMCSponge(2,1);
main.k <== 0;

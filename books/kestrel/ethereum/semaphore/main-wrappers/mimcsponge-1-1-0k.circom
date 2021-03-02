include "../node_modules/circomlib/circuits/mimcsponge.circom"

component main = MiMCSponge(1,1);
main.k <== 0;

include "../node_modules/circomlib/circuits/mimcsponge.circom"

component main = MiMCSponge(5,1);
main.k <== 0;

#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/GeNoC")#|ACL2s-ToDo-Line|#

(include-book "../../network/2Dmesh/network")
(include-book "../../departure/simple/departure")
(include-book "../../router/XY-wormhole/router")

(instantiateStepnetwork_t INST XY-wormhole)
(instantiateStepnetwork INST)
(instantiateGenoc_t INST simple)
(instantiateGenoc INST 2dmesh)
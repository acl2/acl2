#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")

(include-book "../../../generic-modules/GeNoC")
(include-book "../../network/2Dmesh/network")
(include-book "../../departure/simple/departure")
(include-book "../../router/XY-packet/router")

(instantiateStepnetwork_t INST XY-packet)
(instantiateStepnetwork INST)
(instantiateGenoc_t INST simple)
(instantiateGenoc INST 2dmesh)#|ACL2s-ToDo-Line|#

#|$ACL2s-Preamble$;
(begin-book);$ACL2s-Preamble$|#

(in-package "ACL2")#|ACL2s-ToDo-Line|#


(include-book "../../../generic-modules/GeNoC")
(include-book "../../network/spidergon/network")
(include-book "../../departure/simple/departure")
(include-book "../../router/spidergon/router")

(instantiateStepnetwork_t INST spidergon)
(instantiateStepnetwork INST)
(instantiateGenoc_t INST simple)
(instantiateGenoc INST spidergon)
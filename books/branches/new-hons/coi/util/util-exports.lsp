#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

(in-package "ACL2")

(defconst *mv-nth-exports*
  '(met val v0 v1 v2 v3 v4))

(defconst *util-exports*
  (append *mv-nth-exports* nil))

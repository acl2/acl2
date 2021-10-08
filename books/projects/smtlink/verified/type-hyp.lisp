;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;
(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "std/testing/eval" :dir :system)
(include-book "clause-processors/join-thms" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)

(include-book "hint-interface")

(defsection SMT-type-hyp
  :parents (verified)
  :short "The function type-hyp passes type related information onto the
  trusted clause processor."

;; -----------------------------------------------------------------
;;

;; type-hyp for SMT solver
(define type-hyp ((type-hyps booleanp) (tag symbolp))
  :ignore-ok t
  type-hyps)

(in-theory (disable (:d type-hyp)
                    (:e type-hyp)
                    (:t type-hyp)))
)

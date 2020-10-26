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
(define type-hyp ((blist boolean-listp) (tag symbolp))
  (b* ((blist (acl2::boolean-list-fix blist))
       ((unless (consp blist)) t)
       ((cons first rest) blist))
    (and first (type-hyp rest tag))))

(in-theory (disable (:d type-hyp)
                    (:e type-hyp)
                    (:t type-hyp)))

(define is-type-hyp ((expr pseudo-termp))
  :returns (is? booleanp)
  (b* (((unless (equal (len expr) 3))
        nil)
       (fn-name (car expr))
       ((unless (equal fn-name 'type-hyp)) nil))
    t))

)

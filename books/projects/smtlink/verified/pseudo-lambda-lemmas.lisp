;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (July 8th 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
;; for lambda expression
(include-book "kestrel/utilities/system/terms" :dir :system)

(encapsulate ()
  (local (in-theory (enable pseudo-lambdap)))

  (defthm symbol-listp-of-formals-of-pseudo-lambdap
    (implies (pseudo-lambdap x) (symbol-listp (cadr x))))

  (defthm pseudo-termp-of-body-of-pseudo-lambdap
    (implies (pseudo-lambdap x) (pseudo-termp (caddr x))))

  (defthm consp-of-pseudo-lambdap
    (implies (pseudo-lambdap x) (consp x)))

  (defthm consp-of-cdr-of-pseudo-lambdap
    (implies (pseudo-lambdap x) (consp (cdr x))))

  (defthm consp-of-cddr-of-pseudo-lambdap
    (implies (pseudo-lambdap x) (consp (cddr x))))

  (defthm not-stringp-of-cadr-of-pseudo-lambdap
    (implies (pseudo-lambdap x) (not (stringp (cadr x)))))
  )

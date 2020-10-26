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

  (defthm lambda-of-pseudo-lambdap
    (implies (pseudo-lambdap x)
             (equal (car x) 'lambda)))

  (defthm true-listp-of-cdr-of-pseudo-lambdap
    (implies (pseudo-lambdap x)
             (true-listp (cdr x))))

  (defthm true-listp-of-cadr-of-pseudo-lambdap
    (implies (pseudo-lambdap x)
             (true-listp (cadr x))))

  (defthm equal-len-of-pseudo-lambda-formals-and-actuals
    (implies (and (pseudo-termp term)
                  (consp term)
                  (pseudo-lambdap (car term)))
             (equal (len (lambda-formals (car term)))
                    (len (cdr term)))))

  ;; I find that Sol has another version of pseudo-lambda-p and
  ;; pseudo-lambda-fix in clause-processors/pseudo-term-fty.lisp that's
  ;; probably more FTY friendly.
  ;; TODO: I will switch to that version in the future. I suspect I will need
  ;; to change a bunch of places for consistency and now it seems better to
  ;; first focus on function expansion. The :doc pseudo-term-fty stuff looks
  ;; really cool.
  (define pseudo-lambda-fix ((x pseudo-lambdap))
    :returns (fixed pseudo-lambdap)
    (mbe :logic (if (pseudo-lambdap x) x '(lambda nil nil))
         :exec x)
    ///
    (more-returns
     (fixed (implies (pseudo-lambdap x) (equal fixed x))
            :name equal-fixed-and-x-of-pseudo-lambdap)))
  )

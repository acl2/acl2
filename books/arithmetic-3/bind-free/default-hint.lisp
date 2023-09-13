; See the top-level arithmetic-3 LICENSE file for authorship,
; copyright, and license information.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;
;;; default-hint.lisp
;;;
;;; This book contains the definition of the default hint we
;;; will be using to control nonlinear arithmetic.  We put it
;;; into this seperate file for ease of maintenance.
;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; (depends-on "build/defrec-certdeps/REWRITE-CONSTANT.certdep" :dir :system)
; (depends-on "build/defrec-certdeps/PROVE-SPEC-VAR.certdep" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

; Matt K. addition to support acl2-devel inclusion in books/system/fmt.lisp:
; This could be conditioned on #+acl2-devel but it's redundant otherwise, so
; I won't bother with that condition:
(verify-termination observation1-cw
  (declare (xargs :verify-guards t)))

(defun nonlinearp-default-hint (stable-under-simplificationp hist pspv)
  (cond (stable-under-simplificationp
         (if (not (access rewrite-constant
                          (access prove-spec-var pspv :rewrite-constant)
                          :nonlinearp))
             (prog2$
              (observation-cw
               'nonlinearp-default-hint
               "We now enable non-linear arithmetic.")
              '(:computed-hint-replacement t
                                           :nonlinearp t))
           nil))
        ((access rewrite-constant
                 (access prove-spec-var pspv :rewrite-constant)
                 :nonlinearp)
         (if (not (equal (caar hist) 'SETTLED-DOWN-CLAUSE))
             (prog2$
              (observation-cw
               'nonlinearp-default-hint
               "We now disable non-linear arithmetic.")
              '(:computed-hint-replacement t
                                           :nonlinearp nil))
           nil))
        (t
         nil)))

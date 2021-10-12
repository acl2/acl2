;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (11th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "datatypes")

(local (in-theory (enable paragraph-p word-p)))

(define translate-bool ((b booleanp))
  :returns (translated paragraph-p)
  (cond
   ;; Boolean: nil
   ((equal b nil) (list "False"))
   ;; Boolean: t
   (t (list "True"))))

(define SMT-numberp ((sym))
  (declare (xargs :guard t))
  :returns (is? booleanp)
  (if (or (rationalp sym) (integerp sym) (real/rationalp sym))
      t nil))

(local (in-theory (enable SMT-numberp)))

(define SMT-number-fix ((num SMT-numberp))
  :returns (fixed SMT-numberp)
  (mbe :logic (if (SMT-numberp num) num 0)
       :exec num))

(local (in-theory (enable SMT-number-fix)))

(deffixtype SMT-number
  :fix SMT-number-fix
  :pred SMT-numberp
  :equiv SMT-number-equiv
  :define t)

(define translate-number ((num SMT-numberp))
  :returns (translated paragraph-p)
  (b* ((num (SMT-number-fix num))
       ((if (and (rationalp num) (not (integerp num))))
        `("_SMT_.Qx(" ,(numerator num) "," ,(denominator num) ")")))
    (list num)))

(define translate-quote ((term))
  :guard (acl2::quotep term)
  :returns (translated paragraph-p)
  (b* (((unless (mbt (acl2::quotep term))) nil)
       (sym (cadr term)))
    (cond ((SMT-numberp sym) (translate-number sym))
          ((booleanp sym) (translate-bool sym)))))

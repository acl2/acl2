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

(local (in-theory (enable string-or-symbol-p paragraph-p word-p)))

(defalist symbol-string-alist
  :key-type symbolp
  :val-type stringp
  :pred symbol-string-alistp
  :true-listp t)

(local
(defthm assoc-equal-symbol-string-alist
  (implies (and (symbol-string-alistp x)
                (assoc y x))
           (and (consp (assoc y x))
                (stringp (cdr (assoc y x))))))
)

(defthm string-list-of-strip-cdrs-of-symbol-string-alist
  (implies (symbol-string-alistp x)
           (string-listp (strip-cdrs x))))

(defprod symbol-keeper
  ((symbol-map symbol-string-alistp)
   (index natp)
   (avoid-list symbol-listp)))

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

(define generate-symbol-enumeration ((symbol-index natp))
  :returns (new-sym stringp)
  (b* ((symbol-index (nfix symbol-index))
       (new-sym (concatenate 'string "gensym_" (natstr symbol-index))))
    new-sym))

(define translate-symbol ((sym symbolp)
                          (sym-keeper symbol-keeper-p))
  :returns (mv (translated paragraph-p)
               (new-sym-keeper symbol-keeper-p))
  (b* ((sym (symbol-fix sym))
       ((symbol-keeper s) (symbol-keeper-fix sym-keeper))
       (seen? (assoc-equal sym s.symbol-map))
       ((if seen?) (mv (cdr seen?) s))
       (avoid? (member-equal sym s.avoid-list))
       ((if avoid?)
        (mv (generate-symbol-enumeration s.index)
            (change-symbol-keeper s
                                  :symbol-map
                                  (acons sym
                                         (generate-symbol-enumeration s.index)
                                         s.symbol-map)
                                  :index (1+ s.index)))))
    (mv (str::downcase-string (lisp-to-python-names sym))
        (change-symbol-keeper s
                              :symbol-map
                              (acons sym
                                     (str::downcase-string
                                      (lisp-to-python-names sym))
                                     s.symbol-map)))))

(define translate-quote ((term pseudo-termp)
                         (sym-keeper symbol-keeper-p))
  :guard (acl2::quotep term)
  :returns (mv (translated paragraph-p)
               (new-sym-keeper symbol-keeper-p))
  (b* ((sym-keeper (symbol-keeper-fix sym-keeper))
       ((unless (mbt (acl2::quotep term))) (mv nil sym-keeper))
       (sym (cadr term))
       ((if (booleanp sym)) (mv (translate-bool sym) sym-keeper))
       ((if (SMT-numberp sym)) (mv (translate-number sym) sym-keeper))
       ((if (symbolp sym)) (translate-symbol sym sym-keeper)))
    (mv (er hard? 'translate-quote=>translate-quote
            "Cannot translate quotep: ~q0" term)
        sym-keeper)))

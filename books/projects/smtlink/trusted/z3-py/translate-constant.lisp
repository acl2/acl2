;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (Canada Day, 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "../../verified/basics")
(include-book "./datatypes")

(define symbol-append ((asym symbolp) (bsym symbolp))
  :returns (new-sym symbolp)
  (b* ((asym (symbol-fix asym))
       (bsym (symbol-fix bsym))
       (asym-str (string asym))
       (bsym-str (string bsym))
       (new-str (concatenate 'string asym-str bsym-str)))
    (intern-in-package-of-symbol new-str 'SMT)))

(defalist symbol-string-alist
  :key-type symbolp
  :val-type stringp
  :pred symbol-string-alistp
  :true-listp t)

(defthm string-listp-of-strip-cdrs-of-symbol-string-alistp
  (implies (symbol-string-alistp x)
           (string-listp (strip-cdrs x))))

(defthm consp-of-assoc-equal-of-symbol-string-alistp
  (implies (and (symbol-string-alistp x)
                (assoc-equal a x))
           (consp (assoc-equal a x))))

(defthm stringp-of-assoc-equal-of-symbol-string-alistp
  (implies (and (symbol-string-alistp x)
                (assoc-equal a x))
           (stringp (cdr (assoc-equal a x)))))

(local (in-theory (enable paragraph-p word-p
                          string-or-symbol-p)))

(define smt-number-p ((sym))
  (declare (xargs :guard t))
  :returns (is? booleanp)
  (if (or (rationalp sym) (integerp sym) (real/rationalp sym))
      t nil))

(easy-fix smt-number 0)

(local (in-theory (enable smt-number-fix smt-number-p)))

(define translate-number ((num smt-number-p))
  :returns (translated paragraph-p)
  (b* ((num (smt-number-fix num))
       ((if (and (real/rationalp num) (not (rationalp num))))
        (er hard? 'translate-constant=>translate-number
            "Don't know how to translate a real number: ~q0" num))
       ((if (and (rationalp num) (not (integerp num))))
        `("_SMT_.Qx(" ,(numerator num) "," ,(denominator num) ")")))
    num))

(define translate-bool ((b booleanp))
  :returns (translated paragraph-p)
  (if b "True" "False"))

(define translate-symbol ((sym symbolp))
  :returns (translated word-p)
  (str::downcase-string (lisp-to-python-names sym))
  ///
  (more-returns
   (translated
    (stringp translated)
    :name stringp-of-translate-symbol)))

(define translate-symbol-list ((sym-lst symbol-listp))
  :returns (translated paragraph-p)
  :measure (len sym-lst)
  (b* ((sym-lst (symbol-list-fix sym-lst))
       ((unless (consp sym-lst)) nil)
       ((cons first rest) sym-lst))
    (cons (translate-symbol first)
          (translate-symbol-list rest))))

(define generate-symbol-enumeration ((symbol-index natp))
  :returns (new-sym stringp)
  (b* ((symbol-index (nfix symbol-index))
       (new-sym (concatenate 'string "gensym_" (natstr symbol-index))))
    new-sym))

(define translate-constant ((term pseudo-termp)
                            (index natp)
                            (acc symbol-string-alistp)
                            (avoid symbol-listp))
  :returns (mv (translated paragraph-p)
               (new-index natp)
               (new-acc symbol-string-alistp))
  (b* ((term (pseudo-term-fix term))
       (index (nfix index))
       (acc (symbol-string-alist-fix acc))
       ((unless (and (consp term) (acl2::fquotep term)))
        (mv (er hard? 'translate-constant=>translate-constant
                "term has to be acl2::fquotep~%")
            0 nil))
       (the-sym (cadr term))
       ((if (booleanp the-sym))
        (mv (translate-bool the-sym) index acc))
       ((if (smt-number-p the-sym))
        (mv (translate-number the-sym) index acc))
       ((unless (symbolp the-sym))
        (mv (er hard? 'translate-constant=>translate-constant
                "(cadr term) is not symbolp: ~p0~%" the-sym)
            0 nil))
       (exist-map? (assoc-equal the-sym acc))
       ((if exist-map?) (mv (cdr exist-map?) index acc))
       (avoid-sym? (member-equal the-sym avoid))
       ((unless avoid-sym?)
        (mv (translate-symbol the-sym) index
            (acons the-sym (translate-symbol the-sym) acc))))
    (mv (generate-symbol-enumeration index)
        (1+ index)
        (acons the-sym (generate-symbol-enumeration index) acc))))

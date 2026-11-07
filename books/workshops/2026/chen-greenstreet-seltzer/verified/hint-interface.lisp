;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/alists/alist-fix" :dir :system)

(include-book "../config")
(include-book "../utils/basics")
(include-book "../utils/pseudo-term")

;; (defsection SMT-hint-interface
;;   :parents (verified)
;;   :short "Define default Smtlink hint interface"

(local (in-theory (disable pseudo-termp pseudo-term-listp
                           ACL2::PSEUDO-TERM-LISTP-OF-CDR-WHEN-PSEUDO-TERM-LISTP
                           ACL2::PSEUDO-TERM-LISTP-OF-CAR-WHEN-PSEUDO-TERM-LIST-LISTP
                           PSEUDO-TERM-LIST-LISTP
                           PSEUDO-LAMBDAP-OF-FN-CALL-OF-PSEUDO-TERMP)))

(defprod thm-spec
  ((thm symbolp)
   (formals symbol-listp)
   (hypotheses pseudo-termp :default ''t)
   (lhs pseudo-termp :default ''nil)
   (rhs pseudo-termp :default ''nil)
   (judgements pseudo-term-listp)
   (var-term pseudo-termp)
   (var-hyp pseudo-termp :default ''t)
   (hyp-judge pseudo-termp :default ''t)
   (hints true-listp)))

(deflist thm-spec-list
  :elt-type thm-spec-p
  :true-listp t)

(defalist symbol-thm-spec-list-alist
  :key-type symbolp
  :val-type thm-spec-list-p
  :true-listp t)

(defthm assoc-equal-of-symbol-thm-spec-list-alist
  (implies (and (symbol-thm-spec-list-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (thm-spec-list-p (cdr (assoc-equal x alst))))))

(defprod trans-hint
  ((type stringp :default "")
   (translation stringp :default "")
   (formal-types symbol-listp)
   (return-type symbolp)
   (fn-to-const booleanp)))

(defprod smt-function
  :parents (smtlink-hint)
  ((name symbolp)
   (returns thm-spec-list-p)
   (uninterpreted-hints true-listp)
   (depth natp :default 0)
   (kind symbolp) ;; :basic :type :uninterpreted
   (translation-hint trans-hint-p :default (make-trans-hint))))

(defoption maybe-smt-function smt-function-p)

(deflist smt-function-list
  :parents (smt-function)
  :elt-type smt-function-p
  :true-listp t)

(defprod smt-config
  ((smt-cnf smtlink-config-p :default (make-smtlink-config))
   (rm-file booleanp :default t)
   (smt-dir stringp :default "")
   (smt-fname stringp :default "")))

(deftagsum int-to-rat
  (:switch ((okp booleanp :default nil)))
  (:symbol-list ((lst symbol-listp :default nil))))

(defprod smt-hypo
  ((thm symbolp)
   (subst symbol-pseudo-term-alistp)))

(deflist smt-hypo-list
  :elt-type smt-hypo-p
  :true-listp t)

(defprod smt-sub/supertype
  ((type symbolp)
   (thm thm-spec-p :default (make-thm-spec))))

(deflist smt-sub/supertype-list
  :elt-type smt-sub/supertype-p
  :true-listp t)

(defprod smt-sum
  ((tag symbolp :default nil)
   (constructor smt-function-p :default (make-smt-function))
   (destructors smt-function-list-p)))

(deflist smt-sum-list
  :elt-type smt-sum-p
  :true-listp t)

(defprod init
  ((fn smt-function-p :default (make-smt-function))
   (val symbolp)))

(defalist symbol-hints-alist
  :key-type symbolp
  :val-type true-listp
  :true-listp t)

(defthm assoc-equal-of-symbol-hints-alist-p
  (implies (and (symbol-hints-alist-p x)
                (assoc-equal y x))
           (true-listp (cdr (assoc-equal y x)))))

(deftagsum smt-datatype
  ;; property-hints:
  ;; reflexivity-of-equal, symmetricity-of-equal, transitivity-of-equal
  (:basic ((recognizer smt-function-p :default (make-smt-function))
           (equal smt-function-p :default (make-smt-function :name 'equal))
           (property-hints symbol-hints-alist-p)))
  ;; property-hints:
  ;; type-of-constructor, constructor-of-destructor
  ;; type-of-destructors, destructor-of-constructor
  ;; constructor-of-destructor-with-tag
  ;; tag-of-constructor
  ;; tag-uniqueness
  ;; reflexivity-of-equal, symmetricity-of-equal, transitivity-of-equal
  (:sumtype ((kind maybe-smt-function-p)
             (recognizer smt-function-p :default (make-smt-function))
             (equal smt-function-p :default (make-smt-function :name 'equal))
             (sums smt-sum-list-p)
             (property-hints symbol-hints-alist-p)))
  ;; property-hints:
  ;; type-of-init, equal-of-init
  ;; type-of-array-select, array-select-equal, array-select-distinct
  ;; type-of-array-store, array-equal-implies-select-equal,
  ;; select-of-witness-equal-implies-array-equal
  ;; reflexivity-of-equal, symmetricity-of-equal, transitivity-of-equal
  (:array ((recognizer smt-function-p :default (make-smt-function))
           (key-type symbolp)
           (val-type symbolp)
           (init init-p :default (make-init))
           (select smt-function-p :default (make-smt-function))
           (store smt-function-p :default (make-smt-function))
           (equal smt-function-p :default (make-smt-function))
           (equal-witness smt-function-p :default (make-smt-function))
           (property-hints symbol-hints-alist-p)))
  ;; property-hints:
  ;; reflexivity-of-equal, symmetricity-of-equal, transitivity-of-equal
  (:abstract ((recognizer smt-function-p :default (make-smt-function))
              (equal smt-function-p :default (make-smt-function :name 'equal))
              (property-hints symbol-hints-alist-p))))

(define smt-datatype->recognizer ((type smt-datatype-p))
  :returns (rec smt-function-p)
  (b* ((type (smt-datatype-fix type)))
    (cond ((equal (smt-datatype-kind type) :basic)
           (smt-datatype-basic->recognizer type))
          ((equal (smt-datatype-kind type) :sumtype)
           (smt-datatype-sumtype->recognizer type))
          ((equal (smt-datatype-kind type) :array)
           (smt-datatype-array->recognizer type))
          ((equal (smt-datatype-kind type) :abstract)
           (smt-datatype-abstract->recognizer type)))))

(define smt-datatype->equal ((type smt-datatype-p))
  :returns (rec smt-function-p)
  (b* ((type (smt-datatype-fix type)))
    (cond ((equal (smt-datatype-kind type) :basic)
           (smt-datatype-basic->equal type))
          ((equal (smt-datatype-kind type) :sumtype)
           (smt-datatype-sumtype->equal type))
          ((equal (smt-datatype-kind type) :array)
           (smt-datatype-array->equal type))
          ((equal (smt-datatype-kind type) :abstract)
           (smt-datatype-abstract->equal type)))))

(define smt-datatype->property-hints ((type smt-datatype-p))
  :returns (rec symbol-hints-alist-p)
  (b* ((type (smt-datatype-fix type)))
    (cond ((equal (smt-datatype-kind type) :basic)
           (smt-datatype-basic->property-hints type))
          ((equal (smt-datatype-kind type) :sumtype)
           (smt-datatype-sumtype->property-hints type))
          ((equal (smt-datatype-kind type) :array)
           (smt-datatype-array->property-hints type))
          ((equal (smt-datatype-kind type) :abstract)
           (smt-datatype-abstract->property-hints type)))))

(deflist smt-datatype-list
  :elt-type smt-datatype-p
  :true-listp t)

(defoption maybe-smt-datatype
  smt-datatype-p)

(defprod smt-acl2type
  ((recognizer symbolp)
   (subtypes smt-sub/supertype-list-p :default nil)
   (supertypes smt-sub/supertype-list-p :default nil)))

(deflist smt-acl2type-list
  :elt-type smt-acl2type-p
  :true-listp t)

(defalist symbol-smt-acl2type-alist
  :key-type symbolp
  :val-type smt-acl2type-p
  :true-listp t)

(defalist symbol-smt-function-alist
  :key-type symbolp
  :val-type smt-function-p
  :true-listp t)

(defthm assoc-equal-of-symbol-smt-function-alist
  (implies (and (symbol-smt-function-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-function-p (cdr (assoc-equal x alst))))))

(defalist symbol-smt-datatype-alist
  :key-type symbolp
  :val-type smt-datatype-p
  :true-listp t)

(defthm assoc-equal-of-symbol-smt-datatype-alist
  (implies (and (symbol-smt-datatype-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (smt-datatype-p (cdr (assoc-equal x alst))))))

(define get-return-type ((fn smt-function-p)
                         (types symbol-smt-datatype-alist-p))
  :returns (return-type smt-datatype-p)
  (b* ((fn (smt-function-fix fn))
       (types (symbol-smt-datatype-alist-fix types))
       ((smt-function f) fn)
       ((trans-hint th) f.translation-hint)
       (exists? (assoc-equal th.return-type types))
       ((unless exists?)
        (prog2$ (er hard? 'get-return-type=>get-return-type
                    "Unrecognized type ~p0, consider adding it to the hint.~%"
                    th.return-type)
                (make-smt-datatype-basic))))
    (cdr exists?)))

;; ----------------------------------------------------
;;     generate connection map

(define generate-destructors-map ((destructor-lst smt-function-list-p)
                                  (acc symbol-listp))
  :returns (pred-lst symbol-listp)
  :measure (len destructor-lst)
  (b* ((destructor-lst (smt-function-list-fix destructor-lst))
       (acc (symbol-list-fix acc))
       ((unless (consp destructor-lst)) acc)
       ((cons des-hd des-tl) destructor-lst)
       ((smt-function f) des-hd)
       ((trans-hint th) f.translation-hint)
       ((if (member-equal th.return-type acc))
        (generate-destructors-map des-tl acc)))
    (generate-destructors-map des-tl (cons th.return-type acc))))

(define generate-sum-map ((sum smt-sum-p)
                          (acc symbol-listp))
  :returns (pred-lst symbol-listp)
  (b* ((sum (smt-sum-fix sum))
       (acc (symbol-list-fix acc))
       ((smt-sum s) sum))
    (generate-destructors-map s.destructors acc)))

(define generate-sum-list-map ((sums smt-sum-list-p)
                               (acc symbol-listp))
  :returns (pred-lst symbol-listp)
  :measure (len sums)
  (b* ((sums (smt-sum-list-fix sums))
       (acc (symbol-list-fix acc))
       ((unless (consp sums)) acc)
       ((cons sum-hd sum-tl) sums)
       (acc-1 (generate-sum-map sum-hd acc)))
    (generate-sum-list-map sum-tl acc-1)))

(define generate-sumtype-map ((type smt-datatype-p))
  :guard (equal (smt-datatype-kind type) :sumtype)
  :returns (pred-lst symbol-listp)
  (b* ((type (smt-datatype-fix type))
       ((unless (mbt (equal (smt-datatype-kind type) :sumtype))) nil)
       (sums (smt-datatype-sumtype->sums type))
       (lst (generate-sum-list-map sums nil))
       ((if (member-equal 'symbolp lst)) lst))
    (cons 'symbolp lst)))

(define generate-array-map ((type smt-datatype-p))
  :guard (equal (smt-datatype-kind type) :array)
  :returns (pred-lst symbol-listp)
  (b* ((type (smt-datatype-fix type))
       ((unless (mbt (equal (smt-datatype-kind type) :array))) nil)
       (key-type (smt-datatype-array->key-type type))
       (val-type (smt-datatype-array->val-type type))
       ((if (equal key-type val-type)) (list key-type)))
    (list key-type val-type)))

(define generate-connection-map ((type smt-datatype-p))
  :returns (pred-lst symbol-listp)
  (b* ((type (smt-datatype-fix type))
       (kind (smt-datatype-kind type)))
    (cond ((equal kind :sumtype) (generate-sumtype-map type))
          ((equal kind :array) (generate-array-map type))
          ((equal kind :abstract) nil)
          (t nil))))

(define generate-connection-map-list ((types symbol-smt-datatype-alist-p)
                                      (acc symbol-symbol-list-alistp))
  :returns (map symbol-symbol-list-alistp)
  :measure (len (symbol-smt-datatype-alist-fix types))
  (b* ((types (symbol-smt-datatype-alist-fix types))
       (acc (symbol-symbol-list-alist-fix acc))
       ((unless (consp types)) acc)
       ((cons type-hd type-tl) types)
       ((cons name type) type-hd)
       (pred-lst (generate-connection-map type)))
    (generate-connection-map-list type-tl (acons name pred-lst acc))))

;; ----------------------------------------------------

(defalist symbol-trans-hint-alist
  :key-type symbolp
  :val-type trans-hint-p
  :true-listp t)

(defthm assoc-equal-of-symbol-trans-hint-alist
  (implies (and (symbol-trans-hint-alist-p alst)
                (assoc-equal x alst))
           (and (consp (assoc-equal x alst))
                (trans-hint-p (cdr (assoc-equal x alst))))))

(defprod scc-info
  ((scc integer-symbol-list-alistp)
   (order integer-listp)))

(defprod trusted-hint
  ((user-types symbol-smt-datatype-alist-p)
   (user-fns symbol-smt-function-alist-p)
   (scc-info scc-info-p :default (make-scc-info))))

(local (in-theory (disable symbol-listp)))

(defprod smtlink-hint
  :parents (SMT-hint-interface)
  ((functions smt-function-list-p :default nil)
   (acl2types smt-acl2type-list-p :default nil)
   (datatypes smt-datatype-list-p :default nil)
   (replaces thm-spec-list-p :default nil)
   (hypotheses smt-hypo-list-p :default nil)
   (expand-with-vars booleanp :default nil)
   (configurations smt-config-p :default (make-smt-config))
   (int-to-ratp int-to-rat-p :default (make-int-to-rat-switch :okp nil))
   (under-inductionp symbolp :default nil)
   (global-hint symbolp :default nil)
   (wrld-fn-len natp :default 0)
   (translation-theory pseudo-termp :default nil)
   (customp booleanp :default nil)
   (trusted-hint trusted-hint-p :default (make-trusted-hint))))

(defalist smtlink-hint-alist
  :key-type symbolp
  :val-type smtlink-hint-p
  :true-listp t)

(defthm assoc-equal-of-smtlink-hint-alist
  (implies (and (smtlink-hint-alist-p alst)
                (assoc-equal x alst))
           (smtlink-hint-p (cdr (assoc-equal x alst)))))

;; type-alst could be symbol-symbol-alistp or type-to-types-alist-p
(define is-type? ((type symbolp)
                  (type-alst alistp))
  :returns (ok booleanp)
  (b* ((type-alst (acl2::alist-fix type-alst))
       (type (symbol-fix type)))
    (not (null (assoc-equal type type-alst)))))

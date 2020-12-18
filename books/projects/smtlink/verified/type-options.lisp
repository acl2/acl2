;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "hint-interface")

(defprod type-tuple
  ((type symbolp)
   (neighbour-type symbolp)
   (formals symbol-listp)
   (thm symbolp)))

(deflist type-tuple-list
  :elt-type type-tuple-p
  :true-listp t)

(defalist type-to-types-alist
  :key-type symbolp
  :val-type type-tuple-list-p
  :true-listp t)

(defthm assoc-equal-of-type-to-types-alist
  (implies (and (type-to-types-alist-p x)
                (assoc-equal y x))
           (and (consp (assoc-equal y x))
                (type-tuple-list-p (cdr (assoc-equal y x))))))

(defprod return-spec
  ((formals symbol-listp)
   (return-type symbolp)
   (returns-thm symbolp)
   (replace-thm symbolp)))

(deflist return-spec-list
  :elt-type return-spec-p
  :true-listp t)

(fty::deftypes function-description
  (deftagsum arg-decl
    (:next ((next arg-check-p)))
    (:done ((r return-spec-p))))
  (defalist arg-check
    :key-type symbolp
    :val-type arg-decl-p))

(defalist function-description-alist
  :key-type symbolp
  :val-type arg-decl-p
  :true-listp t)

(defthm arg-decl-p-of-assoc-equal-from-function-description-alist-p
  (implies (and (function-description-alist-p y)
                (assoc-equal x y))
           (and (consp (assoc-equal x y))
                (arg-decl-p (cdr (assoc-equal x y))))))

(encapsulate ()
(local (in-theory (disable (:rewrite default-cdr))))

;; example: alist-term = (integer-integer-alistp x)
;; fresh-var = y
;; 1. Generate constraint: y = (alist-to-array-fn x)
;; 2. Use the theorem to establish (alist-array-equiv x y):
;; thm: (implies (and (integer-integer-alistp a)
;;                    (equal b (integer-integer-alist-to-array a)))
;;               (alist-array-equiv a b))
(defprod a2a-info
  ((a2a-fn symbolp) ;; the alist-to-array function
   (formals symbol-listp)
   (thm symbolp))) ;; the theorem justifying the equiv relationship

(defoption maybe-a2a-info a2a-info-p)

(defalist alist-info
  :key-type symbolp ;; the alist type recognizer
  :val-type a2a-info-p
  :true-listp t)

(defthm assoc-equal-of-alist-info-p
  (implies (and (alist-info-p ai)
                (assoc-equal x ai))
           (consp (assoc-equal x ai))))

(defthm maybe-of-assoc-equal-of-alist-info-p
  (implies (alist-info-p ai)
           (maybe-a2a-info-p (cdr (assoc-equal x ai)))))

(defthm a2a-of-assoc-equal-of-alist-info-p
  (implies (and (alist-info-p ai)
                (assoc-equal x ai))
           (a2a-info-p (cdr (assoc-equal x ai)))))

(defprod equiv
  ((formal-map symbol-symbol-alistp)
   (thm symbolp)))

(defthm strip-cars-of-equiv->formal-map
  (implies (equiv-p x)
           (symbol-listp (strip-cars (equiv->formal-map x)))))

(defalist alist-array-map
  :key-type symbolp ;; function name
  :val-type equiv-p ;; equivalence theorem name
  :true-listp t)

(defthm assoc-equal-of-alist-array-map-p
  (implies (and (alist-array-map-p aa)
                (assoc-equal x aa))
           (and (consp (assoc-equal x aa))
                (equiv-p (cdr (assoc-equal x aa))))))
)

(encapsulate ()
  (local (in-theory (disable (:rewrite default-cdr)
                             (:rewrite consp-of-pseudo-lambdap)
                             (:rewrite
                              acl2::pseudo-lambdap-of-car-when-pseudo-termp)
                             (:definition pseudo-termp)
                             (:rewrite
                              acl2::true-listp-of-car-when-true-list-listp)
                             (:definition true-list-listp)
                             (:rewrite
                              acl2::true-list-listp-of-cdr-when-true-list-listp)
                             (:definition true-listp)
                             (:definition symbol-listp))))

(defprod type-options
  ((supertype type-to-types-alist-p)
   (subtype type-to-types-alist-p)
   (functions function-description-alist-p)
   (nil-alst symbol-symbol-alistp)  ;; map from type recognizers to its nil-fn
   (alist alist-info-p)
   (aa-map alist-array-map-p)))
)

(define is-type? ((type symbolp)
                  (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (b* ((supertype-alst (type-to-types-alist-fix supertype-alst))
       (type (symbol-fix type)))
    (not (null (assoc-equal type supertype-alst)))))

(define is-alist? ((type symbolp)
                   (options type-options-p))
  :returns (a2a maybe-a2a-info-p)
  (b* ((options (type-options-fix options))
       ((type-options to) options)
       (yes? (assoc-equal type to.alist)))
    (cdr yes?)))

(define construct-type-options ((smtlink-hint smtlink-hint-p))
  :returns (type-options type-options-p)
  :irrelevant-formals-ok t
  :ignore-ok t
  (b* ((smtlink-hint (smtlink-hint-fix smtlink-hint)))
    (make-type-options)))

(defprod type-inference-hints
  ((type-options type-options-p)
   (names symbol-listp)))

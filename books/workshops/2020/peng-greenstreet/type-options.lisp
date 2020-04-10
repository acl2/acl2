;; Copyright (C) 2019, University of British Columbia
;; Written by Yan Peng (December 30th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "centaur/fty/top" :dir :system)

(include-book "./utils/pseudo-term")
(include-book "./utils/basics")

(fty::defalist type-to-types-alist
  :key-type symbolp
  :val-type symbol-listp
  :true-listp t)

(defthm assoc-equal-of-type-to-types-alist
  (implies (and (type-to-types-alist-p x)
                (assoc-equal y x))
           (consp (assoc-equal y x))))

(fty::defprod type-tuple
  ((type symbolp)
   (neighbour-type symbolp)))

(fty::defalist type-tuple-to-thm-alist
  :key-type type-tuple-p
  :val-type symbolp
  :true-listp t)

(defthm assoc-equal-of-type-tuple-to-thm-alist
  (implies (and (type-tuple-to-thm-alist-p x)
                (assoc-equal y x))
           (and (consp (assoc-equal y x))
                (symbolp (cdr (assoc-equal y x))))))

(fty::defprod return-spec
  ((formals symbol-listp)
   (return-type symbolp)
   (returns-thm symbolp)
   (replace-thm symbolp)))

(fty::deflist return-spec-list
  :elt-type return-spec-p
  :true-listp t)

(fty::deftypes function-description
  (fty::deftagsum arg-decl
    (:next ((next arg-check-p)))
    (:done ((r return-spec-p))))
  (fty::defalist arg-check
    :key-type symbolp
    :val-type arg-decl-p))

(fty::defalist function-description-alist
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

(fty::defprod a2a-info
  ((a2a-fn symbolp) ;; the alist-to-array function
   (thm symbolp))) ;; the theorem justifying the return type of alist-to-array

(fty::defoption maybe-a2a-info a2a-info-p)

(fty::defalist alist-info
  :key-type symbolp ;; the alist type recognizer
  :val-type a2a-info-p
  :true-listp t)

(defthm assoc-equal-of-alist-info-p
  (implies (and (alist-info-p ai)
                (assoc-equal x ai))
           (and (consp (assoc-equal x ai)))))

(defthm maybe-of-assoc-equal-of-alist-info-p
  (implies (alist-info-p ai)
           (maybe-a2a-info-p (cdr (assoc-equal x ai)))))

(fty::defprod equiv-p
  ((formal-map symbol-alistp)
   (thm symbolp)))

(fty::defalist alist-array-map
  :key-type symbolp ;; function name
  :val-type equiv-p ;; equivalence theorem name
  :true-listp t)
)

(encapsulate ()
  (local (in-theory (disable (:rewrite default-cdr)
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

(fty::defprod type-options
  ((supertype type-to-types-alist-p)
   (supertype-thm type-tuple-to-thm-alist-p)
   (subtype type-to-types-alist-p)
   (subtype-thm type-tuple-to-thm-alist-p)
   (functions function-description-alist-p)
   (alist alist-info-p)
   (aa-map alist-array-map-p)))
)

(define is-type? ((type symbolp)
                  (supertype-alst type-to-types-alist-p))
  :returns (ok booleanp)
  (not (null (assoc-equal type (type-to-types-alist-fix supertype-alst)))))

(define is-alist? ((type symbolp)
                   (options type-options-p))
  :returns (a2a maybe-a2a-info-p)
  (b* ((options (type-options-fix options))
       ((type-options to) options)
       (yes? (assoc-equal type to.alist)))
    (cdr yes?)))

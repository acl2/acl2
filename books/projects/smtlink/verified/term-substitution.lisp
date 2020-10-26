;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (December 23rd 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "ordinals/lexicographic-ordering-without-arithmetic" :dir :system)
(include-book "kestrel/std/system/dumb-occur-var-open" :dir :system)

(include-book "../utils/pseudo-term")
(include-book "evaluator")

(define dumb-occur-vars-or ((var-lst symbol-listp)
                            (term pseudo-termp))
  :returns (occur? booleanp)
  :measure (len var-lst)
  (b* ((var-lst (symbol-list-fix var-lst))
       ((unless (consp var-lst)) nil)
       ((cons first-var rest-vars) var-lst))
    (or (acl2::dumb-occur-var-open first-var term)
        (dumb-occur-vars-or rest-vars term))))

(local
(defthm acl2-count-of-car-of-pseudo-term-list-fix
  (implies (consp (pseudo-term-list-fix term-lst))
           (< (acl2-count (pseudo-term-fix (car (pseudo-term-list-fix term-lst))))
              (acl2-count (pseudo-term-list-fix term-lst))))
  :hints (("Goal" :in-theory (enable pseudo-term-list-fix
                                     pseudo-term-fix))))
)

(local
 (defthm acl2-count-of-cadr-of-pseudo-term-fix
   (implies (equal (len (cdr (pseudo-term-fix term))) 3)
            (< (acl2-count (pseudo-term-fix (cadr (pseudo-term-fix term))))
               (1+ (acl2-count (cdr (pseudo-term-fix term))))))
   :hints (("Goal" :in-theory (enable pseudo-term-fix))))
 )

(local
 (defthm acl2-count-of-caddr-of-pseudo-term-fix
   (implies (equal (len (cdr (pseudo-term-fix term))) 3)
            (< (acl2-count (pseudo-term-fix (caddr (pseudo-term-fix term))))
               (1+ (acl2-count (cdr (pseudo-term-fix term))))))
   :hints (("Goal" :in-theory (enable pseudo-term-fix))))
 )

(local
 (defthm pseudo-term-listp-of-cdddr-symbolp
   (implies (and (equal (len (cdr (pseudo-term-fix term))) 3)
                 (symbolp (car (pseudo-term-fix term))))
            (pseudo-term-listp (cdddr (pseudo-term-fix term))))
   :hints (("Goal" :in-theory (enable pseudo-term-fix pseudo-termp)))))

(local
 (defthm pseudo-termp-of-assoc-equal-from-pseudo-term-alistp
   (implies (and (pseudo-term-alistp sub-alst)
                 (assoc-equal x sub-alst))
            (pseudo-termp (cdr (assoc-equal x sub-alst))))
   :hints (("Goal" :in-theory (enable pseudo-term-alistp)))))


(define shadow-sub-alst ((formals symbol-listp)
                         (sub-alst pseudo-term-alistp))
  :returns (new-alst pseudo-term-alistp)
  :measure (len (pseudo-term-alist-fix sub-alst))
  (b* ((formals (symbol-list-fix formals))
       (sub-alst (pseudo-term-alist-fix sub-alst))
       ((unless (consp sub-alst)) nil)
       ((cons (cons subst-term subst) rest-alst) sub-alst)
       (yes? (dumb-occur-vars-or formals subst-term))
       ((if yes?) (shadow-sub-alst formals rest-alst)))
    (acons subst-term subst (shadow-sub-alst formals rest-alst))))

(defines term-substitution
  :well-founded-relation l<
  :verify-guards nil
  :hints (("Goal" :in-theory (disable len)))

  (define term-substitution ((term pseudo-termp)
                             (sub-alst pseudo-term-alistp)
                             (skip-conj booleanp))
    :returns (substed-term pseudo-termp)
    :short "Substitute subterm in term with subst."
    :measure (acl2-count (pseudo-term-fix term))
    (b* ((term (pseudo-term-fix term))
         (sub-alst (pseudo-term-alist-fix sub-alst))
         ((if (assoc-equal term sub-alst)) (cdr (assoc-equal term sub-alst)))
         ((if (acl2::variablep term)) term)
         ((if (acl2::fquotep term)) term)
         ((cons fn actuals) term)
         ((if (and skip-conj
                   (equal fn 'if)
                   (equal (len actuals) 3)
                   (equal (cadr actuals) ''t)
                   (equal (caddr actuals) ''nil)))
          `(,fn ,(term-substitution (car actuals) sub-alst skip-conj)
                ,@(cdr actuals)))
         ((if (and skip-conj
                   (equal fn 'if)
                   (equal (len actuals) 3)
                   (equal (caddr actuals) ''nil)))
          `(,fn ,(term-substitution (car actuals) sub-alst skip-conj)
                ,(term-substitution (cadr actuals) sub-alst skip-conj)
                ,(caddr actuals)))
         ((if (pseudo-lambdap fn))
          (b* ((formals (lambda-formals fn))
               ((unless (mbt (equal (len formals) (len actuals)))) nil)
               (actuals-substed
                (term-substitution-list actuals sub-alst skip-conj))
               ((unless (mbt (equal (len formals) (len actuals-substed))))
                nil)
               (shadowed-sub-alst (shadow-sub-alst formals sub-alst))
               (body (lambda-body fn))
               (body-substed
                (term-substitution body shadowed-sub-alst skip-conj))
               (new-fn `(lambda ,formals ,body-substed)))
            `(,new-fn ,@actuals-substed))))
      `(,fn ,@(term-substitution-list actuals sub-alst skip-conj))))

  (define term-substitution-list ((term-lst pseudo-term-listp)
                                  (sub-alst pseudo-term-alistp)
                                  (skip-conj booleanp))
    :returns (substed-term-lst pseudo-term-listp)
    :measure (acl2-count (pseudo-term-list-fix term-lst))
    (b* ((term-lst (pseudo-term-list-fix term-lst))
         ((unless (consp term-lst)) nil)
         ((cons first-term rest-terms) term-lst))
      (cons (term-substitution first-term sub-alst skip-conj)
            (term-substitution-list rest-terms sub-alst skip-conj))))
  )

(defthm term-substitution-list-maintain-length
  (implies (and (pseudo-term-listp term-lst)
                (pseudo-term-alistp sub-alst))
           (equal (len (term-substitution-list term-lst sub-alst conj))
                  (len term-lst)))
  :hints (("Goal"
           :in-theory (enable term-substitution term-substitution-list)
           :expand (term-substitution-list term-lst sub-alst conj))))

(verify-guards term-substitution)

(skip-proofs
 (defthm correctness-of-term-substitution
   (implies (and (ev-smtcp-meta-extract-global-facts)
                 (pseudo-termp term)
                 (alistp a)
                 (ev-smtcp term a))
            (ev-smtcp (term-substitution term sub-alst skip-conj) sub-alst))))

(define term-substitution-linear ((term-lst pseudo-term-listp)
                                  (subterm-lst pseudo-term-listp)
                                  (subst-lst pseudo-term-listp)
                                  (skip-conj booleanp))
  :returns (substed-term-lst pseudo-term-listp)
  (b* ((term-lst (pseudo-term-list-fix term-lst))
       (subterm-lst (pseudo-term-list-fix subterm-lst))
       (subst-lst (pseudo-term-list-fix subst-lst))
       ((unless (consp term-lst)) nil)
       ((unless (consp subterm-lst)) nil)
       ((unless (consp subst-lst)) nil)
       ((cons term-hd term-tl) term-lst)
       ((cons subterm-hd subterm-tl) subterm-lst)
       ((cons subst-hd subst-tl) subst-lst))
    (cons (term-substitution term-hd `((,subterm-hd . ,subst-hd)) skip-conj)
          (term-substitution-linear term-tl subterm-tl subst-tl skip-conj))))

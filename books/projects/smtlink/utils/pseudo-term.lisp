;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (June 25th 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;
(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "pseudo-lambda")

(set-induction-depth-limit 1)

; The worst offenders for useless runes
(local (in-theory (disable
  true-list-listp member-equal
  acl2::symbol-listp-of-cdr-when-symbol-listp
  acl2::pseudo-lambdap-of-car-when-pseudo-lambda-listp 
  acl2::pseudo-lambdap-when-member-equal-of-pseudo-lambda-listp
  ;acl2::pseudo-term-listp-of-cdr-when-pseudo-term-listp
  acl2::pseudo-lambda-listp-of-cdr-when-pseudo-lambda-listp
  acl2::true-list-listp-of-cdr-when-true-list-listp
  acl2::true-list-listp-when-not-consp
  acl2::subsetp-when-atom-right
  set::sets-are-true-lists-cheap
  )))

(define pseudo-term-fix ((x pseudo-termp))
  :returns (fixed pseudo-termp)
  (mbe :logic (if (pseudo-termp x) x nil)
       :exec x)
  ///
  (more-returns
   (fixed (implies (pseudo-termp x) (equal fixed x))
          :name equal-fixed-and-x-of-pseudo-termp)))

(defthm pseudo-term-fix-idempotent-lemma
  (equal (pseudo-term-fix (pseudo-term-fix x))
         (pseudo-term-fix x))
  :hints (("Goal" :in-theory (enable pseudo-term-fix))))

(deffixtype pseudo-term
  :fix pseudo-term-fix
  :pred pseudo-termp
  :equiv pseudo-term-equiv
  :define t
  :forward t
  :topic pseudo-termp)

(deflist pseudo-term-list
  :pred pseudo-term-listp
  :elt-type pseudo-termp
  :true-listp t)

(defthm pseudo-term-listp-of-symbol-listp
  (implies (symbol-listp x) (pseudo-term-listp x)))

(defthm pseudo-termp-of-fncall
  (implies (and (symbolp fn) (pseudo-termp x))
           (pseudo-termp (list fn x)))
  :hints (("Goal" :in-theory (enable pseudo-termp
                                     pseudo-term-listp))))

(defthmd symbolp-of-fn-call-of-pseudo-termp
  (implies (and (pseudo-termp x)
                (consp x)
                (not (acl2::fquotep x))
                (not (pseudo-lambdap (car x))))
           (symbolp (car x)))
  :hints (("Goal" :in-theory (enable pseudo-lambdap))))

(defthm pseudo-lambdap-of-fn-call-of-pseudo-termp
  (implies (and (pseudo-termp x)
                (consp x)
                (not (acl2::fquotep x))
                (not (symbolp (car x))))
           (pseudo-lambdap (car x)))
  :hints (("Goal" :in-theory (enable pseudo-lambdap))))

(defthmd pseudo-term-listp-of-cdr-pseudo-termp
  (implies (and (pseudo-termp term)
                (consp term)
                (not (equal (car term) 'quote)))
           (pseudo-term-listp (cdr term)))
  :hints (("Goal" :in-theory (enable pseudo-termp))))

(defthmd pseudo-term-listp-of-cdr-pseudo-termp-if
  (implies (and (pseudo-termp term)
                (consp term)
                (equal (car term) 'if))
           (pseudo-term-listp (cdr term)))
  :hints (("Goal" :in-theory (enable pseudo-termp))))

(defthmd pseudo-termp-of-car-of-pseudo-term-listp
  (implies (and (pseudo-term-listp term)
                (consp term))
           (pseudo-termp (car term))))

(defthm pseudo-term-listp-of-cdr-of-pseudo-termp
  (implies (and (pseudo-termp term)
                (consp term)
                (pseudo-lambdap (car term)))
           (and (true-listp (cdr term))
                (pseudo-term-listp (cdr term)))))

;(define pseudo-term-list-list-fix ((x pseudo-term-list-listp))
;  :returns (fixed pseudo-term-list-listp)
;  (mbe :logic (if (consp x)
;                  (cons (pseudo-term-list-fix (car x))
;                        (pseudo-term-list-list-fix (cdr x)))
;                nil)
;       :exec x))
;
;(defthm pseudo-term-list-list-fix-idempotent-lemma
;  (equal (pseudo-term-list-list-fix (pseudo-term-list-list-fix x))
;         (pseudo-term-list-list-fix x))
;  :hints (("Goal" :in-theory (enable pseudo-term-list-list-fix))))

(deflist pseudo-term-list-list
  :pred pseudo-term-list-listp
  :elt-type pseudo-term-listp)

(defalist pseudo-term-alist
  :key-type pseudo-term
  :val-type pseudo-term
  :pred pseudo-term-alistp
  :true-listp t)
;(local (in-theory (disable
;  pseudo-termp-of-caar-when-pseudo-term-alistp
;  pseudo-termp-of-cdar-when-pseudo-term-alistp
;  )))

(defthm pseudo-term-alistp-of-pairlis$-of-symbol-listp-and-pseudo-term-listp
  (implies (and (symbol-listp y)
                (pseudo-term-listp x))
           (pseudo-term-alistp (pairlis$ y x))))

(defthm pseudo-term-alistp-of-pairlis$-of-pseudo-term-listp-and-symbol-listp
  (implies (and (symbol-listp y)
                (pseudo-term-listp x))
           (pseudo-term-alistp (pairlis$ x y))))

(defthm nil-of-assoc-equal-of-pseudo-term-alistp
  (implies (and (pseudo-term-alistp x) (not (consp (assoc-equal y x))))
           (not (assoc-equal y x))))

(defalist pseudo-term-integer
  :key-type pseudo-termp
  :val-type integerp
  :true-listp t
  :pred pseudo-term-integerp)

(defthm assoc-equal-of-pseudo-term-integerp
  (implies (and (pseudo-term-integerp x)
                (assoc-equal y x))
           (integerp (cdr (assoc-equal y x)))))

(defalist symbol-pseudo-term-alist
  :key-type symbolp
  :val-type pseudo-termp
  :pred symbol-pseudo-term-alistp
  :true-listp t)
;(local (in-theory (disable symbolp-of-caar-when-symbol-pseudo-term-alistp)))

(defthm assoc-equal-of-symbol-pseudo-term-alist
  (implies (and (symbol-pseudo-term-alistp alst)
                (assoc-equal x alst))
           (pseudo-termp (cdr (assoc-equal x alst)))))

;; -------------------------------------------
;; acl2-count theorems

(defthm acl2-count-of-lambda-body
  (implies (and (pseudo-termp term)
                (consp term)
                (pseudo-lambdap (car term)))
           (< (acl2-count (pseudo-term-fix (caddr (car term))))
              (acl2-count term)))
  :hints (("Goal" :in-theory (e/d (pseudo-lambdap)
                                  (lambda-of-pseudo-lambdap
                                   pseudo-termp
                                   pseudo-term-listp
                                   acl2-count
                                   symbol-listp
                                   consp-of-pseudo-lambdap)))))

(defthm acl2-count-of-if-cond
  (implies (and (pseudo-termp term)
                (consp term)
                (equal (car term) 'if)
                (equal (len (cdr term)) 3))
           (< (acl2-count (pseudo-term-fix (cadr term)))
              (+ 1 (acl2-count (cdr term))))))

(defthm acl2-count-of-if-then
  (implies (and (pseudo-termp term)
                (consp term)
                (equal (car term) 'if)
                (equal (len (cdr term)) 3))
           (< (acl2-count (pseudo-term-fix (caddr term)))
              (+ 1 (acl2-count (cdr term))))))

(defthm acl2-count-of-if-else
  (implies (and (pseudo-termp term)
                (consp term)
                (equal (car term) 'if)
                (equal (len (cdr term)) 3))
           (< (acl2-count (pseudo-term-fix (cadddr term)))
              (+ 1 (acl2-count (cdr term))))))

(defthm acl2-count-of-pseudo-term-listp
  (implies (and (pseudo-term-listp term-lst)
                (consp term-lst))
           (< (acl2-count (pseudo-term-fix (car term-lst)))
              (acl2-count term-lst))))


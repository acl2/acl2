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

(defthm pseudo-term-listp-of-symbol-listp
  (implies (symbol-listp x) (pseudo-term-listp x)))

(defthm pseudo-termp-of-fncall
  (implies (and (symbolp fn) (pseudo-termp x))
           (pseudo-termp (list fn x)))
  :hints (("Goal" :in-theory (enable pseudo-termp
                                     pseudo-term-listp))))

(defthm symbolp-of-fn-call-of-pseudo-termp
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

(define pseudo-term-list-fix ((x pseudo-term-listp))
  :returns (new-x pseudo-term-listp)
  (mbe :logic (if (consp x)
                  (cons (pseudo-term-fix (car x))
                        (pseudo-term-list-fix (cdr x)))
                nil)
       :exec x)
  ///
  (more-returns
   (new-x (<= (acl2-count new-x) (acl2-count x))
          :name acl2-count-<=-pseudo-term-list-fix
          :rule-classes :linear
          :hints (("Goal" :in-theory (enable pseudo-term-fix))))
   (new-x (implies (pseudo-term-listp x)
                   (equal new-x x))
          :name equal-pseudo-term-list-fix)
   (new-x (implies (pseudo-term-listp x)
                   (equal (len new-x) (len x)))
          :name len-equal-pseudo-term-list-fix
          :rule-classes :linear)))

(defthm pseudo-term-list-fix-idempotent-lemma
  (equal (pseudo-term-list-fix (pseudo-term-list-fix x))
         (pseudo-term-list-fix x))
  :hints (("Goal" :in-theory (enable pseudo-term-list-fix))))

(deffixtype pseudo-term-list
  :fix pseudo-term-list-fix
  :pred pseudo-term-listp
  :equiv pseudo-term-list-equiv
  :define t)

(defthm pseudo-term-listp-of-cdr-pseudo-termp
  (implies (and (pseudo-termp term)
                (consp term)
                (not (equal (car term) 'quote)))
           (pseudo-term-listp (cdr term)))
  :hints (("Goal" :in-theory (enable pseudo-termp))))

(defthm pseudo-term-listp-of-cdr-pseudo-termp-if
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

(defthm consp-of-pseudo-term-list-fix
  (implies (consp x)
           (consp (pseudo-term-list-fix x)))
  :hints(("Goal" :expand (pseudo-term-list-fix x))))

(defthm null-of-pseudo-term-list-fix
  (implies (not (consp x))
           (equal (pseudo-term-list-fix x) nil))
  :hints(("Goal" :expand (pseudo-term-list-fix x))))

(define pseudo-term-list-list-fix ((x pseudo-term-list-listp))
  :returns (fixed pseudo-term-list-listp)
  (mbe :logic (if (consp x)
                  (cons (pseudo-term-list-fix (car x))
                        (pseudo-term-list-list-fix (cdr x)))
                nil)
       :exec x))

(defthm pseudo-term-list-list-fix-idempotent-lemma
  (equal (pseudo-term-list-list-fix (pseudo-term-list-list-fix x))
         (pseudo-term-list-list-fix x))
  :hints (("Goal" :in-theory (enable pseudo-term-list-list-fix))))

(deffixtype pseudo-term-list-list
  :fix pseudo-term-list-list-fix
  :pred pseudo-term-list-listp
  :equiv pseudo-term-list-list-equiv
  :define t
  :forward t
  :topic pseudo-term-list-listp)

(defalist pseudo-term-alist
  :key-type pseudo-term
  :val-type pseudo-term
  :pred pseudo-term-alistp
  :true-listp t)

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


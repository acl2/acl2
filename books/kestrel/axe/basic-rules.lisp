; Basic Axe rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/if" :dir :system)

;; TODO: Rephrase some of these

;;theorems about built-in ACL2 functions.  Many of these are things that ACL2
;;knows by type reasoning (but Axe does not have type reasoning).

(defthm rationalp-of-len
  (equal (rationalp (len x))
         t))

(defthm eql-becomes-equal
  (equal (eql x y)
         (equal x y)))

(defthm nfix-does-nothing
  (implies (natp n)
           (equal (nfix n)
                  n)))

(defthm acl2-numberp-of-*
  (equal (acl2-numberp (* x y))
         t))

(defthm acl2-numberp-of-unary--
  (equal (acl2-numberp (unary-- x))
         t))

;move?
(defthm if-of-non-nil
  (implies (not (equal test nil))
           (equal (if test b c)
                  b))
  :rule-classes nil)

;move? ;rename?
;for axe
(defthmd if-thm
  (equal (if (if x x t) y z)
         y))

(defthm natp-of-len
  (equal (natp (len x))
         t))

(defthm acl2-numberp-of-len
  (equal (acl2-numberp (len x))
         t))

(defthm acl2-numberp-of-+
  (equal (acl2-numberp (+ x y))
         t))

(defthm booleanp-of-iff
  (equal (booleanp (iff x y))
         t))

(defthm booleanp-of-not
  (equal (booleanp (not x))
         t))

(defthm booleanp-of-equal
  (equal (booleanp (equal x y))
         t))

(defthm booleanp-of-<
  (equal (booleanp (< x y))
         t))

(defthm booleanp-of-natp
  (equal (booleanp (natp x))
         t))

(defthm booleanp-of-integerp
  (equal (booleanp (integerp x))
         t))

(defthm booleanp-of-rationalp
  (equal (booleanp (rationalp x))
         t))

(defthm booleanp-of-acl2-numberp
  (equal (booleanp (acl2-numberp x))
         t))

(defthm booleanp-of-consp
  (equal (booleanp (consp x))
         t))

(defthm booleanp-of-true-listp
  (equal (booleanp (true-listp a))
         t))

(defthm booleanp-of-endp
  (equal (booleanp (endp x))
         t))


(in-theory (disable add-to-set-eql)) ;new

(defthm true-listp-of-add-to-set-eql
  (implies (true-listp lst)
           (true-listp (add-to-set-eql x lst)))
  :hints (("Goal" :in-theory (enable add-to-set-eql))))

(defthm eqlable-listp-of-add-to-set-eql
  (implies (and (eqlablep x)
                (eqlable-listp lst))
           (eqlable-listp (add-to-set-eql x lst)))
  :hints (("Goal" :in-theory (enable add-to-set-eql))))

(defthm <-of-max-same
  (not (< (max x y) x)))

(defthm <-of-max-same2
  (not (< (max y x) x)))

(defthm plist-worldp-of-w
  (implies (state-p state)
           (plist-worldp (w state)))
  :hints (("Goal" :in-theory (enable state-p w))))

(defthm fix-when-acl2-numberp
  (implies (acl2-numberp x)
           (equal (fix x)
                  x)))

(defthm acl2-numberp-of-fix
  (equal (acl2-numberp (fix x))
         t))

(defthm equal-same
  (equal (equal x x)
         t))

;rename and rephrase
;; Only needed for Axe, since ACL2 knows this by type reasoning.
;drop if we are commuting?
(defthm equal-cons-nil-1
  (equal (equal (cons a b) nil)
         nil))

;rename and rephrase
;; Only needed for Axe, since ACL2 knows this by type reasoning.
(defthm equal-cons-nil-2
  (equal (equal nil (cons a b))
         nil))

(defthm integer-listp-of-update-nth
  ;; [Jared] updated to match std/lists
  (implies (integer-listp (double-rewrite x))
           (iff (integer-listp (update-nth n y x))
                (and (integerp y)
                     (or (<= (nfix n) (len x))
                         (integerp nil))))) ;; bozo yuck
  :hints (("Goal" :in-theory (enable update-nth))))

;the LHS is unusual in that the nil is not commuted forward.
;however, this can occur when axe improves invariants (it does not turn around equalities)
(defthm equal-of-not-and-nil
  (implies (booleanp x)
           (equal (equal (not x) nil)
                  x)))

;todo: require that y is not a constant?!
(defthmd turn-equal-around-axe
  (implies (syntaxp (quotep x))
           (equal (equal y x)
                  (equal x y))))

;; (defthmd turn-equal-around-axe2
;;   (implies (syntaxp (quotep y))
;;            (equal (equal y x)
;;                   (equal x y))))

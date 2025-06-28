; Basic Axe rules
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2025 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/utilities/if" :dir :system)
(include-book "kestrel/booleans/bool-fix-def" :dir :system)

;; TODO: Rephrase some of these

;;theorems about built-in ACL2 functions.  Many of these are things that ACL2
;;knows by type reasoning (but Axe does not have type reasoning).

(defthmd rationalp-of-len
  (rationalp (len x)))

(defthm nfix-does-nothing
  (implies (natp n)
           (equal (nfix n)
                  n)))

(defthmd acl2-numberp-of-*
  (acl2-numberp (* x y)))

(defthmd acl2-numberp-of-unary--
  (acl2-numberp (unary-- x)))

(defthmd natp-of-len
  (natp (len x)))

(defthmd acl2-numberp-of-len
  (acl2-numberp (len x)))

(defthmd acl2-numberp-of-+
  (acl2-numberp (+ x y)))

(defthmd acl2-numberp-of--
  (acl2-numberp (- x)))

(defthmd booleanp-of-not
  (booleanp (not x)))

(defthmd booleanp-of-equal
  (booleanp (equal x y)))

(defthmd booleanp-of-iff
  (booleanp (iff x y)))

(defthmd booleanp-of-<
  (booleanp (< x y)))

(defthmd booleanp-of-bitp
  (booleanp (bitp x)))

(defthmd booleanp-of-natp
  (booleanp (natp x)))

(defthmd booleanp-of-integerp
  (booleanp (integerp x)))

(defthmd booleanp-of-rationalp
  (booleanp (rationalp x)))

(defthmd booleanp-of-acl2-numberp
  (booleanp (acl2-numberp x)))

(defthmd booleanp-of-consp
  (booleanp (consp x)))

(defthmd booleanp-of-true-listp
  (booleanp (true-listp a)))

(defthmd booleanp-of-endp
  (booleanp (endp x)))


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

(defthmd acl2-numberp-of-fix
  (acl2-numberp (fix x)))

(defthmd integerp-of-ifix
  (integerp (ifix x)))

;; Can't phrase this as just (equal x x), as that is not a legal rewrite rule.
(defthmd equal-same
  (equal (equal x x)
         t))

;rename and rephrase
;; Only needed for Axe, since ACL2 knows this by type reasoning.
;drop if we are commuting?
(defthmd equal-cons-nil-1
  (equal (equal (cons a b) nil)
         nil))

;rename and rephrase
;; Only needed for Axe, since ACL2 knows this by type reasoning.
(defthmd equal-cons-nil-2
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
(defthmd equal-of-not-and-nil
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

;; Since Axe doesn't have force
(defthm force-of-non-nil
  (implies x
           (equal (force x)
                  x)))

;; Can help when opening up reverse
(defthmd not-stringp-of-cons
  (not (stringp (cons x y))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The name is to avoid a conflict with a (probably unnecessary)
;; :type-prescrpiption rule in centaur/fty/basetypes.lisp.
(defthmd booleanp-of-bool-fix-rewrite
  (booleanp (bool-fix x)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Can help resolve whethere there is an error, when the error is a cons and nil means no error
(defthmd not-of-cons
  (equal (not (cons x y))
         nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Probably only needed for Axe
(defthmd acl2-numberp-when-signed-byte-p
  (implies (signed-byte-p size x) ; size is a free var
           (acl2-numberp x)))

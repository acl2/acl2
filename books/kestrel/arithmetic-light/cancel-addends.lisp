; A scheme for cancelling common addends using rewriting
;
; Copyright (C) 2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book contains a scheme for cancelling common addends from equalities of
;; sums using rewriting.  This would be useful if we can't use a :meta rule.
;; For example, an Axe-variant of this scheme would be useful, since Axe doesn't
;; have :meta rules (but note that the syntaxp and bind-free functions will need
;; Axe versions).  This scheme assumes that each + nest has been associated to the
;; right.

;; Overview:
;; 1. Identify a common addend to be cancelled.
;; 2. Add the negation of the common addend to both sides, but use a special function, cancel-in-sum.
;; 3. Rewrite to push the cancel-in-sum inward on each side until it reaches
;; the addend to cancel.  Additional rules then do the cancellation.

;; See cancel-addends-tests.lisp.

;; TODO: What if the nest is not associated?  Generalize this scheme to use
;; the location (within the + nest) of the term to cancel.

;; Gets all the addends from a right-associated nest of calls to +.
(defun strip-addends (term)
  (declare (xargs :guard (pseudo-termp term)))
  (if (and (consp term)
           (eq 'binary-+ (ffn-symb term))
           (consp (rest term))
           (consp (rest (rest term))))
      (cons (fargn term 1)
            (strip-addends (fargn term 2)))
      ;; Not a call of +, so the whole term is the addend:
      (list term)))

;; Finds one common added of TERM1 and TERM2, which should be right-associated + nests.
;; Returns an alist suitable for bind-free, or nil is there is no common addend.
;; todo: require at least one to be a call of binary-+?
;; todo: optimize when only one is call of binary-+?
(defun find-common-addend (term1 term2)
  (declare (xargs :guard (and (pseudo-termp term1)
                              (pseudo-termp term2))))
  (let ((common-addends (intersection-equal (strip-addends term1) (strip-addends term2))))
    (if common-addends
        (acons 'addend (first common-addends) nil)
        nil)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Logically, this is Y-X.  Functionally, it gets pushed inward until it
;; reaches an occurrence of X, which it then causes to be removed from the sum.
(defund cancel-in-sum (x y)
  (declare (xargs :guard (and (acl2-numberp x)
                              (acl2-numberp y))))
  (+ (- x) y))

;; The main rule for EQUAL
;; Finds a common addend and introduces cancel-in-sum to cancel it from both sides.
(defthm cancel-common-addend-in-equal
    (implies (and (bind-free (find-common-addend x y) (addend))
                  (acl2-numberp x)
                  (acl2-numberp y))
             (equal (equal x y)
                    (equal (cancel-in-sum addend x) (cancel-in-sum addend y))))
  :hints (("Goal" :in-theory (enable cancel-in-sum))))

;; The main rule for <
;; Finds a common addend and introduces cancel-in-sum to cancel it from both sides.
(defthm cancel-common-addend-in-<
    (implies (and (bind-free (find-common-addend x y) (addend))
                  (acl2-numberp x)
                  (acl2-numberp y))
             (equal (< x y)
                    (< (cancel-in-sum addend x) (cancel-in-sum addend y))))
  :hints (("Goal" :cases ((< X Y))
                  :in-theory (enable cancel-in-sum))))

;; We want to cancel an X, but Y is a different term, so keep pusing inward.
(defthm cancel-in-sum-of-+-diff
    (implies (syntaxp (not (equal x y)))
             (equal (cancel-in-sum x (+ y z))
                    (+ y (cancel-in-sum x z))))
  :hints (("Goal" :in-theory (enable cancel-in-sum))))

;; We've found an X to cancel (first variant).
;; todo: might ACL2 ever match this when the xs are not syntactically identical?
;; todo: avoid introducing the 0 when we can?
(defthm cancel-in-sum-same
    (equal (cancel-in-sum x x)
           0)
  :hints (("Goal" :in-theory (enable cancel-in-sum))))

;; We've found an X to cancel (second variant).
;; todo: avoid introducing the fix when we can?
(defthm cancel-in-sum-of-+-same
    (equal (cancel-in-sum x (+ x y))
           (fix y))
  :hints (("Goal" :in-theory (enable cancel-in-sum))))

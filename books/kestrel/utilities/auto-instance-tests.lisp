; auto-instance -- Tests
;
; Copyright (C) 2018, Regents of the University of Texas
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author:
;   Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "auto-instance")

; We use assert! instead of assert-event, because :program-mode functions such
; as previous-subsumer-hints run slowly in safe-mode, and assert-event does its
; evaluation in safe-mode.
(include-book "misc/assert" :dir :system)

; For testing:
(include-book "misc/eval" :dir :system)

; We include the following books in order to add more theorems to the world.
(include-book "kestrel/utilities/lists/intersection-theorems" :dir :system)
(include-book "std/lists/union" :dir :system)

(defmacro local-test (&rest args)
  `(local (encapsulate () (local (progn ,@args)))))

; The following utility provides an easy way to translate a term.
(defun easy-trans (x state)
  (declare (xargs :mode :program :stobjs state))
  (mv-let (erp val)
    (translate-cmp x
                   t ; stobjs-out
                   t ; logic-modep
                   t ; known-stobjs
                   'easy-trans ; ctx
                   (w state)
                   (default-state-vars t))
    (cond (erp (er hard erp "~@0" val))
          (t val))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The first test shows generation of a :by hint.

(assert!
 (equal (previous-subsumer-hints
         '(implies (true-listp b)
                   (true-listp (union-equal a b)))
         (w state))
        '(:BY TRUE-LISTP-OF-UNION-EQUAL-TYPE :DO-NOT *ALL-BUT-SIMPLIFY*)))

(local-test
 (defthm<w true-listp-of-union-equal-type-again
   (implies (true-listp b)
            (true-listp (union-equal a b)))
; By default, hints are ignored by defthm<w.
   :hints (("Goal" :in-theory nil))
   :rule-classes nil)
; Check redundancy:
 (defthm<w true-listp-of-union-equal-type-again
   (implies (true-listp b)
            (true-listp (union-equal a b)))
   :rule-classes nil))

; We can check the hints another way (see the call of previous-subsumer-hints
; above for the first way), as follows.
(must-succeed ; with :prove nil, we just get the hints
 (er-let* ((hints (defthm<w true-listp-of-union-equal-type-again
                    (implies (true-listp b)
                             (true-listp (union-equal a b)))
; By default, hints are ignored by defthm<w.
                    :hints (("Goal" :in-theory nil))
                    :rule-classes nil
                    :prove nil)))
   (value
    (equal hints
           '(:BY TRUE-LISTP-OF-UNION-EQUAL-TYPE :DO-NOT *ALL-BUT-SIMPLIFY*)))))

;;; Again, but create an enabled rewrite rule:
(local-test
 (defthm<w true-listp-of-union-equal-type-again
   (implies (true-listp b)
            (true-listp (union-equal a b)))
; By default, hints are ignored by defthm<w.
   :hints (("Goal" :in-theory nil)))
; The rule is disabled:
 (assert! (not (disabledp 'true-listp-of-union-equal-type-again)))
; Check redundancy:
 (defthm<w true-listp-of-union-equal-type-again
   (implies (true-listp b)
            (true-listp (union-equal a b)))))

;;; Again, but create a disabled rewrite rule:
(local-test
 (defthmd<w true-listp-of-union-equal-type-again
   (implies (true-listp b)
            (true-listp (union-equal a b)))
; By default, hints are ignored by defthm<w.
   :hints (("Goal" :in-theory nil)))
; The rule is disabled:
 (assert! (disabledp 'true-listp-of-union-equal-type-again))
; Check redundancy:
 (defthm<w true-listp-of-union-equal-type-again
   (implies (true-listp b)
            (true-listp (union-equal a b))))
 )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The following test is similar to the one above, except that we take
;;; advantage of expanding away calls of functions in
;;; *expandable-boot-strap-non-rec-fns*.  Since the new theorem is no longer an
;;; instance of the old theorem, we generate a :use hint instead of a :by hint.

(assert!
 (equal
  (easy-trans
   '(and (implies (true-listp b)
                  (true-listp (union-equal a b)))
         (mbe :logic t
              :exec (equal v v)))
   state)
  '(IF (IMPLIES (TRUE-LISTP B)
                (TRUE-LISTP (UNION-EQUAL A B)))
       (RETURN-LAST 'MBE1-RAW (EQUAL V V) 'T)
       'NIL)))

(assert!
 (equal (previous-subsumer-hints
         '(IF (IMPLIES (TRUE-LISTP B)
                       (TRUE-LISTP (UNION-EQUAL A B)))
              (RETURN-LAST 'MBE1-RAW (EQUAL V V) 'T)
              'NIL)
         (w state))
        '(:USE
          ((:INSTANCE TRUE-LISTP-OF-UNION-EQUAL-TYPE
                      (X A)
                      (Y B)))
          :IN-THEORY (THEORY 'MINIMAL-THEORY)
          :DO-NOT *ALL-BUT-SIMPLIFY*)))

(local-test
 (defthm<w true-listp-of-union-equal-type-again
   (and (implies (true-listp b)
                 (true-listp (union-equal a b)))
        (mbe :logic t
             :exec (equal v v)))
; By default, hints are ignored by defthm<w.
   :hints (("Goal" :in-theory nil))
   :rule-classes nil)
; Check redundancy:
 (defthm<w true-listp-of-union-equal-type-again
   (and (implies (true-listp b)
                 (true-listp (union-equal a b)))
        (mbe :logic t
             :exec (equal v v)))
   :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Next, we generate a :use hint that pulls together more than one previous
;;; event.

(assert!
 (equal
  (easy-trans
   '(and (implies (true-listp b)
                 (true-listp (union-equal a b)))
        (true-listp (intersection-equal u v)))
   state)
  '(IF (IMPLIES (TRUE-LISTP B)
                (TRUE-LISTP (UNION-EQUAL A B)))
       (TRUE-LISTP (INTERSECTION-EQUAL U V))
       'NIL)))

(assert!
 (equal (previous-subsumer-hints
         '(IF (IMPLIES (TRUE-LISTP B)
                       (TRUE-LISTP (UNION-EQUAL A B)))
              (TRUE-LISTP (INTERSECTION-EQUAL U V))
              'NIL)
         (w state))
        '(:USE
          ((:INSTANCE TRUE-LISTP-OF-INTERSECTION-EQUAL (Y V)
            (X U))
           (:INSTANCE TRUE-LISTP-OF-UNION-EQUAL-TYPE (X A)
                      (Y B)))
          :IN-THEORY (THEORY 'MINIMAL-THEORY)
          :DO-NOT *ALL-BUT-SIMPLIFY*)))

(local-test
 (defthm<w test2
   (and (implies (true-listp b)
                 (true-listp (union-equal a b)))
        (true-listp (intersection-equal u v)))
; By default, hints are ignored by defthm<w.
   :hints (("Goal" :in-theory nil))
   :rule-classes nil)
; Check redundancy:
 (defthm<w test2
   (and (implies (true-listp b)
                 (true-listp (union-equal a b)))
        (true-listp (intersection-equal u v)))
   :rule-classes nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Same as above, but using thm<w.

(must-succeed
 (thm<w
  (and (implies (true-listp b)
                (true-listp (union-equal a b)))
       (true-listp (intersection-equal u v)))
; By default, hints are ignored by defthm<w.
  :hints (("Goal" :in-theory nil))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; When the search fails, then by default, so does defthm<w.

(must-fail ; proved in books/arithmetic/equalities.lisp, not included here
 (thm<w (equal (equal 0 (- x))
               (equal 0 (fix x)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; When the search fails, then the proof is attempted regardless.

(must-succeed ; proved in books/arithmetic/equalities.lisp, not included here
 (thm<w (equal (equal 0 (- x))
               (equal 0 (fix x)))
        :prove t))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Copyright (C) 2019, Regents of the University of Texas
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file contains examples from the paper under development, "Iteration in
; ACL2".  At the end are some additional tests.

(in-package "ACL2")

(include-book "projects/apply/top" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/assert-bang-stobj" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(assert-event
 (equal (loop$ for x in '(1 2 3 4) sum (* x x))
        30))

(thm (equal (loop$ for x in '(1 2 3 4) sum (* x x))
            (SUM$ '(LAMBDA (LOOP$-IVAR)
                           (DECLARE (IGNORABLE LOOP$-IVAR))
                           (RETURN-LAST 'PROGN
                                        '(LAMBDA$ (LOOP$-IVAR)
                                                  (LET ((X LOOP$-IVAR)) (* X X)))
                                        ((LAMBDA (X) (BINARY-* X X))
                                         LOOP$-IVAR)))
                  '(1 2 3 4))))

(thm (equal (sum$ fn lst)
            (if (endp lst)
                0
              (+ (apply$ fn (list (car lst)))
                 (sum$ fn (cdr lst))))))

(assert-event
 (equal (loop$ for i from 0 to 1000000 by 5
               until (> i 30)
               when (evenp i) collect (* i i))
        '(0 100 400 900)))

; We use LAMBDA$ instead of LAMBDA below because otherwise we need to add
; IGNORABLE declarations.
(thm (equal (loop$ for i from lo to hi by k
                   until (> i 30)
                   when (evenp i) collect (* i i))
            (COLLECT$ (LAMBDA$ (I) (BINARY-* I I))
                      (WHEN$ (LAMBDA$ (I) (EVENP I))
                             (UNTIL$ (LAMBDA$ (I) (< '30 I))
                                     (FROM-TO-BY lo hi k))))))

(defun f1 ()
  (declare (xargs :guard t))
  (loop$ for i of-type integer from 0 to 1000000 by 5
         until (> i 30)
         when (evenp i) collect (* i i)))

(assert-event (equal (f1) '(0 100 400 900)))

(defun$ square (n)
  (declare (xargs :guard (integerp n)))
  (* n n))

(defmacro assert-event-error-triple (form val)
  `(assert!-stobj
    (mv-let (erp val2 state)
      ,form
      (mv (and (not erp)
               (equal val2 ',val))
          state))
    state))

(assert-event-error-triple
 (trans1 '(defun$ square (n)
            (declare (xargs :guard (integerp n)))
            (* n n)))
 (PROGN (DEFUN SQUARE (N)
          (DECLARE (XARGS :GUARD (INTEGERP N)))
          (* N N))
        (DEFWARRANT SQUARE)))

(thm (implies (force (apply$-warrant-square))
              (equal (apply$ 'square args)
                     (square (car args))))
     :hints (("Goal" :in-theory '(apply$-square))))

(defun f2 (lower upper)
  (declare (xargs :guard (and (integerp lower) (integerp upper))))
  (loop$ for i of-type integer from lower to upper
         collect (square i)))

(assert-event (equal (f2 3 5) '(9 16 25)))

(thm (implies (warrant square)
              (equal (f2 3 5) '(9 16 25))))

(must-fail
 (thm (equal (f2 3 5) '(9 16 25))))

(thm (implies (and (natp k1) (natp k2) (natp k3)
                   (<= k1 k2) (<= k2 k3)
                   (warrant square))
              (member (* k2 k2) (f2 k1 k3))))

(must-fail
 (thm (implies (and (natp k1) (natp k2) (natp k3)
                    (<= k1 k2) (<= k2 k3))
               (member (* k2 k2) (f2 k1 k3)))))

; Trans doesn't actually return the translated value; it returns (value
; :invisible).  So we call translate instead.
(assert-event-error-triple
 (translate '(loop$ for x in '(1 2 3 4) sum (* x x))
            '(nil) ; stobjs-out
            t      ; logic-modep
            nil    ; known-stobjs
            'top   ; ctx
            (w state)
            state)
 (RETURN-LAST
  'PROGN
  '(LOOP$ FOR X IN '(1 2 3 4) SUM (* X X))
  (SUM$ '(LAMBDA (LOOP$-IVAR)
                 (DECLARE (IGNORABLE LOOP$-IVAR))
                 (RETURN-LAST 'PROGN
                              '(LAMBDA$ (LOOP$-IVAR)
                                        (LET ((X LOOP$-IVAR))
                                          (DECLARE (IGNORABLE X))
                                          (* X X)))
                              ((LAMBDA (X) (BINARY-* X X))
                               LOOP$-IVAR)))
        '(1 2 3 4))))

(assert! ; Assert-event fails because of program-only code and safe-mode.
 (equal
  (untranslate '(RETURN-LAST
                 'PROGN
                 '(LOOP$ FOR X IN '(1 2 3 4) SUM (* X X))
                 (SUM$ '(LAMBDA (LOOP$-IVAR)
                                (DECLARE (IGNORABLE LOOP$-IVAR))
                                (RETURN-LAST 'PROGN
                                             '(LAMBDA$ (LOOP$-IVAR)
                                                       (LET ((X LOOP$-IVAR)) (* X X)))
                                             ((LAMBDA (X) (BINARY-* X X))
                                              LOOP$-IVAR)))
                       '(1 2 3 4)))
               nil
               (w state))
  '(PROG2$ '(LOOP$ FOR X IN '(1 2 3 4) SUM (* X X))
           (SUM$ (LAMBDA$ (LOOP$-IVAR)
                          (LET ((X LOOP$-IVAR)) (* X X)))
                 '(1 2 3 4)))))

(defun sum-squares (lst)
  (loop$ for x in lst sum (* x x)))

(thm (equal (sum-squares lst)
            (SUM$ (LAMBDA$ (X) (* X X))
                  LST)))

(thm (equal (sum-squares lst)
            (SUM$ '(LAMBDA (X)
                           (DECLARE (IGNORABLE X))
                           (BINARY-* X X))
                  LST)))

(assert-event
 (equal
  (body 'sum-squares nil (w state)) ; unnormalized body
  '(RETURN-LAST
    'PROGN
    '(LOOP$ FOR X IN LST SUM (* X X))
    (SUM$ '(LAMBDA (LOOP$-IVAR)
                   (DECLARE (IGNORABLE LOOP$-IVAR))
                   (RETURN-LAST 'PROGN
                                '(LAMBDA$ (LOOP$-IVAR)
                                          (LET ((X LOOP$-IVAR))
                                            (DECLARE (IGNORABLE X))
                                            (* X X)))
                                ((LAMBDA (X) (BINARY-* X X))
                                 LOOP$-IVAR)))
          LST))))

; Perhaps we should clean up the normalized body of a defun provided there are
; no warranted fns in the lambda$s?

(assert-event
 (equal
  (body 'sum-squares t (w state)) ; normalized body
  '(SUM$ '(LAMBDA (LOOP$-IVAR)
                  (BINARY-* LOOP$-IVAR LOOP$-IVAR))
         LST)))

(assert! ; Assert-event fails because of program-only code and safe-mode.
 (equal (untranslate '(SUM$ '(LAMBDA (X)
                                     (DECLARE (IGNORABLE X))
                                     (BINARY-* X X))
                            LST)
                     nil
                     (w state))
        '(SUM$ (LAMBDA$ (X) (* X X))
               LST)))

(defun g (m n lst1 lst2)
  (loop$ for x1 in lst1 as x2 in lst2 sum (* m n x1 x2)))

(assert-event
 (equal (loop$-as '((1 2 3 4) (5 6 7 8)))
        '((1 5) (2 6) (3 7) (4 8))))

(thm (equal (sum$+ fn globals lst)
            (if (endp lst)
                0
              (+ (apply$ fn (list globals (car lst)))
                 (sum$+ fn globals (cdr lst))))))

(thm (equal (loop$ for x1 in lst1 as x2 in lst2 sum (* m n x1 x2))
            (SUM$+ (LAMBDA$ (LOOP$-GVARS LOOP$-IVARS)
                            (DECLARE (XARGS :GUARD
                                            (AND (TRUE-LISTP LOOP$-GVARS)
                                                 (EQUAL (LEN LOOP$-GVARS) 2)
                                                 (TRUE-LISTP LOOP$-IVARS)
                                                 (EQUAL (LEN LOOP$-IVARS) 2))
                                            :SPLIT-TYPES T))
                            (LET ((M (CAR LOOP$-GVARS))
                                  (N (CAR (CDR LOOP$-GVARS)))
                                  (X1 (CAR LOOP$-IVARS))
                                  (X2 (CAR (CDR LOOP$-IVARS))))
                                 (* M N X1 X2)))
                   (LIST M N)
                   (LOOP$-AS (LIST LST1 LST2)))))

(thm (equal (when$ fn lst)
            (if (endp lst)
                nil
              (if (apply$ fn (list (car lst)))
                  (cons (car lst)
                        (when$ fn (cdr lst)))
                (when$ fn (cdr lst))))))

(thm (equal (when$+ fn globals lst)
            (if (endp lst)
                nil
              (if (apply$ fn (list globals (car lst)))
                  (cons (car lst)
                        (when$+ fn globals (cdr lst)))
                (when$+ fn globals (cdr lst))))))

(thm (equal (loop$ for x in '(a b c) collect (mv x x))
            '((a a) (b b) (c c))))

(defthm sum$-revappend
  (equal (sum$ fn (revappend x y))
         (+ (sum$ fn x) (sum$ fn y))))

(thm (equal (sum-squares (reverse x))
            (sum-squares x)))

(defun sum-cubes (lst)
  (loop$ for x in lst sum (* x x x)))

(thm (equal (sum-cubes (reverse x))
            (sum-cubes x)))

(defun sum-cubes-recursive (lst)
  (cond ((endp lst) 0)
        (t (+ (let ((x (car lst)))
                (* x x x))
              (sum-cubes-recursive (cdr lst))))))

(must-fail (thm (equal (sum-cubes-recursive (reverse x))
                       (sum-cubes-recursive x))))

(defthm sum-cubes-recursive-revappend
  (equal (sum-cubes-recursive (revappend x y))
         (+ (sum-cubes-recursive x) (sum-cubes-recursive y))))

(thm (equal (sum-cubes-recursive (reverse x))
            (sum-cubes-recursive x)))

(thm (equal (sum-squares '(1 2 3 4)) 30))

(assert-event (equal (loop$ for i from 1 to 5 collect (* i i))
                     '(1 4 9 16 25)))

(assert-event (equal (f2 1 5)
                     '(1 4 9 16 25)))

(assert-event
 (equal
  (access loop$-alist-entry
          (cdr (assoc-equal '(LOOP$ FOR I OF-TYPE INTEGER
                                    FROM LOWER TO UPPER COLLECT (SQUARE I))
                            (global-val 'loop$-alist (w state))))
          :term)
  '(COLLECT$ '(LAMBDA (LOOP$-IVAR)
                      (DECLARE (TYPE INTEGER LOOP$-IVAR)
                               (XARGS :GUARD (INTEGERP LOOP$-IVAR)
                                      :SPLIT-TYPES T)
                               (IGNORABLE LOOP$-IVAR))
                      (RETURN-LAST 'PROGN
                                   '(LAMBDA$ (LOOP$-IVAR)
                                             (DECLARE (TYPE INTEGER LOOP$-IVAR))
                                             (LET ((I LOOP$-IVAR))
                                               (DECLARE (IGNORABLE I))
                                               (SQUARE I)))
                                   ((LAMBDA (I) (SQUARE I)) LOOP$-IVAR)))
             (FROM-TO-BY LOWER UPPER '1))))

(assert! ; may be able to use assert-event after a bug fix is in place
 (equal
  (prettyify-clause-lst
   (cadr (cadr (mv-list 2 (guard-obligation 'f2 nil nil t 'top-level state))))
   nil
   (w state))
  '((IMPLIES (AND (APPLY$-WARRANT-SQUARE)
                  (INTEGERP LOWER)
                  (INTEGERP UPPER)
                  (MEMBER-EQUAL NEWV (FROM-TO-BY LOWER UPPER 1)))
             (INTEGERP NEWV)))))

(must-fail
 (defun f2-alt (lower upper)
   (declare (xargs :guard (and (integerp lower) (integerp upper))))
   (loop$ for i from lower to upper ; deleted of-type integer
          collect (square i))))

(defun sum-squares-2 (lower upper)
  (declare (xargs :guard (and (integerp lower) (integerp upper))))
  (loop$ for i of-type integer from lower to upper
         sum (square i)))

(thm (implies (warrant square)
              (equal (sum-squares-2 1 4) 30)))

(thm (implies (warrant square)
              (equal (sum-squares-2 1 4) 30))
     :hints
     (("Goal" :in-theory (disable sum-squares-2))))

(must-fail ; need of-type or corresponding :guard
 (defun sum-squares-3 (lower upper)
   (declare (xargs :guard (and (integerp lower) (integerp upper))))
   (loop$ for i from lower to upper
          sum (square i))))

(defun sum-squares-3 (lower upper)
  (declare (xargs :guard (and (integerp lower) (integerp upper))))
  (loop$ for i from lower to upper
         sum :guard (integerp i) (square i)))

(thm (implies (warrant square)
              (equal (sum-squares-3 1 4) 30)))

; The results reported below were from ACL2 (git hash 5eb79e7697) built on CCL
; on April 4, 2018, running on a 3.5 GHz 4-core Intel(R) Xeon(R) with
; Hyper-Threading.  Times in seconds are realtime; also shown are bytes
; allocated.
; In the paper, (a) through (f) are wrapped in time$, but that prevents
; certification of this book because time$ is not allowed for embedded event
; forms.  Also, to make these into embedded event forms we use assert! below.
; We comment out (d) through (f) below to avoid the need for a trust tag to
; certify this bug, as these are Common Lisp evaluations.
; We make this local to avoid a problem, at the time of this writing in April
; 2019, with a stack overflow from ACL2 source function pkg-names-memoize.
(local (progn
(defun$ double (n)
  (declare (xargs :guard (integerp n)))
  (+ n n))
(defun sum-doubles (lst)
  (declare (xargs :guard (and (integer-listp lst)
                              (warrant double))
                  :verify-guards nil))
  (loop$ for x of-type integer in lst sum (double x)))
(make-event `(defconst *m* ',(loop$ for i from 1 to 10000000 collect i)))
; (a) ACL2 top-level loop$ call [0.98 seconds, 160,038,272 bytes]:
(assert! (equal (loop$ for i of-type integer in *m* sum (double i))
                100000010000000))
; (b) ACL2 top-level non-guard-verified function call [0.89 seconds, 160,037,232 bytes]
(assert! (equal (sum-doubles *m*) 100000010000000))
(verify-guards sum-doubles)
; (c) ACL2 top-level guard-verified function call [0.14 seconds, 16 bytes]
(assert! (equal (sum-doubles *m*) 100000010000000))
;;; We comment out the Common Lisp tests for this book, as noted above.
; (value :q)
; ; (d) Common Lisp guard and function call [0.13 seconds, 0 bytes]:
; (time$ (and (integer-listp *m*) (sum-doubles *m*)))
; ; (e) Common Lisp function call [0.09 seconds, 0 bytes]:
; (time$ (sum-doubles *m*))
; ; (f) Common Lisp loop call [0.08 seconds, 0 bytes]:
; (time$ (loop for i of-type integer in *m* sum (double i)))
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Additional tests (not tied to the paper)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; The first batch, involving g1 and g2 below, involves apply$ rather than
;;; loop$ (but is relevant to loop$ because it's relevant to apply$).

(defun$ g1 (x)
  (declare (xargs :guard t))
  x)

(thm (implies (warrant g1) ; necessary
              (equal (apply$ 'g1 (list 3))
                     3)))

(must-fail
; Fails, as it should:
 (thm (equal (apply$ 'g1 (list 3))
             3)))

(memoize 'g1)

(thm (implies (warrant g1) ; necessary
              (equal (apply$ 'g1 (list 3))
                     3)))

(must-fail
; Still fails in spite of memoization, as it should:
 (thm (equal (apply$ 'g1 (list 3))
             3)))

; Now let's bury the apply$ call in a guard-verified function.

(defun$ g2 (x)
  (declare (xargs :guard t))
  (apply$ 'g1 (list x)))

(thm (implies (warrant g1) ; necessary
              (equal (g2 3)
                     3)))

(must-fail
; Fails, as it should:
 (thm (equal (g2 3)
             3)))

(memoize 'g2)

(thm (implies (warrant g1) ; necessary
              (equal (g2 3)
                     3)))

(must-fail
; Still fails in spite of memoization, as it should:
 (thm (equal (g2 3)
             3)))

; Prints a warning about memoization results not being stored:
(value-triple (g2 3))

(must-fail
; Still fails in spite of memoization, as it should:
 (thm (equal (g2 3)
             3)))

;;; The second batch addresses loop$ more directly than above (where we focused
;;; on apply$).

(defun$ loop1 (x)
  (declare (xargs :guard t))
  (loop$ for i from 1 to 3 collect (cons (g2 i) x)))

; Caused an assertion (expecting *aokp* to be non-nil) until fix around
; 4/19/2019.
(thm (implies (and (warrant g1) (warrant g2)) ; both are necessary
              (equal (loop1 'a)
                     '((1 . a) (2 . a) (3 . a)))))

(must-fail
; Fails, as it should:
 (thm (implies (and (warrant g1))
               (equal (loop1 'a)
                      '((1 . a) (2 . a) (3 . a))))))

(must-fail
; Fails, as it should:
 (thm (implies (and (warrant g2))
               (equal (loop1 'a)
                      '((1 . a) (2 . a) (3 . a))))))

(memoize 'loop1) ; and g2 is already memoized

(thm (implies (and (warrant g1) (warrant g2)) ; both are necessary
              (equal (loop1 'a)
                     '((1 . a) (2 . a) (3 . a)))))

(must-fail
; Fails in spite of memoization, as it should:
 (thm (equal (loop1 'a)
             '((1 . a) (2 . a) (3 . a)))))

(must-fail
; Still fails in spite of memoization, as it should:
 (thm (implies (and (warrant g1))
               (equal (loop1 'a)
                      '((1 . a) (2 . a) (3 . a))))))

(must-fail
; Still fails in spite of memoization, as it should:
 (thm (implies (and (warrant g2))
               (equal (loop1 'a)
                      '((1 . a) (2 . a) (3 . a))))))

; -----------------------------------------------------------------
; Now I experiment with do loop$s.

(assert-event
 (equal (loop$ with temp = '(1 2 3 4 5)
               with ans = 0
               do
               (if (endp temp)
                   (return ans)
                   (progn (setq ans (+ (car temp) ans))
                          (setq temp (cdr temp)))))
        15))

(assert-event
 (equal (loop$ with temp = '(1 2 3 NEGATE 4)
               with ans = 0
               do
               (if (endp temp)
                   (loop-finish)
                   (progn
                     (setq ans (if (equal (car temp) 'NEGATE)
                                   (- ans)
                                   (+ (car temp) ans)))
                     (setq temp (cdr temp))))
               finally
               (return ans))
        -2))

; The following function ``loops forever''

(defun infinite-loop ()
  (declare (xargs :verify-guards nil))
  (loop$ with temp of-type integer = 0
         do
         :measure (acl2-count temp)
         (progn (cw "Temp = ~x0~%" temp)
                (setq temp (+ 1 temp)))))

(thm (equal (infinite-loop)
            nil))

(must-fail
 (infinite-loop)
 :expected :hard)

; The error message explains that the measure went from 0 to 1 and so didn't go
; down.  Logically the function returns :DO$-MEASURE-DID-NOT-DECREASE.  We
; can't verify the guards (which includes verifying that the measure
; decreases):

(must-fail
 (verify-guards infinite-loop))

; This loop works as expected.

(defun do-loop1 (lst)
  (loop$ with temp = lst
         with ans = 0
         do
         (if (endp temp)
             (return ans)
             (progn (setq ans (+ (car temp) ans))
                    (setq temp (cdr temp))))))

(assert-event
 (equal (do-loop1 '(1 2 3 4 5)) 15))

; But we can't verify the guards because, for example, we don't know (car temp)
; and ans are numbers.

(must-fail
 (verify-guards do-loop1))

(must-fail
 (defun do-loop2 (lst)
   (declare (xargs :guard (nat-listp lst)))
   (loop$ with temp = lst
          with ans = 0
          do
          (if (endp temp)
              (return ans)
              (progn (setq ans (+ (car temp) ans))
                     (setq temp (cdr temp)))))))
; Checkpoints
; Subgoal 1.3
; (IMPLIES (AND (ALISTP ALIST)
;               (NOT (CONSP (CDR (HONS-ASSOC-EQUAL 'TEMP ALIST)))))
;          (NOT (CDR (HONS-ASSOC-EQUAL 'TEMP ALIST))))

; Subgoal 1.2
; (IMPLIES (AND (ALISTP ALIST)
;               (CONSP (CDR (HONS-ASSOC-EQUAL 'TEMP ALIST))))
;          (ACL2-NUMBERP (CDR (HONS-ASSOC-EQUAL 'ANS ALIST))))

; Subgoal 1.1
; (IMPLIES (AND (ALISTP ALIST)
;               (CONSP (CDR (HONS-ASSOC-EQUAL 'TEMP ALIST))))
;          (ACL2-NUMBERP (CADR (HONS-ASSOC-EQUAL 'TEMP ALIST))))


; Both of the following show ways we can address the above
; failures.

(defun do-loop2-alternative1 (lst)
   (declare (xargs :guard (nat-listp lst)))
   (loop$ with temp = lst
          with ans = 0
          do
          :guard (and (nat-listp temp)
                      (integerp ans))
          (if (endp temp)
              (return ans)
              (progn (setq ans (+ (car temp) ans))
                     (setq temp (cdr temp))))))

(defun do-loop2-alternative2 (lst)
   (declare (xargs :guard (nat-listp lst)))
   (loop$ with temp of-type (satisfies nat-listp) = lst
          with ans of-type integer = 0
          do
          (if (endp temp)
              (return ans)
              (progn (setq ans (+ (car temp) ans))
                     (setq temp (cdr temp))))))

; The following shows that the type-spec is enforced on every setq.

(must-fail
 (loop$ with temp = '(1 2 3 4)
        with ans of-type (satisfies natp) = 0
        do
        (if (endp temp)
            (return ans)
            (progn (setq ans (- ans))
                   (setq ans (+ (- ans) (car temp)))
                   (setq temp (cdr temp)))))
 :expected :hard)

; But if we do the evaluation with guard-checking off, we get the
; right answer, 10.

(make-event
 (state-global-let*
  ((guard-checking-on nil))
  (value-triple
   `(assert-event
     (equal ,(loop$ with temp = '(1 2 3 4)
                    with ans of-type (satisfies natp) = 0
                    do
                    (if (endp temp)
                        (return ans)
                        (progn (setq ans (- ans))
                               (setq ans (+ (- ans) (car temp)))
                               (setq temp (cdr temp)))))
            10)))))

; Alternativey, if we do not specify a TYPE natp for ans and instead just guard
; the body with (natp ans), it works even with guard checking on.  The reason
; it works is that the :guard is checked on every entry to the do body (and ans
; is a natural every time), but of-type is checked on every setq and the first
; setq below violates that even though the second one restores ans to be a
; natp.

(assert-event
 (equal (loop$ with temp = '(1 2 3 4)
               with ans = 0
               do
               :guard (natp ans)
               (if (endp temp)
                   (return ans)
                   (progn (setq ans (- ans))
                          (setq ans (+ (- ans) (car temp)))
                          (setq temp (cdr temp)))))
        10))



; Here we show the same thing, except instead of causing the error at runtime
; we show that we cannot verify the guards of the loop where ans is declared
; of-type natp but we can verify the guards of the loop with the :guard clause
; that ans is a natp.

(must-fail
 (defun do-loop3-type-spec (lst)
   (declare (xargs :guard (nat-listp lst)))
   (loop$ with temp of-type (satisfies nat-listp) = lst
          with ans of-type (satisfies natp) = 0
          do
          (if (endp temp)
              (return ans)
              (progn (setq ans (- ans))
                     (setq ans (+ (- ans) (car temp)))
                     (setq temp (cdr temp)))))))

(defun do-loop3-guard (lst)
  (declare (xargs :guard (nat-listp lst)))
  (loop$ with temp of-type (satisfies nat-listp) = lst
         with ans = 0
         do
         :guard (natp ans)
         (if (endp temp)
             (return ans)
             (progn (setq ans (- ans))
                    (setq ans (+ (- ans) (car temp)))
                    (setq temp (cdr temp))))))


; This defun fails because we can't find a variable that is tested and changed
; (as a function of its old value) on every branch.  This is confusing to the
; user because temp appears to be such a variable.  But we don't count temp as
; always changing below because of the 'xxx branch.

(must-fail
 (defun do-loop4 (lst)
   (declare (xargs :guard (true-listp lst)))
   (loop$ with temp = lst
          with ans = 0
          do
          :guard (and (true-listp temp)
                      (natp ans))
          (if (endp temp)
              (loop-finish)
              (if (eq (car temp) 'stop)
                  (return 'stopped)
                  (progn (setq ans (+ 1 ans))
                         (setq temp (if (eq (car temp) 'skip)
                                        xxx
                                        (cdr temp))))))
          finally
          :guard (integerp ans)
          (return ans))))

; This is accepted and guard verified.
(defun do-loop4 (lst)
  (declare (xargs :guard (true-listp lst)))
  (loop$ with temp = lst
         with ans = 0
         do
         :guard (and (true-listp temp)
                     (natp ans))
         (if (endp temp)
             (loop-finish)
             (if (eq (car temp) 'stop)
                 (return 'stopped)
                 (progn (setq ans (+ 1 ans))
                        (setq temp (if (eq (car temp) 'skip)
                                       (cddr temp)
                                       (cdr temp))))))
         finally
         :guard (integerp ans)
         (return ans)))

(assert-event
 (equal (do-loop4 '(1 2 3)) 3))

(assert-event
 (equal (do-loop4 '(1 2 3 SKIP 5 6)) 5))

(assert-event
 (equal (do-loop4 '(1 2 3 SKIP XXX 5)) 5))

(assert-event
 (equal (do-loop4 '(1 2 3 STOP XXX 5)) 'stopped))

(assert-event
 (equal (do-loop4 '(1 2 3 SKIP STOP 5)) 5))

(defun do-loop-counting-up (i0 max)
  (declare (xargs :guard (and (natp i0) (natp max))
                  :verify-guards nil))
  (loop$ with i of-type (satisfies natp) = i0
         with cnt of-type integer = 0
         do
         :measure (nfix (- max i))
         :guard (natp max)
         (if (>= i max)
             (loop-finish)
             (progn (setq cnt (+ 1 cnt))
                    (setq i (+ 1 i))))
         finally
         (return (list 'from i0 'to max 'is cnt 'steps))))

; The following experiment shows the effect of guard verification!
; But this is just commented out because I don't know how to measure
; times in a certified book!

; (time$ (do-loop-counting-up 1 1000000))
; 59.72 seconds realtime, 59.72 seconds runtime
; (4,079,998,496 bytes allocated).
; (FROM 1 TO 1000000 IS 999999 STEPS)

; (verify-guards do-loop-counting-up)
; Time:  0.15 seconds (prove: 0.13, print: 0.01, other: 0.01)

; (time$ (do-loop-counting-up 1 1000000))
; 0.00 seconds realtime, 0.00 seconds runtime
; (144 bytes allocated).
; (FROM 1 TO 1000000 IS 999999 STEPS)

; Here is an example of lexicographic do loop$:

(defun do-loop-lex (x0 y0)
  (loop$ with x = x0
         with y = y0
         with ans of-type (satisfies true-listp) = nil
         do
         :measure (llist (len x) (len y))
         (if (atom x)
             (loop-finish)
             (if (atom y)
                 (progn (setq y y0)
                        (setq x (cdr x)))
                 (progn (setq ans (cons (cons (car x) (car y)) ans))
                        (setq y (cdr y)))))
         finally
         (return (revappend ans nil))))

(verify-guards do-loop-lex)

(assert-event
 (equal (do-loop-lex '(0 1 2 3) '(0 1 2 3))
        '((0 . 0)
          (0 . 1)
          (0 . 2)
          (0 . 3)
          (1 . 0)
          (1 . 1)
          (1 . 2)
          (1 . 3)
          (2 . 0)
          (2 . 1)
          (2 . 2)
          (2 . 3)
          (3 . 0)
          (3 . 1)
          (3 . 2)
          (3 . 3))))

; Here is a simple challenge: prove that a do loop$ implementing rev1 is correct.
; We keep it simple:  no guards, no type-specs.

(defun do-loop-rev1 (x a)
  (loop$ with temp-x = x
         with temp-a = a
         do
         (progn (if (atom temp-x) (return temp-a) nil)
                (setq temp-a (cons (car temp-x) temp-a))
                (setq temp-x (cdr temp-x)))))

(verify-guards do-loop-rev1)

(defun rev1 (x a)
  (if (atom x)
      a
      (rev1 (cdr x) (cons (car x) a))))

(defthm do-loop-rev1-is-rev1
  (equal (do-loop-rev1 x a) (rev1 x a))
  :rule-classes nil)

; Do we need warrants for functions used in guards?

(defun my-natp (x)
  (natp x))

(defbadge my-natp)

; The thm below cannot be proved without warranting my-natp, even though it is
; only used in an irrelevant arg of return-last.

(must-fail
 (defthm my-natp-test0 
  (implies (and (natp y)
                (natp z))
           (equal (ev$ '(return-last 'progn
                                     (check-dcl-guardian (my-natp x) '(test of my-natp))
                                     (binary-+ '1 x))
                       (list (cons 'x (+ y z))))
                  (+ 1 y z)))))

(defun my-natp-hint (k)
  (if (zp k)
      t
      (my-natp-hint (- k 1))))

(must-fail
 (defthm my-natp-test1
  (implies (natp k)
           (equal (loop$ with temp of-type (satisfies my-natp) = k
                         do
                         (if (zp temp)
                             (return 'done)
                             (setq temp (- temp 1))))
                  'done))
  :hints (("Goal" :induct (my-natp-hint k)))))

(defwarrant my-natp)

(defthm my-natp-test2
  (implies (and (warrant my-natp)
                (natp k))
           (equal (loop$ with temp of-type (satisfies my-natp) = k
                         do
                         (if (zp temp)
                             (return 'done)
                             (setq temp (- temp 1))))
                  'done))
  :hints (("Goal" :induct (my-natp-hint k))))


; We need the concept of a (key . val) alist whose vals are all rational.  We
; will use it as a guard.  We could use a for loop$ to check this but because
; we have to prove things about it, we'll start simply and define it in the
; traditional recursive way.  Later will explore using loop$s.

(defun map-to-ratsp (x)
  (cond
   ((atom x) (equal x nil))
   (t (and (consp (car x))
           (rationalp (cdr (car x)))
           (map-to-ratsp (cdr x))))))

(defbadge map-to-ratsp)

; To use map-to-ratsp as a guard we need to verify its guards first.

(verify-guards map-to-ratsp)

(defwarrant map-to-ratsp)

(defun do-loop-max-pair (alist)

; Assuming alist is a (key . val) alist whose vals are rationals, we compute
; the pair with the largest val.

  (declare (xargs :guard (map-to-ratsp alist)))
  (loop$ with alist of-type (satisfies map-to-ratsp) = alist
         with max-pair = nil
         do
         :guard (or (null max-pair)
                    (and (consp max-pair)
                         (rationalp (cdr max-pair))))
         (progn
           (cond
            ((endp alist) (return max-pair))
            ((or (null max-pair)
                 (> (cdr (car alist))
                    (cdr max-pair)))
             (setq max-pair (car alist))))
           (setq alist (cdr alist)))))

(assert-event
 (equal (do-loop-max-pair '((a . 1)(b . 2)(c . 33) (d . 23) (e . 45) (f . 0)))
        '(e . 45)))

; The following failed before a commit on 10/22/2021.

(assert-event (equal (loop$ with temp = '(a b c)
                            with ans = nil
                            do (cond ((endp temp) (return ans))
                                     (t (let ((foo (car temp)))
                                          (progn (setq ans (cons foo ans))
                                                 (setq temp (cdr temp)))))))
                     '(C B A)))

; Start tests of DO loop$s that return multiple values and/or stobjs.
; These may be labeled do-mv-N.

(defun do-mv-1 (x)
; Returns a single non-stobj value, but uses mv-setq in the loop.
  (declare (xargs :guard (true-listp x)))
  (loop$ with temp = x
         with result = nil
         with len = 0
         do
         :guard (and (true-listp temp)
                     (natp len))
         (if (null temp)
             (loop-finish)
           (mv-setq (temp result len)
                    (mv (cdr temp)
                        (cons (car temp) result)
                        (1+ len))))
         finally (return (list len result))))

(defun do-mv-2 (x)
; Same as do-mv-1, except we return two values.
  (declare (xargs :guard (true-listp x)))
  (loop$ with temp = x
         with result = nil
         with len = 0
         do
         :values (nil nil)
         :guard (and (true-listp temp)
                     (natp len))
         (if (null temp)
             (loop-finish)
           (mv-setq (temp result len)
                    (mv (cdr temp)
                        (cons (car temp) result)
                        (1+ len))))
         finally (return (mv len result))))

(must-fail
; The following defun is identical to the one above, except that the FINALLY
; clause has a non-return exit, which is illegal for :VALUES other than (NIL).
; This test supports a comment in ACL2 source function translate11-do-finally.
 (defun do-mv-2-bad-1 (x)
   (declare (xargs :guard (true-listp x)))
   (loop$ with temp = x
          with result = nil
          with len = 0
          do
          :values (nil nil)
          :guard (and (true-listp temp)
                      (natp len))
          (if (null temp)
              (loop-finish)
            (mv-setq (temp result len)
                     (mv (cdr temp)
                         (cons (car temp) result)
                         (1+ len))))
          finally (mv len result))))

(must-fail
; The following defun is identical to the one above, except that the FINALLY
; clause has a non-return exit, which is illegal for :VALUES other than (NIL).
; This test supports a comment in ACL2 source function translate11-do-finally.
 (defun do-mv-2-bad-2 (x)
   (declare (xargs :guard (true-listp x)))
   (loop$ with temp = x
          with result = nil
          with len = 0
          do
          :values (nil nil)
          :guard (and (true-listp temp)
                      (natp len))
          (if (null temp)
              (loop-finish)
            (mv-setq (temp result len)
                     (mv (cdr temp)
                         (cons (car temp) result)
                         (1+ len))))
          finally (if (equal len 3)
                      (cw "Some msg")
                    (return (mv len result))))))

(defstobj st fld)
(defwarrant fld)
(defwarrant update-fld)

(must-fail
;;; This fails because of the form (return 'stopped), which violates the
;;; expected return of the stobj, st.
 (defun do-mv-3 (lst st)
   (declare (xargs :stobjs st :guard (true-listp lst)))
   (loop$ with temp of-type (satisfies true-listp) = lst
          do
          :values (st)
          (cond ((endp temp)
                 (loop-finish))
                ((eq (car temp) 'stop)
                 (return 'stopped))
                (t (mv-setq (st temp)
                            (let ((st (update-fld
                                       (+ (ifix (car temp)) (ifix (fld st)))
                                       st)))
                              (mv st (cdr temp))))))
          finally (return st))))

; Disallow stobj modification that isn't justified logically.
; Before we got the ACL2 code right, we were able to admit the following, and
; then after evaluating (do-mv-3-bad '(3 4 17 5) st), we found that
; (fld st) = 0, yet we could prove the following.
;   (thm (implies (warrant fld update-fld)
;                 (equal (do-mv-3-bad '(3 4 17 5) '(0)) '(7))))
(must-fail
 (defun do-mv-3 (lst st)
   (declare (xargs :stobjs st
                   :guard (true-listp lst)))
   (let ((st (update-fld 0 st)))
     (loop$ with temp of-type (satisfies true-listp) = lst
            do
            :values (st)
            :measure (len temp)
            :guard
; We include (stp st) because stobj-optp = nil for lambdas; see
; guard-clauses-for-fn1.
            (stp st)
            (cond ((endp temp)
                   (loop-finish))
                  ((eql (car temp) 17)
                   (progn (setq temp nil)
                          (update-fld 0 st)))
                  (t (mv-setq (st temp)
                              (let ((st (update-fld
                                         (+ (ifix (car temp)) (ifix (fld st)))
                                         st)))
                                (mv st (cdr temp))))))
            finally (return st)))))

(must-fail
; This fails because "Single-threaded object names, such as ST, may not be
; LET-bound at the top-level of a DO loop body or FINALLY clause."
 (defun do-mv-3 (lst st)
   (declare (xargs :stobjs st :guard (true-listp lst)))
   (let ((st (update-fld 0 st)))
     (loop$ with temp of-type (satisfies true-listp) = lst
            do
            :values (st)
            :guard
; We include (stp st) because stobj-optp = nil for lambdas; see
; guard-clauses-for-fn1.
            (stp st)
            (cond ((endp temp)
                   (loop-finish))
                  (t (let ((st (update-fld
                                (+ (ifix (car temp)) (ifix (fld st)))
                                st)))
                       (mv-setq (st temp)
                                (mv st (cdr temp))))))
            finally (return st)))))

(must-fail
; Stobjs must not appear in WITH clauses.
 (defun do-mv-3 (lst st)
   (declare (xargs :stobjs st :guard (true-listp lst)))
   (let ((st (update-fld 0 st)))
     (loop$ with temp of-type (satisfies true-listp) = lst
            with st = st
            do
            :values (st)
            :guard
; We include (stp st) because stobj-optp = nil for lambdas; see
; guard-clauses-for-fn1.
            (stp st)
            (cond ((endp temp)
                   (loop-finish))
                  (t (mv-setq (st temp)
                              (let ((st (update-fld
                                         (+ (ifix (car temp)) (ifix (fld st)))
                                         st)))
                                (mv st (cdr temp))))))
            finally (return st)))))

(defun do-mv-3 (lst st)
   (declare (xargs :stobjs st :guard (true-listp lst)))
   (let ((st (update-fld 0 st)))
     (loop$ with temp of-type (satisfies true-listp) = lst
            do
            :values (st)
            :guard
; We include (stp st) because stobj-optp = nil for lambdas; see
; guard-clauses-for-fn1.
            (stp st)
            (cond ((endp temp)
                   (loop-finish))
                  (t (mv-setq (st temp)
                              (let ((st (update-fld
                                         (+ (ifix (car temp)) (ifix (fld st)))
                                         st)))
                                (mv st (cdr temp))))))
            finally (return st))))

(assert-event
 (let ((st (do-mv-3 '(1 2 4) st)))
   (mv (equal (fld st) 7) st))
 :stobjs-out '(nil st))

(must-fail
 (defun do-mv-3-alt (lst st)
; This is like do-mv-3, except that we put a let outside the mv-setq, which is
; illegal (as it would defeat single-threadedness for st).
   (declare (xargs :stobjs st :guard (true-listp lst)))
   (let ((st (update-fld 0 st)))
     (loop$ with temp of-type (satisfies true-listp) = lst
            do
            :values (st)
            (cond ((endp temp)
                   (loop-finish))
                  (t (let* ((a (car temp))
                            (st (update-fld
                                 (+ (ifix a) (ifix (fld st)))
                                 st)))
                       (mv-setq (st temp)
                                (mv st (cdr temp))))))
            finally (return st))))
 )

; We can pass a congruent stobj for st into the function defined just above.

(defstobj st2 fld2 :congruent-to st)
(defwarrant fld2)
(defwarrant update-fld2)

(assert-event
 (let ((st2 (do-mv-3 '(1 2 4) st2)))
   (mv (equal (fld st2) 7) st2))
 :stobjs-out '(nil st2))

(must-fail
; The :values of a do loop$ is taken literally, not allowing for congruent
; stobjs.  The way to allow congruent stobjs in a do loop$ is to wrap the loop
; into a function; see how do-mv-3 is called in the test just above on st2.
 (defun do-mv-3-cong (lst st2)
   (declare (xargs :stobjs st2 :guard (true-listp lst)))
   (let ((st2 (update-fld 0 st2)))
     (loop$ with temp of-type (satisfies true-listp) = lst
            do
            :values (st)
            (cond ((endp temp)
                   (loop-finish))
                  (t (mv-setq (st temp)
                              (let ((st (update-fld
                                         (+ (ifix (car temp)) (ifix (fld st)))
                                         st)))
                                (mv st (cdr temp))))))
            finally (return st)))))

(must-fail
; This fails because :VALUES below contradicts the stobjs-out of the FINALLY
; clause.
 (defun do-mv-4-bug (n lst st)
   (declare (xargs :stobjs st :guard (and (natp n)
                                          (true-listp lst))))
   (loop$ with temp of-type (satisfies true-listp) = lst
          do
          :values (st)
          :guard (integerp n)
          (progn (setq st (update-fld n st))
                 (cond ((endp temp)
                        (loop-finish))
                       (t (mv-setq (st temp)
                                   (let ((st (update-fld
                                              (+ (ifix (car temp))
                                                 (ifix (fld st)))
                                              st)))
                                     (mv st (cdr temp)))))))
          finally
          :guard (integerp n)
          (return (mv (equal (fld st) (+ n 7)) st)))))

(defun do-mv-4 (n lst st)
  (declare (xargs :stobjs st :guard (and (natp n)
                                         (true-listp lst))))
  (let ((st (update-fld n st)))
    (loop$ with temp of-type (satisfies true-listp) = lst
           do
           :values (nil st)
           :guard
; We include (stp st) because stobj-optp = nil for lambdas; see
; guard-clauses-for-fn1.
           (and (stp st)
                (natp n))
           (cond ((endp temp)
                  (loop-finish))
                 (t (mv-setq (st temp)
                             (let ((st (update-fld
                                        (+ (ifix (car temp))
                                           (ifix (fld st)))
                                        st)))
                               (mv st (cdr temp))))))
           finally
           :guard
; We include (stp st) because stobj-optp = nil for lambdas; see
; guard-clauses-for-fn1.
           (and (stp st)
                (integerp n))
           (return (mv (equal (fld st) (+ n 7)) st)))))

(assert-event (do-mv-4 20 '(3 0 4) st)
              :stobjs-out '(nil st))

(thm (implies (warrant fld update-fld)
              (mv-let (equality-flg st)
                (do-mv-4 20 '(3 0 4) '(100))
                (and (equal equality-flg t)
                     (equal st '(27))
                     (equal (fld st) 27)))))

; As just above, but this time use the body of do-mv-4 directly in the loop:
(thm (implies (warrant fld update-fld)
              (mv-let (equality-flg st)
                (let* ((n 20)
                       (lst '(3 0 4))
                       (st '(100)))
                  (let ((st (update-fld n st)))
                    (loop$ with temp of-type (satisfies true-listp) = lst
                           do
                           :values (nil st)
                           :guard
; We include (stp st) because stobj-optp = nil for lambdas; see
; guard-clauses-for-fn1.
                           (and (stp st)
                                (natp n))
                           (cond ((endp temp)
                                  (loop-finish))
                                 (t (mv-setq (st temp)
                                             (let ((st (update-fld
                                                        (+ (ifix (car temp))
                                                           (ifix (fld st)))
                                                        st)))
                                               (mv st (cdr temp))))))
                           finally
                           :guard
; We include (stp st) because stobj-optp = nil for lambdas; see
; guard-clauses-for-fn1.
                           (and (stp st)
                                (integerp n))
                           (return (mv (equal (fld st) (+ n 7)) st)))))
                (and (equal equality-flg t)
                     (equal st '(27))
                     (equal (fld st) 27)))))

(must-fail
; Check that we don't need to worry about handling missing ELSE of IF.  Error
; message says that IF takes three arguments.
 (defun bad-loop ()
   (loop$ with temp = '(1 2 3)
          with x
          do (if (consp temp)
                 (progn (setq x (car temp))
                        (setq temp (cdr temp))))
          finally (return x))))

(must-fail
; As above, but the issue is in the FINALLY clause this time.
 (defun bad-loop ()
   (loop$ with temp = '(1 2 3)
          with x
          do (if (consp temp)
                 (progn (setq x (car temp))
                        (setq temp (cdr temp)))
               (loop-finish))
          finally (if (evenp x)
                      (return x)))))

; Test that it's OK to fall through to a missing finally clause, as is natural
; in this membership function.
(defun member-equal-via-loop (a lst)
  (loop$ with temp = lst
         do
         (cond ((atom temp)
                (loop-finish))
               ((equal (car temp) a)
                (return temp))
               (t (setq temp (cdr temp))))))

; Check that we have indeed defined member-equal using loop$.
(defthm member-equal-via-loop-is-member-equal
  (equal (member-equal-via-loop a x)
         (member-equal a x)))

(must-fail
; This is like member-equal-via-loop except that we return both t and the tail
; when found.  It's an error though, because there is no finally clause.
 (defun bad-loop (a lst)
   (loop$ with temp = lst
          do
          :values (nil nil)
          (cond ((atom temp)
                 (loop-finish))
                ((equal (car temp) a)
                 (return (mv t temp)))
                (t (setq temp (cdr temp)))))))

(must-fail
; This is like the one above, but with a finally clause that is missing a
; return even though its expression has the right output shape.
 (defun bad-loop (a lst)
   (loop$ with temp = lst
          do
          :values (nil nil)
          (cond ((atom temp)
                 (loop-finish))
                ((equal (car temp) a)
                 (return (mv t temp)))
                (t (setq temp (cdr temp))))
          finally (mv nil nil))))

(must-fail
; This is like the bad-loop attempt just above, but this time there is a
; finally clause that, however, doesn't return an mv result on each branch.
 (defun bad-loop (a lst)
   (loop$ with temp = lst
          do
          :values (nil nil)
          (cond ((atom temp)
                 (loop-finish))
                ((equal (car temp) a)
                 (return (mv t temp)))
                (t (setq temp (cdr temp))))
          finally (return (if (null temp)
                              (mv nil nil)
                            (cw "Non-nil atom.~%"))))))

(must-fail
; variant of the one just above
 (defun bad-loop (a lst)
   (loop$ with temp = lst
          do
          :values (nil nil)
          (cond ((atom temp)
                 (loop-finish))
                ((equal (car temp) a)
                 (return (mv t temp)))
                (t (setq temp (cdr temp))))
          finally (if (null temp)
                      (return (mv nil nil))
                    (cw "Non-nil atom.~%")))))

; Unlike the bad-loop definition just above, this timee we include a suitable
; finally clause.
(defun member-equal-via-loop-2 (a lst)
  (loop$ with temp = lst
         do
         :values (nil nil)
         (cond ((atom temp)
                (loop-finish))
               ((equal (car temp) a)
                (return (mv t temp)))
               (t (setq temp (cdr temp))))
         finally (return (mv nil nil))))

; And here's a reasonable theorem about the new function.
(defthm member-equal-via-loop-2-iff-member-equal
  (iff (mv-nth 0 (member-equal-via-loop-2 a x))
       (member-equal a x)))

; Test execution in the prover.
(thm (equal (loop$ with temp = '(1 2 3 4 5 6)
                   do
                   :values (nil nil)
                   (cond ((atom temp)
                          (loop-finish))
                         ((equal (car temp) 3)
                          (return (mv t temp)))
                         (t (setq temp (cdr temp))))
                   finally (return (mv nil nil)))
            '(t (3 4 5 6)))
     :hints (("Goal" :in-theory '((:e do$)))))

; Test execution in the loop.
(assert-event
 (loop$ with temp = '(1 2 3 4 5 6)
        do
        :values (nil nil)
        (cond ((atom temp)
               (loop-finish))
              ((equal (car temp) 3)
               (return (mv t temp)))
              (t (setq temp (cdr temp))))
        finally (return (mv nil nil)))
 :stobjs-out '(nil nil))

; As above, but membership test fails.
(must-fail
 (assert-event
  (loop$ with temp = '(1 2 3 4 5 6)
         do
         :values (nil nil)
         (cond ((atom temp)
                (loop-finish))
               ((equal (car temp) 7)
                (return (mv t temp)))
               (t (setq temp (cdr temp))))
         finally (return (mv nil nil)))
  :stobjs-out '(nil nil)))

; Test default for multiple values.  This shows the importance of the call of
; values-list inserted for DO loop$s in ACL2 source function oneify, using
; loop$-stobjs-out.  Here are also testing that the first argument of progn (or
; prog2) is translated with stobjs-out = t or stobjs-out = (nil).
(defun infinite-loop-mv ()
  (declare (xargs :verify-guards nil))
  (loop$ with temp of-type integer = 0
         do
         :measure (acl2-count temp)
         :values (nil nil)
         (progn (cw "Temp = ~x0~%" temp)
                (setq temp (1+ temp)))
         finally (return (mv 3 4))))

(thm (equal (infinite-loop-mv)
            '(nil nil)))

(must-fail
 (defun do-mv-5-bad (x)
; Modification of do-mv-2 that fails because it returns nil from implicit
; finally clause.
   (declare (xargs :guard (true-listp x)))
   (loop$ with temp = x
          with result = nil
          with len = 0
          do
          :values (nil nil)
          :guard (and (true-listp temp)
                      (natp len))
          (cond ((null temp)
                 (loop-finish))
                ((equal (car temp) 0)
                 (return (mv len result)))
                (t (mv-setq (temp result len)
                            (mv (cdr temp)
                                (cons (car temp) result)
                                (1+ len))))))))

(defun do-mv-5 (x)
; Modification of do-mv-2 that succeeds in spite of having no finally clause,
; because there is no loop-finish call in the do-body.
   (declare (xargs :guard (true-listp x)))
   (loop$ with temp = x
          with result = nil
          with len = 0
          do
          :values (nil nil)
          :guard (and (true-listp temp)
                      (natp len))
          (cond ((null temp)
                 (return (mv len result)))
                ((equal (car temp) 0)
                 (return (mv len result)))
                (t (mv-setq (temp result len)
                            (mv (cdr temp)
                                (cons (car temp) result)
                                (1+ len)))))))

; Here is an analogue of do-loop-counting-up (above) that returns multiple
; values that include a stobj.

(defun do-loop-counting-up-mv (i0 max st)
  (declare (xargs :guard (and (natp i0) (natp max))
                  :verify-guards nil
                  :stobjs st))
  (loop$ with i of-type (satisfies natp) = i0
         with cnt of-type integer = 0
         do
         :measure (nfix (- max i))
         :guard (natp max)
         :values (nil st)
         (if (>= i max)
             (loop-finish)
             (progn (setq cnt (+ 1 cnt))
                    (setq st (update-fld i st))
                    (setq i (+ 1 i))))
         finally
         (return
          (mv (list 'from i0 'to max 'is cnt 'steps 'and 'fld '= (fld st))
              st))))

; Repeating an experiment shown above, but on a different laptop:
#|
ACL2 !>(time$ (do-loop-counting-up 1 1000000))
; (EV-REC *RETURN-LAST-ARG3* ...) took 
; 57.72 seconds realtime, 57.71 seconds runtime
; (4,080,550,752 bytes allocated).
(FROM 1 TO 1000000 IS 999999 STEPS)
ACL2 !>(verify-guards do-loop-counting-up)
[[.. output omitted ..]]
Prover steps counted:  400639
 DO-LOOP-COUNTING-UP
ACL2 !>(time$ (do-loop-counting-up 1 1000000))
; (EV-REC *RETURN-LAST-ARG3* ...) took 
; 0.00 seconds realtime, 0.00 seconds runtime
; (144 bytes allocated).
(FROM 1 TO 1000000 IS 999999 STEPS)
ACL2 !>
|#
; And now repeating that experiment for the new version.
#|
ACL2 !>(time$ (do-loop-counting-up-mv 1 1000000 st))
; (EV-REC *RETURN-LAST-ARG3* ...) took 
; 67.41 seconds realtime, 67.39 seconds runtime
; (4,688,677,328 bytes allocated).
((FROM 1 TO 1000000
       IS 999999 STEPS AND FLD = 999999)
 <st>)
ACL2 !>(verify-guards do-loop-counting-up-mv)
[[.. output omitted ..]]
Prover steps counted:  634086
 DO-LOOP-COUNTING-UP-MV
ACL2 !>(time$ (do-loop-counting-up-mv 1 1000000 st))
; (EV-REC *RETURN-LAST-ARG3* ...) took 
; 0.01 seconds realtime, 0.01 seconds runtime
; (256 bytes allocated).
((FROM 1 TO 1000000
       IS 999999 STEPS AND FLD = 999999)
 <st>)
ACL2 !>
|#

; Test direct execution of do$.

(assert-event
 (equal (nth 3 (body 'do-mv-2 nil (w state)))
        '(DO$
          '(LAMBDA
            (ALIST)
            (DECLARE
             (XARGS :GUARD (IF (ALISTP ALIST)
                               (IF (TRUE-LISTP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                                   (NATP (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))
                                   'NIL)
                               'NIL)
                    :SPLIT-TYPES T)
             (IGNORABLE ALIST))
            (RETURN-LAST
             'PROGN
             '(LAMBDA$
               (ALIST)
               (DECLARE
                (XARGS :GUARD (AND (ALISTP ALIST)
                                   (TRUE-LISTP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                                   (NATP (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))))
               (LET ((TEMP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                     (RESULT (CDR (ASSOC-EQ-SAFE 'RESULT ALIST)))
                     (LEN (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))
                    (DECLARE (IGNORABLE TEMP RESULT LEN))
                    (ACL2-COUNT TEMP)))
             ((LAMBDA (TEMP RESULT LEN)
                      (ACL2-COUNT TEMP))
              (CDR (ASSOC-EQ-SAFE 'TEMP ALIST))
              (CDR (ASSOC-EQ-SAFE 'RESULT ALIST))
              (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))))
          (CONS (CONS 'TEMP X)
                (CONS (CONS 'RESULT 'NIL)
                      (CONS (CONS 'LEN '0) 'NIL)))
          '(LAMBDA
            (ALIST)
            (DECLARE
             (XARGS :GUARD (IF (ALISTP ALIST)
                               (IF (TRUE-LISTP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                                   (NATP (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))
                                   'NIL)
                               'NIL)
                    :SPLIT-TYPES T)
             (IGNORABLE ALIST))
            (RETURN-LAST
             'PROGN
             '(LAMBDA$
               (ALIST)
               (DECLARE
                (XARGS :GUARD (AND (ALISTP ALIST)
                                   (TRUE-LISTP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                                   (NATP (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))))
               (LET
                ((TEMP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                 (RESULT (CDR (ASSOC-EQ-SAFE 'RESULT ALIST)))
                 (LEN (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))
                (DECLARE (IGNORABLE TEMP RESULT LEN))
                (IF
                 (NULL TEMP)
                 (CONS ':LOOP-FINISH
                       (CONS 'NIL
                             (CONS (CONS (CONS 'TEMP TEMP)
                                         (CONS (CONS 'RESULT RESULT)
                                               (CONS (CONS 'LEN LEN) 'NIL)))
                                   'NIL)))
                 (CONS
                  'NIL
                  (CONS
                   (MV-NTH '2
                           (CONS (CDR TEMP)
                                 (CONS (CONS (CAR TEMP) RESULT)
                                       (CONS (BINARY-+ '1 LEN) 'NIL))))
                   (CONS
                    (CONS
                     (CONS 'TEMP
                           (MV-NTH '0
                                   (CONS (CDR TEMP)
                                         (CONS (CONS (CAR TEMP) RESULT)
                                               (CONS (BINARY-+ '1 LEN) 'NIL)))))
                     (CONS
                      (CONS 'RESULT
                            (MV-NTH '1
                                    (CONS (CDR TEMP)
                                          (CONS (CONS (CAR TEMP) RESULT)
                                                (CONS (BINARY-+ '1 LEN) 'NIL)))))
                      (CONS
                       (CONS 'LEN
                             (MV-NTH '2
                                     (CONS (CDR TEMP)
                                           (CONS (CONS (CAR TEMP) RESULT)
                                                 (CONS (BINARY-+ '1 LEN) 'NIL)))))
                       (CONS (CONS 'MV0
                                   (CONS (CDR TEMP)
                                         (CONS (CONS (CAR TEMP) RESULT)
                                               (CONS (BINARY-+ '1 LEN) 'NIL))))
                             'NIL))))
                    'NIL))))))
             ((LAMBDA
               (TEMP RESULT LEN)
               (IF
                (NULL TEMP)
                (CONS ':LOOP-FINISH
                      (CONS 'NIL
                            (CONS (CONS (CONS 'TEMP TEMP)
                                        (CONS (CONS 'RESULT RESULT)
                                              (CONS (CONS 'LEN LEN) 'NIL)))
                                  'NIL)))
                (CONS
                 'NIL
                 (CONS
                  (MV-NTH '2
                          (CONS (CDR TEMP)
                                (CONS (CONS (CAR TEMP) RESULT)
                                      (CONS (BINARY-+ '1 LEN) 'NIL))))
                  (CONS
                   (CONS
                    (CONS 'TEMP
                          (MV-NTH '0
                                  (CONS (CDR TEMP)
                                        (CONS (CONS (CAR TEMP) RESULT)
                                              (CONS (BINARY-+ '1 LEN) 'NIL)))))
                    (CONS
                     (CONS 'RESULT
                           (MV-NTH '1
                                   (CONS (CDR TEMP)
                                         (CONS (CONS (CAR TEMP) RESULT)
                                               (CONS (BINARY-+ '1 LEN) 'NIL)))))
                     (CONS
                      (CONS 'LEN
                            (MV-NTH '2
                                    (CONS (CDR TEMP)
                                          (CONS (CONS (CAR TEMP) RESULT)
                                                (CONS (BINARY-+ '1 LEN) 'NIL)))))
                      (CONS (CONS 'MV0
                                  (CONS (CDR TEMP)
                                        (CONS (CONS (CAR TEMP) RESULT)
                                              (CONS (BINARY-+ '1 LEN) 'NIL))))
                            'NIL))))
                   'NIL)))))
              (CDR (ASSOC-EQ-SAFE 'TEMP ALIST))
              (CDR (ASSOC-EQ-SAFE 'RESULT ALIST))
              (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))))
          '(LAMBDA
            (ALIST)
            (DECLARE (XARGS :GUARD (ALISTP ALIST)
                            :SPLIT-TYPES T)
                     (IGNORABLE ALIST))
            (RETURN-LAST
             'PROGN
             '(LAMBDA$
               (ALIST)
               (DECLARE (XARGS :GUARD (ALISTP ALIST)))
               (LET ((TEMP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                     (RESULT (CDR (ASSOC-EQ-SAFE 'RESULT ALIST)))
                     (LEN (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))
                    (DECLARE (IGNORABLE TEMP RESULT LEN))
                    (CONS ':RETURN
                          (CONS (CONS LEN (CONS RESULT 'NIL))
                                (CONS (CONS (CONS 'TEMP TEMP)
                                            (CONS (CONS 'RESULT RESULT)
                                                  (CONS (CONS 'LEN LEN) 'NIL)))
                                      'NIL)))))
             ((LAMBDA (TEMP RESULT LEN)
                      (CONS ':RETURN
                            (CONS (CONS LEN (CONS RESULT 'NIL))
                                  (CONS (CONS (CONS 'TEMP TEMP)
                                              (CONS (CONS 'RESULT RESULT)
                                                    (CONS (CONS 'LEN LEN) 'NIL)))
                                        'NIL))))
              (CDR (ASSOC-EQ-SAFE 'TEMP ALIST))
              (CDR (ASSOC-EQ-SAFE 'RESULT ALIST))
              (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))))
          '(NIL NIL)
          '(ACL2-COUNT TEMP)
          '(LOOP$ WITH TEMP = X WITH RESULT
                  = NIL WITH LEN = 0 DO :VALUES (NIL NIL)
                  :GUARD
                  (AND (TRUE-LISTP TEMP) (NATP LEN))
                  (IF (NULL TEMP)
                      (LOOP-FINISH)
                      (MV-SETQ (TEMP RESULT LEN)
                               (MV (CDR TEMP)
                                   (CONS (CAR TEMP) RESULT)
                                   (1+ LEN))))
                  FINALLY (RETURN (MV LEN RESULT))))))

; Note that below, we take the form above but replace ' by ` in the :FN slots;
; see :DOC gratuitous-lambda-object-restrictions.
(assert-event
 (mv-let
   (len result)
   (let ((x '(4 6 8)))
     (DO$
      '(LAMBDA
        (ALIST)
        (DECLARE
         (XARGS :GUARD (IF (ALISTP ALIST)
                           (IF (TRUE-LISTP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                               (NATP (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))
                               'NIL)
                           'NIL)
                :SPLIT-TYPES T)
         (IGNORABLE ALIST))
        (RETURN-LAST
         'PROGN
         '(LAMBDA$
           (ALIST)
           (DECLARE
            (XARGS :GUARD (AND (ALISTP ALIST)
                               (TRUE-LISTP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                               (NATP (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))))
           (LET ((TEMP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                 (RESULT (CDR (ASSOC-EQ-SAFE 'RESULT ALIST)))
                 (LEN (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))
                (DECLARE (IGNORABLE TEMP RESULT LEN))
                (ACL2-COUNT TEMP)))
         ((LAMBDA (TEMP RESULT LEN)
                  (ACL2-COUNT TEMP))
          (CDR (ASSOC-EQ-SAFE 'TEMP ALIST))
          (CDR (ASSOC-EQ-SAFE 'RESULT ALIST))
          (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))))
      (CONS (CONS 'TEMP X)
            (CONS (CONS 'RESULT 'NIL)
                  (CONS (CONS 'LEN '0) 'NIL)))
      '(LAMBDA
        (ALIST)
        (DECLARE
         (XARGS :GUARD (IF (ALISTP ALIST)
                           (IF (TRUE-LISTP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                               (NATP (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))
                               'NIL)
                           'NIL)
                :SPLIT-TYPES T)
         (IGNORABLE ALIST))
        (RETURN-LAST
         'PROGN
         '(LAMBDA$
           (ALIST)
           (DECLARE
            (XARGS :GUARD (AND (ALISTP ALIST)
                               (TRUE-LISTP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                               (NATP (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))))
           (LET
            ((TEMP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
             (RESULT (CDR (ASSOC-EQ-SAFE 'RESULT ALIST)))
             (LEN (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))
            (DECLARE (IGNORABLE TEMP RESULT LEN))
            (IF
             (NULL TEMP)
             (CONS ':LOOP-FINISH
                   (CONS 'NIL
                         (CONS (CONS (CONS 'TEMP TEMP)
                                     (CONS (CONS 'RESULT RESULT)
                                           (CONS (CONS 'LEN LEN) 'NIL)))
                               'NIL)))
             (CONS
              'NIL
              (CONS
               (MV-NTH '2
                       (CONS (CDR TEMP)
                             (CONS (CONS (CAR TEMP) RESULT)
                                   (CONS (BINARY-+ '1 LEN) 'NIL))))
               (CONS
                (CONS
                 (CONS 'TEMP
                       (MV-NTH '0
                               (CONS (CDR TEMP)
                                     (CONS (CONS (CAR TEMP) RESULT)
                                           (CONS (BINARY-+ '1 LEN) 'NIL)))))
                 (CONS
                  (CONS 'RESULT
                        (MV-NTH '1
                                (CONS (CDR TEMP)
                                      (CONS (CONS (CAR TEMP) RESULT)
                                            (CONS (BINARY-+ '1 LEN) 'NIL)))))
                  (CONS
                   (CONS 'LEN
                         (MV-NTH '2
                                 (CONS (CDR TEMP)
                                       (CONS (CONS (CAR TEMP) RESULT)
                                             (CONS (BINARY-+ '1 LEN) 'NIL)))))
                   (CONS (CONS 'MV0
                               (CONS (CDR TEMP)
                                     (CONS (CONS (CAR TEMP) RESULT)
                                           (CONS (BINARY-+ '1 LEN) 'NIL))))
                         'NIL))))
                'NIL))))))
         ((LAMBDA
           (TEMP RESULT LEN)
           (IF
            (NULL TEMP)
            (CONS ':LOOP-FINISH
                  (CONS 'NIL
                        (CONS (CONS (CONS 'TEMP TEMP)
                                    (CONS (CONS 'RESULT RESULT)
                                          (CONS (CONS 'LEN LEN) 'NIL)))
                              'NIL)))
            (CONS
             'NIL
             (CONS
              (MV-NTH '2
                      (CONS (CDR TEMP)
                            (CONS (CONS (CAR TEMP) RESULT)
                                  (CONS (BINARY-+ '1 LEN) 'NIL))))
              (CONS
               (CONS
                (CONS 'TEMP
                      (MV-NTH '0
                              (CONS (CDR TEMP)
                                    (CONS (CONS (CAR TEMP) RESULT)
                                          (CONS (BINARY-+ '1 LEN) 'NIL)))))
                (CONS
                 (CONS 'RESULT
                       (MV-NTH '1
                               (CONS (CDR TEMP)
                                     (CONS (CONS (CAR TEMP) RESULT)
                                           (CONS (BINARY-+ '1 LEN) 'NIL)))))
                 (CONS
                  (CONS 'LEN
                        (MV-NTH '2
                                (CONS (CDR TEMP)
                                      (CONS (CONS (CAR TEMP) RESULT)
                                            (CONS (BINARY-+ '1 LEN) 'NIL)))))
                  (CONS (CONS 'MV0
                              (CONS (CDR TEMP)
                                    (CONS (CONS (CAR TEMP) RESULT)
                                          (CONS (BINARY-+ '1 LEN) 'NIL))))
                        'NIL))))
               'NIL)))))
          (CDR (ASSOC-EQ-SAFE 'TEMP ALIST))
          (CDR (ASSOC-EQ-SAFE 'RESULT ALIST))
          (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))))
      '(LAMBDA
        (ALIST)
        (DECLARE (XARGS :GUARD (ALISTP ALIST)
                        :SPLIT-TYPES T)
                 (IGNORABLE ALIST))
        (RETURN-LAST
         'PROGN
         '(LAMBDA$
           (ALIST)
           (DECLARE (XARGS :GUARD (ALISTP ALIST)))
           (LET ((TEMP (CDR (ASSOC-EQ-SAFE 'TEMP ALIST)))
                 (RESULT (CDR (ASSOC-EQ-SAFE 'RESULT ALIST)))
                 (LEN (CDR (ASSOC-EQ-SAFE 'LEN ALIST))))
                (DECLARE (IGNORABLE TEMP RESULT LEN))
                (CONS ':RETURN
                      (CONS (CONS LEN (CONS RESULT 'NIL))
                            (CONS (CONS (CONS 'TEMP TEMP)
                                        (CONS (CONS 'RESULT RESULT)
                                              (CONS (CONS 'LEN LEN) 'NIL)))
                                  'NIL)))))
         ((LAMBDA (TEMP RESULT LEN)
                  (CONS ':RETURN
                        (CONS (CONS LEN (CONS RESULT 'NIL))
                              (CONS (CONS (CONS 'TEMP TEMP)
                                          (CONS (CONS 'RESULT RESULT)
                                                (CONS (CONS 'LEN LEN) 'NIL)))
                                    'NIL))))
          (CDR (ASSOC-EQ-SAFE 'TEMP ALIST))
          (CDR (ASSOC-EQ-SAFE 'RESULT ALIST))
          (CDR (ASSOC-EQ-SAFE 'LEN ALIST)))))
      '(NIL NIL)
      '(ACL2-COUNT TEMP)
      '(LOOP$ WITH TEMP = X WITH RESULT
              = NIL WITH LEN = 0 DO :VALUES (NIL NIL)
              :GUARD
              (AND (TRUE-LISTP TEMP) (NATP LEN))
              (IF (NULL TEMP)
                  (LOOP-FINISH)
                  (MV-SETQ (TEMP RESULT LEN)
                           (MV (CDR TEMP)
                               (CONS (CAR TEMP) RESULT)
                               (1+ LEN))))
              FINALLY (RETURN (MV LEN RESULT)))))
   (and (eql len 3)
        (equal result '(8 6 4)))))

; The following failed in the initial implementation of DO loop$ expressions.
(defun g3 ()
  (loop$ with ans = nil with i = 0
         do
         :measure (nfix (- 3 i))
         (progn (if (> (nfix i) 2)
                    (loop-finish)
                  (setq i (1+ i)))
                (setq ans
                      (loop$ with ans2 = ans with j = 0
                             do
                             :measure (nfix (- 6 j))
                             (progn
                               (if (> (nfix j) 5)
                                   (loop-finish)
                                 (setq j (1+ j)))
                               (setq ans2 (cons (cons i j) ans2)))
                             finally (return ans2))))
         finally (return ans)))

(assert-event (equal (g3)
                     '((3 . 6)
                       (3 . 5)
                       (3 . 4)
                       (3 . 3)
                       (3 . 2)
                       (3 . 1)
                       (2 . 6)
                       (2 . 5)
                       (2 . 4)
                       (2 . 3)
                       (2 . 2)
                       (2 . 1)
                       (1 . 6)
                       (1 . 5)
                       (1 . 4)
                       (1 . 3)
                       (1 . 2)
                       (1 . 1))))

(defun do-mv-6 (x)
; Modification of do-mv-5 that has
; both return and loop-finish in the loop body and also a finally body.
   (declare (xargs :guard (true-listp x)))
   (loop$ with temp = x
          with result = nil
          with len = 0
          do
          :values (nil nil)
          :guard (and (true-listp temp)
                      (natp len))
          (cond ((null temp)
                 (return (mv len result)))
                ((equal (car temp) 0)
                 (loop-finish))
                (t (mv-setq (temp result len)
                            (mv (cdr temp)
                                (cons (car temp) result)
                                (1+ len)))))
          finally
          (return (mv len result))))

(assert-event
 (mv-let
   (len result)
   (do-mv-5 '(a b c))
   (and (= len 3)
        (equal result '(c b a)))))

(assert-event
 (mv-let
   (len result)
   (do-mv-6 '(a b c))
   (and (= len 3)
        (equal result '(c b a)))))

; The following tests aren't about loops, so they may be better placed in a
; different book.  But warrants were first allowed for functions that take
; stobjs when supporting DO loop$ expressions, so we naturally placed the tests
; here.  The first update below is discussed in a comment in
; logic-code-to-runnable-code.

; Initialize st.
(value-triple (update-fld 1 st)
              :stobjs-out '(st))

; Update a non-live version of st.
(assert-event
 (equal (apply$ '(lambda (x)
                   (declare (xargs :guard (stp x) :split-types t))
                   (fld x))
                '((17)))
        17))

; Check that live stobj didn't change.
(assert-event
 (equal (fld st) 1))

; Here is a more complex version of the test above.
(assert-event
 (equal (apply$ 'apply$
                '((lambda (x)
                    (declare (xargs :guard (stp x) :split-types t))
                    (fld x))
                  ((17))))
        17))

; Check that live stobj didn't change.
(assert-event
 (equal (fld st) 1))

; A do loop$ within a for loop$:
(defun loop$-for-with-1 (n)
  (declare (xargs :guard (natp n)))
  (loop$ for i of-type (integer 0 *) from 1 to n
         collect
         (mv-let (x y)
           (loop$ with k2 of-type (integer 0 *) = i
                  with temp = nil
                  do
                  :values (nil nil)
                  (if (zp k2)
                      (return (mv temp temp))
                    (progn (setq temp (cons k2 temp))
                           (setq k2 (1- k2)))))
           (list (len x) y))))

(assert-event (equal (loop$-for-with-1 3)
                     '((1 (1))
                       (2 (1 2))
                       (3 (1 2 3)))))

; A for loop$ within a do loop$:
(defun loop$-with-for-1 (n)
  (declare (type (integer 1 *) n))
  (loop$ with i of-type (integer 0 *) = n
         with ans1 = nil
         with ans2 of-type integer = 0
         do
         :values (nil nil)
         (if (zp i)
             (return (mv ans2 ans1))
           (let ((temp (loop$ for k2 from 1 to i
                              collect k2)))
             (mv-setq (ans1 ans2 i)
                      (mv (append temp ans1)
                          (+ ans2 (len temp))
                          (1- i)))))))

(assert-event (mv-let (a b)
                (loop$-with-for-1 4)
                (and (equal a 10)
                     (equal b '(1 1 2 1 2 3 1 2 3 4)))))

(must-fail
; Error message:
#|
Illegal assignment in the finally body:
it is illegal to attempt an assignment (with SETQ or MV-SETQ) to ANS,
which is not among the local variables (ANS2 and J) in the lexical
scope containing (SETQ ANS ANS2).
|#
 (defun non-local-asst ()
  (loop$ with ans = nil with i = 0
         do
         (progn (if (> (nfix i) 2) (loop-finish) (setq i (1+ i)))
                (loop$ with ans2 = ans with j = 0 do
                       (progn
                         (if (> (nfix j) 5) (loop-finish) (setq j (1+ j)))
                         (setq ans2 (cons (cons i j) ans2)))
                       finally (setq ans ans2)))
         finally (return ans))))

(defwarrant put-global)

(defthm state-p1-update-nth-2-do-mv-7
  (implies (state-p1 st)
           (state-p1 (update-nth 2
                                 (add-pair 'do-mv-7 val (nth 2 st))
                                 st)))
  :hints (("Goal" :in-theory (enable state-p1))))

(defun do-mv-7 (x state)
; Modification of do-mv-6 that modifies state.
   (declare (xargs :guard (true-listp x) :stobjs state))
   (loop$ with temp = x
          with result = nil
          with len = 0
          do
          :values (state nil nil)
          :guard (and (true-listp temp)
                      (natp len)
                      (state-p state))
          (cond ((null temp)
                 (return (mv state len result)))
                ((equal (car temp) 0)
                 (loop-finish))
                (t (mv-setq (temp result len state)
                            (let ((state (f-put-global 'do-mv-7 len state)))
                              (mv (cdr temp)
                                  (cons (car temp) result)
                                  (1+ len)
                                  state)))))
          finally
          (return (mv state len result))))

(assert-event
 (pprogn
  (f-put-global 'do-mv-7 :uninitialized state)
  (mv-let
    (state len result)
    (do-mv-7 '(a b c) state)
    (mv (and (= len 3)
             (equal (f-get-global 'do-mv-7 state) 2)
             (equal result '(c b a)))
        state)))
 :stobjs-out '(nil state))

(must-fail
; It appears that the HyperSpec actually allows repeated variables in a
; multiple-value-setq, so we could presumably allow that for mv-setq.  However,
; that doesn't seem like a particularly useful capability, and somehow it seems
; a bit open to problems (e.g., does every Lisp implementation bind the
; variables from left to right?).  So we disallow that.
 (defun mv-repeated-vars (x)
   (declare (xargs :guard (true-listp x)))
   (loop$ with lst = x
          with val = nil
          do
          (if (atom lst)
              (return val)
            (mv-setq (val val lst)
                     (mv (car lst)
                         (car lst)
                         (cdr lst))))
          finally (return val))))

(defun do-mv-2-a (x)
; This variant of do-mv-2 has loop$ on the else branch of the top-level if,
; where we know the stobjs-out.
  (declare (xargs :guard (true-listp x)))
  (if (eq (car x) 'abc)
      (mv (car x) (cdr x))
    (loop$ with temp = x
           with result = nil
           with len = 0
           do
           :values (nil nil)
           :guard (and (true-listp temp)
                       (natp len))
           (if (null temp)
               (loop-finish)
             (mv-setq (temp result len)
                      (mv (cdr temp)
                          (cons (car temp) result)
                          (1+ len))))
           finally (return (mv len result)))))

(must-fail
; This variant of do-mv-2-a has loop$ on the else branch that doesn't match
; the stobjs-out determined from the then branch.
 (defun do-mv-2-a-bad (x)
   (declare (xargs :guard (true-listp x)))
   (if (eq (car x) 'abc)
       (mv 17 (car x) (cdr x))
     (loop$ with temp = x
            with result = nil
            with len = 0
            do
            :values (nil nil)
            :guard (and (true-listp temp)
                        (natp len))
            (if (null temp)
                (loop-finish)
              (mv-setq (temp result len)
                       (mv (cdr temp)
                           (cons (car temp) result)
                           (1+ len))))
            finally (return (mv len result)))))
 )

(defun do-mv-2-b (x)
; This variant of do-mv-2 has loop$ on the then branch of the top-level if,
; where we do not yet know the stobjs-out.
  (declare (xargs :guard (true-listp x)))
  (if (eq (car x) 'abc)
      (loop$ with temp = x
             with result = nil
             with len = 0
             do
             :values (nil nil)
             :guard (and (true-listp temp)
                         (natp len))
             (if (null temp)
                 (loop-finish)
               (mv-setq (temp result len)
                        (mv (cdr temp)
                            (cons (car temp) result)
                            (1+ len))))
             finally (return (mv len result)))
    (mv (car x) (cdr x))))

(defun do-mv-1-alt (x)
; This variant of do-mv-1 uses an mv-setq to set a locally-scoped variable.
  (declare (xargs :guard (true-listp x)))
  (loop$ with temp = x
         with result = nil
         with len = 0
         with my-car = 17
         do
         :guard (and (true-listp temp)
                     (natp len))
         (if (null temp)
             (loop-finish)
           (let ((my-car 0))
             (progn (setq my-car (car temp))
                    (mv-setq (temp result len)
                             (mv (cdr temp)
                                 (cons my-car result)
                                 (1+ len))))))
         finally (return (list len result my-car))))

; Let's check that do-mv-1-alt returns the same len and result as do-mv-1 and
; that do-mv-1-alt returns the right final value of my-car.
(assert-event (and (equal (do-mv-1-alt '(a b c d))
                          '(4 (D C B A) 17))
                   (equal (do-mv-1     '(a b c d))
                          '(4 (D C B A)))))

(must-fail
; This is just the body of loop-mv-1, with x replaced by '(a b c).  The error
; message says, appropriately, that "We prohibit certain events .. from being
; ancestrally dependent on loop$ and lambda$ expressions...."
 (defconst *c*
   (loop$ with temp = '(a b c)
          with result = nil
          with len = 0
          do
          :guard (and (true-listp temp)
                      (natp len))
          (if (null temp)
              (loop-finish)
            (mv-setq (temp result len)
                     (mv (cdr temp)
                         (cons (car temp) result)
                         (1+ len))))
          finally (return (list len result)))))

; Check that flet isn't allowed.

(defun$ my-op (x y)
  (declare (xargs :guard t))
  (* (nfix x) (nfix y)))

(must-fail
 (defun for-loop-with-flet (lst)
   (declare (xargs :guard (true-listp lst) :verify-guards nil))
   (flet ((my-op (x y) (+ (nfix x) (nfix y))))
     (loop$ for x in lst
            collect (my-op 3 (nfix x))))))

(must-fail
 (defun do-loop-with-flet (lst)
   (declare (xargs :guard t :verify-guards nil))
   (flet ((my-op (x y) (+ (nfix x) (nfix y))))
     (loop$ with temp = lst
            with ans of-type integer = 1
            do
            (if (atom temp)
                (return ans)
              (progn (setq ans (my-op (car temp) ans))
                     (setq temp (cdr temp))))))))

; In the variant of do-mv-3 below, we warrant a function that returns state and
; is not a stobj primitive, and use it in the do loop$.

(defun$ do-mv-3-alt-helper (st a x)
  (declare (xargs :stobjs st))
  (let ((st (update-fld
             (+ (ifix a) (ifix (fld st)))
             st)))
    (mv st x)))

(defun do-mv-3-alt (lst st)
  (declare (xargs :stobjs st :guard (true-listp lst)))
  (let ((st (update-fld 0 st)))
    (loop$ with temp of-type (satisfies true-listp) = lst
           do
           :values (st)
           :guard
; We include (stp st) because stobj-optp = nil for lambdas; see
; guard-clauses-for-fn1.
           (stp st)
           (cond ((endp temp)
                  (loop-finish))
                 (t (mv-setq (st temp)
                             (do-mv-3-alt-helper st (car temp) (cdr temp)))))
           finally (return st))))

(assert-event
 (let ((st (do-mv-3-alt '(1 2 4) st)))
   (mv (equal (fld st) 7) st))
 :stobjs-out '(nil st))

; The following example comes from :DOC loop$.
(defun test-loop$ (i0 max st)
  (declare (xargs :guard (and (natp i0) (natp max))
                  :stobjs st))
  (loop$ with i of-type (satisfies natp) = i0
         with cnt of-type integer = 0
         do
         :measure (nfix (- max i))
         :guard (and (natp max)
                     (natp cnt)
                     (stp st))
         :values (nil st)
         (if (>= i max)
             (loop-finish)
           (progn (setq st (update-fld i st))
                  (mv-setq (cnt i)
                           (mv (+ 1 cnt) (+ 1 i)))))
         finally
         :guard (stp st)
         (return
          (mv (list 'from i0 'to max 'is cnt 'steps 'and 'fld '= (fld st))
              st))))

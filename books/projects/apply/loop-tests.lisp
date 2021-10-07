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
;               (NOT (CONSP (CDR (ASSOC-EQUAL 'TEMP ALIST)))))
;          (NOT (CDR (ASSOC-EQUAL 'TEMP ALIST))))

; Subgoal 1.2
; (IMPLIES (AND (ALISTP ALIST)
;               (CONSP (CDR (ASSOC-EQUAL 'TEMP ALIST))))
;          (ACL2-NUMBERP (CDR (ASSOC-EQUAL 'ANS ALIST))))

; Subgoal 1.1
; (IMPLIES (AND (ALISTP ALIST)
;               (CONSP (CDR (ASSOC-EQUAL 'TEMP ALIST))))
;          (ACL2-NUMBERP (CADR (ASSOC-EQUAL 'TEMP ALIST))))


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
   (loop$ with temp of-type (satistfies nat-listp) = lst
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

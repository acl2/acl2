; Yet simpler Example of an Abstract Stobj with Stobj fields
; Copyright (C) 2021 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Sol Swords <sswords@centtech.com>
; Additional contributions: Matt Kaufmann <matthew.j.kaufmann@gmail.com>

; (Comment from Matt Kaufmann: I wrote this version of Sol Swords's book,
; two-usuallyequal-nums-stobj.lisp, to be simpler by using ordinary stobjs for
; the stobj fields (rather than abstract stobjs).  This serves nicely as an
; introduction, hence is referenced in :DOC nested-stobjs.)

(in-package "ACL2")

; Here are simple concrete stobjs each with a natural number field.
(defstobj n$ (n$val :type (integer 0 *) :initially 0))
(defstobj n$2 (n$val$c :type (integer 0 *) :initially 0)
  :congruent-to n$)

(defstobj two-usuallyequal-nums$c
  (uenslot1$c :type n$) ; stobj slot
  (uenslot2$c :type n$2) ; stobj slot
  (uenvalid$c :type (member t nil) :initially nil))

(defun-nx two-usuallyequal-nums$ap (x)

; A two-usuallyequal-nums contains three fields (valid slot1 . slot2).  Valid
; is Boolean, and slot1 and slot2 are n$ stobjs that must be equal if valid is
; T.

  (declare (xargs :guard t))
  (and (consp x)
       (consp (cdr x))
       (let* ((valid (car x))
              (slot1 (cadr x))
              (slot2 (cddr x)))
         (and (booleanp valid)
              (n$p slot1)
              (n$p slot2)
              (implies valid
                       (equal slot1 slot2))))))

(defun create-two-usuallyequal-nums$a ()
  (declare (xargs :guard t))
  (cons nil (cons '(0) '(0))))

(defun uenvalid$a (x)
  (declare (xargs :guard (two-usuallyequal-nums$ap x)))
  (and (car x) t)) ; coerced to Boolean

(defun uenslot1$a (x)
  (declare (xargs :guard (two-usuallyequal-nums$ap x)))
  (cadr x))

(defun uenslot2$a (x)
  (declare (xargs :guard (two-usuallyequal-nums$ap x)))
  (cddr x))

(local (in-theory (disable mod)))

(defun-nx update-uenslot1$a (n$ x)
  (declare (xargs :guard (and (two-usuallyequal-nums$ap x)
                              (or (not (uenvalid$a x))
                                  (non-exec (equal (n$val n$)
                                                   (n$val (uenslot2$a x))))))
                  :stobjs n$))
  (cons (car x) (cons n$ (cddr x))))

(defun-nx update-uenslot2$a (n$2 x)
  (declare (xargs :guard (and (two-usuallyequal-nums$ap x)
                              (or (not (uenvalid$a x))
                                  (non-exec (equal (n$val (uenslot1$a x))
                                                   (n$val n$2)))))
                  :stobjs n$2))
  (cons (car x) (cons (cadr x) n$2)))

(defun update-uenvalid$a (v x)
  (declare (xargs :guard (and (booleanp v)
                              (two-usuallyequal-nums$ap x)
                              (implies v
                                       (non-exec
                                        (equal (n$val (uenslot1$a x))
                                               (n$val (uenslot2$a x))))))))
  (cons v (cdr x)))

(defun-nx two-usuallyequal-nums$corr (two-usuallyequal-nums$c x)
  (declare (xargs :stobjs (two-usuallyequal-nums$c)))
  (and (two-usuallyequal-nums$cp two-usuallyequal-nums$c)
       (two-usuallyequal-nums$ap x)
       (let* ((n$ (uenslot1$c two-usuallyequal-nums$c))
              (n$2 (uenslot2$c two-usuallyequal-nums$c))
              (v (uenvalid$c two-usuallyequal-nums$c)))
         (let* ((ok (and (equal n$ (cadr x))
                         (equal n$2 (cddr x))
                         (equal v (car x)))))
           ok))))

(local
 (defthm equal-of-len
   (implies (syntaxp (quotep c))
            (equal (equal (len x) c)
                   (cond ((equal c 0) (atom x))
                         ((zp c) nil)
                         (t (and (consp x)
                                 (equal (len (cdr x)) (1- c)))))))))

; The uppercased events below were automatically generated by the defabsstobj
; event below them.

(DEFTHM CREATE-TWO-USUALLYEQUAL-NUMS{CORRESPONDENCE}
        (TWO-USUALLYEQUAL-NUMS$CORR (CREATE-TWO-USUALLYEQUAL-NUMS$C)
                                    (CREATE-TWO-USUALLYEQUAL-NUMS$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-TWO-USUALLYEQUAL-NUMS{PRESERVED}
        (TWO-USUALLYEQUAL-NUMS$AP (CREATE-TWO-USUALLYEQUAL-NUMS$A))
        :RULE-CLASSES NIL)

(DEFTHM UENSLOT1{CORRESPONDENCE}
        (IMPLIES (AND (TWO-USUALLYEQUAL-NUMS$CORR TWO-USUALLYEQUAL-NUMS$C
                                                  TWO-USUALLYEQUAL-NUMS)
                      (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS))
                 (EQUAL (UENSLOT1$C TWO-USUALLYEQUAL-NUMS$C)
                        (UENSLOT1$A TWO-USUALLYEQUAL-NUMS)))
        :RULE-CLASSES NIL)

(DEFTHM UENSLOT2{CORRESPONDENCE}
        (IMPLIES (AND (TWO-USUALLYEQUAL-NUMS$CORR TWO-USUALLYEQUAL-NUMS$C
                                                  TWO-USUALLYEQUAL-NUMS)
                      (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS))
                 (EQUAL (UENSLOT2$C TWO-USUALLYEQUAL-NUMS$C)
                        (UENSLOT2$A TWO-USUALLYEQUAL-NUMS)))
        :RULE-CLASSES NIL)

(DEFTHM UENVALID{CORRESPONDENCE}
        (IMPLIES (AND (TWO-USUALLYEQUAL-NUMS$CORR TWO-USUALLYEQUAL-NUMS$C
                                                  TWO-USUALLYEQUAL-NUMS)
                      (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS))
                 (EQUAL (UENVALID$C TWO-USUALLYEQUAL-NUMS$C)
                        (UENVALID$A TWO-USUALLYEQUAL-NUMS)))
        :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENSLOT1{CORRESPONDENCE}
 (IMPLIES
  (AND
   (TWO-USUALLYEQUAL-NUMS$CORR TWO-USUALLYEQUAL-NUMS$C
                               TWO-USUALLYEQUAL-NUMS)
   (N$P N$)
   (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS)
   (OR
      (NOT (UENVALID$A TWO-USUALLYEQUAL-NUMS))
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(EQUAL (N$VAL N$)
                                                     (N$VAL (UENSLOT2$A X))))
              (EQUAL (N$VAL N$)
                     (N$VAL (UENSLOT2$A TWO-USUALLYEQUAL-NUMS))))))
  (TWO-USUALLYEQUAL-NUMS$CORR (UPDATE-UENSLOT1$C N$ TWO-USUALLYEQUAL-NUMS$C)
                              (UPDATE-UENSLOT1$A N$ TWO-USUALLYEQUAL-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENSLOT1{PRESERVED}
 (IMPLIES
  (AND
   (N$P N$)
   (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS)
   (OR
      (NOT (UENVALID$A TWO-USUALLYEQUAL-NUMS))
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(EQUAL (N$VAL N$)
                                                     (N$VAL (UENSLOT2$A X))))
              (EQUAL (N$VAL N$)
                     (N$VAL (UENSLOT2$A TWO-USUALLYEQUAL-NUMS))))))
  (TWO-USUALLYEQUAL-NUMS$AP (UPDATE-UENSLOT1$A N$ TWO-USUALLYEQUAL-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENSLOT2{CORRESPONDENCE}
 (IMPLIES
  (AND
    (TWO-USUALLYEQUAL-NUMS$CORR TWO-USUALLYEQUAL-NUMS$C
                                TWO-USUALLYEQUAL-NUMS)
    (N$2P N$2)
    (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS)
    (OR (NOT (UENVALID$A TWO-USUALLYEQUAL-NUMS))
        (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(EQUAL (N$VAL (UENSLOT1$A X))
                                                       (N$VAL N$2)))
                (EQUAL (N$VAL (UENSLOT1$A TWO-USUALLYEQUAL-NUMS))
                       (N$VAL N$2)))))
  (TWO-USUALLYEQUAL-NUMS$CORR (UPDATE-UENSLOT2$C N$2 TWO-USUALLYEQUAL-NUMS$C)
                              (UPDATE-UENSLOT2$A N$2 TWO-USUALLYEQUAL-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENSLOT2{PRESERVED}
 (IMPLIES
  (AND
    (N$2P N$2)
    (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS)
    (OR (NOT (UENVALID$A TWO-USUALLYEQUAL-NUMS))
        (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(EQUAL (N$VAL (UENSLOT1$A X))
                                                       (N$VAL N$2)))
                (EQUAL (N$VAL (UENSLOT1$A TWO-USUALLYEQUAL-NUMS))
                       (N$VAL N$2)))))
  (TWO-USUALLYEQUAL-NUMS$AP (UPDATE-UENSLOT2$A N$2 TWO-USUALLYEQUAL-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENVALID{CORRESPONDENCE}
 (IMPLIES
  (AND
   (TWO-USUALLYEQUAL-NUMS$CORR TWO-USUALLYEQUAL-NUMS$C
                               TWO-USUALLYEQUAL-NUMS)
   (BOOLEANP V)
   (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS)
   (IMPLIES
      V
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(EQUAL (N$VAL (UENSLOT1$A X))
                                                     (N$VAL (UENSLOT2$A X))))
              (EQUAL (N$VAL (UENSLOT1$A TWO-USUALLYEQUAL-NUMS))
                     (N$VAL (UENSLOT2$A TWO-USUALLYEQUAL-NUMS))))))
  (TWO-USUALLYEQUAL-NUMS$CORR (UPDATE-UENVALID$C V TWO-USUALLYEQUAL-NUMS$C)
                              (UPDATE-UENVALID$A V TWO-USUALLYEQUAL-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENVALID{GUARD-THM}
 (IMPLIES
  (AND
   (TWO-USUALLYEQUAL-NUMS$CORR TWO-USUALLYEQUAL-NUMS$C
                               TWO-USUALLYEQUAL-NUMS)
   (BOOLEANP V)
   (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS)
   (IMPLIES
      V
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(EQUAL (N$VAL (UENSLOT1$A X))
                                                     (N$VAL (UENSLOT2$A X))))
              (EQUAL (N$VAL (UENSLOT1$A TWO-USUALLYEQUAL-NUMS))
                     (N$VAL (UENSLOT2$A TWO-USUALLYEQUAL-NUMS))))))
  (LET ((X V) (L '(T NIL)))
       (MBE :LOGIC (PROG2$ (MEMBER-EQL-EXEC$GUARD-CHECK X L)
                           (MEMBER-EQUAL X L))
            :EXEC (MEMBER-EQL-EXEC X L))))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENVALID{PRESERVED}
 (IMPLIES
  (AND
   (BOOLEANP V)
   (TWO-USUALLYEQUAL-NUMS$AP TWO-USUALLYEQUAL-NUMS)
   (IMPLIES
      V
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(EQUAL (N$VAL (UENSLOT1$A X))
                                                     (N$VAL (UENSLOT2$A X))))
              (EQUAL (N$VAL (UENSLOT1$A TWO-USUALLYEQUAL-NUMS))
                     (N$VAL (UENSLOT2$A TWO-USUALLYEQUAL-NUMS))))))
  (TWO-USUALLYEQUAL-NUMS$AP (UPDATE-UENVALID$A V TWO-USUALLYEQUAL-NUMS)))
 :RULE-CLASSES NIL)

(defabsstobj two-usuallyequal-nums
  :exports
  ((uenslot1 :logic uenslot1$a :exec uenslot1$c :updater update-uenslot1)
   (uenslot2 :logic uenslot2$a :exec uenslot2$c :updater update-uenslot2)
; Note that uenvalid is used in the guards of update-uenslot1 and
; update-uenslot2, so its function spec must appear before theirs.
   (uenvalid :logic uenvalid$a :exec uenvalid$c)
   (update-uenslot1 :logic update-uenslot1$a :exec update-uenslot1$c)
   (update-uenslot2 :logic update-uenslot2$a :exec update-uenslot2$c)
   (update-uenvalid :logic update-uenvalid$a :exec update-uenvalid$c)))

(defun fields-of-two-usuallyequal-nums (two-usuallyequal-nums)
  (declare (xargs :stobjs two-usuallyequal-nums))
  (stobj-let
; bindings:
   ((n$  (uenslot1 two-usuallyequal-nums))
    (n$2 (uenslot2 two-usuallyequal-nums)))
; producer variable:
   (n1 n2)
; producer:
   (mv (n$val n$) (n$val n$2))
; consumer:
   (list :n n1 :n2 n2 :valid (uenvalid two-usuallyequal-nums))))

(defun update-two-usuallyequal-nums (n two-usuallyequal-nums)

; We set the valid bit to nil first, so that we can sequentially update the two
; child stobjs.  Otherwise, if the valid bit were t after the first call of
; update-n$val below, then the guard proof obligation would fail for the first
; child stobj update (with update-uenslot1).  That update is only implicit in
; the stobj-let form below, but it's really there; if you admit this definition
; and then run

; (untranslate (body 'update-two-usuallyequal-nums nil (w state)) nil (w state))

; then you'll see the update-uenslot1 call in the untranslated body.

#||
(LET
 ((TWO-USUALLYEQUAL-NUMS (UPDATE-UENVALID NIL TWO-USUALLYEQUAL-NUMS)))
 (LET
  ((N$ (UENSLOT1 TWO-USUALLYEQUAL-NUMS))
   (N$2 (UENSLOT2 TWO-USUALLYEQUAL-NUMS)))
  (MV-LET
   (N$ N$2)
   (LET* ((N$ (UPDATE-N$VAL N N$))
          (N$2 (UPDATE-N$VAL N N$2)))
         (LIST N$ N$2))
   (LET*
        ((TWO-USUALLYEQUAL-NUMS (UPDATE-UENSLOT1 N$ TWO-USUALLYEQUAL-NUMS))
         (TWO-USUALLYEQUAL-NUMS (UPDATE-UENSLOT2 N$2 TWO-USUALLYEQUAL-NUMS)))
        (UPDATE-UENVALID T TWO-USUALLYEQUAL-NUMS)))))
||#

  (declare (xargs :guard (natp n)
                  :stobjs two-usuallyequal-nums))
  (let* ((two-usuallyequal-nums (update-uenvalid nil two-usuallyequal-nums)))
    (stobj-let ((n$ (uenslot1 two-usuallyequal-nums))
                (n$2 (uenslot2 two-usuallyequal-nums)))
               (n$ n$2)
               (let* ((n$ (update-n$val n n$))
                      (n$2 (update-n$val n n$2)))
                 (mv n$ n$2))
               (update-uenvalid t two-usuallyequal-nums))))
         
(assert-event (equal (fields-of-two-usuallyequal-nums two-usuallyequal-nums)
                     '(:N 0 :N2 0 :VALID NIL)))

(make-event
 (er-progn (trans-eval '(update-two-usuallyequal-nums 17 two-usuallyequal-nums)
                       'top state nil)
           (value '(value-triple t))))

(assert-event (equal (fields-of-two-usuallyequal-nums two-usuallyequal-nums)
                     '(:N 17 :N2 17 :VALID t)))

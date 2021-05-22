;;; This is a variation on two-usuallyequal-nums-stobj.lisp (copyright by
;;; Centaur Technology) that explores how swapping child stobjs might cause
;;; problems.

; Simple Example of an Abstract Stobj with Stobj fields
; Copyright (C) 2020 Centaur Technology
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

(in-package "ACL2")

;; Simple concrete stobj with a natural number field.  To make it as simple as
;; possible, I'm going to wrap it in an abstract stobj that just is equal to
;; the field.
(defstobj n$c (n$val$c :type (integer 0 *) :initially 0))

(defun n$ap (x)
  (declare (xargs :guard t))
  (natp x))

(defun create-n$a ()
  (declare (xargs :guard t))
  0)

(defun n$val$a (x)
  (declare (xargs :guard t))
  (nfix x))

(defun update-n$val$a (val x)
  (declare (xargs :guard (natp val))
           (ignore x))
  (nfix val))

(defun n-corr (n$c n$a)
  (declare (xargs :stobjs n$c))
  (and (n$cp n$c)
       (equal n$a (n$val$c n$c))))

(DEFTHM CREATE-N${CORRESPONDENCE}
        (N-CORR (CREATE-N$C) (CREATE-N$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-N${PRESERVED} (N$AP (CREATE-N$A))
        :RULE-CLASSES NIL)

(DEFTHM N$VAL{CORRESPONDENCE}
        (IMPLIES (N-CORR N$C N)
                 (EQUAL (N$VAL$C N$C) (N$VAL$A N)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-N$VAL{CORRESPONDENCE}
        (IMPLIES (AND (N-CORR N$C N) (NATP V))
                 (N-CORR (UPDATE-N$VAL$C V N$C)
                         (UPDATE-N$VAL$A V N)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-N$VAL{GUARD-THM}
        (IMPLIES (AND (N-CORR N$C N) (NATP V))
                 (AND (INTEGERP V) (<= 0 V)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-N$VAL{PRESERVED}
        (IMPLIES (AND (N$AP N) (NATP V))
                 (N$AP (UPDATE-N$VAL$A V N)))
        :RULE-CLASSES NIL)

(defabsstobj n$
  :concrete n$c
  :recognizer (n$p :logic n$ap :exec n$cp)
  :creator (create-n$ :logic create-n$a :exec create-n$c)
  :corr-fn n-corr
  :exports ((n$val :logic n$val$a :exec n$val$c)
            (update-n$val :logic update-n$val$a :exec update-n$val$c)))

(defabsstobj n$2
  :concrete n$c
  :recognizer (n2$p :logic n$ap :exec n$cp)
  :creator (create-n2$ :logic create-n$a :exec create-n$c)
  :corr-fn n-corr
  :exports ((n$2val :logic n$val$a :exec n$val$c)
            (update-n$2val :logic update-n$val$a :exec update-n$val$c))
  :congruent-to n$)

(defstobj two-ordered-nums$c
  (uenslot1$c :type n$) ;; stobj slot
  (uenslot2$c :type n$2) ;; stobj slot
  (uenvalid$c :type (member t nil) :initially nil))

;; A two-ordered-nums contains three fields (valid slot1 . slot2).  Valid
;; is Boolean, slot1 and slot2 are natural numbers, and they must be equal if
;; valid is T.
(defun two-ordered-nums$ap (x)
  (declare (xargs :guard t))
  (and (consp x)
       (consp (cdr x))
       (let* ((valid (car x))
              (slot1 (cadr x))
              (slot2 (cddr x)))
         (and (booleanp valid)
              (natp slot1)
              (natp slot2)
              (implies valid
                       (< slot1 slot2))))))

(defun create-two-ordered-nums$a ()
  (declare (xargs :guard t))
  (cons nil (cons 0 0)))

(defun uenvalid$a (x)
  (declare (xargs :guard (two-ordered-nums$ap x)))
  (and (car x) t))

(defun uenslot1$a (x)
  (declare (xargs :guard (two-ordered-nums$ap x)))
  (nfix (cadr x)))

(defun uenslot2$a (x)
  (declare (xargs :guard (two-ordered-nums$ap x)))
  (nfix (cddr x)))

(local (in-theory (disable mod)))

(defun update-uenslot1$a (n$ x)
  (declare (xargs :guard (and (two-ordered-nums$ap x)
                              (or (not (uenvalid$a x))
                                  (non-exec (< (n$val n$)
                                               (n$val (uenslot2$a x))))))
                  :stobjs n$))
  (cons (car x) (cons (n$val n$) (cddr x))))

(defun update-uenslot2$a (n$2 x)
  (declare (xargs :guard (and (two-ordered-nums$ap x)
                              (or (not (uenvalid$a x))
                                  (non-exec (< (n$val (uenslot1$a x))
                                               (n$val n$2)))))
                  :stobjs n$2))
  (cons (car x) (cons (cadr x) (n$val n$2))))

(defun update-uenvalid$a (v x)
  (declare (xargs :guard (and (booleanp v)
                              (two-ordered-nums$ap x)
                              (implies v
                                       (non-exec
                                        (< (n$val (uenslot1$a x))
                                           (n$val (uenslot2$a x))))))))
  (cons v (cdr x)))

(defun-nx two-ordered-nums-corr (two-ordered-nums$c x)
  (declare (xargs :stobjs (two-ordered-nums$c)))
  (and (two-ordered-nums$cp two-ordered-nums$c)
       (two-ordered-nums$ap x)
       (let* ((n$ (uenslot1$c two-ordered-nums$c))
              (n$2 (uenslot2$c two-ordered-nums$c))
              (v (uenvalid$c two-ordered-nums$c)))
         (let* ((ok (and (equal (n$val n$) (cadr x))
                         (equal (n$val n$2) (cddr x))
                         (equal v (car x)))))
           ok))))

(local (defthm equal-of-len
         (implies (syntaxp (quotep c))
                  (equal (equal (len x) c)
                         (cond ((equal c 0) (atom x))
                               ((zp c) nil)
                               (t (and (consp x)
                                       (equal (len (cdr x)) (1- c)))))))))

;; The uppercased events below were automatically generated by the defabsstobj
;; event below them.

(DEFTHM CREATE-TWO-ORDERED-NUMS{CORRESPONDENCE}
  (TWO-ORDERED-NUMS-CORR (CREATE-TWO-ORDERED-NUMS$C)
                         (CREATE-TWO-ORDERED-NUMS$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-TWO-ORDERED-NUMS{PRESERVED}
        (TWO-ORDERED-NUMS$AP (CREATE-TWO-ORDERED-NUMS$A))
        :RULE-CLASSES NIL)

(DEFTHM UENSLOT1{CORRESPONDENCE}
        (IMPLIES (AND (TWO-ORDERED-NUMS-CORR TWO-ORDERED-NUMS$C
                                             TWO-ORDERED-NUMS)
                      (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS))
                 (EQUAL (UENSLOT1$C TWO-ORDERED-NUMS$C)
                        (UENSLOT1$A TWO-ORDERED-NUMS)))
        :RULE-CLASSES NIL)

(DEFTHM UENSLOT2{CORRESPONDENCE}
        (IMPLIES (AND (TWO-ORDERED-NUMS-CORR TWO-ORDERED-NUMS$C
                                             TWO-ORDERED-NUMS)
                      (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS))
                 (EQUAL (UENSLOT2$C TWO-ORDERED-NUMS$C)
                        (UENSLOT2$A TWO-ORDERED-NUMS)))
        :RULE-CLASSES NIL)

(DEFTHM UENVALID{CORRESPONDENCE}
        (IMPLIES (AND (TWO-ORDERED-NUMS-CORR TWO-ORDERED-NUMS$C
                                             TWO-ORDERED-NUMS)
                      (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS))
                 (EQUAL (UENVALID$C TWO-ORDERED-NUMS$C)
                        (UENVALID$A TWO-ORDERED-NUMS)))
        :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENSLOT1{CORRESPONDENCE}
 (IMPLIES
  (AND
   (TWO-ORDERED-NUMS-CORR TWO-ORDERED-NUMS$C
                          TWO-ORDERED-NUMS)
   (N$P N$)
   (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS)
   (OR
      (NOT (UENVALID$A TWO-ORDERED-NUMS))
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(< (N$VAL N$)
                                                 (N$VAL (UENSLOT2$A X))))
              (< (N$VAL N$)
                 (N$VAL (UENSLOT2$A TWO-ORDERED-NUMS))))))
  (TWO-ORDERED-NUMS-CORR (UPDATE-UENSLOT1$C N$ TWO-ORDERED-NUMS$C)
                         (UPDATE-UENSLOT1$A N$ TWO-ORDERED-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENSLOT1{PRESERVED}
 (IMPLIES
  (AND
   (N$P N$)
   (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS)
   (OR
      (NOT (UENVALID$A TWO-ORDERED-NUMS))
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(< (N$VAL N$)
                                                 (N$VAL (UENSLOT2$A X))))
              (< (N$VAL N$)
                 (N$VAL (UENSLOT2$A TWO-ORDERED-NUMS))))))
  (TWO-ORDERED-NUMS$AP (UPDATE-UENSLOT1$A N$ TWO-ORDERED-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENSLOT2{CORRESPONDENCE}
 (IMPLIES
  (AND
    (TWO-ORDERED-NUMS-CORR TWO-ORDERED-NUMS$C
                                TWO-ORDERED-NUMS)
    (N2$P N$2)
    (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS)
    (OR (NOT (UENVALID$A TWO-ORDERED-NUMS))
        (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(< (N$VAL (UENSLOT1$A X))
                                                   (N$VAL N$2)))
                (< (N$VAL (UENSLOT1$A TWO-ORDERED-NUMS))
                   (N$VAL N$2)))))
  (TWO-ORDERED-NUMS-CORR (UPDATE-UENSLOT2$C N$2 TWO-ORDERED-NUMS$C)
                              (UPDATE-UENSLOT2$A N$2 TWO-ORDERED-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENSLOT2{PRESERVED}
 (IMPLIES
  (AND
    (N2$P N$2)
    (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS)
    (OR (NOT (UENVALID$A TWO-ORDERED-NUMS))
        (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(< (N$VAL (UENSLOT1$A X))
                                                   (N$VAL N$2)))
                (< (N$VAL (UENSLOT1$A TWO-ORDERED-NUMS))
                   (N$VAL N$2)))))
  (TWO-ORDERED-NUMS$AP (UPDATE-UENSLOT2$A N$2 TWO-ORDERED-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENVALID{CORRESPONDENCE}
 (IMPLIES
  (AND
   (TWO-ORDERED-NUMS-CORR TWO-ORDERED-NUMS$C
                          TWO-ORDERED-NUMS)
   (BOOLEANP V)
   (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS)
   (IMPLIES
      V
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(< (N$VAL (UENSLOT1$A X))
                                                 (N$VAL (UENSLOT2$A X))))
              (< (N$VAL (UENSLOT1$A TWO-ORDERED-NUMS))
                 (N$VAL (UENSLOT2$A TWO-ORDERED-NUMS))))))
  (TWO-ORDERED-NUMS-CORR (UPDATE-UENVALID$C V TWO-ORDERED-NUMS$C)
                         (UPDATE-UENVALID$A V TWO-ORDERED-NUMS)))
 :RULE-CLASSES NIL)

(DEFTHM
 UPDATE-UENVALID{GUARD-THM}
 (IMPLIES
  (AND
   (TWO-ORDERED-NUMS-CORR TWO-ORDERED-NUMS$C
                          TWO-ORDERED-NUMS)
   (BOOLEANP V)
   (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS)
   (IMPLIES
      V
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(< (N$VAL (UENSLOT1$A X))
                                                 (N$VAL (UENSLOT2$A X))))
              (< (N$VAL (UENSLOT1$A TWO-ORDERED-NUMS))
                 (N$VAL (UENSLOT2$A TWO-ORDERED-NUMS))))))
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
   (TWO-ORDERED-NUMS$AP TWO-ORDERED-NUMS)
   (IMPLIES
      V
      (PROG2$ (THROW-NONEXEC-ERROR :NON-EXEC '(< (N$VAL (UENSLOT1$A X))
                                                 (N$VAL (UENSLOT2$A X))))
              (< (N$VAL (UENSLOT1$A TWO-ORDERED-NUMS))
                 (N$VAL (UENSLOT2$A TWO-ORDERED-NUMS))))))
  (TWO-ORDERED-NUMS$AP (UPDATE-UENVALID$A V TWO-ORDERED-NUMS)))
 :RULE-CLASSES NIL)

(defabsstobj two-ordered-nums
  :recognizer (two-ordered-numsp :logic two-ordered-nums$ap :exec two-ordered-nums$cp)
  :creator (create-two-ordered-nums :logic create-two-ordered-nums$a :exec create-two-ordered-nums$c)
  :corr-fn two-ordered-nums-corr
  :exports ((uenslot1 :logic uenslot1$a :exec uenslot1$c :updater update-uenslot1)
            (uenslot2 :logic uenslot2$a :exec uenslot2$c :updater update-uenslot2)
            ;; Note that uenvalid is used in the guards of update-uenslot1 and
            ;; update-uenslot2, so its function spec must appear before
            ;; theirs.
            (uenvalid :logic uenvalid$a :exec uenvalid$c)
            (update-uenslot1 :logic update-uenslot1$a :exec update-uenslot1$c)
            (update-uenslot2 :logic update-uenslot2$a :exec update-uenslot2$c)
            (update-uenvalid :logic update-uenvalid$a :exec update-uenvalid$c)))

(defun update-two-ordered-nums (n1 n2 two-ordered-nums)
  (declare (xargs :guard (and (natp n1) (natp n2) (< n1 n2))
                  :stobjs two-ordered-nums))
  (let* ((two-ordered-nums (update-uenvalid nil two-ordered-nums)))
    (stobj-let ((n$ (uenslot1 two-ordered-nums))
                (n$2 (uenslot2 two-ordered-nums)))
               (n$ n$2)
               (let* ((n$ (update-n$val n1 n$))
                      (n$2 (update-n$val n2 n$2)))
                 (mv n$ n$2))
               (update-uenvalid t two-ordered-nums))))
         
(defun fields-of-two-ordered-nums (two-ordered-nums)
  (declare (xargs :stobjs two-ordered-nums))
  (stobj-let ((n$ (uenslot1 two-ordered-nums))
              (n$2 (uenslot2 two-ordered-nums)))
             (n1 n2)
             (mv (n$val n$) (n$val n$2))
             (list :n n1 :n2 n2 :valid (uenvalid two-ordered-nums))))

(assert-event (equal (fields-of-two-ordered-nums two-ordered-nums)
                     '(:N 0 :N2 0 :VALID NIL)))

(make-event
 (er-progn (trans-eval '(update-two-ordered-nums 17 23 two-ordered-nums)
                       'top state nil)
           (value '(value-triple t))))

(assert-event (equal (fields-of-two-ordered-nums two-ordered-nums)
                     '(:N 17 :N2 23 :VALID t)))


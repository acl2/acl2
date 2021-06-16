; Defabsstobj Example 5
; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann, Dec., 2018
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Here we illustrate building an abstract stobj on top of an abstract stobj,
; concluding with some tests to check proper operation on that top-level stobj.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Concrete stobj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj st0
  fld0
  (mem0 :type (array (integer 0 *) (100)) :initially 0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Abstract stobj based on conventional concrete stobj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun st1$ap (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 2)
       (mem0p (nth 1 x))
       (equal (len (nth 1 x)) 100)))

(defun lookup1$a (k s)
  (declare (xargs :guard (and (st1$ap s)
                              (natp k)
                              (< k 100))))
  (nth k (nth 1 s)))

(defun update1$a (k v s)
  (declare (xargs :guard (and (st1$ap s)
                              (natp k)
                              (< k 100)
                              (natp v))))
  (list (car s)
        (update-nth k v (nth 1 s))))

(defun fld1$a (s)
  (declare (xargs :guard (st1$ap s)))
  (car s))

(defun update-fld1$a (v s)
  (declare (xargs :guard (st1$ap s)))
  (list v (nth 1 s)))

(defun create-st1$a ()
  (declare (xargs :guard t))
  (list nil (make-list 100 :initial-element 0)))

(defun st1$corr (s0 s1)
  (and (st0p s0)
       (st1$ap s1)
       (equal s0 s1)))

(DEFTHM CREATE-ST1{CORRESPONDENCE}
        (ST1$CORR (CREATE-ST0) (CREATE-ST1$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-ST1{PRESERVED}
        (ST1$AP (CREATE-ST1$A))
        :RULE-CLASSES NIL)

(DEFTHM LOOKUP1{CORRESPONDENCE}
        (IMPLIES (AND (ST1$CORR ST0 ST1)
                      (ST1$AP ST1)
                      (NATP I)
                      (< I 100))
                 (EQUAL (MEM0I I ST0) (LOOKUP1$A I ST1)))
        :RULE-CLASSES NIL)

(DEFTHM LOOKUP1{GUARD-THM}
        (IMPLIES (AND (ST1$CORR ST0 ST1)
                      (ST1$AP ST1)
                      (NATP I)
                      (< I 100))
                 (AND (INTEGERP I)
                      (<= 0 I)
                      (< I (MEM0-LENGTH ST0))))
        :RULE-CLASSES NIL)

(defthm update-nth-open
  (implies (and (syntaxp (quotep n))
                (posp n))
           (equal (update-nth n v x)
                  (cons (car x)
                        (update-nth (1- n) v (cdr x))))))

(defthm equal-plus-len
  (implies (and (acl2-numberp k1)
                (acl2-numberp k2)
                (true-listp x)
                (syntaxp (quotep k1))
                (syntaxp (quotep k2)))
           (equal (equal (+ k1 (len x)) k2)
                  (equal (len x) (- k2 k1)))))

(defthm mem0p-update-nth
  (implies (and (mem0p x)
                (natp n)
                (< n (len x))
                (natp v))
           (mem0p (update-nth n v x))))

(defthm equal-len-0
  (equal (equal (len x) 0)
         (atom x)))

(DEFTHM UPDATE1{CORRESPONDENCE}
        (IMPLIES (AND (ST1$CORR ST0 ST1)
                      (ST1$AP ST1)
                      (NATP I)
                      (< I 100)
                      (NATP V))
                 (ST1$CORR (UPDATE-MEM0I I V ST0)
                           (UPDATE1$A I V ST1)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE1{GUARD-THM}
        (IMPLIES (AND (ST1$CORR ST0 ST1)
                      (ST1$AP ST1)
                      (NATP I)
                      (< I 100)
                      (NATP V))
                 (AND (INTEGERP I)
                      (<= 0 I)
                      (< I (MEM0-LENGTH ST0))
                      (INTEGERP V)
                      (<= 0 V)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE1{PRESERVED}
        (IMPLIES (AND (ST1$AP ST1)
                      (NATP I)
                      (< I 100)
                      (NATP V))
                 (ST1$AP (UPDATE1$A I V ST1)))
        :RULE-CLASSES NIL)

(DEFTHM FLD1{CORRESPONDENCE}
        (IMPLIES (AND (ST1$CORR ST0 ST1) (ST1$AP ST1))
                 (EQUAL (FLD0 ST0) (FLD1$A ST1)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD1{CORRESPONDENCE}
        (IMPLIES (AND (ST1$CORR ST0 ST1) (ST1$AP ST1))
                 (ST1$CORR (UPDATE-FLD0 V ST0)
                           (UPDATE-FLD1$A V ST1)))
        :otf-flg t
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD1{PRESERVED}
        (IMPLIES (ST1$AP ST1)
                 (ST1$AP (UPDATE-FLD1$A V ST1)))
        :RULE-CLASSES NIL)

(defabsstobj st1
  :foundation st0
  :recognizer (st1p :logic st1$ap :exec st0p)
  :creator (create-st1 :logic create-st1$a :exec create-st0)
  :exports ((lookup1 :exec mem0i)
            (update1 :exec update-mem0i)
            (fld1 :exec fld0)
            (update-fld1 :exec update-fld0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Abstract stobj based on abstract stobj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun st2$ap (x)
  (declare (xargs :guard t))
  (st1$ap x))

(defun lookup2$a (k s)
  (declare (xargs :guard (and (st2$ap s)
                              (natp k)
                              (< k 100))))
  (lookup1$a k s))

(defun update2$a (k v s)
  (declare (xargs :guard (and (st2$ap s)
                              (natp k)
                              (< k 100)
                              (natp v))))
  (update1$a k v s))

(defun fld2$a (s)
  (declare (xargs :guard (st2$ap s)))
  (car s))

(defun update-fld2$a (v s)
  (declare (xargs :guard (st2$ap s)))
  (update-fld1$a v s))

(defun create-st2$a ()
  (declare (xargs :guard t))
  (create-st1$a))

(defun st2$corr (s0 s1)
  (and (st1p s0)
       (st2$ap s1)
       (equal s0 s1)))

(DEFTHM CREATE-ST2{CORRESPONDENCE}
        (ST2$CORR (CREATE-ST1) (CREATE-ST1$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-ST2{PRESERVED}
        (ST2$AP (CREATE-ST1$A))
        :RULE-CLASSES NIL)

(DEFTHM LOOKUP2{CORRESPONDENCE}
        (IMPLIES (AND (ST2$CORR ST1 ST2)
                      (ST2$AP ST2)
                      (NATP I)
                      (< I 100))
                 (EQUAL (LOOKUP1 I ST1)
                        (LOOKUP2$A I ST2)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE2{CORRESPONDENCE}
        (IMPLIES (AND (ST2$CORR ST1 ST2)
                      (ST2$AP ST2)
                      (NATP I)
                      (< I 100)
                      (NATP V))
                 (ST2$CORR (UPDATE1 I V ST1)
                           (UPDATE2$A I V ST2)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE2{PRESERVED}
        (IMPLIES (AND (ST2$AP ST2)
                      (NATP I)
                      (< I 100)
                      (NATP V))
                 (ST2$AP (UPDATE2$A I V ST2)))
        :RULE-CLASSES NIL)

(DEFTHM FLD2{CORRESPONDENCE}
        (IMPLIES (AND (ST2$CORR ST1 ST2) (ST2$AP ST2))
                 (EQUAL (FLD1 ST1) (FLD2$A ST2)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD2{CORRESPONDENCE}
        (IMPLIES (AND (ST2$CORR ST1 ST2) (ST2$AP ST2))
                 (ST2$CORR (UPDATE-FLD1 V ST1)
                           (UPDATE-FLD2$A V ST2)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-FLD2{PRESERVED}
        (IMPLIES (ST2$AP ST2)
                 (ST2$AP (UPDATE-FLD2$A V ST2)))
        :RULE-CLASSES NIL)

(defabsstobj st2
  :foundation st1
  :recognizer (st2p :logic st2$ap :exec st1p)
  :creator (create-st2 :logic create-st1$a :exec create-st1)
  :exports ((lookup2 :exec lookup1)
            (update2 :exec update1)
            (fld2 :exec fld1)
            (update-fld2 :exec update-fld1)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Basic tests
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro my-test (form check &optional aok)
  `(local (make-event
           (er-progn
            (trans-eval ',form '(my-test . ,form) state ,aok)
            (value '(assert-event ,check))))))

(set-inhibit-warnings "User-stobjs-modified")

(my-test (update2 3 17 st2)
         (and (equal (lookup2 3 st2) 17)
              (equal (lookup2 4 st2) 0)))

(my-test (let* ((st2 (update2 3 18 st2))
                (val2 (lookup2 3 st2))
                (st2 (update2 4 val2 st2)))
           st2)
         (and (equal (lookup2 4 st2)
                     18)
; Old stobjs aren't modified:
              (equal (lookup1 3 st1)
                     0)
              (equal (mem0i 3 st0)
                     0)))

(defun update-range (i j v st2)

; Update memory fields of st2 for all indices n with i= < n < j, and increments
; fld2 of st2 by j-i.

  (declare (xargs :stobjs st2
                  :guard (and (natp i)
                              (natp j)
                              (<= i j)
                              (<= j 100)
                              (natp v))
                  :measure (nfix (- j i))))
  (cond ((mbe :logic (zp (nfix (- j i)))
              :exec (int= i j))
         st2)
        (t (let* ((f2 (nfix (fld2 st2)))
                  (st2 (update-fld2 (1+ f2) st2))
                  (j (1- j))
                  (st2 (update2 j v st2)))
             (update-range i j v st2)))))

(my-test (update-range 7 20 23 st2)
         (and (equal (lookup2 3 st2) 18)
              (equal (lookup2 4 st2) 18)
              (equal (lookup2 5 st2) 0)
              (equal (lookup2 7 st2) 23)
              (equal (lookup2 8 st2) 23)
              (equal (lookup2 15 st2) 23)
              (equal (lookup2 19 st2) 23)
              (equal (lookup2 20 st2) 0)
              (equal (fld2 st2) 13)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Tests involving memoization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun fld2-fn (st2)
  (declare (xargs :stobjs st2))
  (fld2 st2))

(memoize 'fld2-fn)

(my-test (update-fld2 5 st2)
         (equal (fld2-fn st2) 5))

(my-test t
         (equal (fld2-fn st2) 5))

(my-test (update-fld2 7 st2)
; Make sure the memoize table was flushed.
         (equal (fld2-fn st2) 7))

(defun lookup2-fn (i st2)
  (declare (xargs :stobjs st2
                  :guard (and (natp i)
                              (< i 100))))
  (lookup2 i st2))

(my-test (update2 3 12 st2)
         (equal (lookup2-fn 3 st2) 12))

(my-test (update2 3 13 st2)
; Make sure the memoize table was flushed.
         (equal (lookup2-fn 3 st2) 13))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Congruent stobjs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defabsstobj st3
  :congruent-to st2
  :foundation st1
  :recognizer (st3p :logic st2$ap :exec st1p)
  :creator (create-st3 :logic create-st1$a :exec create-st1)
  :exports ((lookup3 :logic lookup2$a :exec lookup1)
            (update3 :logic update2$a :exec update1)
            (fld3 :logic fld2$a :exec fld1)
            (update-fld3 :logic update-fld2$a :exec update-fld1)))

(my-test (update3 33 17 st3)
         (and (equal (lookup3 33 st3) 17)
              (equal (lookup3 34 st3) 0)))

(memoize 'lookup2-fn)

(my-test (let* ((st3 (update2 33 50 st3))
                (val3 (lookup2-fn 33 st3))
                (st3 (update-fld3 val3 st3))
                (st3 (update3 33 60 st3)))
           st3)
         (and (equal (fld3 st3)
                     50)
; Memoization is flushed:
              (equal (lookup2-fn 33 st3)
                     60)
; Old stobjs aren't modified:
              (equal (lookup2-fn 33 st2)
                     0)
              (equal (lookup2 33 st2)
                     0)
              (equal (lookup1 33 st1)
                     0)
              (equal (mem0i 33 st0)
                     0)))

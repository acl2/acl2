; Copyright (C) 2024, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book is based on books/demos/defabsstobj-example-1.lisp, which has
; the following header.

; Copyright (C) 2012, Regents of the University of Texas
; Written by Matt Kaufmann, July, 2012 (updated Nov. and Dec., 2012)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See impl-top.lisp for explanation, and see gen-support.lisp for an analogous
; book to support a generic stobj that is also based on
; books/demos/defabsstobj-example-1.lisp.

(in-package "ACL2")

(defstobj st{impl}$c
  (mem{impl}$c :type (array (integer 0 *) (100))
         :initially 0 :resizable nil)
  (misc{impl}$c :initially 0))

(defund mem$c-entryp (v)
  (declare (xargs :guard (integerp v)))
  (evenp v))

(defun st{impl}$cp+ (st{impl}$c)
  (declare (xargs :stobjs st{impl}$c))
  (and (st{impl}$cp st{impl}$c)
       (mem$c-entryp (mem{impl}$ci 0 st{impl}$c))))

(defun map$ap (x)
  (declare (xargs :guard t))
  (cond ((atom x) (null x))
        ((atom (car x)) nil)
        (t (and (natp (caar x))
                (< (caar x) 50)
                (natp (cdar x))
                (mem$c-entryp (cdar x))
                (map$ap (cdr x))))))

(defun st$ap (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (equal (len x) 2)
       (map$ap (nth 1 x))))

(defun misc$a (st$a)
  (declare (xargs :guard (st$ap st$a)))
  (nth 0 st$a))

(defun update-misc$a (v st$a)
  (declare (xargs :guard (st$ap st$a)))
  (update-nth 0 v st$a))

(defthm map$ap-forward-to-eqlable-alistp
  (implies (map$ap x)
           (eqlable-alistp x))
  :rule-classes :forward-chaining)

(defun lookup$a (k st$a)
  (declare (type (integer 0 49) k)
           (xargs :guard (st$ap st$a)))
  (let* ((map (nth 1 st$a))
         (pair (assoc k map)))
    (if pair (cdr pair) 0)))

(defun update$a (k val st$a)
  (declare (type (integer 0 49) k)
           (type (integer 0 *) val)
           (xargs :guard (and (st$ap st$a)
                              (mem$c-entryp val))))
  (update-nth 1
              (put-assoc k val (nth 1 st$a))
              st$a))

(defun corr-mem{impl} (n st{impl}$c st$a)
  (declare (xargs :stobjs st{impl}$c :verify-guards nil))
  (cond ((zp n) t)
        (t (let ((i (1- n)))
             (and (equal (mem{impl}$ci i st{impl}$c)
                         (lookup$a i st$a))
                  (corr-mem{impl} i st{impl}$c st$a))))))

(defun st{impl}$corr (st{impl}$c st$a)
  (declare (xargs :stobjs st{impl}$c :verify-guards nil))
  (and (st{impl}$cp+ st{impl}$c)
       (st$ap st$a)
       (equal (misc{impl}$c st{impl}$c) (misc$a st$a))
       (corr-mem{impl} 50 st{impl}$c st$a)))

(defun-nx create-st$a ()
  (declare (xargs :guard t))
  (list 0 ; (nth 1 (create-st{impl}$c))
        nil))

(DEFTHM CREATE-ST{IMPL}{CORRESPONDENCE}
  (ST{IMPL}$CORR (CREATE-ST{IMPL}$C) (CREATE-ST$A))
  :RULE-CLASSES NIL)

(DEFTHM CREATE-ST{IMPL}{PRESERVED}
  (ST$AP (CREATE-ST$A))
  :RULE-CLASSES NIL)

(DEFTHM MISC{IMPL}{CORRESPONDENCE}
  (IMPLIES (AND (ST{IMPL}$CORR ST{IMPL}$C ST{IMPL})
                (ST$AP ST{IMPL}))
           (EQUAL (MISC{IMPL}$C ST{IMPL}$C)
                  (MISC$A ST{IMPL})))
  :RULE-CLASSES NIL)

(defthm update-misc{impl}{correspondence}-lemma
  (implies (corr-mem{impl} k st{impl}$c st{impl})
           (corr-mem{impl} k
                     (update-misc{impl}$c v st{impl}$c)
                     (update-misc$a v st{impl})))
  :rule-classes nil)

(DEFTHM UPDATE-MISC{IMPL}{CORRESPONDENCE}
  (IMPLIES (AND (ST{IMPL}$CORR ST{IMPL}$C ST{IMPL})
                (ST$AP ST{IMPL}))
           (ST{IMPL}$CORR (UPDATE-MISC{IMPL}$C V ST{IMPL}$C)
                    (UPDATE-MISC$A V ST{IMPL})))
  :hints (("Goal" :use ((:instance update-misc{impl}{correspondence}-lemma
                                   (k 50)))))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE-MISC{IMPL}{PRESERVED}
  (IMPLIES (ST$AP ST{IMPL})
           (ST$AP (UPDATE-MISC$A V ST{IMPL})))
  :RULE-CLASSES NIL)

(encapsulate
 ()
 (local
  (defthm corr-mem{impl}-memi
    (implies (and (corr-mem{impl} bound st{impl}$c st{impl})
                  (natp bound)
                  (natp i) (< i bound))
             (equal (mem{impl}$ci i st{impl}$c)
                    (lookup$a i st{impl})))
    :rule-classes nil))

 (DEFTHM LOOKUP{IMPL}{CORRESPONDENCE}
   (IMPLIES (AND (ST{IMPL}$CORR ST{IMPL}$C ST{IMPL})
                 (INTEGERP I) (<= 0 I) (<= I 49)
                 (ST$AP ST{IMPL}))
            (EQUAL (MEM{IMPL}$CI I ST{IMPL}$C)
                   (LOOKUP$A I ST{IMPL})))
   :hints (("Goal" :use ((:instance corr-mem{impl}-memi
                                    (bound 50)))))
   :RULE-CLASSES NIL))

(local
 (DEFTHM LOOKUP{IMPL}{GUARD-THM}
   (IMPLIES (AND (ST{IMPL}$CORR ST{IMPL}$C C)
                 (INTEGERP I)
                 (<= 0 I)
                 (<= I 49)
                 (ST$AP ST{IMPL}))
            (AND (INTEGERP I)
                 (<= 0 I)
                 (< I (MEM{IMPL}$C-LENGTH ST{IMPL}$C))))
   :RULE-CLASSES NIL)
 )

(defthm assoc-equal-put-assoc-equal
  (equal (assoc-equal k1 (put-assoc-equal k2 v a))
         (if (equal k1 k2) (cons k1 v) (assoc-equal k1 a))))

(encapsulate
 ()

 (local
  (defthm mem{impl}$cp-update-nth
    (implies (and (natp i)
                  (< i (len mem))
                  (natp v)
                  (mem{impl}$cp mem))
             (mem{impl}$cp (update-nth i v mem)))))

 (local
  (defthm map$ap-put-assoc-equal
    (implies (and (natp i)
                  (< i 50)
                  (natp v)
                  (mem$c-entryp v)
                  (map$ap mem))
             (map$ap (put-assoc-equal i v mem)))))

 (local
  (defthm corr-mem{impl}-update-memi
    (implies (and (natp bound)
                  (<= bound 50)
                  (equal rest$c (cdr st{impl}$c))
                  (equal rest$a (cdr st{impl}))
                  (st{impl}$cp+ st{impl}$c)
                  (st$ap st{impl})
                  (corr-mem{impl} bound st{impl}$c st{impl})
                  (natp i)
                  (natp v))
             (corr-mem{impl} bound
                       (update-nth *mem{impl}$ci*
                                   (update-nth i v (nth *mem{impl}$ci* st{impl}$c))
                                   st{impl}$c)
                       (update-nth 1
                                   (put-assoc-equal i v (nth 1 st{impl}))
                                   st{impl})))))

 (DEFTHM UPDATE{IMPL}{CORRESPONDENCE}
   (IMPLIES (AND (ST{IMPL}$CORR ST{IMPL}$C ST{IMPL})
                 (INTEGERP I) (<= 0 I) (<= I 49)
                 (INTEGERP V) (<= 0 V)
                 (ST$AP ST{IMPL})
                 (MEM$C-ENTRYP V))
            (ST{IMPL}$CORR (UPDATE-MEM{IMPL}$CI I V ST{IMPL}$C)
                     (UPDATE$A I V ST{IMPL})))
   :hints (("Goal" :in-theory (disable nth update-nth)))
   :RULE-CLASSES NIL))

(DEFTHM UPDATE{IMPL}{PRESERVED}
  (IMPLIES (AND (INTEGERP I) (<= 0 I) (<= I 49)
                (INTEGERP V) (<= 0 V)
                (ST$AP ST{IMPL})
                (MEM$C-ENTRYP V))
           (ST$AP (UPDATE$A I V ST{IMPL})))
  :RULE-CLASSES NIL)

(DEFTHM UPDATE{IMPL}{GUARD-THM}
  (IMPLIES (AND (ST{IMPL}$CORR ST{IMPL}$C C)
                (INTEGERP I) (<= 0 I) (<= I 49)
                (INTEGERP V) (<= 0 V)
                (ST$AP ST{IMPL})
                (MEM$C-ENTRYP V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (MEM{IMPL}$C-LENGTH ST{IMPL}$C))
                (INTEGERP V)
                (<= 0 V)))
  :RULE-CLASSES NIL)

(include-book "std/testing/must-fail" :dir :system)

(must-fail
 (attach-stobj st st{impl}))

(DEFABSSTOBJ ST{IMPL}
  :recognizer (st{impl}p :logic st$ap :exec st{impl}$cp)
  :creator (create-st{impl} :logic create-st$a)
  :EXPORTS ((LOOKUP{impl} :logic lookup$a :EXEC MEM{IMPL}$CI)
            (UPDATE{impl} :logic update$a :EXEC UPDATE-MEM{IMPL}$CI)
            (MISC{impl} :logic misc$a)
            (UPDATE-MISC{impl} :logic update-misc$a)))

(attach-stobj st st{impl})

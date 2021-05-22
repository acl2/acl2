; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book illustrates that even when the "corresponding concrete stobj" for
; an abstract stobj is itself an abstract stobj, one can use an export
; :updater.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Abstract stobj for n (from two-usuallyequal-nums-stobj.lisp)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj n$c (n$c$val :type (integer 0 *) :initially 0))

(defun n$ap (x)
  (declare (xargs :guard t))
  (natp x))

(defun create-n$a ()
  (declare (xargs :guard t))
  0)

(defun n$val$a (x)
  (declare (xargs :guard t))
  x)

(defun update-n$val$a (val x)
  (declare (xargs :guard (natp val))
           (ignore x))
  val)

(defun n-corr (n$c n$a)
  (declare (xargs :stobjs n$c))
  (and (n$cp n$c)
       (equal n$a (n$c$val n$c))))

(DEFTHM CREATE-N${CORRESPONDENCE}
        (N-CORR (CREATE-N$C) (CREATE-N$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-N${PRESERVED} (N$AP (CREATE-N$A))
        :RULE-CLASSES NIL)

(DEFTHM N$VAL{CORRESPONDENCE}
        (IMPLIES (N-CORR N$C N)
                 (EQUAL (N$C$VAL N$C) (N$VAL$A N)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-N$VAL{CORRESPONDENCE}
        (IMPLIES (AND (N-CORR N$C N) (NATP V))
                 (N-CORR (UPDATE-N$C$VAL V N$C)
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
  :exports ((n$val :logic n$val$a :exec n$c$val)
            (update-n$val :logic update-n$val$a :exec update-n$c$val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Low-level main abstract stobj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj main$c
  (main$c$val :type n$)
  main$misc$c)

(defun main$lo$ap (x) ; (cons val misc)
  (declare (xargs :guard t))
  (and (consp x)
       (natp (car x))))

(defun create-main$lo$a ()
  (declare (xargs :guard t))
  (cons 0 nil))

(defun main$lo$val$a (x)
  (declare (xargs :guard (main$lo$ap x)))
  (car x))

(defun update-main$lo$val$a (n$ x)
  (declare (xargs :stobjs n$
                  :guard (main$lo$ap x)))
  (cons (n$val n$)
        (cdr x)))

(defun-nx main$lo$-corr (main$c main$lo$a)
  (declare (xargs :stobjs main$c))
  (and (main$cp main$c)
       (main$lo$ap main$lo$a)
       (equal main$lo$a
              (let ((n$ (main$c$val main$c))
                    (misc (main$misc$c main$c)))
                (cons (n$val n$) misc)))))

(DEFTHM CREATE-MAIN$LO${CORRESPONDENCE}
        (MAIN$LO$-CORR (CREATE-MAIN$C)
                       (CREATE-MAIN$LO$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-MAIN$LO${PRESERVED}
        (MAIN$LO$AP (CREATE-MAIN$LO$A))
        :RULE-CLASSES NIL)

(DEFTHM MAIN$LO$VAL{CORRESPONDENCE}
        (IMPLIES (AND (MAIN$LO$-CORR MAIN$C MAIN$LO$)
                      (MAIN$LO$AP MAIN$LO$))
                 (EQUAL (MAIN$C$VAL MAIN$C)
                        (MAIN$LO$VAL$A MAIN$LO$)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-MAIN$LO$VAL{CORRESPONDENCE}
        (IMPLIES (AND (MAIN$LO$-CORR MAIN$C MAIN$LO$)
                      (N$P N$)
                      (MAIN$LO$AP MAIN$LO$))
                 (MAIN$LO$-CORR (UPDATE-MAIN$C$VAL N$ MAIN$C)
                                (UPDATE-MAIN$LO$VAL$A N$ MAIN$LO$)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-MAIN$LO$VAL{PRESERVED}
        (IMPLIES (AND (N$P N$)
                      (MAIN$LO$AP MAIN$LO$))
                 (MAIN$LO$AP (UPDATE-MAIN$LO$VAL$A N$ MAIN$LO$)))
        :RULE-CLASSES NIL)

(defabsstobj main$lo$
  :concrete main$c
  :recognizer (main$lo$p :logic main$lo$ap :exec main$cp)
  :creator (create-main$lo$ :logic create-main$lo$a :exec create-main$c)
  :corr-fn main$lo$-corr
  :exports ((main$lo$val :logic main$lo$val$a
                         :exec main$c$val
                         :updater update-main$lo$val)
            (update-main$lo$val :logic update-main$lo$val$a
                                :exec update-main$c$val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; High-level main abstract stobj
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Just for kicks, we switch the car and cdr between lo and hi.

(defun main$hi$ap (x) ; (cons val misc)
  (declare (xargs :guard t))
  (and (consp x)
       (natp (cdr x))))

(defun create-main$hi$a ()
  (declare (xargs :guard t))
  (cons nil 0))

(defun main$hi$val$a (x)
  (declare (xargs :guard (main$hi$ap x)))
  (cdr x))

(defun update-main$hi$val$a (n$ x)
  (declare (xargs :stobjs n$
                  :guard (main$hi$ap x)))
  (cons (car x)
        (n$val n$)))

(defun-nx main$hi$-corr (main$lo$ main$hi$a)
  (declare (xargs :stobjs main$lo$))
  (and (main$lo$p main$lo$)
       (main$hi$ap main$hi$a)
       (equal main$hi$a
              (cons (cdr main$lo$)
                    (car main$lo$)))))

(DEFTHM CREATE-MAIN$HI${CORRESPONDENCE}
        (MAIN$HI$-CORR (CREATE-MAIN$LO$)
                       (CREATE-MAIN$HI$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-MAIN$HI${PRESERVED}
        (MAIN$HI$AP (CREATE-MAIN$HI$A))
        :RULE-CLASSES NIL)

(DEFTHM MAIN$HI$VAL{CORRESPONDENCE}
        (IMPLIES (AND (MAIN$HI$-CORR MAIN$LO$ MAIN$HI$)
                      (MAIN$HI$AP MAIN$HI$))
                 (EQUAL (MAIN$LO$VAL MAIN$LO$)
                        (MAIN$HI$VAL$A MAIN$HI$)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-MAIN$HI$VAL{CORRESPONDENCE}
        (IMPLIES (AND (MAIN$HI$-CORR MAIN$LO$ MAIN$HI$)
                      (N$P N$)
                      (MAIN$HI$AP MAIN$HI$))
                 (MAIN$HI$-CORR (UPDATE-MAIN$LO$VAL N$ MAIN$LO$)
                                (UPDATE-MAIN$HI$VAL$A N$ MAIN$HI$)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-MAIN$HI$VAL{PRESERVED}
        (IMPLIES (AND (N$P N$) (MAIN$HI$AP MAIN$HI$))
                 (MAIN$HI$AP (UPDATE-MAIN$HI$VAL$A N$ MAIN$HI$)))
        :RULE-CLASSES NIL)

(defabsstobj main$hi$
  :concrete main$lo$
  :recognizer (main$hi$p :logic main$hi$ap :exec main$lo$p)
  :creator (create-main$hi$ :logic create-main$hi$a :exec create-main$lo$)
  :corr-fn main$hi$-corr
  :exports ((main$hi$val :logic main$hi$val$a
                         :exec main$lo$val
                         :updater update-main$hi$val)
            (update-main$hi$val :logic update-main$hi$val$a
                                :exec update-main$lo$val)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Testing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun update-main$hi$ (n main$hi$)
  (declare (xargs :guard (natp n)
                  :stobjs main$hi$))
  (stobj-let ((n$ (main$hi$val main$hi$)))
             (n$)
             (update-n$val n n$)
             main$hi$))
         
(defun field-of-main$hi$ (main$hi$)
  (declare (xargs :stobjs main$hi$))
  (stobj-let ((n$ (main$hi$val main$hi$)))
             (n)
             (n$val n$)
             n))

(assert-event (equal (field-of-main$hi$ main$hi$)
                     0))

(make-event
 (er-progn (trans-eval '(update-main$hi$ 17 main$hi$)
                       'top state nil)
           (value '(value-triple t))))

(assert-event (equal (field-of-main$hi$ main$hi$)
                     17))

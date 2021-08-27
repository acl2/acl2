; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(set-gag-mode nil) ; avoid goal names from proofs admitting defuns

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Basic stobj-table writes, reads, and counts
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj top (tbl :type (stobj-table)))

; Fails: "ST1 is not the name of a stobj"
; (but admissible later, after defstobj st1).
(defun basic-1 (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st1 (st1$fix (tbl-get 'st1 top))))
   (val1)
   (fld1 st1)
   val1))

(defstobj st1 (fld1 :type integer :initially 0))
(defstobj st2 (fld2 :type integer :initially 0))
(defstobj st3 (fld3 :type integer :initially 0))
(defstobj st3a (fld3a :type integer :initially 0)
  :congruent-to st3)

; Failed earlier, but accepted now that st1 has been introduced.
(defun basic-1 (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st1 (st1$fix (tbl-get 'st1 top))))
   (val1)
   (fld1 st1)
   val1))

; Illegal variant of definition above: missing st1$fix.
; Error: "the stobj fixer for ST1 should be applied to that expression".
(defun bad (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st1 (tbl-get 'st1 top)))
   (val1)
   (fld1 st1)
   val1))

; Update copies of st1, st2 and st3 in the stobj-table of top.  At this point
; we aren't doing anything with st3a.
(defun update-1 (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st1 (st1$fix (tbl-get 'st1 top)))
    (st2 (st2$fix (tbl-get 'st2 top)))
    (st3 (st3$fix (tbl-get 'st3 top)))
    (st3a (st3a$fix (tbl-get 'st3a top))))
   (st3 st2 st1 e)
   (let* ((val1 (fld1 st1))
          (val2 (fld2 st2))
          (val3 (fld3 st3))
          (val3a (fld3a st3a))
          (st1 (update-fld1 (+ 1 val1) st1))
          (st2 (update-fld2 (+ 2 val2) st2))
          (st3 (update-fld3 (+ 3 val3) st3)))
     (mv st3 st2 st1 (equal val3 val3a)))
   (mv e top)))

; Read out the values in the stobj-table of top.
(defun read-1 (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st1 (st1$fix (tbl-get 'st1 top)))
    (st2 (st2$fix (tbl-get 'st2 top)))
    (st3 (st3$fix (tbl-get 'st3 top)))
    (st3a (st3a$fix (tbl-get 'st3a top))))
   (val1 val2 val3 val3a)
   (mv (fld1 st1) (fld2 st2) (fld3 st3) (fld3a st3a))
   (list val1 val2 val3 val3a)))

; Define a bunch of updates, clears, and checks, restoring the world
; afterwards.
(defmacro runs (i &key stobj-index)
  (let ((read-i (packn (list 'read- i)))
        (update-i (packn (list 'update- i)))
        (stobj (if stobj-index
                   (packn (list 'top stobj-index))
                 'top))
        (tbl-boundp (if stobj-index
                        (packn (list 'tbl stobj-index '-boundp))
                      'tbl-boundp))
        (tbl-clear (if stobj-index
                       (packn (list 'tbl stobj-index '-clear))
                     'tbl-clear))
        (tbl-init (if stobj-index
                      (packn (list 'tbl stobj-index '-init))
                    'tbl-init))
        (sti (if (eql i 2)
                 'st4
               'st1)))
    `(ld
      '((assert-event (equal (,read-i ,stobj) '(0 0 0 0)))
        (assert-event (not (,tbl-boundp ',sti ,stobj)))
        (,update-i ,stobj) ; returns (T <,stobj>)
        (assert-event (,tbl-boundp ',sti ,stobj))
        (assert-event (equal (,read-i ,stobj) '(1 2 3 0)))
        (,update-i ,stobj) ; returns (NIL <,stobj>):
        (assert-event (equal (,read-i ,stobj) '(2 4 6 0)))
        (,tbl-clear ,stobj)
        (assert-event (not (,tbl-boundp ',sti ,stobj)))
        (assert-event (equal (,read-i ,stobj) '(0 0 0 0))) ; yes, back to start
        (,update-i ,stobj)
        (assert-event (equal (,read-i ,stobj) '(1 2 3 0)))
        (,tbl-init 100 5/3 8/10 ,stobj) ; (ht-size rehash-size rehash-threshold ,stobj)
        (assert-event (equal (,read-i ,stobj) '(0 0 0 0))) ; yes, back to start
        (,update-i ,stobj) 
        ))))

; Do the tests above with update-1 and read-1 not yet guard-verified.  This
; tests the ability of *1* to handle things, including stobj fixers.
(runs 1)
(assert-event (equal (tbl-count top) 3))
(ubt 'st3)
; When a stobj is undone, its presence in a stobj-table disappears:
(assert-event (equal (tbl-count top) 2))
(tbl-clear top)
(oops) ; restore events from ubt above

; Now do those same tests after guard verificatin of update-1 and read-1.
(verify-guards update-1)
(verify-guards read-1)
(runs 1)
(assert-event (equal (tbl-count top) 3))
(tbl-rem 'st1 top)
(assert-event (equal (tbl-count top) 2))

; Updating congruent stobjs works fine.
(defun update-1a (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st3  (st3$fix  (tbl-get 'st3  top)))
    (st3a (st3a$fix (tbl-get 'st3a top))))
   (st3 st3a val3 val3a)
   (let* ((val3  (fld3  st3a))
          (val3a (fld3  st3a))
          (st3  (update-fld3 (+ 3 val3)  st3))
          (st3a (update-fld3 (+ 3 val3a) st3a)))
     (mv st3 st3a val3 val3a))
   (mv val3 val3a top)))

; This variant of the defun just above causes an error because of aliasing.
(defun update-1a-bad (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st3  (st3$fix  (tbl-get 'st3  top)))
    (st3a (st3$fix  (tbl-get 'st3 top))))
   (st3 st3a val3 val3a)
   (let* ((val3  (fld3  st3a))
          (val3a (fld3  st3a))
          (st3  (update-fld3 (+ 3 val3)  st3))
          (st3a (update-fld3 (+ 3 val3a) st3a)))
     (mv st3 st3a val3 val3a))
   (mv val3 val3a top)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stobj array in stobj-table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj st4 (ar4 :type (array integer (8)) :initially 0))

(defthm integerp-nth-ar4p
  (implies (and (ar4p ar)
                (natp i)
                (< i (len ar)))
           (integerp (nth i ar)))
  :rule-classes :type-prescription)

(defun update-2 (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st4 (st4$fix (tbl-get 'st4 top))))
   (st4)
   (let* ((v0 (ar4i 0 st4))
          (v1 (ar4i 1 st4))
          (v2 (ar4i 2 st4))
          (st4 (update-ar4i 0 (+ 1 v0) st4))
          (st4 (update-ar4i 1 (+ 2 v1) st4))
          (st4 (update-ar4i 2 (+ 3 v2) st4)))
     st4)
   top))

(defun read-2 (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st4 (st4$fix (tbl-get 'st4 top))))
   (v0 v1 v2 v3)
   (mv (ar4i 0 st4) (ar4i 1 st4) (ar4i 2 st4) (ar4i 3 st4))
   (list v0 v1 v2 v3)))

(tbl-clear top)
(runs 2)
(assert-event (equal (tbl-count top) 1))

(verify-guards update-2)
(verify-guards read-2)
(tbl-clear top)
(runs 2)
(assert-event (equal (tbl-count top) 1))
(ubt 'st4)
; When a stobj is undone, its presence in a stobj-table disappears:
(assert-event (equal (tbl-count top) 0))
(oops) ; restore events from ubt above

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Abstract stobj with stobj-table
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun top2$ap (x)
  (declare (xargs :guard t))
  (alistp x))

(defun create-top2$a ()
  (declare (xargs :guard t))
  nil)

(defun tbl2$a-get (key x)
  (declare (xargs :guard (and (symbolp key)
                              (top2$ap x))))
  (cdr (assoc-eq key x)))

(defun tbl2$a-put (key val x)
  (declare (xargs :guard (and (symbolp key)
                              (top2$ap x))))
  (acons key val x))

(defun tbl2$a-clear (x)
  (declare (xargs :guard t)
           (ignore x))
  nil)

(defun tbl2$a-init (ht-size rehash-size rehash-threshold x)
  (declare (XARGS :GUARD (AND (top2$ap x)
                              (OR (NATP HT-SIZE) (NOT HT-SIZE))
                              (OR (AND (RATIONALP REHASH-SIZE)
                                       (<= 1 REHASH-SIZE))
                                  (NOT REHASH-SIZE))
                              (OR (AND (RATIONALP REHASH-THRESHOLD)
                                       (<= 0 REHASH-THRESHOLD)
                                       (<= REHASH-THRESHOLD 1))
                                  (NOT REHASH-THRESHOLD))))
           (ignorable ht-size rehash-size rehash-threshold x))
  nil)

(defun tbl2$a-boundp (key x)
  (declare (xargs :guard (and (symbolp key)
                              (top2$ap x))))
  (consp (assoc-eq key x)))

(defun-nx top2$corr (top x)
  (declare (xargs :stobjs top))
  (equal (car top)
         x))

(DEFTHM CREATE-TOP2{CORRESPONDENCE}
        (TOP2$CORR (CREATE-TOP) (CREATE-TOP2$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-TOP2{PRESERVED}
        (TOP2$AP (CREATE-TOP2$A))
        :RULE-CLASSES NIL)

(defthm hons-assoc-equal-is-assoc-equal
  (implies (alistp alist)
           (equal (hons-assoc-equal key alist)
                  (assoc-equal key alist))))

(DEFTHM TBL2-GET{CORRESPONDENCE}
        (IMPLIES (AND (TOP2$CORR TOP TOP2)
                      (SYMBOLP K)
                      (TOP2$AP TOP2))
                 (EQUAL (TBL-GET K TOP)
                        (TBL2$A-GET K TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM TBL2-PUT{CORRESPONDENCE}
        (IMPLIES (AND (TOP2$CORR TOP TOP2)
                      (SYMBOLP K)
                      (TOP2$AP TOP2))
                 (TOP2$CORR (TBL-PUT K V TOP)
                            (TBL2$A-PUT K V TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM TBL2-PUT{PRESERVED}
        (IMPLIES (AND (SYMBOLP K) (TOP2$AP TOP2))
                 (TOP2$AP (TBL2$A-PUT K V TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM TBL2-CLEAR{CORRESPONDENCE}
        (IMPLIES (TOP2$CORR TOP TOP2)
                 (TOP2$CORR (TBL-CLEAR TOP)
                            (TBL2$A-CLEAR TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM TBL2-CLEAR{PRESERVED}
        (IMPLIES (TOP2$AP TOP2)
                 (TOP2$AP (TBL2$A-CLEAR TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM TBL2-INIT{CORRESPONDENCE}
        (IMPLIES (AND (TOP2$CORR TOP TOP2)
                      (TOP2$AP TOP2)
                      (OR (NATP HT-SIZE) (NOT HT-SIZE))
                      (OR (AND (RATIONALP REHASH-SIZE)
                               (<= 1 REHASH-SIZE))
                          (NOT REHASH-SIZE))
                      (OR (AND (RATIONALP REHASH-THRESHOLD)
                               (<= 0 REHASH-THRESHOLD)
                               (<= REHASH-THRESHOLD 1))
                          (NOT REHASH-THRESHOLD)))
                 (TOP2$CORR (TBL-INIT HT-SIZE
                                      REHASH-SIZE REHASH-THRESHOLD TOP)
                            (TBL2$A-INIT HT-SIZE
                                         REHASH-SIZE REHASH-THRESHOLD TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM TBL2-INIT{PRESERVED}
        (IMPLIES (AND (TOP2$AP TOP2)
                      (OR (NATP HT-SIZE) (NOT HT-SIZE))
                      (OR (AND (RATIONALP REHASH-SIZE)
                               (<= 1 REHASH-SIZE))
                          (NOT REHASH-SIZE))
                      (OR (AND (RATIONALP REHASH-THRESHOLD)
                               (<= 0 REHASH-THRESHOLD)
                               (<= REHASH-THRESHOLD 1))
                          (NOT REHASH-THRESHOLD)))
                 (TOP2$AP (TBL2$A-INIT HT-SIZE
                                       REHASH-SIZE REHASH-THRESHOLD TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM TBL2-BOUNDP{CORRESPONDENCE}
        (IMPLIES (AND (TOP2$CORR TOP TOP2)
                      (SYMBOLP K)
                      (TOP2$AP TOP2))
                 (EQUAL (TBL-BOUNDP K TOP)
                        (TBL2$A-BOUNDP K TOP2)))
        :RULE-CLASSES NIL)

(defabsstobj top2
  :foundation top
  :creator (create-top2 :logic create-top2$a :exec create-top)
  :recognizer (top2p :logic top2$ap :exec topp)
  :exports ((tbl2-get :logic tbl2$a-get :exec tbl-get :updater tbl2-put)
            (tbl2-put :logic tbl2$a-put :exec tbl-put)
            (tbl2-clear :logic tbl2$a-clear :exec tbl-clear)
            (tbl2-init :logic tbl2$a-init :exec tbl-init)
            (tbl2-boundp :logic tbl2$a-boundp :exec tbl-boundp)))

; Now introduce analogues of update-1 and read-1 for top2.

(defun update-3 (top2)
  (declare (xargs :stobjs top2 :verify-guards nil))
  (stobj-let
   ((st1 (st1$fix (tbl2-get 'st1 top2)))
    (st2 (st2$fix (tbl2-get 'st2 top2)))
    (st3 (st3$fix (tbl2-get 'st3 top2)))
    (st3a (st3a$fix (tbl2-get 'st3a top2))))
   (st3 st2 st1 e)
   (let* ((val1 (fld1 st1))
          (val2 (fld2 st2))
          (val3 (fld3 st3))
          (val3a (fld3a st3a))
          (st1 (update-fld1 (+ 1 val1) st1))
          (st2 (update-fld2 (+ 2 val2) st2))
          (st3 (update-fld3 (+ 3 val3) st3)))
     (mv st3 st2 st1 (equal val3 val3a)))
   (mv e top2)))

; Read out the values in the stobj-table of top.
(defun read-3 (top2)
  (declare (xargs :stobjs top2 :verify-guards nil))
  (stobj-let
   ((st1 (st1$fix (tbl2-get 'st1 top2)))
    (st2 (st2$fix (tbl2-get 'st2 top2)))
    (st3 (st3$fix (tbl2-get 'st3 top2)))
    (st3a (st3a$fix (tbl2-get 'st3a top2))))
   (val1 val2 val3 val3a)
   (mv (fld1 st1) (fld2 st2) (fld3 st3) (fld3a st3a))
   (list val1 val2 val3 val3a)))

(tbl2-clear top2)
(runs 3 :stobj-index 2)

; Now do those same tests after guard verificatin of update-1 and read-1.
(verify-guards update-1)
(verify-guards read-1)
(tbl2-clear top2)
(runs 3 :stobj-index 2)
(assert-event (equal (tbl2-count top2) 3))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Recursive stobj-tables
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj top0
  (tbl0 :type (stobj-table))
  :congruent-to top)

(defun update-1-rec (top0 n)
  (declare (xargs :stobjs top0
                  :guard (natp n)
                  :verify-guards nil))
  (cond
   ((zp n) (mv-let (e top0)
             (update-1 top0)
             (declare (ignore e))
             top0))
   (t (stobj-let
       ((top (top$fix (tbl-get 'top top0))))
       (top)
       (update-1-rec top (1- n))
       top0))))

(defun read-1-rec (top0 n)
  (declare (xargs :stobjs top0
                  :guard (natp n)
                  :verify-guards nil))
  (cond
   ((zp n) (read-1 top0))
   (t (stobj-let
       ((top (top$fix (tbl-get 'top top0))))
       (val)
       (read-1-rec top (1- n))
       val))))

(defmacro rec-test ()
  '(ld
    '((tbl-clear top)
      (update-1-rec top 3)
      (assert-event (equal (list (read-1-rec top 0)
                                 (read-1-rec top 1)
                                 (read-1-rec top 2)
                                 (read-1-rec top 3)
                                 (read-1-rec top 4)
                                 (read-1-rec top 5))
                           '((0 0 0 0)
                             (0 0 0 0)
                             (0 0 0 0)
                             (1 2 3 0)
                             (0 0 0 0)
                             (0 0 0 0))))
      (update-1-rec top 3)
      (assert-event (equal (list (read-1-rec top 0)
                                 (read-1-rec top 1)
                                 (read-1-rec top 2)
                                 (read-1-rec top 3)
                                 (read-1-rec top 4)
                                 (read-1-rec top 5))
                           '((0 0 0 0)
                             (0 0 0 0)
                             (0 0 0 0)
                             (2 4 6 0)
                             (0 0 0 0)
                             (0 0 0 0))))
      (update-1-rec top 3)
      (assert-event (equal (list (read-1-rec top 0)
                                 (read-1-rec top 1)
                                 (read-1-rec top 2)
                                 (read-1-rec top 3)
                                 (read-1-rec top 4)
                                 (read-1-rec top 5))
                           '((0 0 0 0)
                             (0 0 0 0)
                             (0 0 0 0)
                             (3 6 9 0)
                             (0 0 0 0)
                             (0 0 0 0))))
      (assert-event (equal (tbl-count top) 1))
      (tbl-clear top)
      (assert-event (equal (tbl-count top) 0))
      (assert-event (equal (list (read-1-rec top 0)
                                 (read-1-rec top 1)
                                 (read-1-rec top 2)
                                 (read-1-rec top 3)
                                 (read-1-rec top 4)
                                 (read-1-rec top 5))
                           '((0 0 0 0)
                             (0 0 0 0)
                             (0 0 0 0)
                             (0 0 0 0)
                             (0 0 0 0)
                             (0 0 0 0)))))))

(rec-test)

(verify-guards update-1-rec)
(verify-guards read-1-rec)
(rec-test)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Additional, miscellaneous errors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We submitted the same function as this much earlier in the file, except this
; time we try to trick the system by using tbl0-get in place of tbl-get to hide
; the aliasing a bit.  It's still an error, because the accessor for a stobj
; (in this case st3) must truly be an accessor for that stobj, not merely for
; one congruent to it.
(defun update-1a-bad (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st3  (st3$fix  (tbl-get 'st3  top)))
    (st3a (st3$fix  (tbl0-get 'st3 top))))
   (st3 st3a val3 val3a)
   (let* ((val3  (fld3  st3a))
          (val3a (fld3  st3a))
          (st3  (update-fld3 (+ 3 val3)  st3))
          (st3a (update-fld3 (+ 3 val3a) st3a)))
     (mv st3 st3a val3 val3a))
   (mv val3 val3a top)))

; This time we change the fixer instead of the accessor, and happily we still
; get a suitable error (fixer mismatch).
(defun update-1a-bad (top)
  (declare (xargs :stobjs top :verify-guards nil))
  (stobj-let
   ((st3  (st3$fix  (tbl-get 'st3  top)))
    (st3a (st3a$fix  (tbl-get 'st3 top))))
   (st3 st3a val3 val3a)
   (let* ((val3  (fld3  st3a))
          (val3a (fld3  st3a))
          (st3  (update-fld3 (+ 3 val3)  st3))
          (st3a (update-fld3 (+ 3 val3a) st3a)))
     (mv st3 st3a val3 val3a))
   (mv val3 val3a top)))

; The :type should be (stobj-table), not stobj-table.
(defstobj top-bad (tbl :type stobj-table))

; Disallow stobj fixer calls at the top level.
(st1$fix t)

; Disallow stobj fixer calls in code.
(defun foo ()
  (st1$fix t))

; Allow stobj fixer calls in theorems.  Note that we don't get an array from
; the fixer by execution in the middle of the proof!
(with-output :on :all :off proof-tree
  (thm (equal (st1$fix t)
              (create-st1))))

; As above, and succeed even though we have enabled the executable-counterpart
; of the fixer.  Notice the throws done by create-st1 if we first evaluate
; (trace$ st1$fix create-st1).
(with-output :on :all :off proof-tree
  (thm (equal (st1$fix t)
              (create-st1))
       :hints (("Goal" :in-theory (enable (:e st1$fix))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Locally-defined stobj issue
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Thanks to Sol Swords for raising this issue and outlining the following
; example.

; This event is admitted.
(encapsulate ()
  (defstobj st5 fld5)

  (defun set-st-in-stobj-table (fld-val top)
    (declare (xargs :stobjs top))
    (stobj-let ((st5 (st5$fix (tbl-get 'st5 top))))
               (st5)
               (update-fld5 fld-val st5)
               top))

  ;; store a st in the stobj-table
  (make-event
   (let ((top (set-st-in-stobj-table 100 top)))
     (mv nil '(value-triple :ok) state top))))

; Now undo the event above and change it only by making the defstobj local.
; The result fails in pass 2 of the encapsulate, saying: "However, that alleged
; stobj-table access is illegal because ST5 is not the name of a stobj."

(u)

; Fails (see comment just above):
(encapsulate ()
  (local (defstobj st5 fld5))

  (defun set-st-in-stobj-table (fld-val top)
    (declare (xargs :stobjs top))
    (stobj-let ((st5 (st5$fix (tbl-get 'st5 top))))
               (st5)
               (update-fld5 fld-val st5)
               top))

  ;; store a st in the stobj-table
  (make-event
   (let ((top (set-st-in-stobj-table 100 top)))
     (mv nil '(value-triple :ok) state top))))

; As Sol points out, if this succeeded then we could prove nil by
; defining st so that fld is a symbol, and then using tricks with mbe and
; clause-processors to prove nil.

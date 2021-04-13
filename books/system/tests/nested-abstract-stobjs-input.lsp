; Copyright (C) 2021, ForrestHunt, Inc.
; Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This file illustrates how ACL2 protects against a potential unsoundness
; caused by aliasing when two child stobj fields of an abstract stobj are
; implemented by the same child stobj of a concrete stobj.  Thanks to Sol
; Swords for supplying the stobj-let form for the first example below, which
; provided critical guidance in the development of the appropriate check.

; For a more complex example of nested abstract stobjs, see community book
; demos/two-usuallyequal-nums-stobj.lisp.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Example 1
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj sub$c fld0$c)
(defstobj top$c (sub0$c :type sub$c))

(defun sub$ap (x)
  (declare (xargs :guard t))
  (and (consp x)
       (null (cdr x))
       (or (natp (car x))
           (null (car x)))))

(defun top$ap (x)
  (declare (xargs :guard t))
  (and (consp x)
       (null (cdr x))
       (sub$ap (car x))))

(defun create-top$a ()
  (declare (xargs :guard t))
  (list (list nil)))

(defun sub0$a (x)
  (declare (xargs :guard (top$ap x)))
  (car x))

(defun-nx update-sub0$a (sub$c x)
  (declare (xargs :stobjs sub$c
                  :guard (and (top$ap x)
                              (natp (fld0$c sub$c)))))
  (list sub$c))

(defun-nx top-corr (top$c x)
  (declare (xargs :stobjs top$c))
  (equal top$c x))

(DEFTHM CREATE-TOP{CORRESPONDENCE}
        (TOP-CORR (CREATE-TOP$C) (CREATE-TOP$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-TOP{PRESERVED}
        (TOP$AP (CREATE-TOP$A))
        :RULE-CLASSES NIL)

(DEFTHM SUB0{CORRESPONDENCE}
        (IMPLIES (AND (TOP-CORR TOP$C TOP) (TOP$AP TOP))
                 (EQUAL (SUB0$C TOP$C) (SUB0$A TOP)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-SUB0{CORRESPONDENCE}
        (IMPLIES (AND (TOP-CORR TOP$C TOP)
                      (SUB$CP SUB$C)
                      (TOP$AP TOP)
                      (NATP (FLD0$C SUB$C)))
                 (TOP-CORR (UPDATE-SUB0$C SUB$C TOP$C)
                           (UPDATE-SUB0$A SUB$C TOP)))
        :RULE-CLASSES NIL)

(defthm equal-len-1
  (equal (equal (len x) 1)
         (and (consp x)
              (atom (cdr x)))))

(DEFTHM UPDATE-SUB0{PRESERVED}
        (IMPLIES (AND (SUB$CP SUB$C)
                      (TOP$AP TOP)
                      (NATP (FLD0$C SUB$C)))
                 (TOP$AP (UPDATE-SUB0$A SUB$C TOP)))
        :RULE-CLASSES NIL)

(DEFTHM SUB0-AGAIN{CORRESPONDENCE}
        (IMPLIES (AND (TOP-CORR TOP$C TOP) (TOP$AP TOP))
                 (EQUAL (SUB0$C TOP$C) (SUB0$A TOP)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-SUB0-AGAIN{CORRESPONDENCE}
        (IMPLIES (AND (TOP-CORR TOP$C TOP)
                      (SUB$CP SUB$C)
                      (TOP$AP TOP)
                      (NATP (FLD0$C SUB$C)))
                 (TOP-CORR (UPDATE-SUB0$C SUB$C TOP$C)
                           (UPDATE-SUB0$A SUB$C TOP)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-SUB0-AGAIN{PRESERVED}
        (IMPLIES (AND (SUB$CP SUB$C)
                      (TOP$AP TOP)
                      (NATP (FLD0$C SUB$C)))
                 (TOP$AP (UPDATE-SUB0$A SUB$C TOP)))
        :RULE-CLASSES NIL)

; The child stobj fields sub0 and sub0-again both correspond to the same stobj
; field, sub0$c, of a concrete stobj, top$c.
(defabsstobj top
  :recognizer (topp :logic top$ap :exec top$cp)
  :creator (create-top :logic create-top$a :exec create-top$c)
  :corr-fn top-corr
  :exports ((sub0 :logic sub0$a :exec sub0$c :updater update-sub0)
            (sub0-again :logic sub0$a :exec sub0$c :updater update-sub0)
            (update-sub0 :logic update-sub0$a :exec update-sub0$c)))

; The following event succeeds; no surprises here.  But below we show how an
; attempt to update both stobj fields fails, as it should.
(defun foo (top)
  (declare (xargs :stobjs top))
  (stobj-let ((sub$c (sub0 top)))
	     (sub$c sub$c-val)
	     (let* ((sub$c (update-fld0$c 1 sub$c))
		    (sub$c-val (fld0$c sub$c)))
	       (mv sub$c sub$c-val))
	     (mv top sub$c-val)))

; Prepare to try to bind both child stobj fields of the abstract stobj.
(defstobj sub$c-cong fld0$c-cong :congruent-to sub$c)

; The following fails, as it should, with this message:
;   ACL2 Error in ( DEFUN FOO-BAD ...):  The accessors SUB0 and SUB0-AGAIN
;   ultimately invoke the same accessor, SUB0$C, of the same concrete stobj,
;   TOP$C.  The form ....
; FAILS!
(defun foo-bad (top)
  (declare (xargs :stobjs top))
  (stobj-let ((sub$c (sub0 top))
	      (sub$c-cong (sub0-again top)
; The following isn't needed if we include update-sub0-again among the exports
; of top.
                       update-sub0))
	     (sub$c sub$c-val sub$c-cong sub$c-cong-val)
	     (let* ((sub$c (update-fld0$c 1 sub$c))
		    (sub$c-cong (update-fld0$c 2 sub$c-cong))
		    (sub$c-val (fld0$c sub$c))
		    (sub$c-cong-val (fld0$c sub$c-cong)))
	       (mv sub$c sub$c-val sub$c-cong sub$c-cong-val))
	     (mv top sub$c-val sub$c-cong-val)))

; Before the check was installed that caused the error above, the following
; could be admitted, in spite of contradiccting the evaluation shown below.
#||
(thm (implies (topp top)
              (mv-let (top sub$c-val sub$c-cong-val)
                (foo top)
                (declare (ignore top sub$c-cong-val))
                (equal sub$c-val 1))))


ACL2 !>(foo top)
(<top> 2 2)
ACL2 !>
||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Example 2
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following variant of Example 1 shows introduces abstract stobj top2 with
; foundational stobj top.  Top2 has two child stobj fields (sub02 and
; sub02-again) with different corresponding child stobj fields (sub0 and
; sub0-again) of the foundational stobj, top.  But those two fields, in turn,
; correspond to the same child stobj field of the foundational stobj top$c of
; top.

(DEFTHM CREATE-TOP2{CORRESPONDENCE}
        (TOP-CORR (CREATE-TOP) (CREATE-TOP$A))
        :RULE-CLASSES NIL)

(DEFTHM CREATE-TOP2{PRESERVED}
        (TOP$AP (CREATE-TOP$A))
        :RULE-CLASSES NIL)

(DEFTHM SUB02{CORRESPONDENCE}
        (IMPLIES (AND (TOP-CORR TOP TOP2) (TOP$AP TOP2))
                 (EQUAL (SUB0 TOP) (SUB0$A TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM SUB02-AGAIN{CORRESPONDENCE}
        (IMPLIES (AND (TOP-CORR TOP TOP2) (TOP$AP TOP2))
                 (EQUAL (SUB0-AGAIN TOP) (SUB0$A TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-SUB02{CORRESPONDENCE}
        (IMPLIES (AND (TOP-CORR TOP TOP2)
                      (SUB$CP SUB$C)
                      (TOP$AP TOP2)
                      (NATP (FLD0$C SUB$C)))
                 (TOP-CORR (UPDATE-SUB0 SUB$C TOP)
                           (UPDATE-SUB0$A SUB$C TOP2)))
        :RULE-CLASSES NIL)

(DEFTHM UPDATE-SUB02{PRESERVED}
        (IMPLIES (AND (SUB$CP SUB$C)
                      (TOP$AP TOP2)
                      (NATP (FLD0$C SUB$C)))
                 (TOP$AP (UPDATE-SUB0$A SUB$C TOP2)))
        :RULE-CLASSES NIL)

(defabsstobj top2
  :concrete top
  :recognizer (top2p :logic top$ap :exec topp)
  :creator (create-top2 :logic create-top$a :exec create-top)
  :corr-fn top-corr
  :exports ((sub02 :logic sub0$a :exec sub0 :updater update-sub02)
            (sub02-again :logic sub0$a :exec sub0-again :updater update-sub02)
            (update-sub02 :logic update-sub0$a :exec update-sub0)))

(defun foo2 (top2)
  (declare (xargs :stobjs top2))
  (stobj-let ((sub$c (sub02 top2)))
	     (sub$c sub$c-val)
	     (let* ((sub$c (update-fld0$c 1 sub$c))
		    (sub$c-val (fld0$c sub$c)))
	       (mv sub$c sub$c-val))
	     (mv top2 sub$c-val)))

; The following fails, as it should, with this message:
;   ACL2 Error in ( DEFUN FOO2-BAD ...):  The accessors SUB02 and SUB02-AGAIN
;   ultimately invoke the same accessor, SUB0$C, of the same concrete stobj,
;   TOP$C.  The form 
;;; FAILS!
(defun foo2-bad (top2)
  (declare (xargs :stobjs top2))
  (stobj-let ((sub$c (sub02 top2))
	      (sub$c-cong (sub02-again top2)
                        update-sub02))
             (sub$c sub$c-val sub$c-cong sub$c-cong-val)
	     (let* ((sub$c (update-fld0$c 1 sub$c))
		    (sub$c-cong (update-fld0$c 2 sub$c-cong))
		    (sub$c-val (fld0$c sub$c))
		    (sub$c-cong-val (fld0$c sub$c-cong)))
	       (mv sub$c sub$c-val sub$c-cong sub$c-cong-val))
	     (mv top2 sub$c-val sub$c-cong-val)))

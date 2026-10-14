; This book, modified only as noted below, was produced by Claude and passed
; along by Eric Smith.  It illustrates a soundness bug fixed before ACL2
; Version 8.8.

; Finding 62: a hash-table field's <fld>-GET? never gets a 'stobjs-out, so for a
; double-float or child-stobj element type a raw double -- or a LIVE CHILD STOBJ
; -- leaks into the ordinary object world.
;
; put-stobjs-in-and-outs1 (other-events.lisp:20857-20860):
;   (if (eq (car type) 'hash-table)
;       (putprop accessor?-fn 'stobjs-in (list nil name) wrld)
; and nothing else, while the plain accessor twelve lines above gets
;   (putprop-unless acc-fn 'stobjs-out (list stobj-flg) '(nil) ...)
; where stobj-flg is :df for a double-float element type and the stobj name for a
; stobj element type.  accessor?-fn therefore keeps the (nil nil) that ordinary
; defun processing assigned, because put-stobjs-in-and-outs runs AFTER the
; axiomatic defuns were processed.
;
; THE AUTHORS' OWN TABLE records the wrong value as intended
; (other-events.lisp:20917):
;   ; hash-table accessor?     (nil name)         (nil nil)
;
; <fld>-GET?'s logical body is (mv (<fld>-GET k st) (<fld>-BOUNDP k st)), so slot
; 0 is whatever <fld>-GET returns; the raw definition (basis-a.lisp:8867-8878)
; returns (mv val t) with val read straight out of the live hash table.
;
; Measured: (getpropc 'tbl-get 'stobjs-out ...) = (:DF) but
; (getpropc 'tbl-get? 'stobjs-out ...) = (NIL NIL); at the loop (tbl-get 'a st1)
; prints #d0.3333333333333333 while (tbl-get? 'a st1) prints
; (0.3333333333333333 T) -- no #d prefix, i.e. an ordinary object that is a raw
; double.
;
; MUST BE FIXED TOGETHER WITH N254: <fld>-GET?'s raw default value is not
; df-aware while <fld>-GET's is, so fixing the stobjs-out alone makes the
; table-miss path wrong instead of the hit path.
;
; POLARITY: the MUST-FAIL states the CORRECT behaviour -- the logical value of
; slot 0 is a rational, so (test) must be true.  RED while present.
(in-package "ACL2")
(include-book "std/testing/must-fail" :dir :system)

(defstobj st1 (tbl :type (hash-table eql 10 double-float) :initially 1))

(must-fail ; Must-fail wrapper added by Matt Kaufmann
(defun f (st1)
  (declare (xargs :stobjs st1))
  (mv-let (v b) (tbl-get? 'a st1)
    (declare (ignore b))
    (rationalp v)))
)

; Commented out by Matt Kaufmann: f can no longer be defined, so neither can
; test.
#|
(defun test ()
  (with-local-stobj
    st1
    (mv-let (val st1)
            (let ((st1 (tbl-put 'a (tbl-get 'b st1) st1)))
              (mv (f st1) st1))
            val)))

; The logical value: dfs are rationals in the logic, so (test) is T.  Must stay
; provable.
(defthm logic-says-t
  (test)
  :hints (("Goal" :in-theory (disable (:executable-counterpart test))))
  :rule-classes nil)

; THE DEFECT: raw evaluation yields a raw double-float, for which rationalp is
; NIL.
(must-fail (defthm raw-says-nil (not (test)) :rule-classes nil))
|#

; CONTROL: an integer element type, where stobj-flg is NIL so (NIL) matches the
; (NIL NIL) that was left in place and raw agrees with the logic.  This pins the
; defect to the element types for which stobj-flg is non-NIL.
(defstobj st2 (tbl2 :type (hash-table eql 10 integer) :initially 1))
(defun f2 (st2)
  (declare (xargs :stobjs st2))
  (mv-let (v b) (tbl2-get? 'a st2)
    (declare (ignore b))
    (rationalp v)))
(defun test2 ()
  (with-local-stobj
    st2
    (mv-let (val st2)
            (let ((st2 (tbl2-put 'a (tbl2-get 'b st2) st2)))
              (mv (f2 st2) st2))
            val)))
(defthm control-integer-agrees (test2) :rule-classes nil)

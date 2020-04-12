; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, April, 2012
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

; We start with an example from :doc defstobj.

(defconst *mem-size* 10)

(defstobj st1
  (reg1 :type (array (unsigned-byte 31) (8))
        :initially 0)
  (pc1 :type (unsigned-byte 31)
       :initially 555)
  halt1
  (mem1 :type (array (unsigned-byte 31) (*mem-size*))
        :initially 0 :resizable t))

(defstobj st2
  (reg2 :type (array (unsigned-byte 31) (8))
        :initially 0)
  (pc2 :type (unsigned-byte 31)
       :initially 555)
  halt2
  (mem2 :type (array (unsigned-byte 31) (*mem-size*))
        :initially 0 :resizable t)
  :congruent-to st1)

(defstobj st3
  (reg3 :type (array (unsigned-byte 31) (8))
        :initially 0)
  (pc3 :type (unsigned-byte 31)
       :initially 555)
  halt3
  (mem3 :type (array (unsigned-byte 31) (*mem-size*))
        :initially 0 :resizable t)
  :congruent-to st2)

(defun foo1 (st1)
  (declare (xargs :stobjs st1))
  (reg1i 3 st1))

(defun bar1 (st1)
  (declare (xargs :stobjs st1))
  (foo1 st1))

(defun bar2-tough (st2)
  (declare (xargs :stobjs st2))
  (foo1 st2))

(defun bar2 (st2)
  (declare (xargs :stobjs st2))
  (if (halt2 st2)
      0
    (foo1 st2)))

(defun update1 (x st1)
  (declare (xargs :stobjs st1))
  (update-halt1 x st1))

(defun update2 (x st2)
  (declare (xargs :stobjs st2))
  (update1 x st2))

(defmacro eval-form (form)
  `(make-event
    (er-progn (trans-eval ',form 'top state t)
              (value '(value-triple :nil)))))

(eval-form
 (update2 3 st2))

(assert-event (equal (list (halt1 st1) (halt2 st1) (halt2 st2) (halt1 st2))
                     '(NIL NIL 3 3)))

(eval-form
 (update2 7 st1))

(assert-event (equal (list (halt1 st1) (halt2 st1) (halt2 st2) (halt1 st2))
                     '(7 7 3 3)))

(defun swap-st1-st2 (st1 st2)
  (declare (xargs :stobjs (st1 st2)))
  (mv st2 st1))

(eval-form
 (swap-st1-st2 st1 st2)) ; returns (<st2> <st1>)

; Swap doesn't change stobjs:
(assert-event (equal (list (halt1 st1) (halt2 st1) (halt2 st2) (halt1 st2))
                     '(7 7 3 3)))

(eval-form
 (swap-st1-st2 st2 st1)) ; returns (<st1> <st2>)

; Swap doesn't change stobjs:
(assert-event (equal (list (halt1 st1) (halt2 st1) (halt2 st2) (halt1 st2))
                     '(7 7 3 3)))

(include-book "std/testing/eval" :dir :system)

; ERROR!  Not congruent.
(must-fail
 (defstobj st4
   (reg3 :type (array (unsigned-byte 31) (8))
         :initially 0)
   (pc3 :type (unsigned-byte 31)
        :initially 555)
   halt3
   :congruent-to st2))

(must-fail
 (defstobj st4
   (reg4 :type (array (unsigned-byte 31) (8))
         :initially 0)
   (pc4 :type (unsigned-byte 30) ; changed from 31!
        :initially 555)
   halt4
   (mem4 :type (array (unsigned-byte 31) (*mem-size*))
         :initially 0 :resizable t)
   :congruent-to st1))

(defmacro must-not-translate (form)
  `(must-eval-to-t ; use essentially the translate1 call from trans-eval
    (mv-let
     (erp trans bindings state)
     (translate1 ',form :stobjs-out '((:stobjs-out . :stobjs-out))
                 t
                 'must-not-translate (w state) state)
     (declare (ignore trans bindings))
     (value (not (not erp))))))

(defmacro must-fail+ (form)
  `(make-event
    (mv-let (erp val state)
            (trans-eval ',form 'must-fail+ state t)
            (declare (ignore val))
            (cond (erp (value '(value-triple :failed-as-expected)))
                  (t (silent-error state))))))

(defmacro must-succeed+ (form)
  `(must-succeed
    (trans-eval ',form 'must-not-translate state t)))

; The error message for the following isn't as helpful as it might be, but it's
; good enough; in fact it's essentially identical to the corresponding message
; when using v4-3.
(must-not-translate
 (swap-st1-st2 st1 st1))

(must-succeed+
 (mv-let (st1 st2)
         (swap-st1-st2 st2 st1)
         (mv st1 st2)))

(must-succeed+
 (mv-let (st2 st1)
         (swap-st1-st2 st1 st2)
         (mv st1 st2)))

(must-not-translate ; this doesn't swap
 (mv-let (st1 st2)
         (swap-st1-st2 st1 st2)
         (mv st1 st2)))

(must-not-translate ; this doesn't swap
 (mv-let (st2 st1)
         (swap-st1-st2 st2 st1)
         (mv st1 st2)))

; Test with-local-stobj.  Note that swap doesn't actually change st1 or st2,
; which is why val0 = val.
(defun test1 ()
  (with-local-stobj
   st1
   (mv-let
    (result st1)
    (with-local-stobj
     st2
     (mv-let
      (st2 st1 val0 val)
      (let* ((st1 (update2 4 st1))
             (st2 (update2 5 st2))
             (val0 (list (halt1 st1) (halt2 st1) (halt2 st2) (halt1 st2))))
        (mv-let
         (st2 st1)
         (swap-st1-st2 st1 st2)
         (mv st2 st1
             val0
             (list (halt1 st1) (halt2 st1) (halt2 st2) (halt1 st2)))))
      (mv (and (equal val0 '(4 4 5 5))
               (equal val '(4 4 5 5)))
          st1)))
    result)))

; Test with-local-stobj.  Note that swap doesn't actually change st1 or st2,
; which is why val0 = val.
(defun test2 ()
  (with-local-stobj
   st1
   (mv-let
    (result st1)
    (with-local-stobj
     st2
     (mv-let
      (st2 st1 val0 val)
      (let* ((st1 (update2 4 st1))
             (st2 (update2 5 st2))
             (val0 (list (halt1 st1) (halt2 st1) (halt2 st2) (halt1 st2))))
        (mv-let
         (st1 st2)
         (swap-st1-st2 st2 st1)
         (mv st2 st1
             val0
             (list (halt1 st1) (halt2 st1) (halt2 st2) (halt1 st2)))))
      (mv (and (equal val0 '(4 4 5 5))
               (equal val '(4 4 5 5)))
          st1)))
    result)))

(assert-event (test1))
(assert-event (test2))

; Test guard violation messages.
(defun update3 (x st2)
  (declare (xargs :stobjs st2
                  :guard (acl2-numberp x)))
  (update1 x st2))

; Should cause same guard violation message as before.
; (Note: The with-guard-checking wrapper is needed during book certification.)
(must-fail+ (with-guard-checking t (update3 'a st2)))

; Guard violation message should complain about call on st1, not on st2.
; (Note: The with-guard-checking wrapper is needed during book certification.)
(must-fail+ (with-guard-checking t (update3 'a st1)))

(must-not-translate (update3 3 'b))

(defun update4 (x st1 st2)
  (declare (xargs :stobjs (st1 st2)
                  :guard (acl2-numberp x)))
  (declare (ignore st1))
  (update1 x st2))

; Error message explains that the problem arises in spite of congruent stobjs.
(must-not-translate (update4 3 st1 st1))

; Example from :doc print-gv.

(defstobj st fld)

(defun g (x st)
  (declare (xargs :guard (consp x) :stobjs st)
           (ignore x))
  (fld st))

(defun test ()
  (with-local-stobj
   st
   (mv-let (result st)
           (mv (g 3 st) st)
           result)))

(must-fail+ (with-guard-checking t (test)))

(make-event (er-progn (print-gv)
                      (value '(value-triple :ok))))

; Test memoization

(defstobj st0 fld0 :congruent-to st)

(defun h (st)
  (declare (xargs :stobjs st))
  (fld st))

(must-succeed+ (if (hons-enabledp state)
                   (memoize 'h)
                 (value nil)))

(must-succeed+ (update-fld 0 st0))
(must-succeed+ (update-fld 1 st))
(assert-event (equal (h st0) 0))
(assert-event (equal (h st) 1))
(assert-event (equal (h st0) 0))
(assert-event (equal (h st) 1))

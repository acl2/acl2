; Copyright (C) 2013, Regents of the University of Texas
; Written by Matt Kaufmann, April, 2012 (revised July, 2020)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Note: This file was originally a book, books/misc/congruent-stobjs-test.lisp.
; As of this writing it is still certifiable as a book (after changing its file
; extension from "lsp" to "lisp"), because various uses of make-event
; (including must-fail, for example) have been retained.  (They could probably
; be eliminated if we don't care about certifiability.)  However, in July, 2020
; I decided to automate the checking of output from this file (after adding
; tests for translate11-call, as noted below).  The run-script utility was
; handy for that purpose, so this file is now treated as input for that
; utility.

; Warning: Keep the last part, labeled "Tests referenced in ACL2 source
; function translate11-call", in sync with corresponding comments in that
; function's definition.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)
(include-book "std/testing/must-succeed" :dir :system)

(defmacro must-fail^ (x) `(must-fail ,x :with-output-off nil))

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

; ERROR!  Not congruent.
(must-fail^
 (defstobj st4
   (reg3 :type (array (unsigned-byte 31) (8))
         :initially 0)
   (pc3 :type (unsigned-byte 31)
        :initially 555)
   halt3
   :congruent-to st2))

(must-fail^
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
      (value (not (not erp))))
    :with-output-off nil))

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

; As just above:
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

; Sadly, when processing this file by certifying congruent-stobjs-book.lisp,
; the output from the following call of print-gv shows up in the channel
; *standard-co*, hence in congruent-stobjs-book.cert.out, not in
; congruent-stobjs-log.out.
(make-event (er-progn (print-gv)
                      (value '(value-triple :ok))))

; Test memoization

(defstobj st0 fld0 :congruent-to st)

(defun h (st)
  (declare (xargs :stobjs st))
  (fld st))

(must-succeed+ (memoize 'h))

(must-succeed+ (update-fld 0 st0))
(must-succeed+ (update-fld 1 st))
(assert-event (equal (h st0) 0))
(assert-event (equal (h st) 1))
(assert-event (equal (h st0) 0))
(assert-event (equal (h st) 1))

;;; Tests referenced in ACL2 source function translate11-call

(defstobj s$1 fld1)
(defstobj s$2 fld2 :congruent-to s$1)
(defstobj s$3 fld3)

; Our first two examples are simple violations of single-threadedness.  In both
; of these, the arguments of update-fld1 are reversed, so there is an input
; error.  But in the second, there is also an output signature mismatch, which
; we (perhaps arbitrarily) report because we think it might be more useful to
; the user if we point out that every call of update-fld1 is illegal in the
; given context, rather than pointing out a problem with its arguments.

;;; (1a)
(must-fail^
(defun f (s$1)
  (declare (xargs :stobjs s$1))
  (let ((s$1 (update-fld1 s$1 3)))
    s$1))
)

#|
ACL2 Error in ( DEFUN F ...):  A single-threaded object, namely S$1,
is being used where an ordinary object is expected.  Note:  this error
occurred in the context (UPDATE-FLD1 S$1 3).
|#

;;; (1b)
(must-fail^
(defun f (x s$1)
  (declare (xargs :stobjs s$1))
  (list (update-fld1 s$1 x)))
)

#|
ACL2 Error in ( DEFUN F ...):  It is illegal to invoke UPDATE-FLD1
here because of a signature mismatch.  This function call returns a
result of shape S$1 where a result of shape * is required.  Note: 
this error occurred in the context (UPDATE-FLD1 S$1 X).
|#

; Let us now consider variants of the two examples above in which we replace
; s$1 with s$2, which is congruent to s$1.  We see that the errors in (2a),
; (2a'), and (2a'') correspond to the error in (1a), complaining about an input
; since the output isn't obviously problematic; while the error in (2b)
; corresponds to the error in (2b).

;;; (2a) [change (1a), replacing s$1 by congruent stobj s$2]
(must-fail^
(defun f (s$2)
  (declare (xargs :stobjs s$2))
  (let ((s$2 (update-fld1 s$2 3)))
    s2))
)

#|
ACL2 Error in ( DEFUN F ...):  A single-threaded object, namely S$2,
is being used where an ordinary object is expected.  Note:  this error
occurred in the context (UPDATE-FLD1 S$2 3).
|#

;;; (2a') [subtler than (2a), but still not clearly an output problem]
(must-fail^
(defun f (s$1 s$2)
  (declare (xargs :stobjs (s$1 s$2)))
  (let ((s$1 (update-fld1 s$2 3)))
    (mv s$1 s$2)))
)

#|
ACL2 Error in ( DEFUN F ...):  A single-threaded object, namely S$2,
is being used where an ordinary object is expected.  Note:  this error
occurred in the context (UPDATE-FLD1 S$2 3).
|#

;;; (2a'') [like (2a') but with s$1 and s$2 reversed in the binding]
(must-fail^
(defun f (s$1 s$2)
  (declare (xargs :stobjs (s$1 s$2)))
  (let ((s$2 (update-fld1 s$1 3)))
    (mv s$1 s$2)))
)

#|
ACL2 Error in ( DEFUN F ...):  A single-threaded object, namely S$1,
is being used where an ordinary object is expected.  Note:  this error
occurred in the context (UPDATE-FLD1 S$1 3).
|#

;;; (2b) [as with (1b), clearly an output problem -- Note that the use of s$2
;         in the wrong argument position isn't much of a hint that the output
;         should be s$2 instead of s$1, so we can live with mention of s$1
;         instead of s$2 in the error message.]
(must-fail^
(defun f (x s$2)
  (declare (xargs :stobjs s$2))
  (list (update-fld1 s$2 x)))
)

#|
ACL2 Error in ( DEFUN F ...):  It is illegal to invoke UPDATE-FLD1
here because of a signature mismatch.  This function call returns a
result of shape S$1 where a result of shape * is required.  Note: 
this error occurred in the context (UPDATE-FLD1 S$2 X).
|#

;;; (2b') [like (2b) except computed stobjs-out is (s$2) now, not (s$1)]
(must-fail^
(defun f (x s$2)
  (declare (xargs :stobjs s$2))
  (list (update-fld1 x s$2)))
)

#|
ACL2 Error in ( DEFUN F ...):  It is illegal to invoke UPDATE-FLD1
here because of a signature mismatch.  This function call returns a
result of shape S$2 (after accounting for the replacement of some input
stobjs by congruent stobjs) where a result of shape * is required.
Note:  this error occurred in the context (UPDATE-FLD1 X S$2).
|#

;;; (3) [like (2a'') but using non-congruent s$3 in place of s$2,
;;;      which results now in an output mismatch]
(must-fail^
(defun f (s$1 s$3)
  (declare (xargs :stobjs (s$1 s$3)))
  (let ((s$3 (update-fld1 s$1 3)))
    (mv s$1 s$3)))
)

#|
ACL2 Error in ( DEFUN F ...):  It is illegal to invoke UPDATE-FLD1
here because of a signature mismatch.  This function call returns a
result of shape S$1 where a result of shape S$3 is required.  Note:
this error occurred in the context (UPDATE-FLD1 S$1 3).
|#

;;; (4) [Sol Swords provided this example, where the arguments of update-fld1
;;;      are in the correct order and we should report an output error, since
;;;      the inputs are legal.]

(must-fail^
(defun foo (s$1 s$2)
  (declare (xargs :stobjs (s$1 s$2)))
  (let ((s$1 (update-fld1 0 s$2)))
    (mv s$1 s$2)))
)

#|
ACL2 Error in ( DEFUN FOO ...):  It is illegal to invoke UPDATE-FLD1
here because of a signature mismatch.  This function call returns a
result of shape S$2 (after accounting for the replacement of some input
stobjs by congruent stobjs) where a result of shape S$1 is required.
Note:  this error occurred in the context (UPDATE-FLD1 0 S$2).
|#

;;; (5) [The following example, a trivial renaming of one provided by Sol
;;;      Swords, illustrates why stobjs-in-out does the best it can even when
;;;      that ultimately still results in an error.  If stobjs-in-out instead
;;;      returned the stobjs-in and stobjs-out without accommodating the
;;;      congruence of s$1 and s$2, then the complaint would be that s$2 is
;;;      being used where s$1 is expected, even though that isn't the error.]

(defun foo (s$1 s$3)
  (declare (xargs :stobjs (s$1 s$3))
           (ignore s$1))
  s$3)

(must-fail^
(defun bar (s$2 s$3)
  (declare (xargs :stobjs (s$2 s$3)))
  (let ((s$3 (foo s$2 s$3x)))
    s$3))
)

#|
ACL2 Error in ( DEFUN BAR ...):  The form S$3X is being used, as an
argument to a call of FOO, where the single-threaded object S$3 is
required.  Note that the variable S$3 is required, not merely a term
that returns such a single-threaded object, so you may need to bind
S$3 with LET; see :DOC stobj.  Note:  this error occurred in the context
(FOO S$2 S$3X).
|#

(defun bar (s$2 s$3)
  (declare (xargs :stobjs (s$2 s$3)))
  (let ((s$3 (foo s$2 s$3)))
    s$3))

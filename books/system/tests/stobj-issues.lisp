; Copyright (C) 2020, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

;;; This book contains tests involving stobj issues.

(in-package "ACL2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; First we test that stobjs are not strings, even in the case of a single
;;; field that is an array of characters.  This is important so that live
;;; stobjs are recognized.  A fix for such stobjs was made 1/24/2020.
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; #+(or gcl sbcl lispworks) ; needed for the "Before the fix" form below
(defstobj st1 (arr1 :type (array (member #\a #\b #\c) (3)) :initially #\b))
#+(or gcl sbcl lispworks)
(make-event (if (st1p st1) '(value-triple t) (mv t nil state)))

(defstobj st2 (arr2 :type (array character (3)) :initially #\b))
(make-event (if (st2p st2) '(value-triple t) (mv t nil state)))

(defstobj st3 (arr3 :type (array standard-char (3)) :initially #\b))
(make-event (if (st3p st3) '(value-triple t) (mv t nil state)))

; #+gcl ; needed for the "Before the fix" form below
(defstobj st4 (arr4 :type (array (satisfies characterp) (3)) :initially #\b))
#+gcl
(make-event (if (st4p st4) '(value-triple t) (mv t nil state)))

(defstobj st5 (arr5 :type (array (or character character) (3)) :initially #\b))
(make-event (if (st5p st5) '(value-triple t) (mv t nil state)))

(defstobj st6 (arr6 :type (array (and character t) (3)) :initially #\b))
(make-event (if (st6p st6) '(value-triple t) (mv t nil state)))

; And finally:

(defttag t)
(remove-untouchable 'USER-STOBJ-ALIST t)
; Before the fix made 1/24/2020:
; (loop$ for pair in (user-stobj-alist state) always (stringp (cdr pair)))
; After that fix (even if we include st1 and st4 in all Lisps):
(assert-event
 (loop$ for pair in (user-stobj-alist state) always (not (stringp (cdr pair)))))
(defttag nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Next we test equality handling for stobjs with a single field that is an
;;; array of bits.  Before a fix made 1/24/2020, the following test failed
;;; because of the use of rassoc-equal instead of rassoc-eq in
;;; actual-stobjs-out1 (which was dramatically changed on 2/18/2020, but we
;;; might as well keep this test).
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; This test is essentially due to Sol Swords.

(defstobj foo
  (arr :type (array bit (0)) :initially 0 :resizable t))
(defstobj bar
  (barr :type (array bit (0)) :initially 0 :resizable t))

(assert-event (equal (arr-length foo) 0))
(assert-event (equal (barr-length bar) 0))

(make-event (er-progn
             (trans-eval-no-warning '(resize-arr 10 foo) 'top state nil)
             (value '(value-triple t))))

(assert-event (equal (arr-length foo) 10)) ;; not 0, as before!
(assert-event (equal (barr-length bar) 0)) ;; not 10, as before!

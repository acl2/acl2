; Error-Value Tuples
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "error-value-tuples")

(include-book "std/testing/assert-equal" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

; cert_param: (non-acl2r)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define zero-vals ((x integerp))
  :returns erp
  (b* (((reterr))
       ((when (>= x 0)) (retok)))
    (reterr (msg "~x0 is negative." x))))

(assert-equal (zero-vals 5)
              nil)

(assert-equal (zero-vals -2)
              (msg "~x0 is negative." -2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define one-val ((x integerp))
  :returns (mv erp (a stringp))
  (b* (((reterr) "")
       ((when (>= x 0)) (retok "okay")))
    (reterr (msg "~x0 is negative." x))))

(assert-equal (mv-list 2 (one-val 5))
              (list nil "okay"))

(assert-equal (mv-list 2 (one-val -2))
              (list (msg "~x0 is negative." -2) ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define two-vals ((x integerp))
  :returns (mv erp (a stringp) (b symbolp))
  (b* (((reterr) "" nil)
       ((when (>= x 0)) (retok "okay" 'okay)))
    (reterr (msg "~x0 is negative." x))))

(assert-equal (mv-list 3 (two-vals 5))
              (list nil "okay" 'okay))

(assert-equal (mv-list 3 (two-vals -2))
              (list (msg "~x0 is negative." -2) "" nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-zero-from-zero ((x integerp))
  :returns erp
  (b* (((reterr))
       ((erp) (zero-vals x)))
    (retok)))

(assert-equal (call-zero-from-zero 5)
              nil)

(assert-equal (call-zero-from-zero -2)
              (msg "~x0 is negative." -2))

;;;;;;;;;;;;;;;;;;;;

(define call-zero-from-zero-iferr ((x integerp))
  :returns erp
  (b* (((reterr))
       ((erp) (zero-vals x) :iferr "Overwrite."))
    (retok)))

(assert-equal (call-zero-from-zero-iferr 5)
              nil)

(assert-equal (call-zero-from-zero-iferr -2)
              "Overwrite.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-zero-from-one ((x integerp))
  :returns (mv erp (a stringp))
  (b* (((reterr) "")
       ((erp) (zero-vals x)))
    (retok "okay")))

(assert-equal (mv-list 2 (call-zero-from-one 5))
              (list nil "okay"))

(assert-equal (mv-list 2 (call-zero-from-one -2))
              (list (msg "~x0 is negative." -2) ""))

;;;;;;;;;;;;;;;;;;;;

(define call-zero-from-one-iferr ((x integerp))
  :returns (mv erp (a stringp))
  (b* (((reterr) "")
       ((erp) (zero-vals x) :iferr "Overwrite."))
    (retok "okay")))

(assert-equal (mv-list 2 (call-zero-from-one-iferr 5))
              (list nil "okay"))

(assert-equal (mv-list 2 (call-zero-from-one-iferr -2))
              (list "Overwrite." ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-zero-from-two ((x integerp))
  :returns (mv erp (a stringp) (b symbolp))
  (b* (((reterr) "" nil)
       ((erp) (zero-vals x)))
    (retok "okay" 'okay)))

(assert-equal (mv-list 3 (call-zero-from-two 5))
              (list nil "okay" 'okay))

(assert-equal (mv-list 3 (call-zero-from-two -2))
              (list (msg "~x0 is negative." -2) "" nil))

;;;;;;;;;;;;;;;;;;;;

(define call-zero-from-two-iferr ((x integerp))
  :returns (mv erp (a stringp) (b symbolp))
  (b* (((reterr) "" nil)
       ((erp) (zero-vals x) :iferr "Overwrite."))
    (retok "okay" 'okay)))

(assert-equal (mv-list 3 (call-zero-from-two-iferr 5))
              (list nil "okay" 'okay))

(assert-equal (mv-list 3 (call-zero-from-two-iferr -2))
              (list "Overwrite." "" nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-one-from-zero ((x integerp))
  :returns erp
  (b* (((reterr))
       ((erp &) (one-val x)))
    (retok)))

(assert-equal (call-one-from-zero 5)
              nil)

(assert-equal (call-one-from-zero -2)
              (msg "~x0 is negative." -2))

;;;;;;;;;;;;;;;;;;;;

(define call-one-from-zero-iferr ((x integerp))
  :returns erp
  (b* (((reterr))
       ((erp &) (one-val x) :iferr "Overwrite."))
    (retok)))

(assert-equal (call-one-from-zero-iferr 5)
              nil)

(assert-equal (call-one-from-zero-iferr -2)
              "Overwrite.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-one-from-one ((x integerp))
  :returns (mv erp (a stringp))
  (b* (((reterr) "")
       ((erp &) (one-val x)))
    (retok "okay")))

(assert-equal (mv-list 2 (call-one-from-one 5))
              (list nil "okay"))

(assert-equal (mv-list 2 (call-one-from-one -2))
              (list (msg "~x0 is negative." -2) ""))

;;;;;;;;;;;;;;;;;;;;

(define call-one-from-one-iferr ((x integerp))
  :returns (mv erp (a stringp))
  (b* (((reterr) "")
       ((erp &) (one-val x) :iferr "Overwrite."))
    (retok "okay")))

(assert-equal (mv-list 2 (call-one-from-one-iferr 5))
              (list nil "okay"))

(assert-equal (mv-list 2 (call-one-from-one-iferr -2))
              (list "Overwrite." ""))

;;;;;;;;;;;;;;;;;;;;

(define call-one-from-one-iferr-wrap ((x integerp))
  :returns (mv erp (a stringp))
  (b* (((reterr) "irrelevant")
       ((erp a) (one-val x) :iferr (cons :wrapped erp)))
    (retok a)))

(assert-equal (mv-list 2 (call-one-from-one-iferr-wrap 5))
              (list nil "okay"))

(assert-equal (mv-list 2 (call-one-from-one-iferr-wrap -2))
              (list (cons :wrapped (msg "~x0 is negative." -2))
                    "irrelevant"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-one-from-two ((x integerp))
  :returns (mv erp (a stringp) (b symbolp))
  (b* (((reterr) "" nil)
       ((erp &) (one-val x)))
    (retok "okay" 'okay)))

(assert-equal (mv-list 3 (call-one-from-two 5))
              (list nil "okay" 'okay))

(assert-equal (mv-list 3 (call-one-from-two -2))
              (list (msg "~x0 is negative." -2) "" nil))

;;;;;;;;;;;;;;;;;;;;

(define call-one-from-two-iferr ((x integerp))
  :returns (mv erp (a stringp) (b symbolp))
  (b* (((reterr) "" nil)
       ((erp &) (one-val x) :iferr "Overwrite."))
    (retok "okay" 'okay)))

(assert-equal (mv-list 3 (call-one-from-two-iferr 5))
              (list nil "okay" 'okay))

(assert-equal (mv-list 3 (call-one-from-two-iferr -2))
              (list "Overwrite." "" nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-two-from-zero ((x integerp))
  :returns erp
  (b* (((reterr))
       ((erp & &) (two-vals x)))
    (retok)))

(assert-equal (call-two-from-zero 5)
              nil)

(assert-equal (call-two-from-zero -2)
              (msg "~x0 is negative." -2))

;;;;;;;;;;;;;;;;;;;;

(define call-two-from-zero-iferr ((x integerp))
  :returns erp
  (b* (((reterr))
       ((erp & &) (two-vals x) :iferr "Overwrite."))
    (retok)))

(assert-equal (call-two-from-zero-iferr 5)
              nil)

(assert-equal (call-two-from-zero-iferr -2)
              "Overwrite.")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-two-from-one ((x integerp))
  :returns (mv erp (a stringp))
  (b* (((reterr) "")
       ((erp & &) (two-vals x)))
    (retok "okay")))

(assert-equal (mv-list 2 (call-two-from-one 5))
              (list nil "okay"))

(assert-equal (mv-list 2 (call-two-from-one -2))
              (list (msg "~x0 is negative." -2) ""))

;;;;;;;;;;;;;;;;;;;;

(define call-two-from-one-iferr ((x integerp))
  :returns (mv erp (a stringp))
  (b* (((reterr) "")
       ((erp & &) (two-vals x) :iferr "Overwrite."))
    (retok "okay")))

(assert-equal (mv-list 2 (call-two-from-one-iferr 5))
              (list nil "okay"))

(assert-equal (mv-list 2 (call-two-from-one-iferr -2))
              (list "Overwrite." ""))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define call-two-from-two ((x integerp))
  :returns (mv erp (a stringp) (b symbolp))
  (b* (((reterr) "" nil)
       ((erp & &) (two-vals x)))
    (retok "okay" 'okay)))

(assert-equal (mv-list 3 (call-two-from-two 5))
              (list nil "okay" 'okay))

(assert-equal (mv-list 3 (call-two-from-two -2))
              (list (msg "~x0 is negative." -2) "" nil))

;;;;;;;;;;;;;;;;;;;;

(define call-two-from-two-iferr ((x integerp))
  :returns (mv erp (a stringp) (b symbolp))
  (b* (((reterr) "" nil)
       ((erp & &) (two-vals x) :iferr "Overwrite."))
    (retok "okay" 'okay)))

(assert-equal (mv-list 3 (call-two-from-two-iferr 5))
              (list nil "okay" 'okay))

(assert-equal (mv-list 3 (call-two-from-two-iferr -2))
              (list "Overwrite." "" nil))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define h ((i integerp))
  :returns (mv erp (x symbolp) (y stringp))
  (b* (((reterr) nil "")
       ((when (= i 0)) (retok 'zero "zero"))
       ((when (= i 1)) (reterr (msg "ONE"))))
    (retok :other "Other.")))

(define g ((i integerp))
  :returns (mv erp (k integerp))
  (b* (((reterr) 0)
       ((erp x y) (h (1+ i)))
       ((when (equal x y)) (reterr 888))
       ((erp z w) (h i) :iferr :rethrow))
    (retok
     (+ (if (eq z 'some) 5 8)
        (length w)))))

(define f ((s stringp))
  :returns erp
  (b* (((reterr))
       ((erp k) (g (length s)))
       ((when (> k 0)) (reterr "bad")))
    (retok)))

(define e ((x consp))
  :returns (mv erp (c characterp))
  (b* (((reterr) #\a)
       ((when (> (len x) 10)) (reterr 'large))
       ((erp) (f "abc")))
    (retok #\G)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define a (x state)
  :returns (mv erp (int integerp) (key keywordp) state)
  (b* (((reterr) 0 :kwd state)
       ((when (consp x)) (reterr "ERR")))
    (retok 1 :good state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj store)

(define b (x state store)
  :returns (mv erp store (int integerp) (key keywordp) state)
  (b* (((reterr) store 0 :key state)
       ((when (consp x)) (reterr "ERR")))
    (mv nil store 1 :good state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define c ((x integerp))
  :returns (mv erp (y integerp))
  (b* (((reterr) (ifix x)))
    (if (> x 0)
        (retok (1- (ifix x)))
      (reterr "negative"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj box
  (stored-value :type integer :initially 0))

(define update-box ((x integerp) box)
  :returns (mv erp box)
  (b* (((reterr) box)
       (box (update-stored-value x box))
       ((when (< x 0)) (reterr :negative)))
    (retok box)))

(define call-update-box ((x integerp) box)
  :returns (mv erp (donep booleanp) box)
  (b* (((reterr) nil box)
       ((erp box) (update-box x box)))
    (retok t box)))

(assert-event
 (b* (((mv erp donep box) (call-update-box 5 box)))
   (mv (and (not erp)
            donep
            (equal (stored-value box) 5))
       box))
 :stobjs-out '(nil box))

(assert-event
 (b* (((mv erp donep box) (call-update-box -2 box)))
   (mv (and (equal erp :negative)
            (not donep)
            (equal (stored-value box) -2))
       box))
 :stobjs-out '(nil box))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define static-exclude-zero (x)
  (b* (((reterr))
       ((unless (and (integerp x) (>= x 0))) (reterr :fail))
       ((noerp) (zero-vals x)))
    nil)
  :guard-hints (("Goal" :in-theory (enable zero-vals))))

(assert-equal (static-exclude-zero 1)
              nil)

(assert-equal (static-exclude-zero -1)
              :fail)

;;;;;;;;;;;;;;;;;;;;

(local
 (progn
   (define static-exclude-zero-invalid ((x integerp))
     :verify-guards nil
     (b* (((reterr))
          ((noerp) (zero-vals x))) ; x may be negative
       nil))

   (must-fail
    (verify-guards static-exclude-zero-invalid
      :hints (("Goal" :in-theory (enable zero-vals)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define static-exclude-one (x)
  (b* (((reterr) "irrelevant")
       ((unless (and (integerp x) (>= x 0))) (reterr :fail))
       ((noerp a) (one-val x)))
    (retok a))
  :guard-hints (("Goal" :in-theory (enable one-val))))

(assert-equal (mv-list 2 (static-exclude-one 1))
              (list nil "okay"))

(assert-equal (mv-list 2 (static-exclude-one -1))
              (list :fail "irrelevant"))

;;;;;;;;;;;;;;;;;;;;

(local
 (progn
   (define static-exclude-one-invalid ((x integerp))
     :verify-guards nil
     (b* (((reterr) "irrelevant")
          ((noerp a) (one-val x))) ; x may be negative
       (retok a)))

   (must-fail
    (verify-guards static-exclude-one-invalid
      :hints (("Goal" :in-theory (enable one-val)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define static-exclude-two (x)
  (b* (((reterr) "irrelevant" 'irrelevant)
       ((unless (and (integerp x) (>= x 0))) (reterr :fail))
       ((noerp a b) (two-vals x)))
    (retok a b))
  :guard-hints (("Goal" :in-theory (enable two-vals))))

(assert-equal (mv-list 3 (static-exclude-two 1))
              (list nil "okay" 'okay))

(assert-equal (mv-list 3 (static-exclude-two -1))
              (list :fail "irrelevant" 'irrelevant))

;;;;;;;;;;;;;;;;;;;;

(local
 (progn
   (define static-exclude-two-invalid ((x integerp))
     :verify-guards nil
     (b* (((reterr) "irrelevant" 'irrelevant)
          ((noerp a b) (two-vals x))) ; x may be negative
       (retok a b)))

   (must-fail
    (verify-guards static-exclude-two-invalid
      :hints (("Goal" :in-theory (enable two-vals)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define static-exclude-zero-no-reterr ((x natp))
  (b* (((noerp) (zero-vals x)))
    :done)
  :guard-hints (("Goal" :in-theory (enable zero-vals))))

(assert-equal (static-exclude-zero-no-reterr 1)
              :done)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define static-exclude-one-no-reterr ((x natp))
  (b* (((noerp a) (one-val x)))
    a)
  :guard-hints (("Goal" :in-theory (enable one-val))))

(assert-equal (static-exclude-one-no-reterr 1)
              "okay")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define static-exclude-two-no-reterr ((x natp))
  (b* (((noerp a b) (two-vals x)))
    (mv a b))
  :guard-hints (("Goal" :in-theory (enable two-vals))))

(assert-equal (mv-list 2 (static-exclude-two-no-reterr 1))
              (list "okay" 'okay))

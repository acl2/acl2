; An assert utility that supports stobjs
;
; Copyright (C) 2017-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Is this now superseded by other assert utilities?

;; TODO: Use this more (e.g., to test the rewriter?)?

;; See also assert!-stobj and friends.  Note that assert-equal-with-stobjs
;; supports multiple stobjs.

;; FORM should return (mv result ...) where the ... stands for the indicated
;; stobjs.  This checks whether the RESULT returned is equal to EXPECTED-RESULT
;; and deals with returning the stobjs.
(defun assert-equal-with-stobjs-fn (form
                                    expected-result
                                    stobjs
                                    whole-form)
  `(make-event
    (mv-let (result ,@stobjs)
      ,form
      (if (equal result ,expected-result)
          (mv nil ;; no error
              '(value-triple ':success)
               ,@stobjs)
        (mv t ;; error
            (er hard 'assert-equal-with-stobjs-fn
                "Result of ~x0 is ~x1, but we expected ~x2."
                ',whole-form
                result
                ,expected-result)
             ,@stobjs)))))

;; FORM should return (mv result ...) where the ... stands for the indicated
;; stobjs.  This checks whether the RESULT returned is equal to EXPECTED-RESULT
;; and deals with returning the stobjs.
(defmacro assert-equal-with-stobjs (&whole whole-form
                                           form
                                           expected-result
                                           &key
                                           (stobjs '(state)))
  `(with-output
     :off summary
     :gag-mode nil
     ,(assert-equal-with-stobjs-fn form expected-result stobjs whole-form)))

;;;
;;; assert-equal-with-stobjs2
;;;

;; FORM should return (mv erp result ...) where the ... stands for the indicated
;; stobjs.  This checks whether the RESULT returned is equal to EXPECTED-RESULT
;; and deals with returning the stobjs.
(defun assert-equal-with-stobjs2-fn (form
                                     expected-result
                                     stobjs
                                     whole-form)
  `(make-event
    (mv-let (erp result ,@stobjs)
      ,form
      (if erp
          (mv t
              (er hard 'assert-equal-with-stobjs2-fn"Calling ~x0 returned an error." ',whole-form)
              ,@stobjs)
        (if (equal result ,expected-result)
            (mv nil ;; no error
                '(value-triple ':success)
                ,@stobjs)
          (mv t ;; error
              (er hard 'assert-equal-with-stobjs2-fn
                  "Result of ~x0 is ~x1, but we expected ~x2."
                  ',whole-form
                  result
                  ,expected-result)
              ,@stobjs))))))

;; FORM should return (mv erp result ...) where the ... stands for the indicated
;; stobjs.  This checks whether the RESULT returned is equal to EXPECTED-RESULT
;; and deals with returning the stobjs.
(defmacro assert-equal-with-stobjs2 (&whole whole-form
                                            form
                                            expected-result
                                            &key
                                            (stobjs '(state)))
  `(with-output
     :off summary
     :gag-mode nil
     ,(assert-equal-with-stobjs2-fn form expected-result stobjs whole-form)))

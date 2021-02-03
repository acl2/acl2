; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann (original date November, 2016)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; First, an example from Eric Smith
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(encapsulate
  (((foo *) => *))
  (local (defund foo (x) (declare (ignore x)) 7))
  (defthm natp-of-foo
    (natp (foo x))
    :rule-classes (:rewrite :type-prescription)))

(defthm natp-of-foo-squared
  (natp (* (foo x) (foo x))))

(defthm natp-of-foo-cubed
  (natp (* (foo x) (foo x) (foo x))))

; We make the following local to an encapsulate, so that it doesn't affect
; subsequent events.

(encapsulate
  nil
  (local
   (progn

     ;; Return a particular natp:
     (defun bar (x) (declare (ignore x)) 7)

     (encapsulate
       nil
       ;; Proof by functional instantiation, requires proving that bar
       ;; returns a natp.
       (defthm natp-of-bar-squared
         (natp (* (bar x) (bar x)))
         :hints (("Goal" :in-theory '(bar (:executable-counterpart natp))
                  :use (:instance (:functional-instance natp-of-foo-squared
                                                        (foo bar)))))))

; This uses the same functional substitution as above.  Before November 2016 it
; failed when trying to prove the constraint, because of the surrounding
; encapsulate.  That has been fixed.

     (defthm natp-of-bar-cubed
       (natp (* (bar x) (bar x) (bar x)))
       :hints (("Goal" :in-theory nil
                :use (:instance (:functional-instance natp-of-foo-cubed
                                                      (foo bar)))))))))

; As above, but with local event still supplying the saved info.  Ah, but since
; it's an empty encapsulate, this fails.

(must-fail
(encapsulate
  nil
  (local
   (progn

     ;; Return a particular natp:
     (defun bar (x) (declare (ignore x)) 7)

     (encapsulate
       nil
       ;; Proof by functional instantiation, requires proving that bar
       ;; returns a natp.
       (local
        (defthm natp-of-bar-squared
          (natp (* (bar x) (bar x)))
          :hints (("Goal" :in-theory '(bar (:executable-counterpart natp))
                   :use (:instance (:functional-instance natp-of-foo-squared
                                                         (foo bar))))))))

; This uses the same functional substitution as above.  Before November 2016 it
; failed when trying to prove the constraint, because of the surrounding
; encapsulate.  That has been fixed.

     (defthm natp-of-bar-cubed
       (natp (* (bar x) (bar x) (bar x)))
       :hints (("Goal" :in-theory nil
                :use (:instance (:functional-instance natp-of-foo-cubed
                                                      (foo bar)))))))))
)

; Here's a version of the test just above where the encapsulate is not empty.

(encapsulate
  nil
  (local
   (progn

     ;; Return a particular natp:
     (defun bar (x) (declare (ignore x)) 7)

     (encapsulate
       nil

       (defun h (x) x) ; prevent encapsulate from being empty

       ;; Proof by functional instantiation, requires proving that bar
       ;; returns a natp.
       (local
        (defthm natp-of-bar-squared
          (natp (* (bar x) (bar x)))
          :hints (("Goal" :in-theory '(bar (:executable-counterpart natp))
                   :use (:instance (:functional-instance natp-of-foo-squared
                                                         (foo bar))))))))

; This uses the same functional substitution as above.  Before November 2016 it
; failed when trying to prove the constraint, because of the surrounding
; encapsulate.  That has been fixed.

     (defthm natp-of-bar-cubed
       (natp (* (bar x) (bar x) (bar x)))
       :hints (("Goal" :in-theory nil
                :use (:instance (:functional-instance natp-of-foo-cubed
                                                      (foo bar)))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Avoid caching from non-trivial encapsulate
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we check that when a proved constraint depends logically on axiomatic
; events not exported from the encapsulate, that constraint is not stored.
; Actually, ACL2 simply refuses to do such caching inside any encapsulate with
; non-empty signature.

(encapsulate
  nil
  (local
   (progn
     (encapsulate
       ((bar (x) t))

       ;; Return a particular natp:
       (local (defun bar (x) (declare (ignore x)) 7))

       ;; Proof by functional instantiation, requires proving that bar
       ;; returns a natp.
       (defthm natp-of-bar-squared
         (natp (* (bar x) (bar x)))
         :hints (("Goal" :in-theory '(bar (:executable-counterpart natp))
                  :use (:instance (:functional-instance natp-of-foo-squared
                                                        (foo bar)))))))

; This uses the same functional substitution as above.  Before November 2016 it
; failed when trying to prove the constraint, because of the surrounding
; encapsulate.  That has been fixed.

     (must-fail
      (defthm natp-of-bar-cubed
        (natp (* (bar x) (bar x) (bar x)))
        :hints (("Goal" :in-theory nil
                 :use (:instance (:functional-instance natp-of-foo-cubed
                                                       (foo bar))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Avoid caching for :program mode
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail
(encapsulate
  nil
  (local
   (progn

     ;; Return a particular natp:
     (defun bar (x)
       (declare (ignore x)
                (xargs :mode :program))
       7)

     (encapsulate
       nil

       (local (verify-termination bar))

       (defun h (x) x) ; prevent encapsulate from being empty

       ;; Proof by functional instantiation, requires proving that bar
       ;; returns a natp.
       (local
        (defthm natp-of-bar-squared
          (natp (* (bar x) (bar x)))
          :hints (("Goal" :in-theory '(bar (:executable-counterpart natp))
                   :use (:instance (:functional-instance natp-of-foo-squared
                                                         (foo bar))))))))

; This uses the same functional substitution as above.  Before November 2016 it
; failed when trying to prove the constraint, because of the surrounding
; encapsulate.  That has been fixed.

     (defthm simple
       (equal x x)
       :hints (("Goal" :in-theory nil
                :use (:instance (:functional-instance natp-of-foo-cubed
                                                      (foo bar)))))
       :rule-classes nil))))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Caching still works when event is local
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Try (set-gag-mode nil) to see how the message differs here from the first
; example above.

(encapsulate
  nil
  (local
   (progn

     ;; Return a particular natp:
     (defun bar (x) (declare (ignore x)) 7)

     (encapsulate
       nil
       (defun h (x) x) ; avoid empty encapsulate
       ;; Proof by functional instantiation, requires proving that bar
       ;; returns a natp.
       (local (defthm natp-of-bar-squared
         (natp (* (bar x) (bar x)))
         :hints (("Goal" :in-theory '(bar (:executable-counterpart natp))
                  :use (:instance (:functional-instance natp-of-foo-squared
                                                        (foo bar))))))))

; This uses the same functional substitution as above.  Before November 2016 it
; failed when trying to prove the constraint, because of the surrounding
; encapsulate.  That has been fixed.

     (defthm natp-of-bar-cubed
       (natp (* (bar x) (bar x) (bar x)))
       :hints (("Goal" :in-theory nil
                :use (:instance (:functional-instance natp-of-foo-cubed
                                                      (foo bar)))))))))

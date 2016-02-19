; Ensuring that Conditions Hold -- Tests
;
; Copyright (C) 2015-2016 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file contains tests for the macros that ensure that conditions hold.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "ensure")
(include-book "kestrel/general/testing" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (define f (x)
   :verify-guards nil
   (b* ((- (ensure (natp x) "~x0 must be a natural number." x))
        (- (ensure (> x 10) "~x0 must be larger than 10." x)))
     nil))

 (must-succeed (defconst *c* (f 20)))

 (must-fail (defconst *c* (f "a")))

 (must-fail (defconst *c* (f 4/5)))

 (must-fail (defconst *c* (f 2))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (define g (x y)
   :verify-guards nil
   (b* ((- (ensure (stringp x) "1st argument must be a string."))
        (- (ensure (stringp y) "2nd argument must be a string."))
        (- (ensure (not (equal x y)) "~x0 and ~x1 must differ." x y)))
     nil))

 (must-succeed (defconst *c* (g "abc" "def")))

 (must-fail (defconst *c* (g "z" 5)))

 (must-fail (defconst *c* (g 'a "w")))

 (must-fail (defconst *c* (g "3" "3"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (define h (state)
   (ensure$ (mv t t state) ""))

 (must-fail (h state)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*

 (define h (x state)
   :verify-guards nil
   (b* (((er &) (ensure$ (value (natp x)) "~x0 must be a natural number." x))
        ((er &) (ensure$ (value (> x 10)) "~x0 must be larger than 10." x)))
     (value '(defun f (y) y))))

 (must-succeed (make-event (h 20 state)))

 (must-fail (make-event (h 8 state)))

 (must-fail (make-event (h "aa" state))))

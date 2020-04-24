; Messages -- Tests
;
; Copyright (C) 2020 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "messages")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (maybe-msgp nil))

(assert! (maybe-msgp "abc"))

(assert! (maybe-msgp (msg "xy")))

(assert! (maybe-msgp (msg "~x0 and ~x1" #\a '(1 2 3))))

(assert! (not (maybe-msgp 33)))

(assert! (not (maybe-msgp '(#\c "a"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (msg-listp nil))

(assert! (msg-listp '("abc" "xy")))

(assert! (msg-listp (list "qqq" (msg "~x0 and ~x1" #\a '(1 2 3)))))

(assert! (not (msg-listp 7/4)))

(assert! (not (msg-listp '("ABU" :no))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; convert a message to a string (used in the tests below):
(defun msg-to-string (msg)
  (declare (xargs :mode :program :guard (msgp msg)))
  (let ((string (fms-to-string "~@0" (list (cons #\0 msg)))))
    (implode (cdr (explode string))))) ; remove starting new line

; MSG-DOWNCASE-FIRST:

(assert! (let ((msg "A message"))
           (equal (msg-to-string (msg-downcase-first msg))
                  (str::downcase-first (msg-to-string msg)))))

(assert! (let ((msg "a message"))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "A message")))
           (equal (msg-to-string (msg-downcase-first msg))
                  (str::downcase-first (msg-to-string msg)))))

(assert! (let ((msg (msg "a message")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." 33)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." 'symb)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." '|a=b|)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." #\F)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." "abc")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." (cons 3 'a))))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." 33)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." 'symb)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." '|a=b|)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." #\F)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." "abc")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." (cons 3 'a))))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." 33 nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." 'symb nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." '|a=b| nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." #\F nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." "abc" nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." (cons 3 'a) nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." 33 nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." 'symb nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." '|a=b| nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." #\F nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." "abc" nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." (cons 3 'a) nil)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." 33)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." 'symb)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." '|a=b|)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." #\F)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." "abc")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." (cons 3 'a))))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." 33)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." 'symb)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." '|a=b|)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." #\F)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." "abc")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." (cons 3 'a))))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~t0 etc." 10)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~c0 etc." (cons 17 3))))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~ etc.")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~_0 etc." 5)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~
                          etc.")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~%etc.")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~|etc.")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~~etc.")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~-etc.")))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~n0" 7)))
           (equal (msg-downcase-first msg) msg)))

(assert! (let ((msg (msg "~N0" 7)))
           (equal (msg-to-string (msg-downcase-first msg))
                  (str::downcase-first (msg-to-string msg)))))

(assert! (let ((msg (msg "~@0" (msg "A message ~x0" 0))))
           (equal (msg-to-string (msg-downcase-first msg))
                  (str::downcase-first (msg-to-string msg)))))

(assert! (let ((msg (msg "~s0" "A message")))
           (equal (msg-to-string (msg-downcase-first msg))
                  (str::downcase-first (msg-to-string msg)))))

(assert! (let ((msg (msg "~S0" "A message")))
           (equal (msg-to-string (msg-downcase-first msg))
                  (str::downcase-first (msg-to-string msg)))))

(must-fail
 (assert!
  (msg-downcase-first (msg "~#0~[a~/b~]" 1))))

(must-fail
 (assert!
  (msg-downcase-first (msg "~*0" (list* "str0" "str1" "str2" "str3" nil nil)))))

(must-fail
 (assert!
  (msg-downcase-first (msg "~&0" '(a b c)))))

(must-fail
 (assert!
  (msg-downcase-first (msg "~v0" '(a b c)))))

; MSG-UPCASE-FIRST:

(assert! (let ((msg "a message"))
           (equal (msg-to-string (msg-upcase-first msg))
                  (str::upcase-first (msg-to-string msg)))))

(assert! (let ((msg "A message"))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "a message")))
           (equal (msg-to-string (msg-upcase-first msg))
                  (str::upcase-first (msg-to-string msg)))))

(assert! (let ((msg (msg "A message")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." 33)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." 'symb)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." '|a=b|)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." #\F)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." "abc")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~x0 etc." (cons 3 'a))))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." 33)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." 'symb)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." '|a=b|)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." #\F)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." "abc")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~y0 etc." (cons 3 'a))))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." 33 nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." 'symb nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." '|a=b| nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." #\F nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." "abc" nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~X01 etc." (cons 3 'a) nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." 33 nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." 'symb nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." '|a=b| nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." #\F nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." "abc" nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~Y01 etc." (cons 3 'a) nil)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." 33)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." 'symb)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." '|a=b|)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." #\F)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." "abc")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~f0 etc." (cons 3 'a))))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." 33)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." 'symb)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." '|a=b|)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." #\F)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." "abc")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~F0 etc." (cons 3 'a))))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~t0 etc." 10)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~c0 etc." (cons 17 3))))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~ etc.")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~_0 etc." 5)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~
                          etc.")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~%etc.")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~|etc.")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~~etc.")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~-etc.")))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~N0" 7)))
           (equal (msg-upcase-first msg) msg)))

(assert! (let ((msg (msg "~n0" 7)))
           (equal (msg-to-string (msg-upcase-first msg))
                  (str::upcase-first (msg-to-string msg)))))

(assert! (let ((msg (msg "~@0" (msg "a message ~x0" 0))))
           (equal (msg-to-string (msg-upcase-first msg))
                  (str::upcase-first (msg-to-string msg)))))

(assert! (let ((msg (msg "~s0" "a message")))
           (equal (msg-to-string (msg-upcase-first msg))
                  (str::upcase-first (msg-to-string msg)))))

(assert! (let ((msg (msg "~S0" "a message")))
           (equal (msg-to-string (msg-upcase-first msg))
                  (str::upcase-first (msg-to-string msg)))))

(must-fail
 (assert!
  (msg-upcase-first (msg "~#0~[a~/b~]" 1))))

(must-fail
 (assert!
  (msg-upcase-first (msg "~*0" (list* "str0" "str1" "str2" "str3" nil nil)))))

(must-fail
 (assert!
  (msg-upcase-first (msg "~&0" '(a b c)))))

(must-fail
 (assert!
  (msg-upcase-first (msg "~v0" '(a b c)))))

; String Utilities -- Tests
;
; Copyright (C) 2017 Kestrel Institute (http://www.kestrel.edu)s
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "strings")
(include-book "testing")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert! (nonempty-stringp "ab"))

(assert! (not (nonempty-stringp "")))

(assert! (not (nonempty-stringp 33)))

(assert! (not (nonempty-stringp '(1 g))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (nats=>string nil) "")

(assert-equal (nats=>string '(72 32 109)) "H m")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (string=>nats "") nil)

(assert-equal (string=>nats "#if") '(35 105 102))

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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-equal (ubyte8s=>hexstring nil)
              "")

(assert-equal (ubyte8s=>hexstring '(0))
              "00")

(assert-equal (ubyte8s=>hexstring '(1 2 3))
              "010203")

(assert-equal (ubyte8s=>hexstring '(70 160 180 255 11))
              "46A0B4FF0B")

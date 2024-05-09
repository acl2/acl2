(in-package :cl-user)
(defpackage fast-http-test.util
  (:use :cl
        :fast-http.util
        :prove))
(in-package :fast-http-test.util)

(plan nil)

(defun is-number (string expected)
  (etypecase expected
    (number
     (ok (number-string-p string) (format nil "~S is a number" string))
     (is (read-from-string string) expected (format nil "~S is ~S" string expected)))
    (null
     (ok (not (number-string-p string)) (format nil "~S is not a number" string)))))

(subtest "number-string-p"
  (is-number "100" 100)
  (is-number "  200" 200)
  (is-number (format nil "~C250" #\Tab) 250)
  (is-number " 300  " 300)
  (is-number "10." 10)
  (is-number "" nil)
  (is-number " " nil)
  (is-number (format nil "~C" #\Tab) nil)
  (is-number "10a" nil)
  (is-number "b20" nil)
  (is-number "127.0.0.1" nil)
  (is-number "1 2 3 4" nil))

(finalize)

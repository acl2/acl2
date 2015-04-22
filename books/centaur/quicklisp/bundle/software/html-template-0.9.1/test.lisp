;;; -*- Mode: LISP; Syntax: COMMON-LISP; Package: HTML-TEMPLATE-TEST; Base: 10 -*-
;;; $Header: /usr/local/cvsrep/html-template/test.lisp,v 1.13 2007/01/01 23:49:16 edi Exp $

;;; Copyright (c) 2003-2007, Dr. Edmund Weitz. All rights reserved.

;;; Redistribution and use in source and binary forms, with or without
;;; modification, are permitted provided that the following conditions
;;; are met:

;;;   * Redistributions of source code must retain the above copyright
;;;     notice, this list of conditions and the following disclaimer.

;;;   * Redistributions in binary form must reproduce the above
;;;     copyright notice, this list of conditions and the following
;;;     disclaimer in the documentation and/or other materials
;;;     provided with the distribution.

;;; THIS SOFTWARE IS PROVIDED BY THE AUTHOR 'AS IS' AND ANY EXPRESSED
;;; OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
;;; WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE
;;; ARE DISCLAIMED.  IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY
;;; DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
;;; DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE
;;; GOODS OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS
;;; INTERRUPTION) HOWEVER CAUSED AND ON ANY THEORY OF LIABILITY,
;;; WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT (INCLUDING
;;; NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
;;; SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

(in-package #:cl-user)

#-:cormanlisp
(defpackage #:html-template-test
  (:use #:cl #:html-template))

#+:cormanlisp
(defpackage "HTML-TEMPLATE-TEST"
  (:use "CL" "HTML-TEMPLATE"))

(in-package #:html-template-test)

(format t "~&Please wait a couple of seconds.")
(force-output)

(defvar tmp-dir #p"/tmp/")

(defmacro failedp (&body body)
  `(handler-case
    (progn ,@body nil)
    (condition () t)))

(defmacro warnedp (&body body)
  `(handler-case
    (progn ,@body nil)
    (warning () t)))

(defmacro test (result &rest args)
  (cond (result
          `(assert (string= ,result
                            (with-output-to-string (*default-template-output*)
                              (fill-and-print-template ,@args)))))
        (`(assert (failedp (fill-and-print-template ,@args))))))

(test "abc" "<!-- TMPL_VAR foo -->" '(:foo "abc"))
(test "abc" "<!-- tmpl_var foo -->" '(:foo "abc"))
(test "<!-- tmpl_vaar foo -->" "<!-- tmpl_vaar foo -->" '(:foo "abc"))
(test "xabcy" "x<!-- TMPL_VAR foo -->y" '(:foo "abc"))
(test "" "<!-- TMPL_VAR foo -->" nil)
(test "" "<!-- TMPL_VAR foo -->" '(foo "abc"))
(test "" "<!-- TMPL_VAR foo -->" '(:bar "abc"))
(test "abc" "<!-- TMPL_VAR 'foo' -->" '(:foo "abc"))
(test "abc" "<!-- TMPL_VAR \"foo\" -->" '(:foo "abc"))
(test nil "<!-- TMPL_VAR foo-->" '(:foo "abc"))
(test "" "<!-- TMPL_IF foo -->abc<!-- /TMPL_IF -->" nil)
(test "" "<!-- TMPL_IF foo -->abc<!-- /TMPL_IF -->" '(:foo nil))
(test "abc" "<!-- TMPL_IF foo -->abc<!-- /TMPL_IF -->" '(:foo t))
(test "abc" "<!-- TMPL_IF foo -->abc<!-- /TMPL_IF -->" '(:foo t :bar 42))
(test nil "<!-- TMPL_IF foo -->abc<!-- /TMPL_IF foo -->" nil)
(test nil "<!-- TMPL_IF -->abc<!-- /TMPL_IF -->" nil)
(test "def" "<!-- TMPL_IF foo -->abc<!-- TMPL_ELSE-->def<!-- /TMPL_IF -->" nil)
(test nil "<!-- TMPL_IF foo -->abc<!-- TMPL_ELSE-->def<!-- /TMPL_UNLESS -->" nil)
(test "def" "<!-- TMPL_IF foo -->abc<!-- TMPL_ELSE-->def<!-- /TMPL_IF -->" '(:foo nil))
(test "abc" "<!-- TMPL_IF foo -->abc<!-- TMPL_ELSE-->def<!-- /TMPL_IF -->" '(:foo t))
(test "abc" "<!-- TMPL_UNLESS foo -->abc<!-- TMPL_ELSE-->def<!-- /TMPL_UNLESS -->" '(:foo nil))
(test "def" "<!-- TMPL_UNLESS foo -->abc<!-- TMPL_ELSE-->def<!-- /TMPL_UNLESS -->" '(:foo t))
(test nil "<!-- TMPL_UNLESS foo -->abc<!-- TMPL_ELSE-->def<!-- /TMPL_IF -->" '(:foo t))
(test "abc" "<!-- TMPL_IF foo --><!-- TMPL_VAR foo --><!-- TMPL_ELSE-->def<!-- /TMPL_IF -->" '(:foo "abc"))
(test "def" "<!-- TMPL_IF foo --><!-- TMPL_VAR foo --><!-- TMPL_ELSE-->def<!-- /TMPL_IF -->" '(:foo nil))
(test "abcabcabc" "<!-- TMPL_IF foo --><!-- TMPL_VAR foo -->abc<!-- TMPL_VAR foo --><!-- TMPL_ELSE-->def<!-- /TMPL_IF -->" '(:foo "abc"))
(test "defdefdef" "<!-- TMPL_IF foo --><!-- TMPL_VAR foo -->abc<!-- TMPL_VAR foo --><!-- TMPL_ELSE--><!-- TMPL_VAR bar -->def<!-- TMPL_VAR bar --><!-- /TMPL_IF -->" '(:bar "def"))
(test "[]" "[<!-- TMPL_LOOP foo -->[x]<!-- /TMPL_LOOP -->]" '(:foo nil))
(test "[xxx]" "[<!-- TMPL_REPEAT foo -->x<!-- /TMPL_REPEAT -->]" '(:foo 3))
(test "[]" "[<!-- TMPL_REPEAT foo -->x<!-- /TMPL_REPEAT -->]" '(:foo 0))
(test "[]" "[<!-- TMPL_REPEAT foo -->x<!-- /TMPL_REPEAT -->]" '(:foo "foo"))
(test nil "[<!-- TMPL_REPEAT foo -->x<!-- /TMPL_LOOP -->]" '(:foo 3))
(test nil "[<!-- TMPL_LOOP foo -->x<!-- /TMPL_REPEAT -->]" '(:foo 3))
(test "[[x][x][x]]" "[<!-- TMPL_LOOP foo -->[x]<!-- /TMPL_LOOP -->]" '(:foo (1 2 3)))
(test "[[1][2][3]]" "[<!-- TMPL_LOOP foo -->[<!-- TMPL_VAR bar -->]<!-- /TMPL_LOOP -->]" '(:foo ((:bar "1") (:bar "2") (:bar "3"))))
(test "[[][][]]" "[<!-- TMPL_LOOP foo -->[<!-- TMPL_VAR bar -->]<!-- /TMPL_LOOP -->]" '(:foo (() () ())))
(test "[[1][2][3]]" "[<!-- TMPL_LOOP foo -->[<!-- TMPL_VAR bar -->]<!-- /TMPL_LOOP -->]" '(:foo ((:bar "1") (:bar "2") (:bar "3"))))
(test "[[1][][3]]" "[<!-- TMPL_LOOP foo -->[<!-- TMPL_VAR bar -->]<!-- /TMPL_LOOP -->]" '(:foo ((:bar "1") () (:bar "3"))))
(test "[[1][2][3]]" "[<!-- TMPL_LOOP foo -->[<!-- TMPL_IF 'bar' --><!-- TMPL_VAR bar --><!-- TMPL_ELSE-->2<!-- /TMPL_IF -->]<!-- /TMPL_LOOP -->]" '(:foo ((:bar "1") () (:bar "3"))))
(test "[[123][456][789]]" "[<!-- TMPL_LOOP 'foo' -->[<!-- TMPL_LOOP 'bar' --><!-- TMPL_VAR 'bar' --><!-- /TMPL_LOOP -->]<!-- /TMPL_LOOP -->]" '(:foo ((:bar ((:bar "1") (:bar "2") (:bar "3")))
                                                                                                                                                      (:bar ((:bar "4") (:bar "5") (:bar "6")))
                                                                                                                                                      (:bar ((:bar "7") (:bar "8") (:bar "9"))))))
(test "[[123][baz][789]]" "[<!-- TMPL_LOOP 'foo' -->[<!-- TMPL_IF baz --><!-- TMPL_LOOP 'baz' --><!-- TMPL_VAR 'bar' --><!-- /TMPL_LOOP --><!-- TMPL_ELSE -->baz<!-- /TMPL_IF -->]<!-- /TMPL_LOOP -->]" '(:foo ((:baz ((:bar "1") (:bar "2") (:bar "3")))
                                                                                                                                                      ()
                                                                                                                                                      (:baz ((:bar "7") (:bar "8") (:bar "9"))))))
(test nil "<!-- TMPL_ELSE -->" nil)
(test "<!-- /TMPL_ELSE -->" "<!-- /TMPL_ELSE -->" nil)
(test nil "<!-- /TMPL_IF -->" nil)
(test nil "<!-- /TMPL_UNLESS -->" nil)
(test nil "<!-- /TMPL_LOOP -->" nil)
(test nil "<!-- TMPL_IF foo --><!-- TMPL_ELSE -->" nil)
(test nil "<!-- TMPL_UNLESS foo --><!-- TMPL_ELSE -->" nil)
(test nil "<!-- TMPL_LOOP foo --><!-- TMPL_ELSE -->" nil)
(test nil "<!-- TMPL_LOOP foo --><!-- TMPL_ELSE --><!-- /TMPL_LOOP -->" nil)
(test nil "<!-- TMPL_IF bar --><!-- TMPL_LOOP foo --><!-- TMPL_ELSE --><!-- /TMPL_LOOP -->" nil)
(test nil "<!-- TMPL_IF foo --><!-- TMPL_IF bar -->1<!-- TMPL_ELSE -->2<!-- /TMPL_IF --><!-- TMPL_ELSE --><!-- TMPL_IF baz -->3<!-- TMPL_ELSE -->4<!-- /TMPL_IF -->" nil)
(test "1" "<!-- TMPL_IF foo --><!-- TMPL_IF bar -->1<!-- TMPL_ELSE -->2<!-- /TMPL_IF --><!-- TMPL_ELSE --><!-- TMPL_IF baz -->3<!-- TMPL_ELSE -->4<!-- /TMPL_IF --><!-- /TMPL_IF -->" '(:foo t :bar t))
(test "2" "<!-- TMPL_IF foo --><!-- TMPL_IF bar -->1<!-- TMPL_ELSE -->2<!-- /TMPL_IF --><!-- TMPL_ELSE --><!-- TMPL_IF baz -->3<!-- TMPL_ELSE -->4<!-- /TMPL_IF --><!-- /TMPL_IF -->" '(:foo t :bar nil))
(test "3" "<!-- TMPL_IF foo --><!-- TMPL_IF bar -->1<!-- TMPL_ELSE -->2<!-- /TMPL_IF --><!-- TMPL_ELSE --><!-- TMPL_IF baz -->3<!-- TMPL_ELSE -->4<!-- /TMPL_IF --><!-- /TMPL_IF -->" '(:foo nil :baz t))
(test "4" "<!-- TMPL_IF foo --><!-- TMPL_IF bar -->1<!-- TMPL_ELSE -->2<!-- /TMPL_IF --><!-- TMPL_ELSE --><!-- TMPL_IF baz -->3<!-- TMPL_ELSE -->4<!-- /TMPL_IF --><!-- /TMPL_IF -->" '(:foo nil :baz nil))
(test "X" "<!-- TMPL_CALL foo -->" '(:foo (("X"))))
(test "QUUX" "<!-- TMPL_VAR baz --><!-- TMPL_CALL foo -->" '(:baz "Q"
                                                             :foo (("<!-- TMPL_VAR bar -->" :bar "U")
                                                                   ("<!-- TMPL_VAR bar -->X" :bar "U"))))
(test "" "<!-- TMPL_IF foo --><!-- TMPL_CALL bar --><!-- /TMPL_IF -->" '(:foo (("---"))))
(test nil "<!-- TMPL_CALL foo -->" '(:foo 57))

(let ((temp-name (make-pathname :name (format nil "template-test-~A" (random 1000000))
                                :defaults tmp-dir)))
  (with-open-file (stream temp-name :direction :output :if-exists :error)
    (write-string "<!-- TMPL_VAR foo -->" stream))
  (let ((*warn-on-creation* nil))
    (test "abc" temp-name '(:foo "abc")))
  (with-open-file (stream temp-name :direction :input)
    (test "def" stream '(:foo "def")))
  (with-open-file (stream temp-name :direction :input)
    (let ((tp (create-template-printer stream)))
      (test "ghi" tp '(:foo "ghi"))))
  (let ((tp (create-template-printer temp-name)))
    (test "jkl" tp '(:foo "jkl")))
  (let ((tp (create-template-printer "<!-- TMPL_VAR foo -->")))
    (test "mno" tp '(:foo "mno")))
  (delete-file temp-name)
  ;; sleep because of FILE-WRITE-DATE
  (sleep 2)
  (with-open-file (stream temp-name :direction :output :if-exists :error)
    (write-string "<!-- TMPL_VAR bar -->" stream))
  (assert (warnedp (create-template-printer temp-name)))
  (assert (not (warnedp (create-template-printer temp-name))))
  (assert (warnedp (create-template-printer temp-name :force t)))
  (delete-from-template-cache temp-name)
  (assert (warnedp (create-template-printer temp-name)))
  (clear-template-cache)
  (assert (warnedp (create-template-printer temp-name)))
  (delete-file temp-name))

(let ((*template-start-marker* "<")
      (*template-end-marker* ">"))
  (test "The quick <brown> fox" "The <TMPL_VAR 'speed'> <brown> fox"
        '(:speed "quick")))

(let* ((random-string (format nil "template-test-~A" (random 1000000)))
       (temp-name (merge-pathnames random-string tmp-dir))
       (*default-template-pathname* tmp-dir))
  (with-open-file (stream temp-name :direction :output :if-exists :error)
    (write-string "The <!-- TMPL_VAR speed --> brown fox" stream))
  (let ((*warn-on-creation* nil))
    (test "The very fast brown fox"
          (make-pathname :name random-string)
          '(:speed "very fast")))
  (delete-file temp-name)
  ;; sleep because of FILE-WRITE-DATE
  (sleep 2)
  (with-open-file (stream temp-name :direction :output :if-exists :error)
    (write-string "The <!-- TMPL_VAR speed --> brown fox" stream))
  (let ((*warn-on-creation* nil))
    (test "The very fast brown fox"
          (format nil "<!-- TMPL_INCLUDE '~A' -->" random-string)
          '(:speed "very fast")))
  (delete-file temp-name))

(let* ((random-string (format nil "template-test-~A" (random 1000000)))
       (temp-name (merge-pathnames random-string tmp-dir))
       (random-string-2 (format nil "template-test-2-~A" (random 1000000)))
       (temp-name-2 (merge-pathnames random-string-2 tmp-dir))
       (*default-template-pathname* tmp-dir))
  (with-open-file (stream temp-name :direction :output :if-exists :error)
    (format stream "<!-- TMPL_INCLUDE '~A' -->" random-string-2))
  (with-open-file (stream temp-name-2 :direction :output :if-exists :error)
    (format stream "<!-- TMPL_INCLUDE '~A' -->" random-string))
  (test nil (format nil "<!-- TMPL_INCLUDE '~A' -->" random-string) nil)
  (delete-file temp-name)
  (delete-file temp-name-2))

(assert (string= "The slow brown fox"
                 (with-output-to-string (stream)
                   (let ((*default-template-output* stream))
                     (fill-and-print-template "The <!-- TMPL_VAR speed --> brown fox"
                                              '(:speed "slow"))))))

(let* ((tp (create-template-printer "The <!-- TMPL_VAR speed --> brown fox"))
       (*convert-nil-to-empty-string* nil))
  (with-output-to-string (*default-template-output*)
    (test nil tp '(:foo "bar"))))

(let ((tp (create-template-printer "The <!-- TMPL_VAR speed --> brown fox")))
  (handler-bind
    ((template-missing-value-error (lambda (condition)
                                     (declare (ignore condition))
                                     (use-value "slow"))))
    (let ((*convert-nil-to-empty-string* nil))
      (test "The slow brown fox" tp '(:foo "bar")))))

(let ((*sequences-are-lists* nil))
  (test "[1][2][3]"
        "<!-- TMPL_LOOP vector -->[<!-- TMPL_VAR item -->]<!-- /TMPL_LOOP -->"
        '(:vector #((:item "1")
                    (:item "2")
                    (:item "3"))))
  (test "QUUX" "<!-- TMPL_VAR baz --><!-- TMPL_CALL foo -->"
        '(:baz "Q"
          :foo #(("<!-- TMPL_VAR bar -->" :bar "U")
                 ("<!-- TMPL_VAR bar -->X" :bar "U")))))

(let ((*upcase-attribute-strings* nil))
  (test "The slow brown fox"
        "The <!-- TMPL_VAR speed --> brown fox"
        '(:speed "quick" :|speed| "slow")))

(let ((*template-symbol-package* *package*))
  (test "The slow brown fox"
        "The <!-- TMPL_VAR speed --> brown fox"
        '(:speed "quick" speed "slow")))

(let ((tp (create-template-printer "The <!-- TMPL_VAR speed --> brown fox"))
      (*value-access-function* #'gethash)
      (hash (make-hash-table :test #'eq)))
  (setf (gethash :speed hash) "fast")
  (test "The fast brown fox" tp hash))

(let ((values (list :row-loop
                    (loop for row in '((1 2 3 4) (2 3 4 5) (3 4 5 6))
                          collect (list :col-loop
                                        (loop for col in row
                                              collect (list :item
                                                            (format nil "~A" col)))))))
      (template "<table>
  <!-- TMPL_LOOP row-loop -->
  <tr>
    <!-- TMPL_LOOP col-loop -->
    <td><!-- TMPL_VAR item --></td>
    <!-- /TMPL_LOOP -->
  </tr>
  <!-- /TMPL_LOOP -->
</table>")
      (result "<table>
  <tr>
    <td>1</td>
    <td>2</td>
    <td>3</td>
    <td>4</td>
  </tr>
  <tr>
    <td>2</td>
    <td>3</td>
    <td>4</td>
    <td>5</td>
  </tr>
  <tr>
    <td>3</td>
    <td>4</td>
    <td>5</td>
    <td>6</td>
  </tr>
</table>")
      (*ignore-empty-lines* t))
  (test result template values))

(let ((tp (create-template-printer "A square has <!-- TMPL_VAR number --> corners"))
      (*format-non-strings* nil))
  (handler-bind
    ((template-not-a-string-error (lambda (condition)
                                    (use-value
                                     (format nil "~R"
                                             (template-not-a-string-error-value condition))))))
    (test "A square has four corners" tp '(:number 4))))

(format t "~&All tests passed...")
; Copyright (C) 2017, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; The tests in this file serve as examples for how to use
; read-file-into-string.  Of course, having them included in the regression is
; nice, too.

(in-package "ACL2")

(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-eval-to-t" :dir :system)

; The file read-file-into-string-test.txt should be kept in sync with the
; following constant.

(defconst *test-file-contents*
"This file, which has 140 characters, should be kept in sync with the
definition of *test-file-contents* in file read-file-into-string.lisp.
")

(assert!
 (equal (read-file-into-string "read-file-into-string-test.txt")
        *test-file-contents*))

(assert!
 (equal (read-file-into-string "read-file-into-string-test.txt"
                               :bytes 36)
        "This file, which has 140 characters,"))

(assert!
 (equal (read-file-into-string "read-file-into-string-test.txt"
                               :start 36 :bytes 97)
        " should be kept in sync with the
definition of *test-file-contents* in file read-file-into-string"))

(assert!
 (equal (read-file-into-string "read-file-into-string-test.txt"
                               :start 133)
        ".lisp.
"))

; It is OK to read 0 bytes.

(assert!
 (equal (read-file-into-string "read-file-into-string-test.txt"
                               :bytes 0)
        ""))

; Read-file-into-string for entire file agrees with its logical definition:

(must-eval-to-t
 (let ((str2 (read-file-into-string "read-file-into-string-test.txt")))
   (mv-let (chan state)
     (open-input-channel "read-file-into-string-test.txt" :character state)
     (mv-let (str1 state)
       (read-file-into-string1 chan state nil *read-file-into-string-bound*)
       (value (equal str1 str2))))))

(defun read-file-into-string-in-chunks-rec (bound filename chunk-size start
                                                  state acc)
  (declare (xargs :stobjs state
                  :guard (and (natp bound)
                              (stringp filename)
                              (posp chunk-size)
                              (natp start)
                              (true-listp acc))))
  (let ((string (read-file-into-string filename
                                       :start start
                                       :bytes chunk-size)))
    (cond ((or (zp bound)
               (< (length string) chunk-size))
           (reverse (cons string acc)))
          (t (read-file-into-string-in-chunks-rec (1- bound)
                                                  filename
                                                  chunk-size
                                                  (+ start chunk-size)
                                                  state
                                                  (cons string acc))))))

(defun read-file-into-string-in-chunks (filename chunk-size state)
  (declare (xargs :stobjs state
                  :guard (and (stringp filename)
                              (posp chunk-size))))
  (read-file-into-string-in-chunks-rec *read-file-into-string-bound*
                                       filename chunk-size 0 state nil))

(defun string-append* (lst)
  (cond ((null lst) "")
        ((null (cdr lst)) (car lst))
        (t (string-append (car lst)
                          (string-append* (cdr lst))))))

(assert!
 (equal (string-append* (read-file-into-string-in-chunks
                         "read-file-into-string-test.txt"
                         30 ; which does not divide 140
                         state))
        *test-file-contents*))

(assert!
 (equal (string-append* (read-file-into-string-in-chunks
                         "read-file-into-string-test.txt"
                         20 ; which divides 140
                         state))
        *test-file-contents*))

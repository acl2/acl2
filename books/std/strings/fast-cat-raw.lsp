; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STR")

(defun fast-string-append (x y)
  (declare (type string x)
           (type string y))
  (let* ((xl  (length x))
         (yl  (length y))
         (rl  (the fixnum (+ (the fixnum xl) (the fixnum yl))))
         (ret (make-array rl :element-type 'character))
         (i 0)
         (j 0))
    (declare (type fixnum xl)
             (type fixnum yl)
             (type fixnum rl)
             (type fixnum i)
             (type fixnum j)
             (type string ret))
    (loop until (= i xl)
          do
          (setf (schar ret i) (schar x i))
          (incf i))
    (loop until (= i rl)
          do
          (setf (schar ret i) (schar y j))
          (incf i)
          (incf j))
    ret))

(defun fast-string-append-lst (x)
  (when (atom x)
    (return-from fast-string-append-lst ""))
  (when (atom (cdr x))
    (return-from fast-string-append-lst (car x)))
  (let ((result-length 0))
    (declare (type fixnum result-length))
    (loop for str in x do
          (incf result-length (length (the string str))))
    (let ((ret (make-array result-length :element-type 'character))
          (i   0)
          (j   0))
      (declare (type string ret)
               (type fixnum i)
               (type fixnum j))
      (loop for str in x do
            (let ((strlen (length str)))
              (declare (type fixnum strlen))
              (setq j 0)
              (loop until (= j strlen)
                    do
                    (setf (schar ret i) (schar str j))
                    (incf i)
                    (incf j))))
      ret)))

(defun rchars-to-string (rchars)
  (the string
    (nreverse
     (the string (coerce (the list rchars) 'string)))))


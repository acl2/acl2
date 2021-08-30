; Centaur Miscellaneous Books
; Copyright (C) 2014 Centaur Technology
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

(in-package "ACL2")

(defparameter *spacewalk-min-fn-size*  8000)
(defparameter *spacewalk-min-str-size* 10000)

(defun spacewalk-gather-functions ()
  (let* ((all-fns
          ;; Gather up all functions and their costs
          (let ((results nil))
            (ccl:map-heap-objects
             (lambda (x)
               (when (functionp x)
                 (push (cons (ccl:object-direct-size x) x)
                       results))))
            results))
         ;; Throw out inexpensive functions and sort the rest
         (expensive (remove-if (lambda (x) (< (car x) *spacewalk-min-fn-size*)) all-fns))
         (sorted    (sort expensive (lambda (x y) (> (car x) (car y))))))
    sorted))

(defun spacewalk-gather-strings ()
  (let* ((all-strs (let ((results nil))
                     (ccl:map-heap-objects
                      (lambda (x)
                        (when (stringp x)
                          (push x results))))
                     results))
         (expensive (remove-if (lambda (x) (< (length x) *spacewalk-min-str-size*)) all-strs))
         (sorted    (sort expensive (lambda (x y) (> (length x) (length y))))))
    sorted))

(defun spacewalk-main ()
  (format t "Spacewalk Report~%")
  (format t "--- Heap Utilization by Object Type ---~%")
  (force-output)
  (ccl:heap-utilization)

  (let ((fns (spacewalk-gather-functions)))
    (format t "~%--- Found ~D Large Functions (Size > ~D bytes) ---~%"
            (len fns)
            *spacewalk-min-fn-size*)
    (format t "        Size   Name~%")
    (loop for size/fn in fns do
          (let ((size (car size/fn))
                (fn   (ccl:function-name (cdr size/fn))))
            (format t "  ~10D   ~S~%" size fn))))

  (let ((strs (spacewalk-gather-strings)))
    (format t "~%--- Found ~D Large Strings (Length > ~D bytes) ---~%"
            (len strs) *spacewalk-min-str-size*)
    (format t "        Size   Elided contents~%")
    (loop for str in strs do
          (let ((elide (substitute #\\ #\Newline (subseq str 0 (min 70 *spacewalk-min-str-size*)))))
            (format t "  ~10D   " (length str))
            (write-string elide)
            (format t "~%"))))

  (progn
    (format t "~%--- Hons memory usage ---~%")
    (hons-summary)
    (hons-analyze-memory nil)))

(defun spacewalk ()
  (spacewalk-main)
  nil)

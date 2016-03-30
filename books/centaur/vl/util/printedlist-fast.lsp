; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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

(in-package "VL")
(progn

  (defun vl-printedlist->string-aux (x ret i)
    (declare (type string ret)
             (type fixnum i))
    ;; Returns the updated value of i, equal to (- i (vl-printedlist-length x)).
    (loop while (consp x)
             do
             (let ((elem (car x)))
               (cond ((characterp elem)
                      (progn (setf (schar ret i) elem)
                             (decf i)))
                     ((stringp elem)
                      ;; For strings, things are trickier because the characters of
                      ;; the string *are* in the right order.  It's very helpful to
                      ;; think of a concrete example.  Suppose we do:
                      ;;
                      ;;   print #\A
                      ;;   print #\B
                      ;;   print #\C
                      ;;   print "abc"
                      ;;   print #\D
                      ;;   print #\E
                      ;;
                      ;; Then the rchars we'll have are (#\E #\D "abc" #\C #\B #\A).
                      ;; The ret array is 8 entries long and we've already set
                      ;;   ret[7] = #\E
                      ;;   ret[6] = #\D
                      ;; So we now want to set
                      ;;   ret[5] = #\c
                      ;;   ret[4] = #\b
                      ;;   ret[3] = #\a
                      ;;
                      ;; I think it's easiest to just go down from the end of the
                      ;; string so we can (decf i) like before.
                      (loop for j fixnum from (- (length (the string elem)) 1) downto 0 do
                            (setf (schar ret i) (schar elem j))
                            (decf i)))
                     (t ;; Recursively a list.
                      (setq i (vl-printedlist->string-aux (car x) ret i)))))
             (setq x (cdr x)))
    i)

 (defun vl-printedlist->string (x)

   ;; Optimized PS->STRING routine.  We're going to build the return string in
   ;; two passes.  In the first pass we'll determine how big of an array we
   ;; need.  In the second, we'll fill in its characters with the reverse of
   ;; the elems.

   (let* ((size  (vl-printedlist-length x 0)))
     (unless (typep size 'fixnum)
       (er hard? 'vl-ps->string-fn
           "Printed list will will be longer than a fixnum (~x0).  You don't ~
            actually want to turn it into a string, I think." size))

     ;; Since the elems are in reverse order, we'll work backwards from the end
     ;; of the array.
     (let* ((ret (make-array size :element-type 'character))
            (i   (the fixnum (- (the fixnum size) 1))))
       (declare (type fixnum i))
       (setq i (vl-printedlist->string-aux x ret i))
       (unless (eql i -1)
         (cw "Vl-printedlist->string bug: wrote down to character ~x0 instead of 0~%" (+ i 1)))
       ret))))

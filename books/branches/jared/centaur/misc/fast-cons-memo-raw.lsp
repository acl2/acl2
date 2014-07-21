; Centaur Miscellaneous Books
; Copyright (C) 2012 Centaur Technology
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
; fast cons memoization utility -- raw Lisp
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

(defun restore-conses-from-array (arr)
  (loop for i from 3 to (- (length arr) 3) by 3 do
        (let ((cons (aref arr i)))
          (when (atom cons)
            (return-from restore-conses-from-array nil))
          (setf (car cons) (aref arr (+ 1 i)))
          (setf (cdr cons) (aref arr (+ 2 i))))))

(defparameter *fast-cons-memo-array* nil)

;; Checks to see if a cons X has been visited -- its cdr set to the unique marker
;; value that we generated at the start of the computation.  If so, return T
;; and the value stored in its car.  Otherwise, nil.
(defmacro cons-was-visited (x restore-array)
  `(eq (cdr ,x) (aref ,restore-array 0))) ;; cdr of cons is eq to marker

;; Marks a cons X as visited, storing val in its car.
(defmacro mark-visited-cons (x val restore-array)
  `(let* ((x ,x)
          (restore-array ,restore-array)
          (marker (aref restore-array 0))
          (idx (aref restore-array 1))
          (nextidx (+ 3 idx))
          (restore-array (if (< (length restore-array) nextidx)
                             (setq *fast-cons-memo-array*
                                   (adjust-array restore-array
                                                 (* 2 nextidx)
                                                 :initial-element nil))
                           restore-array)))
     ;; Within each of these setfs, the order doesn't matter.
     ;; But the ordering among them does, for interrupt safety.
     (setf (aref restore-array (+ 1 idx)) (car x)
           (aref restore-array (+ 2 idx)) (cdr x))
     (setf (aref restore-array idx) x)
     (setf (car x) ,val
           (cdr x) marker
           (aref restore-array 1) nextidx)
     restore-array))
          


(defmacro with-fast-cons-memo
  (&key fnname return-vals restore-array initial-size body)
  (let ((restoredp (gensym "RESTORED"))
        (return-val-syms (loop for v in return-vals
                               collect (gensym (symbol-name v)))))
    `(let* (,restoredp
            ,@return-val-syms
            (,restore-array
             (make-array ,initial-size :initial-element nil)))
       ;; slot 0 holds unique pointer used to identify seen conses
       (setf (aref ,restore-array 0) (list 'fcm-marker))
       ;; slot 1 holds the current index, starting at 3
       (setf (aref ,restore-array 1) 3)
       ;; slot 2 is currently unused.
       (setq *fast-cons-memo-array* ,restore-array)
       (unwind-protect
           (progn (multiple-value-setq
                      ,return-val-syms
                    ,body)
                  (restore-conses-from-array
                   *fast-cons-memo-array*)
                  (setq ,restoredp t))
         (unless ,restoredp
           (cw "*** ~s0: Emergency restore... ***~%" ',fnname)
           (cwtime (restore-conses-from-array *fast-cons-memo-array*))
           (cw "*** ~s0: Done emergency restore. ***~%" ',fnname)))
       (values . ,return-val-syms))))

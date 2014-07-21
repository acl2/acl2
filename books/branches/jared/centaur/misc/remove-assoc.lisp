; Centaur Miscellaneous Books
; Copyright (C) 2008-2013 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")

; REMOVE-ASSOC-EQUAL is like DELETE-ASSOC-EQUAL, but removes all occurrences of
; the key from the alist instead of just removing the first occurrence.

; Modifications below to remove-assoc-xxx are from Matt K., 5/19/2014, to
; support changes in let-mbe that provide better guard-checking.

(defun-with-guard-check remove-assoc-eq-exec (x alist)
  (if (symbolp x)
      (alistp alist)
    (symbol-alistp alist))
  (cond ((endp alist) nil)
        ((eq x (car (car alist))) (remove-assoc-eq-exec x (cdr alist)))
        (t (cons (car alist)
                 (remove-assoc-eq-exec x (cdr alist))))))

(defun-with-guard-check remove-assoc-eql-exec (x alist)
  (if (eqlablep x)
      (alistp alist)
    (eqlable-alistp alist))
  (cond ((endp alist) nil)
        ((eql x (car (car alist))) (remove-assoc-eql-exec x (cdr alist)))
        (t (cons (car alist) (remove-assoc-eql-exec x (cdr alist))))))

(defun remove-assoc-equal (x alist)
  (declare (xargs :guard (alistp alist)))
  (cond ((endp alist) nil)
        ((equal x (car (car alist))) (remove-assoc-equal x (cdr alist)))
        (t (cons (car alist) (remove-assoc-equal x (cdr alist))))))

(defmacro remove-assoc-eq (x lst)
  `(remove-assoc ,x ,lst :test 'eq))

(defthm remove-assoc-eq-exec-is-remove-assoc-equal
  (equal (remove-assoc-eq-exec x l)
         (remove-assoc-equal x l)))

(defthm remove-assoc-eql-exec-is-remove-assoc-equal
  (equal (remove-assoc-eql-exec x l)
         (remove-assoc-equal x l)))

(defmacro remove-assoc (x alist &key (test ''eql))
  (declare (xargs :guard (or (equal test ''eq)
                             (equal test ''eql)
                             (equal test ''equal))))
  (cond
   ((equal test ''eq)
    `(let-mbe ((x ,x) (alist ,alist))
              :logic (remove-assoc-equal x alist)
              :exec  (remove-assoc-eq-exec x alist)))
   ((equal test ''eql)
    `(let-mbe ((x ,x) (alist ,alist))
              :logic (remove-assoc-equal x alist)
              :exec  (remove-assoc-eql-exec x alist)))
   (t ; (equal test 'equal)
    `(remove-assoc-equal ,x ,alist))))

(defthm assoc-of-remove-assoc-split
  (equal (assoc j (remove-assoc k a))
         (if (equal j k)
             nil
           (assoc j a))))


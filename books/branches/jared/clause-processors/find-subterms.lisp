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
; Original author: Sol Swords <sswords@centtech.com>


(in-package "ACL2")

;; A set of utility functions for finding or collecting certain subterms of a
;; term/clause.

;; Basic: find one occurrence of a call of a particular function.  Don't look
;; in lambda bodies.
(mutual-recursion
 (defun find-call (fn x)
   (declare (xargs :guard (and (symbolp fn)
                               (pseudo-termp x))))
   (cond ((or (variablep x) (fquotep x)) nil)
         ((eq fn (car x)) x)
         (t (find-call-lst fn (cdr x)))))
 (defun find-call-lst (fn x)
   (declare (xargs :guard (and (symbolp fn)
                               (pseudo-term-listp x))))
   (if (endp x)
       nil
     (or (find-call fn (car x))
         (find-call-lst fn (cdr x))))))

;; Find all occurrences of a call of a particular function.
(mutual-recursion
 (defun find-calls (fn x)
   (declare (xargs :guard (and (symbolp fn)
                               (pseudo-termp x))))
   (cond ((or (variablep x) (fquotep x)) nil)
         ((eq fn (car x))
          (cons x
                (find-calls-lst fn (cdr x))))
         (t (find-calls-lst fn (cdr x)))))
 (defun find-calls-lst (fn x)
   (declare (xargs :guard (and (symbolp fn)
                               (pseudo-term-listp x))))
   (if (endp x)
       nil
     (append (find-calls fn (car x))
             (find-calls-lst fn (cdr x))))))


;; Find all calls of several functions
(mutual-recursion
 (defun find-calls-of-fns (fns x)
   (declare (xargs :guard (and (symbol-listp fns)
                               (pseudo-termp x))))
   (cond ((or (variablep x) (fquotep x)) nil)
         ((member (car x) fns)
          (cons x
                (find-calls-of-fns-lst fns (cdr x))))
         (t (find-calls-of-fns-lst fns (cdr x)))))
 (defun find-calls-of-fns-lst (fns x)
   (declare (xargs :guard (and (symbol-listp fns)
                               (pseudo-term-listp x))))
   (if (endp x)
       nil
     (append (find-calls-of-fns fns (car x))
             (find-calls-of-fns-lst fns (cdr x))))))

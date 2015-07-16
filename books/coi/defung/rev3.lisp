; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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

(in-package "ACL2")

(include-book "defung")

(def::ung rev3 (x)
  (declare (xargs :signature ((true-listp) true-listp)
		  :default-value x))
  (cond
   ((endp x) nil)
   ((endp (cdr x)) (list (car x)))
   (t
    ;; a.b*.c
    (let* ((b.c       (cdr x))
	   (c.rev-b   (rev3 b.c))
	   (rev-b     (cdr c.rev-b))
	   (b         (rev3 rev-b))
	   (a         (car x))
	   (a.b       (cons a b))
	   (rev-b.a   (rev3 a.b))
	   (c         (car c.rev-b))
	   (c.rev-b.a (cons c rev-b.a)))
      c.rev-b.a))))

(defthm len-rev3
  (equal (len (rev3 x))
	 (len x)))

(defthm consp-rev3
  (equal (consp (rev3 x))
	 (consp x)))

(def::total rev3 (x)
  (declare (xargs :measure (len x)))
  t)

;; This is probably true w/out the termination proof ..
;; but it is easier here.
(def::signature rev3 (t) true-listp)

;; [Jared] renamed this from rev to rev1 for compatibility with std/lists/rev
;; which is now being included.

(def::un rev1 (x)
  (declare (xargs :signature ((true-listp) true-listp)))
  (if (endp x) nil
    (append (rev1 (cdr x)) (list (car x)))))

(def::signature rev1 (t) true-listp)

(defthm rev1-rev1
  (equal (rev1 (rev1 x))
	 (list-fix x)))

(defthm consp-rev1
  (equal (consp (rev1 x))
	 (consp x)))

(def::signature cdr (true-listp) true-listp)

(defthm rev3-reduction
  (equal (rev3 x) (rev1 x))
  :hints (("Goal" :induct (rev3 x))))

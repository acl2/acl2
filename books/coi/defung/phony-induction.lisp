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

(in-package "DEFUNG")

(include-book "coi/generalize/generalize" :dir :system)

;; With phony induction it looks like we can induce ACL2 to generalize
;; and induct on the original goal without specialized hints.

(defmacro def::phony-induction (fn args)

  (let* ((phony-test           (symbol-fns::suffix fn '-phony-test))
	 (phony-induction      (symbol-fns::suffix fn '-phony-induction))
	 (phony-induction-rule (symbol-fns::suffix fn '-phony-induction-rule)))

    `(encapsulate
	 ()

       (defun ,phony-test (,@args)
	 (declare (ignore ,@args)) nil)

       (local (in-theory (disable (:type-prescription ,phony-test))))

       (defun ,phony-induction (,@args)
	 (declare (xargs :measure 0))
	 (if (,phony-test ,@args) (,phony-induction ,@args) nil))

       (defthm ,phony-induction-rule t
	 :rule-classes ((:induction :pattern (,fn ,@args)
				    :scheme (,phony-induction ,@args))))

       )))


(local
 (encapsulate
     ()

   (defun goo (x)
     (if (zp x) 0
       (goo (1- x))))

   (in-theory (disable (:type-prescription goo)))

   (defun hoo (x)
     (declare (ignore x)) 0)

   (defthm hoo-is-goo
     (equal (hoo x) (goo (gensym::generalize x)))
     :otf-flg t
     :hints (("Goal" :expand (:free (x) (gensym::generalize x)))))

   (in-theory (disable (:type-prescription hoo) hoo))

   (def::phony-induction hoo (x))

   (defstub arg () nil)

   (acl2::add-generalization-pattern (arg))

   (defthm bar
     (integerp (hoo (arg)))
     :hints (("Goal" :induct (hoo (arg)))))

   ))
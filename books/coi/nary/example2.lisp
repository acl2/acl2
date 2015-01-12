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

;; Using nary to overcome weaknesses in ACL2 congruence capabilities.
;; The term "NOTE:" indicates nary specific steps.

;; NOTE: include the nary library
(include-book "coi/nary/nary" :dir :system)
(include-book "coi/util/deffix" :dir :system)

;; Imagine that we have a couple of equivalence relations ..

(encapsulate
    (
     ((equiv1 * *) => *)
     ((equiv2 * *) => *)
     ((something *) => *)
     )

  (local
   (defun equiv1 (x y)
     (equal x y)))

  (defequiv equiv1)

  (local
   (defun equiv2 (x y)
     (equal x y)))

  (defequiv equiv2)

  (local
   (defun something (x) x))

  ;; Here is something that we can ignore in an equiv1 context ..
  (defthm nuthin-from-something
    (equiv1 (something x) x))

  )

;; NOTE: You need a "fixing" function for your equivalence relation.
;; If you don't have one and don't want to write one, the following
;; macro will create one for you.
(def::fix fix-equiv1 equiv1)

;; NOTE: Once you have your fixing function, you can define it as an
;; nary context using the following macro:
(defcontext (fix-equiv1 x) 1)

;; Here some functions we care about ..
(encapsulate
    (
     ((foo * *) => (mv * *))
     ((goo *)  => *)
     )

  (local
   (defun foo (x y)
     (declare (ignore x y))
     (mv 1 2)))

  (local
   (defun goo (x)
     (declare (ignore x))
     0))

  ;; NOTE: The nary congruence theorem below emulates the following
  ;; theoretical congruence relations:
  ;;
  ;; (defcong equiv1 equiv2 (mv-nth 0 (foo x y)) 1)
  ;; (defcong equiv1 equiv2 (mv-nth 0 (foo x y)) 2)
  ;;
  (defthm mv-nth-foo-cong
    (implies
     ;; NOTE: notice how equiv1 and fix-equiv1 are used here
     ;; to define rewriting contexts for variables x and y
     (bind-context ((x (equiv1 a (fix-equiv1 x)))
		    (y (equiv1 b (fix-equiv1 y)))))
     (equiv2 (mv-nth 0 (foo x y))
	     (skip-rewrite (mv-nth 0 (foo a b))))))

  (defcong equiv2 equal (goo x) 1)

  )

(in-theory (disable mv-nth))

;; Here we see it in action ..

(defthm test-nary-congruence
  (equal (goo (mv-nth 0 (foo (something v) (something w))))
	 (goo (mv-nth 0 (foo v w))))
  :hints (("Goal" :do-not '(preprocess))))

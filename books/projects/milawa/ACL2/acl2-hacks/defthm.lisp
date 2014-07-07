; Milawa - A Reflective Theorem Prover
; Copyright (C) 2005-2009 Kookamara LLC
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
;
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")

#|

;; this isn't needed anymore because we have no-fertilize.lisp instead.
;; we have added defthm and defthmd to the milawa package now.

(defund mangle-hints2 (x)
  ;; X should be a list of instructions to attach to a specific goal, i.e., X
  ;; might be (:in-theory ... :induct ... :do-not ...).  If no :do-not key is
  ;; provided, we add :do-not '(generalize fertilize).
  (declare (xargs :guard (true-listp x)))
  (if (member :do-not x)
      x
    (list* :do-not ''(generalize fertilize) x)))

(defund mangle-hints1 (x)
  ;; X should be a list of hints such as (("Goal" ...) ("Subgoal 1" ...)).  We
  ;; find the goal hint and mangle2 it by adding :do-not '(generalize
  ;; fertilize).  If no goal hint exists, we insert one.
  (declare (xargs :guard t))
  (if (consp x)
      (if (and (consp (car x))
               (stringp (car (car x)))
               (standard-char-listp (coerce (car (car x)) 'list))
               (equal (string-downcase (car (car x))) "goal")
               (true-listp (car x)))
          (cons (cons "Goal" (mangle-hints2 (cdr (car x)))) (cdr x))
        (cons (car x) (mangle-hints1 (cdr x))))
    (cons (cons "Goal" (mangle-hints2 nil))
          nil)))

(defund mangle-hints (x)
  ;; X should be an argument list given to defthm, e.g., something like
  ;; ((implies hyps concl) :rule-classes ... :hints ... :otf-flg t).  We find
  ;; the :hints argument and augment it with our :do-not instruction, or if
  ;; there are no hints we insert our do-not hint on "Goal".
  (declare (xargs :guard t))
  (if (consp x)
      (if (and (equal (car x) :hints)
               (consp (cdr x)))
          (list* :hints
                 (mangle-hints1 (second x))
                 (cddr x))
        (cons (car x) (mangle-hints (cdr x))))
    (list* :hints
           (mangle-hints1 nil)
           nil)))

(defmacro MILAWA::thm (&rest args)
  `(ACL2::thm ,@(mangle-hints args)))

(defmacro MILAWA::defthm (&rest args)
  `(ACL2::defthm ,@(mangle-hints args)))

(defmacro MILAWA::defthmd (&rest args)
  `(ACL2::defthmd ,@(mangle-hints args)))



|#
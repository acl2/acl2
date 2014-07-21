; Fully Ordered Finite Sets
; Copyright (C) 2003-2012 Kookamara LLC
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

(in-package "SET")
(include-book "membership")
(set-verify-guards-eagerness 2)


(defsection delete
  :parents (std/osets)
  :short "@(call delete) removes the element @('a') from the set @('X')."

  :long "<p>If @('a') is not a member of @('X'), then the result is just @('X')
itself.</p>

<p>Efficiency note.  Delete is @('O(n)').  It is very inefficient to call it
repeatedly.  Instead, consider removing multiple elements with @(see
difference) or @(see intersect).</p>

<p>The theorem @('delete-in') is the essential correctness property for
@('delete').</p>"

  (defun delete (a X)
    (declare (xargs :guard (setp X)
                    :verify-guards nil))
    (mbe :logic
         (cond ((empty X) nil)
               ((equal a (head X)) (tail X))
               (t (insert (head X) (delete a (tail X)))))
         :exec
         (cond ((endp X) nil)
               ((equal a (car X)) (cdr X))
               (t (insert (car X) (delete a (cdr X)))))))

  (defthm delete-set
    (setp (delete a X)))

  (verify-guards delete
    :hints(("Goal" :in-theory (enable (:ruleset primitive-rules)))))

  (defthm delete-preserves-empty
    (implies (empty X)
             (empty (delete a X))))

  (defthm delete-in
    (equal (in a (delete b X))
           (and (in a X)
                (not (equal a b)))))

  (defthm delete-sfix-cancel
    (equal (delete a (sfix X))
           (delete a X)))

  (defthm delete-nonmember-cancel
    (implies (not (in a X))
             (equal (delete a X) (sfix X))))

  (defthm delete-delete
    (equal (delete a (delete b X))
           (delete b (delete a X)))
    :rule-classes ((:rewrite :loop-stopper ((a b)))))

  (defthm repeated-delete
    (equal (delete a (delete a X))
           (delete a X)))

  (defthm delete-insert-cancel
    (equal (delete a (insert a X))
           (delete a X)))

  (defthm insert-delete-cancel
    (equal (insert a (delete a X))
           (insert a X)))

  (defthm subset-delete
    (subset (delete a X) X)))

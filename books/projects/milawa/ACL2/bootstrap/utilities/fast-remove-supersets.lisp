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

(in-package "MILAWA")
(include-book "extended-subsets")
(include-book "mergesort")
(%interactive)


(%deflist ordered-list-listp (x)
          (ordered-listp x))

(%defprojection :list (mergesort-list x)
                :element (mergesort x)
                :nil-preservingp t)

(%autoprove ordered-list-listp-of-mergesort-list
            (%cdr-induction x))

(%autoprove superset-of-somep-of-mergesort-left
            (%cdr-induction x))

(%autoprove superset-of-somep-of-mergesort-list-right
            (%cdr-induction x))


(%autoadmit fast-superset-of-somep)

(%autoprove fast-superset-of-somep-when-not-consp
            (%restrict default fast-superset-of-somep (equal x 'x)))

(%autoprove fast-superset-of-somep-of-cons
            (%restrict default fast-superset-of-somep (equal x '(cons b x))))

(%autoprove fast-superset-of-somep-removal
            (%cdr-induction x)
            (%enable default
                     fast-superset-of-somep-when-not-consp
                     fast-superset-of-somep-of-cons))



(%autoadmit fast-remove-supersets1)

(%autoprove fast-remove-supersets1-when-not-consp
            (%restrict default fast-remove-supersets1 (equal todo-sorted 'todo-sorted)))

(%autoprove fast-remove-supersets1-of-cons
            (%restrict default fast-remove-supersets1 (equal todo-sorted '(cons a todo-sorted))))

(%autoprove fast-remove-supersets1-removal
            (%autoinduct remove-supersets1 todo done)
            (%enable default
                     fast-remove-supersets1-when-not-consp
                     fast-remove-supersets1-of-cons))




(%autoadmit cdr-10-times)
(%autoadmit cdr-50-times)
(%autoadmit cdr-250-times)
(%autoadmit len-over-250p)
(%autoadmit some-len-over-250p)

(%autoadmit fast-remove-supersets)

(%autoprove fast-remove-supersets-removal
            (%enable default
                     fast-remove-supersets
                     remove-supersets)
            (%disable default
                      fast-remove-supersets1-removal
                      [outside]fast-remove-supersets1-removal)
            (%use (%instance (%thm fast-remove-supersets1-removal)
                             (todo x)
                             (done nil))))

(%ensure-exactly-these-rules-are-missing "../../utilities/fast-remove-supersets")
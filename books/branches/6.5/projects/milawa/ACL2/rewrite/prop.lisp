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
(include-book "../build/prop")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)

(defderiv rw.crewrite-twiddle-bldr
  :derive (v B (v A C))
  :from   ((proof x (v (v A B) C)))
  :proof  (@derive
           ((v (v A B) C)    (@given x))
           ((v C (v A B))    (build.commute-or @-))
           ((v (v C A) B)    (build.associativity @-))
           ((v B (v C A))    (build.commute-or @-))
           ((v B (v A C))    (build.disjoined-commute-or @-))))

(defderiv rw.crewrite-twiddle2-lemma
  :derive (v B (v (v C D) A))
  :from   ((proof x (v (v (v A B) C) D)))
  :proof  (@derive
           ((v (v (v A B) C) D)    (@given x))
           ((v D (v (v A B) C))    (build.commute-or @-))
           ((v (v D (v A B)) C)    (build.associativity @-))
           ((v C (v D (v A B)))    (build.commute-or @-))
           ((v (v C D) (v A B))    (build.associativity @-))
           ((v (v (v C D) A) B)    (build.associativity @-))
           ((v B (v (v C D) A))    (build.commute-or @-))))

(defderiv rw.crewrite-twiddle2-bldr
  :derive (v (v B C) (v A D))
  :from   ((proof x (v (v (v A B) C) D)))
  :proof  (@derive
           ((v (v (v A B) C) D)    (@given x))
           ((v B (v (v C D) A))    (rw.crewrite-twiddle2-lemma @-))
           ((v B (v C (v D A)))    (build.disjoined-right-associativity @-))
           ((v (v B C) (v D A))    (build.associativity @-))
           ((v (v B C) (v A D))    (build.disjoined-commute-or @-))))

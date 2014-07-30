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

;; I like to write (force (and hyp1 ... hypN)).  I have found that most of the
;; time, this works just fine and has the same behavior as (and (force HYP1)
;; ... (force HYPN)).  However, I have also discovered a case where it does not
;; behave the same, and it caused a proof to fail.  So I redefine force as a
;; macro which expands (force (and hyp1 ... hypn)) into (and (force hyp1)
;; ... (force hypn)).

(defun aux-force-fn (hyps)
  (declare (xargs :mode :program))
  (if (consp hyps)
      (cons `(MILAWA::force ,(car hyps))
            (aux-force-fn (cdr hyps)))
    nil))

(defun jareds-force-fn (hyp)
  ;; Produce the expansion for (force hyp)
  (declare (xargs :mode :program))
  (cond ((and (consp hyp)
              (equal (car hyp) 'AND))
         `(AND ,@(aux-force-fn (cdr hyp))))
        ((and (consp hyp)
              (equal (car hyp) 'MILAWA::force))
         hyp)
        (t
         `(ACL2::force ,hyp))))

(defmacro MILAWA::force (hyp)
  (jareds-force-fn hyp))

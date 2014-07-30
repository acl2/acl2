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
(include-book "proofp")

(defmacro trace-proofp ()
  ;; Trace proofp, but show only the conclusions and hide the axioms, theorems,
  ;; and arity table.
  `(acl2::trace$ (logic.proofp :entry (list (logic.conclusion (car acl2::arglist))))))

(defmacro untrace$ ()
  `(acl2::untrace$))

(defun collect-axioms-aux (x)
  ;; Collect the appeals to axioms and theorems used throughout a proof, which
  ;; might be useful for debugging.
  (declare (xargs :mode :program))
  (if (consp x)
      (cond ((equal (car x) 'axiom)
             (if (equal (len x) 2)
                 (cons (list (second x)) nil)
               (cons (list 'ERROR-AXIOM-NOT-LEN-2) nil)))
            ((equal (car x) 'theorem)
             (if (equal (len x) 2)
                 (cons nil (list (second x)))
               (cons nil (list 'ERROR-THEOREM-NOT-LEN-2))))
            (t
             (let ((car-part (collect-axioms-aux (car x)))
                   (cdr-part (collect-axioms-aux (cdr x))))
               (cons (app (car car-part)
                          (car cdr-part))
                     (app (cdr car-part)
                          (cdr cdr-part))))))
    nil))

(defun collect-axioms (x)
  (declare (xargs :mode :program))
  (let ((data (collect-axioms-aux x)))
    (list (cons 'axioms (remove-duplicates (car data)))
          (cons 'theorems (remove-duplicates (cdr data))))))

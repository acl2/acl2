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
(include-book "translate")
(include-book "substitute-term")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defund logic.translate-sigma (x)
  ;; We should be given a true-list of (var term) 2-tuples, where each var is a
  ;; variable symbol and each term is an untranslated term.  We translate each
  ;; term and call the resulting (var . translated term) pairs the answer.
  ;;
  ;; We return (t . answer) if all the terms are successfully translated, or
  ;; nil otherwise.  If we return nil, a message will be printed indicating
  ;; where the error occurs.
  (declare (xargs :guard t))
  (if (consp x)
      (and (tuplep 2 (car x))
           (let* ((var        (first (car x)))
                  (term       (second (car x)))
                  (trans-term (logic.translate term)))
             (and (logic.variablep var)
                  trans-term
                  (let ((others (logic.translate-sigma (cdr x))))
                    (and others
                         (let* ((others-answer (cdr others))
                                (answer        (cons (cons var trans-term) others-answer)))
                           (cons t answer)))))))
    (if (equal x nil)
        (cons t nil)
      nil)))

(defthm logic.sigmap-of-cdr-of-logic.translate-sigma
  (equal (logic.sigmap (cdr (logic.translate-sigma x)))
         t)
  :hints(("Goal" :in-theory (enable logic.translate-sigma))))


(defund logic.translate-sigma-list (x)
  ;; We should be given a true-list of translatable sigmas.  We translate them
  ;; all, producing answer = (sigma1 ... sigmaN), and return (t . answer) upon
  ;; success.  If any sigma is not translatable, we return nil.
  (if (consp x)
      (let ((part1 (logic.translate-sigma (car x))))
        (and part1
             (let ((part2 (logic.translate-sigma-list (cdr x))))
               (and part2
                    (let ((answer (cons (cdr part1) (cdr part2))))
                      (cons t answer))))))
    (if (equal x nil)
        (cons t nil)
      nil)))

(defthm logic.sigma-listp-of-cdr-of-logic.translate-sigma-list
  (equal (logic.sigma-listp (cdr (logic.translate-sigma-list x)))
         t)
  :hints(("Goal" :in-theory (enable logic.translate-sigma-list))))



(defund logic.translate-sigma-list-list (x)
  ;; We should be given a true-list of translatable sigma lists.  We translate
  ;; them all, producing answer = (sigmas1 ... sigmasN), and return (t
  ;; . answer) upon success.  If any sigma is not translatable, we return nil.
  (if (consp x)
      (let ((part1 (logic.translate-sigma-list (car x))))
        (and part1
             (let ((part2 (logic.translate-sigma-list-list (cdr x))))
               (and part2
                    (let ((answer (cons (cdr part1) (cdr part2))))
                      (cons t answer))))))
    (if (equal x nil)
        (cons t nil)
      nil)))

(defthm logic.sigma-list-listp-of-cdr-of-logic.translate-sigma-list-list
  (equal (logic.sigma-list-listp (cdr (logic.translate-sigma-list-list x)))
         t)
  :hints(("Goal" :in-theory (enable logic.translate-sigma-list-list))))
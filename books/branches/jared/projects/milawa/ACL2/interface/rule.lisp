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
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Rule structure creation
;;
;; We provide some macros for generating rewrite rule structures.

(defmacro %hyp (term &key force limit)
  `(%hyp-fn ',term ,force ,limit))

(defun %hyp-fn (term force limit)
  (declare (xargs :mode :program))
  (let ((term-trans (logic.translate term)))
    (cond ((not term-trans)
           (ACL2::er hard '%hyp "The proposed hyp, ~x0, is not translatable.~%" term))
          ((not (rw.force-modep force))
           (ACL2::er hard '%hyp "The proposed force mode, ~x0, is invalid.~%" force))
          (t
           (rw.hyp term-trans
                   force
                   (if limit t nil)
                   (nfix limit))))))

(defun %hyps-fn-aux (terms force limit)
  (declare (xargs :mode :program))
  (if (consp terms)
      (cons `(%hyps ,(car terms) :force ,force :limit ,limit)
            (%hyps-fn-aux (cdr terms) force limit))
    nil))

(defun %hyps-fn (flag hyp force limit)
  (declare (xargs :mode :program))
  (if (equal flag 'term)
      (if (and (consp hyp)
               (equal (car hyp) 'and))
          (%hyps-fn 'list (cdr hyp) force limit)
        (list `(%hyp ,hyp :force ,force :limit ,limit)))
    (if (consp hyp)
        (fast-app (%hyps-fn 'term (car hyp) force limit)
                  (%hyps-fn 'list (cdr hyp) force limit))
      nil)))

(defmacro %hyps (hyp &key force limit)
  (cons 'list (%hyps-fn 'term hyp force limit)))

(defmacro %rule (name &key (type 'inside) hyps lhs rhs (equiv 'equal) syntax)
  `(%rule-fn ',name ',type ,hyps ',lhs ',rhs ',equiv ',syntax))

(defun %rule-fn (name type hyps lhs rhs equiv syntax)
  (declare (xargs :mode :program))
  (let ((lhs-trans (logic.translate lhs))
        (rhs-trans (logic.translate rhs))
        (syntax-trans (logic.translate-list syntax)))
    (cond ((not (symbolp name))
           (ACL2::er hard '%rule "The proposed name, ~x0, is not a symbol.~%" name))
          ((not (memberp type '(inside outside manual)))
           (ACL2::er hard '%rule "The proposed type, ~x0, is not supported.~%" type))
          ((not lhs-trans)
           (ACL2::er hard '%rule "The proposed lhs, ~x0, is not translatable.~%" lhs))
          ((not rhs-trans)
           (ACL2::er hard '%rule "The proposed rhs, ~x0, is not translatable.~%" rhs))
          ((not (car syntax-trans))
           (ACL2::er hard '%rule "The proposed syntax, ~x0, is not translatable.~%" syntax))
          ((not (logic.all-functionsp (cdr syntax-trans)))
           (ACL2::er hard '%rule "The proposed syntax, ~x0, is not a list of function calls.~%" syntax))
          ((not (memberp equiv '(iff equal)))
           (ACL2::er hard '%rule "The proposed equiv, ~x0, is not equal or iff.~%" equiv))
          (t
           (rw.rule name
                    type
                    (rw.limit-hyps lhs-trans hyps)
                    equiv
                    lhs-trans
                    rhs-trans
                    (cdr syntax-trans)
                    (rw.critical-hyps lhs-trans hyps))))))



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

(defthm not-hide-forward
  (implies
   (not (hide x))
   (not x))
  :hints (("Goal" :expand (hide x)))
  :rule-classes (:forward-chaining))

(defthm not-rewrite-equiv-forward
  (implies
   (not (rewrite-equiv term))
   (not term))
  :rule-classes (:forward-chaining))

(defun member? (x list)
  (declare (type t x list))
  (if (consp list)
      (or (equal x (car list))
          (member? x (cdr list)))
    nil))

(defun equiv-term (equivs term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'not)
       (consp (cdr term))
       (consp (cadr term))
       (let ((term (cadr term)))
         (and (member? (car term) equivs)
              (consp (cdr term))
              (consp (cddr term))
              (not (equal (cadr term) (caddr term)))
              term))))

;; In general, we probably want to rewrite smaller terms with larger terms.
;; For now we just rewrite variables into terms.

(defun optimize-equiv-term (term)
  (declare (type t term))
  (if (and (consp term)
           (consp (cdr term))
           (consp (cddr term))
           (symbolp (caddr term)))
      `(,(car term) ,(caddr term) ,(cadr term))
    term))

;; There may be some advantage to doing this slowly (one at a time).
;; Perhaps a hint to that effect ..

;; [Jared] renamed rewrite-equiv-hint to nary-require-equiv-hint for name
;; compatibility with coi/util/rewrite-equiv.lisp

(defun nary-rewrite-equiv-hint (once cases equivs clause)
  (declare (type (satisfies true-listp) cases))
  (if (consp clause)
      (let ((term (car clause)))
        (let ((term (equiv-term equivs term)))
          (if term
              (nary-rewrite-equiv-hint once (cons `(not (hide (rewrite-equiv ,(optimize-equiv-term term))))
                                             cases) equivs (cdr clause))
            (nary-rewrite-equiv-hint once cases equivs (cdr clause)))))
    (if cases
        (if once nil
          `(:computed-hint-replacement ((nary-rewrite-equiv-hint 't 'nil ',equivs clause)) :cases (,@cases)))
      (if once
          ;; When the following is tried:
          ;; `(:computed-hint-replacement  ((nary-rewrite-equiv-hint 'nil 'nil clause)))
          ;;
          ;; ACL2 produces the following error:
#|

ACL2 Error in a computed hint: The computed hint (NARY-REWRITE-EQUIV-HINT T NIL
CLAUSE) produced the non-nil result
 (:COMPUTED-HINT-REPLACEMENT ((NARY-REWRITE-EQUIV-HINT 'NIL 'NIL CLAUSE))).
But this is an illegal value:  There is no point in attaching the empty
list of hints to "Subgoal 1'".  We suspect that you have made a mistake
in presenting your hints.  See :DOC hints.

|#

          `(:computed-hint-replacement  ((nary-rewrite-equiv-hint 'nil 'nil ',equivs clause)) :cases (t))
        nil))))

(defmacro rewrite-with-equality ()
  `(nary-rewrite-equiv-hint nil nil '(equal) clause))

(defmacro rewrite-with-equiv (&rest args)
  `(nary-rewrite-equiv-hint nil nil '(,@args) clause))

(defun step-nary-rewrite-equiv-hint (stable once cases equivs clause)
  (declare (type (satisfies true-listp) cases))
  (if (and stable (consp clause))
      (let ((term (car clause)))
        (let ((term (equiv-term equivs term)))
          (if term
              (nary-rewrite-equiv-hint once (cons `(not (hide (rewrite-equiv ,(optimize-equiv-term term))))
                                             cases) equivs (cdr clause))
            (nary-rewrite-equiv-hint once cases equivs (cdr clause)))))
    (if (and stable cases)
        (if once nil
          `(:computed-hint-replacement ((step-nary-rewrite-equiv-hint stable-under-simplificationp
                                                            't 'nil ',equivs clause)) :cases (,@cases)))
      (if (and stable once)
          `(:computed-hint-replacement  ((step-nary-rewrite-equiv-hint stable-under-simplificationp
                                                             'nil 'nil ',equivs clause)) :cases (t))
        nil))))

(defmacro step-rewrite-with-equality ()
  `(step-nary-rewrite-equiv-hint stable-under-simplificationp nil nil '(equal) clause))

(defmacro step-rewrite-with-equiv (&rest args)
  `(step-nary-rewrite-equiv-hint stable-under-simplificationp nil nil '(,@args) clause))


;; [Jared] renamed equiv-var-term to nary-equiv-var-term for name compatibility
;; with coi/rewrite-equiv.lisp
(defun nary-equiv-var-term (equivs term)
  (declare (type t term))
  (and (consp term)
       (equal (car term) 'not)
       (consp (cdr term))
       (consp (cadr term))
       (let ((term (cadr term)))
         (and (member? (car term) equivs)
              (consp (cdr term))
              (consp (cddr term))
              (if (symbolp (cadr term))
                  (not (symbolp (caddr term)))
                (if (symbolp (caddr term))
                    (not (symbolp (cadr term)))
                  nil))
              (not (equal (cadr term) (caddr term)))
              term))))

;; [Jared] renamed find-equiv to nary-find-equiv for name compatibility with
;; coi/rewrite-equiv.lisp
(defun nary-find-equiv (equivs clause)
  (declare (type t clause))
  (if (consp clause)
      (let ((term (car clause)))
        (let ((term (nary-equiv-var-term equivs term)))
          (or term (nary-find-equiv equivs (cdr clause)))))
    nil))

#+joe
(defun slow-nary-rewrite-equiv-hint (once cases equivs clause)
  (declare (type (satisfies true-listp) cases))
  (if (consp clause)
      (let ((term (car clause)))
        (let ((term (nary-equiv-var-term equivs term)))
          (if term
              (slow-nary-rewrite-equiv-hint once (cons `(not (hide (rewrite-equiv ,(optimize-equiv-term term))))
                                             cases) equivs (cdr clause))
            (slow-nary-rewrite-equiv-hint once cases equivs (cdr clause)))))
    (if cases
        (if once nil
          `(:computed-hint-replacement ((slow-nary-rewrite-equiv-hint 't 'nil ',equivs clause)) :cases (,@cases)))
      (if once
          `(:computed-hint-replacement  ((slow-nary-rewrite-equiv-hint 'nil 'nil ',equivs clause)) :cases (t))
        nil))))

(defun slow-nary-rewrite-equiv-hint (stbl once equivs clause)
  (declare (type t clause))
  (if stbl
      (let ((term (nary-find-equiv equivs clause)))
        (if term
            (if once nil
              (let ((term `(not (hide (rewrite-equiv ,(optimize-equiv-term term))))))
                `(:computed-hint-replacement
                  ((slow-nary-rewrite-equiv-hint stable-under-simplificationp 't ',equivs clause))
                  :cases (,term))))
          (if once
              `(:computed-hint-replacement
                ((slow-nary-rewrite-equiv-hint stable-under-simplificationp 'nil ',equivs clause)) :cases (t))
            nil)))
    nil))

(defmacro slow-rewrite-with-equiv (&rest args)
  `(slow-nary-rewrite-equiv-hint stable-under-simplificationp nil '(,@args) clause))

(defmacro slow-rewrite-with-equality ()
  `(slow-nary-rewrite-equiv-hint stable-under-simplificationp nil '(equal) clause))

(local
 (encapsulate
  ()

(defstub foo (x) nil)
(defstub goo (x) nil)
(defstub hoo (x) nil)

(encapsulate
 (
  ((fred *) => *)
  )

 (local
  (defun fred (x)
    (declare (ignore x))
    t))

 (defthm fred-goo
   (fred (+ 3 (goo x))))

 )

;;
;; This theorem does not prove without the rewrite-with-equality hint ..
;;
(defthm simple-example
  (implies
   (and
    (integerp x)
    (equal (foo x) (goo x))
    (equal (hoo x) (+ 3 (foo x))))
   (fred (hoo x)))
  :hints ((rewrite-with-equality)))

(defun cnt (list)
  (if (consp list)
      (1+ (cnt (cdr list)))
    0))

;;
;; Here we use it to help apply an induction hypothesis.
;;
(defthm cnt-reduction
  (equal (cnt list)
         (len list))
  :hints ((rewrite-with-equality)))

))

(local
 (encapsulate
  ()

  (defun equiv (x y) (equal x y))

  (defequiv equiv)

  (defcong equiv equal (fred x) 1)

  (defcong equiv equal (binary-+ x y) 1)

  (defcong equiv equal (binary-+ x y) 2)

  (in-theory (disable equiv))

  (defthm simple-equiv-example-1
    (implies
     (and
      (integerp x)
      (equiv (foo x) (goo x))
      (equiv (hoo x) (+ 3 (foo x))))
     (fred (hoo x)))
    :rule-classes nil
    :hints ((rewrite-with-equiv equiv)))

  ;; slow-rewrite currently rewrites only variables.
  #+joe
  (defthm simple-equiv-example-2
    (implies
     (and
      (integerp x)
      (equiv (foo x) (goo x))
      (equiv (hoo x) (+ 3 (foo x))))
     (fred (hoo x)))
    :rule-classes nil
    :hints ((slow-rewrite-with-equiv equiv)))

  ))

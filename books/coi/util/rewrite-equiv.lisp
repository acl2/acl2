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

(include-book "xdoc/top" :dir :system)
(include-book "good-rewrite-order")
(include-book "clause-processor")

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

(defun equiv-var-term (equivs term)
  (declare (xargs :mode :program))
  (and (consp term)
       (equal (car term) 'not)
       (consp (cdr term))
       (consp (cadr term))
       (let ((term (cadr term)))
	 (and (member? (car term) equivs)
	      (consp (cdr term))
	      (consp (cddr term))
	      (let ((lhs (cadr term))
		    (rhs (caddr term)))
		(or (and (good-rewrite-order lhs rhs) `(not (hide (rewrite-equiv ,term))))
		    (and (good-rewrite-order rhs lhs) `(not (hide (rewrite-equiv (,(car term) ,rhs ,lhs)))))
		    nil))))))

(defun find-equiv (equivs clause)
  (declare (xargs :mode :program))
  (if (consp clause)
      (let ((term (car clause)))
	(let ((nterm (equiv-var-term equivs term)))
	  (or (and nterm (cons term nterm))
	      (find-equiv equivs (cdr clause)))))
    nil))

(defun clause-contains (term1 clause)
  (declare (type t clause))
  (if (consp clause)
      (or (equal (car clause) term1)
	  (clause-contains term1 (cdr clause)))
    nil))

(defun replace-1 (term1 term2 clause)
  (declare (type t term1 term2 clause))
  (if (consp clause)
      (if (equal (car clause) term1)
	  (cons term2 (cdr clause))
	(cons (car clause)
	      (replace-1 term1 term2 (cdr clause))))
    nil))

(defun rewrite-equiv-clause-processor (clause hints)
  (if (consp hints)
      (let ((term1 (car hints))
	    (term2 (cdr hints)))
	(let ((clause (replace-1 term1 term2 clause)))
	  (list
	   clause
	   (list (clause-implies term2 term1)))))
    (list clause)))

(defevaluator rewrite-equiv-eval rewrite-equiv-list
  (
   (if a b c)
   ))

(clause-eval-facts rewrite-equiv-eval rewrite-equiv-list)

(local (in-theory (disable alistp)))

(defthm rewrite-equiv-clause-processor-works
  (implies
   (and
    (pseudo-term-listp cl)
    (alistp a)
    (rewrite-equiv-eval (conjoin-clauses
			 (rewrite-equiv-clause-processor cl hints)) a))
   (rewrite-equiv-eval (disjoin cl) a))
  :rule-classes :clause-processor
  :otf-flg t)

;;
;; This would probably work better as a clause processor.
;;
;; What we would need to do is to create two subgoals: one
;; containing the new rewrite-equiv in place of the equivalence
;; and the other with an assertion that the old equivalence
;; justified the replacment.
;;
(defun slow-rewrite-equiv-hint (stbl old equivs clause)
  (declare (xargs :mode :program))
  (if (and old (clause-contains old clause)) nil
    (let ((default (and old `(:COMPUTED-HINT-REPLACEMENT
			      ((slow-rewrite-equiv-hint stable-under-simplificationp nil ',equivs clause))
			      :cases (t)
			      ))))
      (or (and (or old stbl)
	       (let ((hint (find-equiv equivs (reverse clause))))
		 (or (and hint
			  (let ((old (car hint)))
			    (let ((hint `(:clause-processor (rewrite-equiv-clause-processor clause ',hint))))
			      `(:COMPUTED-HINT-REPLACEMENT
				((slow-rewrite-equiv-hint stable-under-simplificationp ',old ',equivs clause))
				,@hint
				))))
		     default)))
	  default))))

;;
;; OK .. again without clause processors.
;;
#+joe
(defun slow-rewrite-equiv-hint (stbl old equivs clause)
  (declare (xargs :mode :program))
  (if (and old (clause-contains old clause)) nil
    (let ((default (and old `(:COMPUTED-HINT-REPLACEMENT
			      ((slow-rewrite-equiv-hint stable-under-simplificationp nil ',equivs clause))
			      ))))
      (or (and (or stbl old)
	       (let ((hint (find-equiv equivs clause)))
		 (or (and hint
			  (let ((old (car hint))
				(new (cdr hint)))
			    `(:COMPUTED-HINT-REPLACEMENT
			      ((slow-rewrite-equiv-hint stable-under-simplificationp ',old ',equivs clause))
			      :cases (,new))))
		     default)))
	  default))))

(defmacro rewrite-equiv-hint (&rest args)
  (if (consp args)
      `(slow-rewrite-equiv-hint stable-under-simplificationp nil '(,@args) clause)
    `(slow-rewrite-equiv-hint stable-under-simplificationp nil '(equal) clause)))

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
    :hints ((rewrite-equiv-hint)))
  
  (defun cnt (list)
    (if (consp list)
        (1+ (cnt (cdr list)))
      0))

  ;;
  ;; A bit convoluted, but here we use it to help apply an induction hypothesis.
  ;;
  (defthm cnt-reduction
    (equal (cnt list)
           (len list))
    :hints (("Goal" :induct (len list)
             :in-theory (disable cnt))
            (rewrite-equiv-hint)
            (and stable-under-simplificationp
                 '(:in-theory (enable cnt)))))
  
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
      :hints ((rewrite-equiv-hint equiv)))
    
    )

  ))

(defxdoc rewrite-equiv-hint
  :short "A hint to induce ACL2 to perform substitutions using equivalence relations from the hypothesis"
  :parents (proof-automation)
  :long "
<p>
@('Rewrite-equiv-hint') is a clause-processor hint that leverages @(see rewrite-equiv)
to induce ACL2 to perform substitution using equivalence relations in the hypothesis.
@('(rewrite-equiv-hint equiv)') will apply @('rewrite-equiv') to any equivalence relation
involving @('equiv') appearing in the hypothesis.  Without an argument, @('(rewrite-equiv-hint)'),
it will apply  @('rewrite-equiv') to any equality in the hypothesis.
</p>
<p>
Example Usage:
</p>
@({
  (include-book \"coi/util/rewrite-equiv\" :dir :system)

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

   (defun equiv (x y) (equal x y))
   
   (defequiv equiv)
   
   (defcong equiv equal (fred x) 1)
   
   (defcong equiv equal (binary-+ x y) 1)
   
   (defcong equiv equal (binary-+ x y) 2)
   
   (in-theory (disable equiv))

  ;;
  ;; This theorem does not prove without rewrite-equiv-hint ..
  ;;
  (defthm simple-example
    (implies
     (and
      (integerp x)
      (equiv (foo x) (goo x))
      (equiv (hoo x) (+ 3 (foo x))))
     (fred (hoo x)))
    :hints ((rewrite-equiv-hint equiv)))

})
")

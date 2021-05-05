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

;;
;; A generic generalization routine
;;

(include-book "coi/symbol-fns/symbol-fns" :dir :system)
(include-book "coi/util/mv-nth" :dir :system)
(include-book "coi/gensym/gensym-list" :dir :system)

(local (include-book "coi/bags/top" :dir :system))
(local (include-book "coi/lists/set" :dir :system))

;; You may wrap terms that you wish to generalize with the
;; function (gensym::generalize term)

(defun gensym::generalize (x) x)

(defevaluator gensym::eval gensym::eval-list
  (
   (if a b c)
   (gensym::generalize x)
   )
  )

(in-theory (disable GENSYM::EVAL-constraint-8))
(in-theory (disable GENSYM::EVAL-constraint-9))

(defun pattern-match-rec (args terms alist)
  (declare (type (satisfies alistp) alist)
	   (xargs :verify-guards nil))
  (if (and (consp args)
	   (consp terms))
      (met ((hit alist)
	    (let ((pattern (car args))
		  (term    (car terms)))
	      (cond
	       ((symbolp pattern)
		(let ((hit (assoc pattern alist)))
		  (if (consp hit)
		      (if (equal (cdr hit) term)
			  (mv t alist)
			(mv nil nil))
		    (mv t (cons (cons pattern term) alist)))))
	       ((consp pattern)
		(cond
		 ((and (consp term) (not (equal (car term) 'quote)))
		  (let ((pfn   (car pattern))
			(pargs (cdr pattern))
			(tfn   (car term))
			(targs (cdr term)))
		    (if (equal pfn tfn)
			(pattern-match-rec pargs targs alist)
		      (mv nil nil))))
		 (t (mv nil nil))))
	       (t
		(mv nil nil)))))
	(if hit (pattern-match-rec (cdr args) (cdr terms) alist)
	  (mv nil nil)))
    (if (and (null args) (null terms))
	(mv t alist)
      (mv nil nil))))

(defthm alistp-pattern-match-rec
  (implies
   (alistp alist)
   (alistp (v1 (pattern-match-rec args terms alist)))))

(verify-guards pattern-match-rec)

(defun clause-keys (clauses)
  (declare (type t clauses)
	   (xargs :Verify-guards nil))
  (if (consp clauses)
      (let ((clause (car clauses)))
	(cond
	 ((symbolp clause)
          (if clause
              (cons clause (clause-keys (cdr clauses)))
            (clause-keys (cdr clauses))))
	 ((atom clause)
	  (clause-keys (cdr clauses)))
	 ((eq (car clause) 'quote)
	  (clause-keys (cdr clauses)))
	 ((consp (car clause))
	  (append (clause-keys (cdr clause))
		  (clause-keys (cdr clauses))))
	 (t
	  (append (clause-keys (cdr clause))
		  (clause-keys (cdr clauses))))))
    nil))

(defthm non-nil-symbol-listp-clause-keys
  (non-nil-symbol-listp (clause-keys clauses))
  :rule-classes ((:forward-chaining :trigger-terms ((clause-keys clauses)))))

(verify-guards clause-keys)

(defthm not-member-key-clause-keys-reduction
  (implies
   (and
    (consp a)
    (pseudo-term-listp clauses)
    (not (bag::memberp (caar a) (clause-keys clauses))))
   (equal (gensym::eval-list clauses a)
	  (gensym::eval-list clauses (cdr a))))
  :hints (("Goal" :in-theory (enable PSEUDO-TERMP pseudo-term-listp)
	   :induct (clause-keys clauses))
	  (and stable-under-simplificationp
	       '(:in-theory (enable GENSYM::EVAL-CONSTRAINT-0)))))

(local (include-book "coi/alists/keyquiv" :dir :system))

(local
 (defthm disjoint-keys-clause-keys-reduction
   (implies
    (and
     (pseudo-term-listp clauses)
     (bag::disjoint (alist::keys x) (clause-keys clauses)))
    (equal (gensym::eval-list clauses (append x y))
           (gensym::eval-list clauses y)))
   :hints (("Goal" :induct (len x)))))

(defun term-keys (term)
  (declare (type t term))
  (cond
   ((symbolp term)
    (and term (list term)))
   ((atom term)
    nil)
   ((eq (car term) 'quote)
    nil)
   ((consp (car term))
    (clause-keys (cdr term)))
   (t
    (clause-keys (cdr term)))))

(defthm non-nil-symbol-listp-term-keys
  (non-nil-symbol-listp (term-keys term))
  :rule-classes ((:forward-chaining :trigger-terms ((term-keys term)))))

(defthm not-member-key-term-keys-reduction
  (implies
   (and
    (consp a)
    (pseudo-termp term)
    (not (bag::memberp (caar a) (term-keys term))))
   (equal (gensym::eval term a)
	  (gensym::eval term (cdr a))))
  :hints (("Goal" :in-theory (enable GENSYM::EVAL-CONSTRAINT-0 pseudo-termp))))

(local
 (defun alist::vals (list)
   (declare (type t list))
   (if (not (consp list)) nil
     (let ((entry (car list)))
       (cons (if (consp entry) (cdr entry) nil)
             (alist::vals (cdr list)))))))

(local
 (defthm vals-append
   (equal (alist::vals (append x y))
          (append (alist::vals x)
                  (alist::vals y)))))
 
(local
 (defthm disjoint-keys-term-keys-reduction
   (implies
    (and
     (pseudo-termp term)
     (bag::disjoint (alist::keys x) (term-keys term)))
    (equal (gensym::eval term (append x y))
           (gensym::eval term y)))))

(local
 (defthm subset-keys-clause-keys-reduction
   (implies
    (and
     (pseudo-term-listp clause)
     (subsetp-equal (clause-keys clause) (alist::keys x)))
    (equal (gensym::eval-list clause (append x y))
           (gensym::eval-list clause x)))
   :hints (("Goal" :expand ((pseudo-term-listp clause)
                            (pseudo-termp (car clause)))
            :in-theory (enable GENSYM::EVAL-CONSTRAINT-0)
            :induct (clause-keys clause)))))

(local
(defthm subset-keys-term-keys-reduction
  (implies
   (and
    (pseudo-termp term)
    (subsetp-equal (term-keys term) (alist::keys x)))
   (equal (gensym::eval term (append x y))
          (gensym::eval term x)))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable GENSYM::EVAL-CONSTRAINT-0)
           :expand ((pseudo-termp term)
                    (term-keys term))))))

(in-theory (disable term-keys))

(defun gensym::pattern-match-list (list terms)
  (declare (type t list terms))
  (if (and (consp list) (consp (car list)))
      (let ((pattern (caar list))
	    (type-p  (cdar list)))
	(met ((hit alist) (pattern-match-rec pattern terms nil))
	     (declare (ignore alist))
	     (if hit (mv terms type-p)
	       (gensym::pattern-match-list (cdr list) terms))))
    (mv nil nil)))

(defun pattern-match-args (fn args terms)
  (declare (type t fn args terms))
  (if (consp terms)
      (let ((term (car terms)))
	(cond
	 ((atom term)
	  (pattern-match-args fn args (cdr terms)))
	 ((eq (car term) 'quote)
	  (pattern-match-args fn args (cdr terms)))
	 ((consp (car term))
	  (or
	   (pattern-match-args fn args (cdr term))
	   (pattern-match-args fn args (cdr terms))))
	 (t
	  (or (and (equal fn (car term))
		   (met ((subterm type-p) (gensym::pattern-match-list args (cdr term)))
			(and subterm (cons (cons fn subterm) type-p))))
	      (pattern-match-args fn args (cdr term))
	      (pattern-match-args fn args (cdr terms))))))
    nil))

(defun fn-symbolp (x)
  (declare (type t x))
  (or (consp x)
      (and (non-nil-symbolp x)
           (not (equal x 'quote)))))
         
(defthm fn-symbolp-implies
  (implies
   (fn-symbolp x)
   (or (consp x)
       (and (non-nil-symbolp x)
            (not (equal x 'quote)))))
  :rule-classes (:forward-chaining))

(in-theory (disable fn-symbolp))

(defun wf-map (map)
  (declare (type t map))
  (if (atom map) (null map)
    (let ((entry (car map)))
      (and (consp entry)
           (pseudo-termp (car entry))
           (non-nil-symbolp (cdr entry))
           (wf-map (cdr map))))))

(defthm wf-map-pairlis$
  (implies
   (force
    (and
     (pseudo-term-listp keys)
     (non-nil-symbol-listp vals)
     (equal (len keys) (len vals))))
   (wf-map (pairlis$ keys vals))))

(defthm wf-map-implies-alistp
  (implies
   (wf-map map)
   (alistp map))
  :rule-classes (:Forward-chaining))

(defthm wf-map-implication
  (implies
   (and
    (wf-map map)
    (assoc-equal key map))
   (non-nil-symbolp (cdr (assoc-equal key map))))
  :rule-classes ((:forward-chaining :trigger-terms ((assoc-equal key map)))))

(defun assox (key alist)
  (declare (type (satisfies alistp) alist))
  (assoc-equal key alist))

(defun replace-matching-subterms (map term-list)
  (declare (type (satisfies alistp) map))
  (if (consp term-list)
      (let ((term (car term-list)))
        (let ((hit (assox term map)))
          (if hit
              (cons (cdr hit) (replace-matching-subterms map (cdr term-list)))
            (cond
             ((atom term)
              (cons term (replace-matching-subterms map (cdr term-list))))
             ((eq (car term) 'quote)
              (cons term (replace-matching-subterms map (cdr term-list))))
             ((consp (car term))
              (cons (cons (car term) (replace-matching-subterms map (cdr term)))
                    (replace-matching-subterms map (cdr term-list))))
             (t
              (cons (cons (car term) (replace-matching-subterms map (cdr term)))
                    (replace-matching-subterms map (cdr term-list))))))))
    nil))

(defthm len-replace-matching-subterms
  (equal (len (replace-matching-subterms map list))
	 (len list)))

(defthm pseudo-termp-listp-replace-matching-subterms
  (implies
   (and
    (wf-map map)
    (pseudo-term-listp clauses))
   (pseudo-term-listp (replace-matching-subterms map clauses)))
  :hints (("Goal" :in-theory (enable pseudo-termp
				     pseudo-term-listp))))

(defun bound-map (map a)
  (if (endp map) t
    (let ((entry (car map)))
      (and (equal (gensym::eval (cdr entry) a) (gensym::eval (car entry) a))
           (bound-map (cdr map) a)))))

(local
(defthmd bound-map-alt
  (equal (bound-map map a)
         (equal (gensym::eval-list (alist::vals map) a)
                (gensym::eval-list (alist::keys map) a))))
)

(defthm bound-map-implication
  (implies
   (and
    (bound-map map a)
    (assoc-equal term map))
   (equal (gensym::eval (cdr (assoc-equal term map)) a) (gensym::eval term a))))

(defthm generic-replace-matching-subterms-reduction
  (implies
   (force 
    (and
     (wf-map map)
     (bound-map map a)))
   (equal (gensym::eval-list (replace-matching-subterms map terms) a)
	  (gensym::eval-list terms a)))
  :hints ((and stable-under-simplificationp
	       '(:in-theory (enable GENSYM::EVAL-CONSTRAINT-0)))
	  ("Goal" :induct (replace-matching-subterms map terms))))

(local (in-theory (e/d (bound-map-alt) (bound-map))))

(local
 (defthm non-membership-from-non-memberp-superset-free
   (implies
    (and
     (not (list::memberp a x))
     (list::subsetp y x))
    (not (list::memberp a y))))
 )

(local
 (defthm subsetp-term-append-term
   (list::subsetp term (append term x)))
 )

(local
 (defthm subsetp-x-append-term-x
   (list::subsetp x (append term x)))
 )

(defund generalization-symbol-base (subterm)
  (declare (type t subterm))
  (case-match subterm
    (('gensym::generalize (fn . &))
     (if (symbolp fn) fn `gensym::var))
    ((fn . &)
     (if (symbolp fn) fn `gensym::var))
    (& `gensym::var)))

(defun generalization-symbol-base-list (list)
  (declare (type t list))
  (if (not (consp list)) nil
    (cons (generalization-symbol-base (car list))
          (generalization-symbol-base-list (cdr list)))))

(defthm true-listp-generalization-symbol-base-list
  (true-listp (generalization-symbol-base-list list))
  :rule-classes (:type-prescription))

(defthm len-generalization-symbol-base-list
  (equal (len (generalization-symbol-base-list list))
         (len list)))

(defthm alistp-pairlis$-rewrite
  (alistp (pairlis$ keys vals)))

(defund car? (x)
  (declare (type t x))
  (if (consp x) (car x) nil))

(defun generalize-clause-processor (clause subterms)
  (declare (type t clause subterms)
           (type (satisfies true-listp) subterms))
  (let ((base-vars (generalization-symbol-base-list subterms)))
    (let ((avoid (append (clause-keys subterms) (clause-keys clause))))
      (let ((vars (gensym::gensym-list base-vars avoid)))
        (mv vars (replace-matching-subterms (pairlis$ subterms vars) clause))))))

(defthm pseudo-term-listp-v1-eneralize-clause-processor
  (implies
   (and
    (pseudo-term-listp clause)
    (pseudo-term-listp subterms))
   (pseudo-term-listp (v1 (generalize-clause-processor clause subterms))))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((generalize-clause-processor clause subterms)))))

(defthm non-nil-symbol-listp-v0-eneralize-clause-processor
  (non-nil-symbol-listp (v0 (generalize-clause-processor clause subterms)))
  :rule-classes (:rewrite
                 (:forward-chaining :trigger-terms ((generalize-clause-processor clause subterms)))))

(defthm len-v0-generalize-clause-processor
  (equal (len (val 0 (generalize-clause-processor cl list)))
         (len list)))

(defun generalize-clause-alist (clause a subterms)
  (declare (type t clause subterms)
           (type (satisfies true-listp) subterms))
  (let ((var-bases (generalization-symbol-base-list subterms)))
    (let ((avoid (append (clause-keys subterms) (clause-keys clause))))
      (let ((vars (gensym::gensym-list var-bases avoid)))
        (append (pairlis$ vars (gensym::eval-list subterms a)) a)))))

(local
 (defun len-len-induction (x y)
   (if (and (consp x) (consp y))
       (len-len-induction (cdr x) (cdr y))
     (list x y))))

(defthmd equal-to-list-equiv
  (implies
   (true-listp x)
   (iff (equal x y)
        (and (true-listp y)
             (acl2::list-equiv x y)))))

(in-theory (disable list::equiv-of-two-true-listps))

(defthm true-listp-eval-list
  (true-listp (gensym::eval-list list env))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :induct (len list))))

(defthm len-eval-list
  (equal (len (gensym::eval-list list env))
         (len list)))

(defthm nth-eval-list
  (equal (nth i (gensym::eval-list list env))
         (if (< (nfix i) (len list))
             (gensym::eval (nth i list) env)
           nil))
  :hints (("Goal" :induct (nth i list))))

(local
(defthm nth-memberp
  (implies
   (and
    (natp i)
    (< i (len list)))
   (list::memberp (nth i list) list))
  :rule-classes (:rewrite (:forward-chaining :trigger-terms ((nth i list)))))
)

(local
(defthm keys-pairlis$
  (implies
   (equal (len x) (len y))
   (equal (alist::keys (pairlis$ x y))
          (list::fix x))))
)

(local
(defthm vals-pairlis$
  (implies
   (equal (len x) (len y))
   (equal (alist::vals (pairlis$ x y))
          (list::fix y))))
)

(local
(defthm assoc-equal-append
  (implies
   (list::memberp a (alist::keys x))
   (equal (assoc-equal a (append x y))
          (assoc-equal a x))))
)

(defthm assoc-nth-pairlis$
  (implies
   (and
    (< (nfix i) (len symbols))
    (bag::unique symbols)
    (equal (len symbols) (len values)))
   (equal (assoc-equal (nth i symbols) (pairlis$ symbols values))
          (cons (nth i symbols) (nth i values))))
  :hints (("Goal" :in-theory (enable bag::unique)
           :induct (cons (nth i symbols) (nth i values)))))

(local
(defthm nth-outside
  (implies
   (<= (len list) (nfix i))
   (equal (nth i list) nil)))
)

(defthm eval-list-symbols
  (implies
   (and
    (non-nil-symbol-listp symbols)
    (true-listp values)
    (bag::unique symbols)
    (equal (len symbols) (len values)))
   (equal (gensym::eval-list symbols (append (pairlis$ symbols values) env))
          values))
  :hints (("Goal" :do-not-induct t
           :in-theory (enable list::equiv-by-multiplicity equal-to-list-equiv))))

(encapsulate
    ()

  (local (include-book "coi/nary/nary" :dir :system))
     
  (local
   (encapsulate
       ()

     (defthm pseudo-termp-disjoin
       (implies
        (pseudo-term-listp clause)
        (pseudo-termp (disjoin clause)))
       :rule-classes (:rewrite (:forward-chaining :trigger-terms ((disjoin clause)))))
     
     (defthm subset-omit-implies-disjoint
       (implies
        (subsetp x omit)
        (list::disjoint x (gensym::gensym-list base omit))))
     
     (defthm open-term-keys
       (implies
        (consp term)
        (equal (term-keys term)
               (COND ((SYMBOLP TERM) (AND TERM (LIST TERM)))
                     ((ATOM TERM) NIL)
                     ((EQ (CAR TERM) 'QUOTE) NIL)
                     ((CONSP (CAR TERM))
                      (CLAUSE-KEYS (CDR TERM)))
                     (T (CLAUSE-KEYS (CDR TERM))))))
       :hints (("Goal" :in-theory (enable term-keys))))
     
     (defthm open-clause-keys
       (equal (clause-keys (cons x y))
              (append (term-keys x)
                      (clause-keys y)))
       :hints (("Goal" :do-not-induct t
                :expand (clause-keys (cons x y)))
               (and stable-under-simplificationp
                    '(:expand (term-keys x)))))
     
     (encapsulate
         ()
       
       ;; --------------------------------------------------------------
       
       (defequiv+ (subsetp x y)
         :equiv   set-upper-bound-equiv
         :context set-upper-bound-ctx
         :pred    set-upper-bound-pred
         ;;:congruences ((y set-equiv-quant))
         :keywords nil
         :skip nil
         )
       
       (defequiv+ (list::memberp a x)
         :pred    memberp-upper-bound-pred
         :equiv   memberp-upper-bound-equiv
         :context memberp-upper-bound-ctx
         ;;:congruences ((x set-equiv-quant))
         :chaining-ctx set-upper-bound-ctx
         :keywords nil
         :skip nil
         )
       
       ;; --------------------------------------------------------------
       
       (defcongp+ memberp-upper-bound-equiv-cons-1
         (cons x y)
         :rhs (append maxx y)
         :cong ((x (equal maxx (memberp-upper-bound-ctx x))))
         :equiv set-upper-bound-equiv
         :skip nil
         )
       
       (defcongp+ memberp-upper-bound-equiv-cons-2
         (cons x y)
         :cong ((y (equal maxy (set-upper-bound-ctx y))))
         :equiv set-upper-bound-equiv
         :skip nil
         )
       
       (defcongp+ set-upper-bound-append
         (append x y)
         :equiv set-upper-bound-equiv
         :cong ((x (equal a (set-upper-bound-ctx x)))
                (y (equal b (set-upper-bound-ctx y))))
         :skip nil
         )
       
       ;; --------------------------------------------------------------
       
       (defthm memberp-member-upper-bound-backchaining-subset
         (implies
          (and
           (bind-contextp (a (equal max (memberp-upper-bound-ctx a))) :asymmetric t)
           (double-rewrite (subsetp max x)))
          (list::memberp a x)))
       
       (defthm memberp-set-upper-bound-backchaining
         (implies
          (and
           (bind-contextp (x (equal max (set-upper-bound-ctx x))))
           (double-rewrite (not (list::memberp a max))))
          (not (list::memberp a x))))
       
       (defthm subsetp-upper-bound-backchaining
         (implies
          (and
           (bind-contextp (x (equal max (set-upper-bound-ctx x))))
           (force (double-rewrite (subsetp max z))))
          (subsetp x z)))
       
       )
     
     (defthm term-keys-disjoin2
       (set-upper-bound-equiv (term-keys (disjoin2 x y))
                              (append (term-keys x)
                                      (term-keys y)))
       :hints (("Goal" :in-theory (enable list::memberp list::memberp-of-append)
                :expand (clause-keys (list y)))
               (and stable-under-simplificationp
                    '(:expand (:free (y) (term-keys y))))))
     
     (in-theory (disable disjoin2))
     
     (defun disjoin-1 (x list)
       (if (not (consp list)) x
         (disjoin2 x (disjoin-1 (car list) (cdr list)))))
     
     (defthm term-keys-disjoin-1
       (set-upper-bound-equiv (term-keys (disjoin-1 x clause))
                              (append (term-keys x) (clause-keys clause)))
       :hints (("Goal" :induct (disjoin-1 x clause)
                :in-theory (enable list::memberp-of-append))))
     
     (defthmd disjoin-redef
       (equal (disjoin list)
              (if (consp list)
                  (disjoin-1 (car list) (cdr list))
                *nil*)))
     
     (defthm term-keys-disjoin
       (set-upper-bound-equiv (term-keys (disjoin clause))
                              (clause-keys clause))
       :hints (("Goal" :in-theory (enable disjoin-redef)
                :do-not-induct t)))
     
     ))

  (defthm eval-clause-ignores-GENERALIZE-CLAUSE-ALIST
    (implies
     (pseudo-term-listp clause)
     (equal (gensym::eval (disjoin clause) (GENERALIZE-CLAUSE-ALIST clause A subterms))
            (gensym::eval (disjoin clause) A)))
    :hints (("Goal" :in-theory (disable LIST::DISJOINT-REMOVE-DEFINITION
                                        SUBSET-KEYS-TERM-KEYS-REDUCTION))))

  )

(defthm eval-v0-generalize-clause-processor
  (implies
   (pseudo-term-listp subterms)
   (equal (gensym::eval-list (v0 (generalize-clause-processor clause subterms)) (GENERALIZE-CLAUSE-ALIST clause A subterms))
	  (gensym::eval-list subterms a)))
  :hints (("Goal" :do-not-induct t)))

(encapsulate
 ()
 (local
  (encapsulate
      ()
    
    (defthm list-euqiv-implies-nth-equiv
      (implies
       (list-equiv x y)
       (iff (equal (nth i x)
                   (nth i y)) t)))
    
    (defthmd eval-nth-v0-generalize-clause-processor-helper
      (implies
       (pseudo-term-listp subterms)
       (equal (nth i (gensym::eval-list (v0 (generalize-clause-processor clause subterms)) (GENERALIZE-CLAUSE-ALIST clause A subterms)))
              (nth i (gensym::eval-list subterms a))))
      :hints (("Goal" :in-theory '(list-euqiv-implies-nth-equiv equal-to-list-equiv true-listp-eval-list)
               :use eval-v0-generalize-clause-processor)))
    ))

 (defthm eval-nth-v0-generalize-clause-processor
   (implies
    (and
     (pseudo-term-listp subterms)
     (< (nfix i) (len subterms)))
    (equal (gensym::eval (nth i (v0 (generalize-clause-processor clause subterms))) (GENERALIZE-CLAUSE-ALIST clause A subterms))
           (gensym::eval (nth i subterms) a)))
   :hints (("Goal" :do-not-induct t
            :in-theory (disable nth nfix eval-v0-generalize-clause-processor generalize-clause-processor GENERALIZE-CLAUSE-ALIST)
            :use eval-nth-v0-generalize-clause-processor-helper)))
 
 )


(defthm disjoint-from-disjoint-subset
  (implies
   (and
    (subsetp-equal x y)
    (bag::disjoint y z))
   (bag::disjoint x z))
  :rule-classes (:rewrite :forward-chaining))

(defthm eval-subterm-GENERALIZE-CLAUSE-ALIST
  (implies
   (and
    (pseudo-term-listp subterms)
    (pseudo-termp term)
    (list::subsetp (term-keys term) (append (clause-keys subterms) (clause-keys clause))))
   (equal (gensym::eval term (GENERALIZE-CLAUSE-ALIST clause A subterms))
	  (gensym::eval term a)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable LIST::SUBSETP-APPEND-2))))

(defthm eval-list-clauses-GENERALIZE-CLAUSE-ALIST
  (implies
   (and
    (pseudo-term-listp subterms)
    (pseudo-term-listp z)
    (list::subsetp (clause-keys z) (append (clause-keys subterms) (clause-keys clause))))
   (equal (gensym::eval-list z (GENERALIZE-CLAUSE-ALIST clause A subterms))
	  (gensym::eval-list z a)))
  :hints (("Goal" :do-not-induct t
           :in-theory (disable LIST::SUBSETP-APPEND-2))))

(defthm generalize-clause-processor-reduction
  (implies
   (and
    (pseudo-term-listp clause)
    (pseudo-term-listp subterms))
   (equal (gensym::eval-list (v1 (generalize-clause-processor clause subterms))
			     (generalize-clause-alist clause a subterms))
	  (gensym::eval-list clause a)))
  :hints (("Goal" :do-not-induct t)))

(defthm generalize-clause-alist-reduction
  (implies
   (and
    (pseudo-term-listp clause)
    (pseudo-term-listp subterms))
   (equal (gensym::eval-list clause (generalize-clause-alist clause a subterms))
	  (gensym::eval-list clause a)))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable generalize-clause-processor generalize-clause-alist))

(in-theory (enable GENSYM::EVAL-constraint-8))
(in-theory (enable GENSYM::EVAL-constraint-9))

(include-book "coi/util/clause-processor" :dir :system)

;;(conjoin-disjoin gensym::eval gensym::eval-list)
(clause-eval-facts gensym::eval gensym::eval-list)

(defthmd disjoin-congruence
  (implies
   (equal (gensym::eval-list args1 a1)
	  (gensym::eval-list args2 a2))
   (iff (iff (gensym::eval (disjoin args1) a1)
	     (gensym::eval (disjoin args2) a2)) t))
  :hints (("Goal" :expand ((disjoin args2)
			   (disjoin args1))
	   :induct (list::len-len-induction args1 args2))))

;;
;; This may be generally useful .. push back into clause-processor?
;;

(defthm disjoin-implication
  (implies
   (and
    (equal (gensym::eval-list args1 a1)
	   (gensym::eval-list args2 a2))
    (gensym::eval (disjoin args1) a1))
   (gensym::eval (disjoin args2) a2))
  :hints (("Goal" :use disjoin-congruence)))

#|
(defthm disjoin2-congruence-1
  (implies
   (and
    (gensym::eval (disjoin2 w x) a1)
    (iff (gensym::eval w a1) (gensym::eval y a2))
    (iff (gensym::eval x a1) (gensym::eval z a2)))
   (gensym::eval (disjoin2 y z) a2)))

(defthm disjoin2-congruence-2
  (implies
   (and
    (not (gensym::eval (disjoin2 w x) a1))
    (iff (gensym::eval w a1) (gensym::eval y a2))
    (iff (gensym::eval x a1) (gensym::eval z a2)))
   (not (gensym::eval (disjoin2 y z) a2))))

(local (in-theory (disable disjoin2)))

(defthm disjoin2-ite-reduction
  (implies
   (and
    (consp ite)
    (equal (car ite) 'if))
   (iff (gensym::eval (disjoin2 ite x) a)
	(if (gensym::eval (cadr ite) a)
	    (gensym::eval (disjoin2 (caddr ite) x) a)
	  (gensym::eval (disjoin2 (cadddr ite) x) a))))
  :hints (("Goal" :in-theory (enable disjoin2))))

(in-theory (disable conjoin2))

(defthm eval-conjoin2
  (iff (gensym::eval (conjoin2 x y) a)
       (and (gensym::eval x a)
	    (gensym::eval y a)))
  :hints (("Goal" :in-theory (enable conjoin2))))

(defthm eval-disjoin2
  (iff (gensym::eval (disjoin2 x y) a)
       (or (gensym::eval x a)
	   (gensym::eval y a)))
  :hints (("Goal" :in-theory (enable disjoin2))))
|#

(defun generalize-termp (term)
  (declare (type t term))
  (and (pseudo-termp term)
       (consp term)
       (consp (cdr term))
       (null (cddr term))
       (equal (car term) 'gensym::generalize)))

(local
(defthm consp-implies-memberp-car
  (implies
   (consp list)
   (list::memberp (car list) list))
  :rule-classes (:forward-chaining)))

(defun type-pred (type-p arg)
  (declare (type t type-p))
  `(,type-p ,arg))

(defun print-generalization-rec (terms vars)
  (declare (type t terms vars))
  (if (and (consp terms) (consp vars))
      (let ((zed (cw "Generalizing ~p0 to ~p1~%" (car terms) (car vars))))
        (declare (ignore zed))
        (print-generalization-rec (cdr terms) (cdr vars)))
    nil))

(defun print-generalization (terms vars)
  (declare (type t terms vars)
           (irrelevant terms vars))
  (let ((zed (cw "~%")))
    (declare (ignore zed))
    (let ((zed (print-generalization-rec terms vars)))
      (declare (ignore zed))
      (cw "~%"))))

(defun generalize-clause-processor-wrapper (clause hint)
  (declare (type t clause hint))
  (if (consp hint)
      (let ((subterm (car hint))
	    (type-p  (cdr hint)))
	(met ((var new) (generalize-clause-processor clause (list subterm)))
          (if (and (consp var) (or (not type-p) (fn-symbolp type-p)) (generalize-termp subterm))
              (let ((zed (print-generalization (list subterm) var)))
                (declare (ignore zed))
                (if (not type-p) (list new)
                  (let ((subterm (cadr subterm)))
                    (list
                     (cons `(if ,(type-pred type-p subterm) ,*t* ,*nil*) new)
                     (cons `(if ,(type-pred type-p (nth 0 var)) ,*nil* ,*t*) new)
                     ))))
            (list clause))))
    (list clause)))

(local (in-theory (disable nth)))

(defun generalize-clause-alist-wrapper (clause a hint)
  (declare (type t clause hint))
  (if (consp hint)
      (let ((subterm (car hint))
	    (type-p  (cdr hint)))
	(met ((var new) (generalize-clause-processor clause (list subterm)))
	     (declare (ignore new))
	     (if (and (consp var) (or (not type-p) (fn-symbolp type-p)) (generalize-termp subterm))
		 (generalize-clause-alist clause a (list subterm))
	       a)))
    a))

(defthm term-keys-generalize-termp
  (implies
   (generalize-termp subterm)
   (equal (term-keys subterm)
	  (clause-keys (cdr subterm))))
  :hints (("Goal" :in-theory (enable CLAUSE-KEYS term-keys))))

(defthm open-clause-keys
  (implies
   (and
    (syntaxp (not (symbolp terms)))
    (consp terms))
   (equal (clause-keys terms)
	  (append (term-keys (car terms))
		  (clause-keys (cdr terms)))))
  :hints (("Goal" :in-theory (enable term-keys clause-keys))))

(defthm clause-keys-null
  (implies
   (not (consp terms))
   (equal (clause-keys terms) nil))
  :hints (("Goal" :in-theory (enable term-keys clause-keys))))

(defthm type-pred-congruence
  (implies
   (and
    (fn-symbolp type-p)
    (pseudo-termp c1)
    (pseudo-termp c2)
    (equal (gensym::eval c1 a1)
           (gensym::eval c2 a2)))
   (iff (equal (GENSYM::EVAL (type-pred type-p c1) a1)
               (gensym::eval (type-pred type-p c2) a2)) t))
  :hints (("Goal" :in-theory (enable fn-symbolp GENSYM::EVAL-CONSTRAINT-0))))

(defthm type-pred-congruence-2
  (implies
   (and
    (GENSYM::EVAL (type-pred type-p c1) a1)
    (fn-symbolp type-p)
    (pseudo-termp c1)
    (equal (gensym::eval c1 a1)
           (gensym::eval c2 a2))
    (pseudo-termp c2))
   (gensym::eval (type-pred type-p c2) a2))
  :rule-classes (:forward-chaining)
  :hints (("Goal" :use type-pred-congruence)))

(defthm ungeneralize-type-pred
  (implies
   (and
    (fn-symbolp type-p)
    (generalize-termp x))
   (equal (gensym::eval (type-pred type-p x) a)
          (gensym::eval (type-pred type-p (cadr x)) a)))
  :hints (("Goal" :in-theory (enable fn-symbolp  GENSYM::EVAL-CONSTRAINT-0))))

(defthm generalize-termp-implies-pseudo-termp
  (implies
   (generalize-termp x)
   (and (pseudo-termp x)
        (pseudo-termp (cadr x))))
  :rule-classes (:rewrite :forward-chaining))

(defthm clause-keys-generaliz-termp
  (implies
   (generalize-termp x)
   (equal (clause-keys (list x))
          (term-keys (cadr x)))))

(defthm non-nil-symbol-listp-is-pseudo-term-listp
  (implies
   (non-nil-symbol-listp list)
   (pseudo-term-listp list))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :expand ((pseudo-termp (car list))
                           (pseudo-term-listp list)))))

(defthm pseudo-termp-member-pseudo-term-listp
  (implies
   (and
    (pseudo-term-listp list)
    (list::memberp a list))
   (pseudo-termp a))
  :hints (("Goal" :in-theory (enable list::memberp)))
  :rule-classes (:rewrite :forward-chaining))

(defthm pseudo-termp-nth
  (implies
   (and
    (pseudo-term-listp list)
    (< (nfix i) (len list)))
   (pseudo-termp (nth i list)))
  :hints (("Goal" :in-theory (enable nth))))

(defthm unlist-type-pred
  (implies
   (fn-symbolp type-p)
   (equal (gensym::eval (list type-p x) a)
          (gensym::eval (type-pred type-p x) a))))

(in-theory (disable type-pred))

(defthm type-pred-rule-1
  (implies
   (and
    (pseudo-termp gensubterm)
    (pseudo-term-listp genlist)
    (fn-symbolp type-p)
    (list::subsetp (term-keys gensubterm) (append (clause-keys genlist) (clause-keys cl))))
   (equal (GENSYM::EVAL (TYPE-PRED type-p gensubterm) (GENERALIZE-CLAUSE-ALIST CL A genlist))
          (gensym::eval (TYPE-PRED type-p gensubterm) A))))

(in-theory (disable LIST::LEN-EQUAL-0-REWRITE))

(defthm type-pred-rule-2
  (implies
   (and (pseudo-termp genterm) (pseudo-term-listp cl) (fn-symbolp type-p))
   (equal (GENSYM::EVAL (TYPE-PRED type-p (NTH 0 (VAL 0 (GENERALIZE-CLAUSE-PROCESSOR CL (LIST genterm)))))
                        (GENERALIZE-CLAUSE-ALIST CL A (LIST genterm)))
          (gensym::eval (type-pred type-p genterm) a))))

(in-theory (disable generalize-termp))

(defthm generalize-clause-processor-works
  (implies
   (and
    (pseudo-term-listp cl)
    (alistp a)
    (gensym::eval (conjoin-clauses (generalize-clause-processor-wrapper cl hint))
	      (generalize-clause-alist-wrapper cl a hint)))
   (gensym::eval (disjoin cl) a))
  :hints (("Goal" :do-not-induct t
	   :do-not '(eliminate-destructors generalize)
	   :in-theory (e/d nil
			   (open-disjoin open-conjoin disjoin LIST::SUBSETP-APPEND-2))
           :use ((:instance disjoin-implication
                            (args1 (val 1 (generalize-clause-processor cl (list (car hint)))))
                            (a1    (generalize-clause-alist cl a (list (car hint))))
                            (args2 cl)
                            (a2    a)))))
  :rule-classes :clause-processor)

(defun get-generalization-patterns (world)
  (declare (xargs :guard (and (plist-worldp world)
                              (alistp (table-alist 'generalization world)))))
  (cdr (assoc-eq :patterns (table-alist 'generalization world))))

(defun generalize-pattern-hint (patterns clause)
  (declare (xargs :mode :program))
  (let ((hint (pattern-match-args 'gensym::generalize patterns clause)))
    (and hint
	 (let ((hints `(:clause-processor (generalize-clause-processor-wrapper clause ',hint))))
	   `(:computed-hint-replacement
	     ((generalize-clause-hint id clause world))
	     ,@hints)))))

(defun generalize-clause-hint (id clause world)
  (declare (xargs :mode :program)
	   (ignore id))
  (or (generalize-pattern-hint (get-generalization-patterns world) clause)
      nil))

(add-default-hints!
 '((generalize-clause-hint id clause world)))

(defmacro add-generalization-pattern (pattern &key (type 'nil))
  `(table generalization :patterns
	  (cons ',(cons `(,pattern) type)
		(cdr (assoc :patterns (table-alist 'generalization world))))))

;; Can we add a fixing function to the mix?  Create a new symbol and apply the
;; fixing function?
;;
;;(add-generalization-pattern (foo x y z) :type fix)

(in-theory (disable gensym::generalize))

(encapsulate
 ()
(local
(encapsulate
 ()

 (defun foo (x) (nfix x))
 (defun goo (x)
   (declare (ignore x))
   t)

 (defthm open-goo
   (implies
    (and
     (syntaxp (symbolp x))
     (integerp x))
    (goo x)))

 (in-theory (disable goo (:type-prescription goo)))

 (defthm foo-type
   (implies
    (integerp x)
    (and (integerp (foo x))
         (<= 0 (foo x)))))

 (in-theory (disable (tau-system) foo (:type-prescription foo)))

 (add-generalization-pattern (foo x) :type (lambda (x) (if (integerp x) (if (not (< x (quote 0))) (quote t) (quote nil)) (quote nil))))

 ;; This works only because of the generalization of (foo x)
 (defthm pred-foo
   (implies
    (integerp x)
    (goo (gensym::generalize (foo x)))))

 )))

#+joe
(defun map-type (type-p list)
  (declare (type t list))
  (if (atom list) *t*
    (let ((entry (car list)))
      `(if (,type-p ,entry) ,(map-type type-p (cdr list)) ,*nil*))))

(defun map-types (types list)
  (declare (type t list))
  (if (not (and (consp types) (consp list))) *t*
    (let ((entry  (car list))
          (type-p (car types)))
      `(if (,type-p ,entry) ,(map-types (cdr types) (cdr list)) ,*nil*))))

(defun fn-symbol-listp (list)
  (declare (type t list))
  (if (not (consp list)) t
    (and (fn-symbolp (car list))
         (fn-symbol-listp (cdr list)))))

(defun generalize-list-clause-processor-wrapper (clause hint)
  (declare (type t clause hint))
  (if (and (alistp hint) (consp hint))
      (let ((subterms (strip-cars hint))
	    (types    (strip-cdrs hint)))
        (if (and (pseudo-term-listp subterms) (fn-symbol-listp types))
            (met ((vars new) (generalize-clause-processor clause subterms))
              (let ((zed (print-generalization subterms vars)))
                (declare (ignore zed))
                (list
                 (cons `(if ,(map-types types subterms) ,*t* ,*nil*) clause)
                 (cons `(if ,(map-types types vars) ,*nil* ,*t*) new)
                 )))
          (list clause)))
    (list clause)))

(defun generalize-list-clause-alist-wrapper (clause a hint)
  (declare (type t clause hint))
  (if (and (alistp hint) (consp hint))
      (let ((subterms (strip-cars hint))
	    (types    (strip-cdrs hint)))
        (if (and (pseudo-term-listp  subterms) (fn-symbol-listp types))
            (generalize-clause-alist clause a subterms)
          a))
    a))

(defthm not-eval-list-implies-not-list
  (implies
   (not (gensym::eval-list c a))
   (not (consp c)))
  :rule-classes (:forward-chaining))

(local
 (defun len-len-len-induction (a x y)
   (if (and (consp a) (consp x) (consp y))
       (len-len-len-induction (cdr a) (cdr x) (cdr y))
     (list a x y))))

(defthm map-types-congruence-1
  (implies
   (and
    (fn-symbol-listp types)
    (pseudo-term-listp c1)
    (pseudo-term-listp c2)
    (equal (gensym::eval-list c1 a1)
           (gensym::eval-list c2 a2)))
   (iff (equal (GENSYM::EVAL (MAP-TYPEs types c1) a1)
               (gensym::eval (map-types types c2) a2)) t))
  :hints (("Goal" :induct (len-len-len-induction types c1 c2)
           :in-theory (enable GENSYM::EVAL-CONSTRAINT-0))))

(defthm map-types-rule-1
  (implies
   (and
    (fn-symbol-listp types)
    (pseudo-term-listp cl)
    (pseudo-term-listp clauses))
   (equal (GENSYM::EVAL (MAP-TYPEs types (VAL 0 (GENERALIZE-CLAUSE-PROCESSOR CL clauses)))
                        (GENERALIZE-CLAUSE-ALIST CL A clauses))
          (gensym::eval (map-types types clauses) a)))
  :hints (("Goal" :do-not-induct t)))

(defthm map-types-rule-2
  (implies
   (and
    (fn-symbol-listp types)
    (pseudo-term-listp cl)
    (pseudo-term-listp clauses))
   (equal (GENSYM::EVAL (MAP-TYPEs types clauses) (GENERALIZE-CLAUSE-ALIST CL A clauses))
          (gensym::eval (map-types types clauses) a)))
  :hints (("Goal" :do-not-induct t)))

(in-theory (disable open-disjoin open-conjoin))

(defthm generalize-list-clause-processor-works
  (implies
   (and
    (pseudo-term-listp cl)
    (alistp a)
    (gensym::eval (conjoin-clauses (generalize-list-clause-processor-wrapper cl hint))
	          (generalize-list-clause-alist-wrapper cl a hint)))
   (gensym::eval (disjoin cl) a))
  :hints (("Goal" :do-not-induct t
           :use (:instance disjoin-implication
                           (args1 (val 1 (generalize-clause-processor cl (strip-cars hint))))
                           (a1    (generalize-clause-alist cl a (strip-cars hint)))
                           (args2 cl)
                           (a2    a))))
  :rule-classes :clause-processor)

;; (defun generalize-rfix-getval-hint (clause)
;;   (declare (xargs :mode :program))
;;   (let ((hint (and (no-ev-args clause) (find-rfix-getval-args clause))))
;;     (and hint `(:clause-processor (generalize-list-clause-processor-wrapper clause '(,hint . rationalp))))))

;; (set-default-hints! '((generalize-rfix-getval-hint clause)))

(in-package "ACL2")

(include-book "qi")

; Some general lemmas that should be relocated...

(defthm no-duplicatesp-subsetp
  (implies (and (subsetp l1 l2)
                (no-duplicatesp l1)
                (equal (car l1) (car l2)))
           (subsetp (cdr l1) (cdr l2))))

(defthm member-delete
  (implies (and (member v1 l)
                (not (eql v1 v2)))
           (member v1 (delete-hql v2 l))))

; The issue for the next two events is the use of DELETE-HQL.

(defthm subset-eq-delete
  (implies (and (subsetp l1 l2)
                (not (member v l1)))
           (subsetp l1 (delete-hql v l2))))

(defthm delete-subsetp
  (implies (and (subsetp l1 l2)
                (no-duplicatesp l1)
                (member v l1))
           (subsetp (delete-hql v l1)
                    (delete-hql v l2))))

; Some definitions and lemmas dealing with the arguments given to
; EVAL-BDD.

(defun get-val (v vals vars)
  (declare (xargs :guard (and (boolean-listp vals)
                              (eqlable-listp vars))))
  (if (atom vars)
      nil
    (if (eql v (car vars))
        (car vals)
      (get-val v (cdr vals) (cdr vars)))))

(defun delete-val (vals v vars)
  (declare (xargs :guard (and (boolean-listp vals)
                              (eqlable-listp vars))
                  :verify-guards nil))
  (if (atom vars)
      vals
    (if (eql v (car vars))
        (cdr vals)
      (cons (car vals)
            (delete-val (cdr vals) v (cdr vars))))))

(defthm boolean-listp-delete-val
  (implies (boolean-listp vals)
           (boolean-listp (delete-val vals v vars))))

(verify-guards delete-val)

(defun vals-reorder (vals vars nvars)
  (declare (xargs :guard (and (boolean-listp vals)
                              (eqlable-listp vars)
                              (eqlable-listp nvars))))
  (if (atom nvars)
      vals
    (cons (get-val (car nvars) vals vars)
          (vals-reorder (delete-val vals (car nvars) vars)
                        (delete-hql (car nvars) vars) (cdr nvars)))))

; The proofs that Q-RESTRICT and Q-REORDER are OK.  This provides a
; guide to proving the correctness of UBDD variable re-ordering
; heuristics.

(defun q-restrict-shrink-induct (x vals v vars)
  (declare (xargs :guard (and (boolean-listp vals)
                              (eqlable-listp vars))))
  (if (atom x)
      (list x vals v vars)
    (if (eql v (car vars))
        (if (car vals)
            (q-restrict-shrink-induct (car x) (cdr vals) v vars)
          (q-restrict-shrink-induct (cdr x) (cdr vals) v vars))
      (if (car vals)
          (q-restrict-shrink-induct (car x) (cdr vals) v (cdr vars))
        (q-restrict-shrink-induct (cdr x) (cdr vals) v (cdr vars))))))

(defthm q-restrict-shrink-correct
  (implies  (and (iff (get-val v vals vars) n)
                 (member v vars))
            (equal (eval-bdd (q-restrict-shrink x n v vars)
                             (delete-val vals v vars))
                   (eval-bdd x vals)))
  :hints (("Goal"
           :induct (q-restrict-shrink-induct x vals v vars))))

(defun q-reorder-induct (x vals vars nvars)
  (declare (xargs :measure (acl2-count nvars)
                  :guard (and (boolean-listp vals)
                              (eqlable-listp vars)
                              (eqlable-listp nvars))))
  (if (or (atom x)
          (atom nvars))
      nil
    (if (eql (car nvars) (car vars))
        (if (car vals)
            (q-reorder-induct
             (car x) (cdr vals) (cdr vars) (cdr nvars))
          (q-reorder-induct
           (cdr x) (cdr vals) (cdr vars) (cdr nvars)))
      (let ((val (get-val (car nvars) vals vars)))
        (if val
            (q-reorder-induct (q-restrict-shrink x t (car nvars) vars)
                              (delete-val vals (car nvars) vars)
                              (delete-hql (car nvars) vars)
                              (cdr nvars))
          (q-reorder-induct (q-restrict-shrink x nil (car nvars) vars)
                            (delete-val vals (car nvars) vars)
                            (delete-hql (car nvars) vars)
                            (cdr nvars)))))))

(defthm q-reorder-correct
  (implies (and (no-duplicatesp nvars)
                (subsetp nvars vars))
           (equal (eval-bdd (q-reorder x vars nvars)
                            (vals-reorder vals vars nvars))
                  (eval-bdd x vals)))
  :hints (("Goal" :induct (q-reorder-induct x vals vars nvars))))


; Funny, but critical fact to the theorem prover.

(defthm blp-implies-t
  (implies (and (booleanp x) x)
           (equal (equal x t) t)))


; We prove the correctness of the various UBDD manipulation functions
; in such a manner that their correctness is always in terms of the
; correctness of Q-ITE; that is, we convert every operation into Q-ITE
; operations that can then be rewritten into IF expressions.  We treat
; Q-NOT and Q-NOT specially, we show that these functions a simple
; NOT.  We always prove two main lemmas about each UBDD function: that
; it produces a NORMP, and that it is correct with respect to some
; Boolean function.

; We start with Q-NOT and Q-NOT-ITE.

(encapsulate
 ()
 (local
  (defthm consp-q-not
    (implies (and (normp x)
                  (consp x))
             (and (consp (q-not x))
                  (normp (q-not x))))))

 (local
  (defthm atom-q-not
    (implies (and (normp x)
                  (atom x))
             (normp (q-not x)))))

 (defthm normp-q-not
   (implies (normp x)
            (normp (q-not x)))
   :hints (("Goal" :in-theory (e/d (booleanp) (q-not))))))

(defthm q-not-correct
  (implies (normp x)
           (equal (eval-bdd (q-not x) vals)
                  (not (eval-bdd x vals)))))

; Now we consider Q-ITE

(defthm normp-q-ite
  (implies (and (normp x)
                (normp y)
                (normp z))
           (normp (q-ite x y z)))
  :hints
  (("Goal"
    :induct (q-ite x y z)
    :in-theory (disable q-not))))

(defun q-ite-induct (x y z vals)
  (declare (xargs :measure (acl2-count x)
                  :guard (boolean-listp vals)))
  (cond ((null x) (eval-bdd z vals))
        ((atom x) (eval-bdd y vals))
        (t (let ((y (if (equal x y) t y))
                 (z (if (equal x z) nil z)))
             (cond ((equal y z) (eval-bdd y vals))
                   ((and (eq y t) (eq z nil) (eval-bdd x vals)))
                   ((and (eq y nil) (eq z t))
                    (eval-bdd (q-not x) vals))
                   ((atom vals)
                    (q-ite-induct (cdr x) (qcdr y) (qcdr z) nil))
                   ((car vals)
                    (q-ite-induct
                     (car x) (qcar y) (qcar z) (cdr vals)))
                   (t (q-ite-induct (cdr x) (qcdr y) (qcdr z)
                                    (cdr vals))))))))

; (defthm q-ite-correct
;   (implies (and (normp x)
;                 (normp y)
;                 (normp z))
;            (equal (eval-bdd (q-ite x y z) vals)
;                   (if (eval-bdd x vals)
;                       (eval-bdd y vals)
;                     (eval-bdd z vals))))
;   :hints (("Goal"
;            :induct (q-ite-induct x y z vals)
;            :in-theory (disable q-not q-not-equiv-q-not-ite)
;            )))


; Rough time: 121.07 seconds (prove: 103.72, print: 17.35, other:
; 0.00)

; Robert Krug looked at this proof, and produced the following set of
; improvements.

; A couple of expand hints sped things up a good bit.  I had examined
; the original proof, and decided that the first set of case-splits
; looked like the correct thing, but didn't like the two rounds of
; destructor elimination before the next set of big case-splits.  I
; wanted to force this second set to occur earlier in the flow, and
; saw that these terms terms appeared regularly, so I suggested to
; ACL2 that it be a little more eager to expand them.

; (defthm q-ite-correct
;   (implies (and (normp x)
;                 (normp y)
;                 (normp z))
;            (equal (eval-bdd (q-ite x y z) vals)
;                   (if (eval-bdd x vals)
;                       (eval-bdd y vals)
;                     (eval-bdd z vals))))
;   :hints (("Goal"
;            :induct (q-ite-induct x y z vals)
; 	   :expand ((EVAL-BDD (Q-ITE X Y Z) VALS)
; 		    (Q-ITE X Y Z))
;            :in-theory (disable q-not q-not-equiv-q-not-ite)
;            )))

; Time:  20.60 seconds (prove: 17.22, print: 3.38, other: 0.00)


; A few more expand hints got me even further:

; (defthm q-ite-correct
;   (implies (and (normp x)
;                 (normp y)
;                 (normp z))
;            (equal (eval-bdd (q-ite x y z) vals)
;                   (if (eval-bdd x vals)
;                       (eval-bdd y vals)
;                     (eval-bdd z vals))))
;   :hints (("Goal"
;            :induct (q-ite-induct x y z vals)
; 	   :expand ((EVAL-BDD (Q-ITE X Y Z) VALS)
; 		    (Q-ITE X Y Z)
; 		    (Q-ITE X Y T)
; 		    (Q-ITE X Y NIL)
; 		    (Q-ITE X T Z)
; 		    (Q-ITE X NIL Z)
; 		    (Q-ITE X X Z)
; 		    (Q-ITE X Y X))
;            :in-theory (disable q-not q-not-equiv-q-not-ite)
;            )))

; Time:  13.76 seconds (prove: 12.34, print: 1.42, other: 0.00)


; I then got greedy, and disabled eval-bdd and q-ite, and told ACL2
; just which instances to expand:

(defthm q-ite-correct
  (implies (and (normp x)
                (normp y)
                (normp z))
           (equal (eval-bdd (q-ite x y z) vals)
                  (if (eval-bdd x vals)
                      (eval-bdd y vals)
                    (eval-bdd z vals))))
  :hints (("Goal"
	   :do-not '(eliminate-destructors generalize fertilize)
           :induct (q-ite-induct x y z vals)
	   :expand ((EVAL-BDD (Q-ITE X Y Z) VALS)
		    (:free (a) (EVAL-BDD X a))
		    (:free (a) (EVAL-BDD Y a))
		    (:free (a) (EVAL-BDD Z a))
		    (:free (a) (EVAL-BDD T a))
		    (:free (a) (EVAL-BDD NIL a))
		    (:free (a b c) (EVAL-BDD (CONS a b) c))
		    (Q-ITE X Y Z)
		    (Q-ITE X Y T)
		    (Q-ITE X Y NIL)
		    (Q-ITE X T Z)
		    (Q-ITE X NIL Z)
		    (Q-ITE X X Z)
		    (Q-ITE X Y X)
		    (Q-ITE X Y Y)
		    (Q-ITE X NIL X)
		    (Q-ITE NIL Y Z)
		    (Q-ITE T Y Z)
		    (Q-ITE X X X)
		    (Q-ITE X X T)
		    (Q-ITE X X NIL)
		    (Q-ITE X T T)
		    (Q-ITE X T X)
		    (Q-ITE X T NIL)
		    (Q-ITE X NIL T))
           :in-theory (disable q-not eval-bdd q-ite)
           )))

; Time:  5.97 seconds (prove: 4.41, print: 1.56, other: 0.00)


; This concludes all that we really need to know about our UBDD
; functions.  We now consider other UBDD manipulation functions.



(encapsulate
 ()
 (local
    (defthm q-not-equiv-q-not-ite
    (implies (normp x)
             (equal (q-not-ite x)
                    (q-not x))))
    )

 (defthm normp-q-not-ite
   (implies (normp x)
            (normp (q-not-ite x))))

; Question: would it be better to make the RHS (if (eval-bdd x vals) t
; nil) ?

 (defthm q-not-ite-correct
   (implies (normp x)
            (equal (eval-bdd (q-not-ite x) vals)
                   (not (eval-bdd x vals))))
   :hints (("Goal" :in-theory (e/d () (q-not))))))


; Q-AND and Q-AND-ITE

(defthm normp-q-and
  (implies (and (normp x)
                (normp y))
           (normp (q-and x y))))

(defthm normp-q-and-ite
  (implies (and (normp x)
                (normp y))
           (normp (q-and-ite x y))))

(defthm q-and-correct
    (implies (and (normp x)
                  (normp y))
             (equal (eval-bdd (q-and x y) vals)
                    (and (eval-bdd x vals)
                         (eval-bdd y vals)))))

(defthm q-and-equiv-q-and-ite
  (implies (and (normp x)
                (normp y))
           (equal (q-and-ite x y)
                  (q-and x y))))

(defthm q-and-args-identical-is-arg
  (implies (normp x)
           (equal (q-and x x) x)))


; Q-OR and Q-OR-ITE

(defthm normp-q-or
  (implies (and (normp x)
                (normp y))
           (normp (q-or x y))))

(defthm normp-q-or-ite
  (implies (and (normp x)
                (normp y))
           (normp (q-or-ite x y))))

(defthm q-or-correct
  (implies (and (normp x)
                (normp y))
           (equal (eval-bdd (q-or x y) vals)
                  (or (eval-bdd x vals)
                      (eval-bdd y vals))))
  :hints (("goal" :in-theory
           (enable q-or eval-bdd normp))))

(defthm q-or-equiv-q-or-ite
  (implies (and (normp x)
                (normp y))
           (equal (q-or-ite x y)
                  (q-or x y))))

(defthm q-or-args-identical-is-arg
  (implies (normp x)
           (equal (q-or x x) x)))


; Q-XOR and Q-XOR-ITE

(defthm normp-q-xor
  (implies (and (normp x)
                (normp y))
           (normp (q-xor x y)))
  :hints (("Goal" :in-theory (disable q-not))))

(defthm normp-q-xor-ite
  (implies (and (normp x)
                (normp y))
           (normp (q-xor-ite x y))))

(defthm q-xor-correct
  (implies (and (normp x)
                (normp y))
           (equal (eval-bdd (q-xor x y) vals)
                  (xor (eval-bdd x vals)
                       (eval-bdd y vals))))
  :hints (("Goal" :in-theory
           (enable q-xor eval-bdd normp))))

; Note:  Proved Q-XOR-ITE correct directly; it is difficult to prove
; that Q-XOR-ITE is equal to Q-XOR.

(defthm q-xor-ite-correct
  (implies (and (normp x)
                (normp y)
                (boolean-listp vals))
           (equal (eval-bdd (q-xor-ite x y) vals)
                  (xor (eval-bdd x vals)
                       (eval-bdd y vals))))
  :hints (("Goal" :in-theory (disable q-ite q-not))))

(defthm q-xor-ite-args-identical-is-arg
  (implies (normp x)
           (equal (q-xor-ite x x) nil)))

(defthm q-xor-args-identical-is-arg
  (implies (normp x)
           (equal (q-xor x x) nil)))


; Shut off Q-functions.

(in-theory (disable q-ite))
(in-theory (disable q-not))
(in-theory (disable q-and))
(in-theory (disable q-or))
(in-theory (disable q-xor))

(defthm q-and-ite-is-and
  (implies (and (normp x)
                (normp y))
           (equal (eval-bdd (q-and-ite x y) vals)
                  (and (eval-bdd x vals)
                       (eval-bdd y vals)))))

(defthm q-or-ite-is-or
  (implies (and (normp x)
                (normp y))
           (equal (eval-bdd (q-or-ite x y) vals)
                  (or (eval-bdd x vals)
                      (eval-bdd y vals)))))

(in-theory (disable q-and-ite))
(in-theory (disable q-or-ite))
(in-theory (disable q-xor-ite))


; Below here we deal with human readable terms...

(defun sym-val (term vars vals)
  (declare (xargs :guard (and (eqlable-listp vars)
                              (boolean-listp vals))))
  (if (endp vars) nil
    (if (eql term (car vars))
        (car vals)
      (sym-val term (cdr vars) (cdr vals)))))

(defun term-eval (term vars vals)

 ":Doc-section Hons-and-Memoization

  Semantics for IF-expressions.~/
  (TERM vars vals) is the meaning of the TO-IF expression TERM with
  respect to the bindings of the variables in the list VARS to the
  Booleans in the list VALS.~/~/"

  (declare (xargs :guard (and (qnorm1-guard term)
                              (eqlable-listp vars)
                              (boolean-listp vals))))
  (cond ((eq term t) t)
        ((eq term nil) nil)
        ((eqlablep term)
         (sym-val term vars vals))
        (t (let ((fn (car term))
                 (args (cdr term)))
             (case fn
               (if (if (term-eval (car args) vars vals)
                       (term-eval (cadr args) vars vals)
                     (term-eval (caddr args) vars vals)))
               (quote (eval-bdd (car args) vals))
               (t nil))))))

(defun term-all-p (term vars)
  (declare (xargs :guard (and (qnorm1-guard term)
                              (eqlable-listp vars))))
  (if (atom term)
      (or (booleanp term)
          (member term vars))
    (let ((fn (car term))
          (args (cdr term)))
      (if (eq fn 'if)
          (and (term-all-p (car args) vars)
               (term-all-p (cadr args) vars)
               (term-all-p (caddr args) vars))
        t))))

(defthm normp-qnorm1
  (implies (and (qnorm1-guard term)
                (term-all-p term vars))
           (normp (qnorm1 term vars))))


; ++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

(defthm fold-constants-in-plus
  (implies (and (syntaxp (quotep x))
                (syntaxp (quotep y)))
           (equal (+ x y z)
                  (+ (+ x y) z))))

(defthm qvar-n-+1
  (implies (and (integerp n)
                (<= 0 n))
           (equal (qvar-n (+ 1 n))
                  (cons (qvar-n n)
                        (qvar-n n))))
  :hints (("Goal" :expand (qvar-n (+ 1 n)))))

(defthm eval-bdd-qvar-n+1-lemma
  (implies (and (integerp n)
                (<= 0 n))
           (equal (eval-bdd (qvar-n (+ 1 n)) vals)
                  (eval-bdd (qvar-n n) (cdr vals)))))

(defthm sym-val-nil
  (implies (and (not (consp term))
                (not (equal term t))
                ter)
           (equal (sym-val term vars nil)
                  nil)))

(in-theory (enable qvar-n))

(defthm eval-qvar-n
  (equal (eval-bdd (qvar-n i) nil)
         nil))

(defthm <loc
  (implies (member term vars)
           (<= 0 (locn term vars))))

(defthm eval-bdd-qvar-n
  (implies (and (eqlablep term)
                (not (equal term t))
                (not (equal term nil))
                (boolean-listp vals)
                (member term vars))
           (equal (eval-bdd (qvar-n (locn term vars)) vals)
                  (sym-val term vars vals))))

(defthm not-mem
  (implies (not (member term vars))
           (equal (locn term vars)
                  (len vars))))

(defthm eval-bdd-var-to-tree
  (implies (and (eqlablep term)
                (not (equal term t))
                (not (equal term nil))
                (boolean-listp vals)
                (member term vars))
           (equal (eval-bdd (var-to-tree term vars) vals)
                  (sym-val term vars vals)))
  :hints (("Goal"
           :expand (var-to-tree term vars)
           :do-not-induct t)))

(defthm qnorm-correct
  (implies (and (qnorm1-guard term)
                (term-all-p term vars)
                (boolean-listp vals))
           (equal (eval-bdd (qnorm1 term vars) vals)
                  (term-eval term vars vals))))

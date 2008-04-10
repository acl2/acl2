(in-package "ACL2")

(include-book "qi")

(defun get-val (v vals vars)
  (declare (xargs :guard (and (boolean-listp vals)
                              (symbol-listp vars))))
  (if (atom vars)
      nil
    (if (eq v (car vars))
        (car vals)
      (get-val v (cdr vals) (cdr vars)))))

(defun delete-val (vals v vars)
  (declare (xargs :guard (and (boolean-listp vals)
                              (symbol-listp vars))
                  :verify-guards nil))
  (if (atom vars)
      vals
    (if (eq v (car vars))
        (cdr vals)
      (cons (car vals)
            (delete-val (cdr vals) v (cdr vars))))))

(defthm boolean-listp-delete-val
  (implies (boolean-listp vals)
           (boolean-listp (delete-val vals v vars))))

(verify-guards delete-val)

(defun vals-reorder (vals vars nvars)
  (declare (xargs :guard (and (boolean-listp vals)
                              (symbol-listp vars)
                              (symbol-listp nvars))))
  (if (atom nvars)
      vals
    (cons (get-val (car nvars) vals vars)
          (vals-reorder (delete-val vals (car nvars) vars)
                        (delete-hq (car nvars) vars) (cdr nvars)))))

(defun q-restrict-shrink-induct (x vals v vars)
  (declare (xargs :guard (and (boolean-listp vals)
                              (symbol-listp vars))))
  (if (atom x)
      (list x vals v vars)
    (if (eq v (car vars))
        (if (car vals)
            (q-restrict-shrink-induct (car x) (cdr vals) v vars)
          (q-restrict-shrink-induct (cdr x) (cdr vals) v vars))
      (if (car vals)
          (q-restrict-shrink-induct (car x) (cdr vals) v (cdr vars))
        (q-restrict-shrink-induct (cdr x) (cdr vals) v (cdr vars))))))

(defthm q-restrict-shrink-correct
  (implies  (and (iff (get-val v vals vars) n)
                 (member-eq v vars))
            (equal (eval-bdd (q-restrict-shrink x n v vars)
                             (delete-val vals v vars))
                   (eval-bdd x vals)))
  :hints (("Goal"
           :induct (q-restrict-shrink-induct x vals v vars))))

(defun q-reorder-induct (x vals vars nvars)
  (declare (xargs :measure (acl2-count nvars)
                  :guard (and (boolean-listp vals)
                              (symbol-listp vars)
                              (symbol-listp nvars))))
  (if (or (atom x)
          (atom nvars))
      nil
    (if (eq (car nvars) (car vars))
        (if (car vals)
            (q-reorder-induct
             (car x) (cdr vals) (cdr vars) (cdr nvars))
          (q-reorder-induct
           (cdr x) (cdr vals) (cdr vars) (cdr nvars)))
      (let ((val (get-val (car nvars) vals vars)))
        (if val
            (q-reorder-induct (q-restrict-shrink x t (car nvars) vars)
                              (delete-val vals (car nvars) vars)
                              (delete-hq (car nvars) vars)
                              (cdr nvars))
          (q-reorder-induct (q-restrict-shrink x nil (car nvars) vars)
                            (delete-val vals (car nvars) vars)
                            (delete-hq (car nvars) vars)
                            (cdr nvars)))))))

(defun unique-eq (l)
  (declare (xargs :guard (symbol-listp l)))
  (if (endp l) t
    (if (member-eq (car l) (cdr l)) nil
      (unique-eq (cdr l)))))

(defthm unique-eq-subsetp-eq
  (implies (and (subsetp-eq l1 l2)
                (unique-eq l1)
                (equal (car l1) (car l2)))
           (subsetp-eq (cdr l1) (cdr l2))))

(defthm member-eq-delete
  (implies (and (member-eq v1 l)
                (not (eq v1 v2)))
           (member-eq v1 (delete-hq v2 l))))

(defthm subset-eq-delete
  (implies (and (subsetp-eq l1 l2)
                (not (member-eq v l1)))
           (subsetp-eq l1 (delete-hq v l2))))

(defthm delete-subsetp-eq
  (implies (and (subsetp-eq l1 l2)
                (unique-eq l1)
                (member-eq v l1))
           (subsetp-eq (delete-hq v l1)
                       (delete-hq v l2))))

(defthm q-reorder-correct
  (implies (and (unique-eq nvars)
                (subsetp-eq nvars vars))
           (equal (eval-bdd (q-reorder x vars nvars)
                            (vals-reorder vals vars nvars))
                  (eval-bdd x vals)))
  :hints (("Goal" :induct (q-reorder-induct x vals vars nvars))))

;=====================================================================

;; (defthm eval-bdd-cdr
;;   (implies (and (consp y)
;;                 (not (car vals)))
;;            (equal (eval-bdd y vals)
;;                   (eval-bdd (cdr y) (cdr vals)))))

;; (defthm eval-bdd-car
;;   (implies (and (consp y)
;;                 (car vals))
;;            (equal (eval-bdd y vals)
;;                   (eval-bdd (car y) (cdr vals)))))


(defthm q-and-correct
  (implies (and (normp x)
                (normp y))
           (equal (eval-bdd (q-and x y) vals)
                  (and (eval-bdd x vals)
                       (eval-bdd y vals)))))

(defthm normp-q-and
  (implies (and (normp x)
                (normp y))
           (normp (q-and x y))))

(defthm q-or-correct
  (implies (and (normp x)
                (normp y))
           (equal (eval-bdd (q-or x y) vals)
                  (or (eval-bdd x vals)
                      (eval-bdd y vals)))))

(defthm normp-q-or
  (implies (and (normp x)
                (normp y))
           (normp (q-or x y))))

(defthm q-not-correct
  (implies (normp x)
           (equal (eval-bdd (q-not x) vals)
                  (not (eval-bdd x vals)))))

(defthm consp-q-not
  (implies (and (normp x)
                (consp x))
           (and (consp (q-not x))
                (normp (q-not x)))))

(defthm atom-q-not
  (implies (and (normp x)
                (atom x))
           (normp (q-not x))))

(defthm normp-q-not
  (implies (normp x)
           (normp (q-not x)))
  :hints (("Goal" :in-theory (e/d (booleanp) (q-not)))))

(in-theory (disable consp-q-not))
(in-theory (disable atom-q-not))

(defthm q-not-equiv-q-not-ite
  (implies (normp x)
           (equal (q-not x)
                  (q-not-ite x))))

(defthm q-and-args-identical-is-arg
  (implies (normp x)
           (equal (q-and x x) x)))

(defthm q-and-equiv-q-and-ite
  (implies (and (normp x)
                (normp y))
           (equal (q-and x y)
                  (q-and-ite x y))))

(defthm normp-q-and-ite
  (implies (and (normp x)
                (normp y))
           (normp (q-and-ite x y))))

(defthm q-or-args-identical-is-arg
  (implies (normp x)
           (equal (q-or x x) x)))

(defthm q-or-equiv-q-or-ite
  (implies (and (normp x)
                (normp y))
           (equal (q-or x y)
                  (q-or-ite x y))))

(defthm normp-q-or-ite
  (implies (and (normp x)
                (normp y))
           (normp (q-or-ite x y))))

(defthm normp-q-ite
  (implies (and (normp x)
                (normp y)
                (normp z))
           (normp (q-ite x y z)))
  :hints
  (("Goal"
    :induct (q-ite x y z)
    :in-theory (disable q-not q-not-equiv-q-not-ite))))

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


; Rough time:  121.07 seconds (prove: 103.72, print: 17.35, other: 0.00)

; Robert Krug looked at this proof, and produced the following set
; of improvements.

; A couple of expand hints sped things up a good bit.  I had examined the
; original proof, and decided that the first set of case-splits looked
; like the correct thing, but didn't like the two rounds of destructor
; elimination before the next set of big case-splits.  I wanted to force
; this second set to occur earlier in the flow, and saw that these terms
; terms appeared regularly, so I suggested to ACL2 that it be a little more
; eager to expand them.

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


; I then got greedy, and disabled eval-bdd and q-ite, and told ACL2 just
; which instances to expand:

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
           :in-theory (disable q-not q-not-equiv-q-not-ite
			       eval-bdd q-ite)
           )))

; Time:  5.97 seconds (prove: 4.41, print: 1.56, other: 0.00)


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


; Below here we deal with human readable terms...

(defun sym-val (term vars vals)
  (declare (xargs :guard (and (symbol-listp vars)
                              (boolean-listp vals))))
  (if (endp vars) nil
    (if (eq term (car vars))
        (car vals)
      (sym-val term (cdr vars) (cdr vals)))))

(defun term-eval (term vars vals)
  (declare (xargs :guard (and (qnorm1-guard term)
                              (symbol-listp vars)
                              (boolean-listp vals))))
  (cond ((eq term t) t)
        ((eq term nil) nil)
        ((symbolp term)
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
                              (symbol-listp vars))))
  (if (atom term)
      (or (booleanp term)
          (member-eq term vars))
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

(defthm eval-qvar-n (equal (eval-bdd (qvar-n i) nil)
                          nil))

(defthm <loc (implies (member term vars)
                      (<= 0 (locn term vars))))

(defthm eval-bdd-qvar-n
  (implies (and (symbolp term)
                (not (equal term t))
                (not (equal term nil))
                (boolean-listp vals)
                (member-eq term vars))
           (equal (eval-bdd (qvar-n (locn term vars)) vals)
                  (sym-val term vars vals))))

(defthm not-mem (implies (not (member term vars))
                         (equal (locn term vars) (len vars))))

(defthm eval-bdd-var-to-tree
  (implies (and (symbolp term)
                (not (equal term t))
                (not (equal term nil))
                (boolean-listp vals)
                (member-eq term vars))
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

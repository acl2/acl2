; Equality substitution clause processor
; Jared Davis <jared@cs.utexas.edu>

(in-package "ACL2")

; Modified for v3-4 by Matt K.: or-list and and-list are now defined in ACL2.

(defun iff-list (x y)
  (if (and (consp x)
           (consp y))
      (and (iff (car x) (car y))
           (iff-list (cdr x) (cdr y)))
    (and (not (consp x))
         (not (consp y)))))

(encapsulate
 ()
 (defthm iff-list-reflexive
   (iff-list x x))
 
 (defthm iff-list-symmetric
   (implies (iff-list x y)
            (iff-list y x)))
 
 (defthm iff-list-transitive
   (implies (and (iff-list x y)
                 (iff-list y z))
            (iff-list x z)))
 
 (defequiv iff-list))

(defcong iff-list equal (or-list x) 1)

(defcong iff-list equal (and-list x) 1)

(defevaluator evl evl-list
  ((if x y z) (equal x y) (not x)))

(defthm JARED-CONSTRAINT-1
  (implies 
   (and (symbolp fn)
        (not (equal fn 'quote))
        (equal (evl-list args1 env)
               (evl-list args2 env)))
   (equal (evl (cons fn args1) env)
          (evl (cons fn args2) env)))
  :hints (("Goal" :use ((:instance evl-constraint-0
                                   (x (cons fn args1))
                                   (a env))
                        (:instance evl-constraint-0
                                   (x (cons fn args2))
                                   (a env))))))
                        
(defthm evl-of-disjoin2
  (iff (evl (disjoin2 t1 t2) env)
       (or (evl t1 env)
           (evl t2 env))))

(in-theory (disable disjoin2))

(defthm evl-of-disjoin
  (iff (evl (disjoin x) env)
       (or-list (evl-list x env))))

(in-theory (disable disjoin))

(defthm evl-of-conjoin2
  (iff (evl (conjoin2 t1 t2) env)
       (and (evl t1 env)
            (evl t2 env))))

(in-theory (disable conjoin2))

(defthm evl-of-conjoin
  (iff (evl (conjoin x) env)
       (and-list (evl-list x env)))
  :hints(("Goal" :induct (and-list x))))

(in-theory (disable conjoin))

(defun pseudo-term-alistp (x)
  ;; Recognize an alist whose keys and values are all pseudo-terms 
  (declare (xargs :guard t))
  (if (consp x)
      (and (consp (car x))
           (pseudo-termp (car (car x)))
           (pseudo-termp (cdr (car x)))
           (pseudo-term-alistp (cdr x)))
    (equal x nil)))

(defthm alistp-when-pseudo-term-alistp
  (implies (pseudo-term-alistp x)
           (alistp x)))


(defun pseudo-term-alist-to-equalities (x)
  ;; Turn a pseudo-term alist into a list of (equal key val) terms.
  (declare (xargs :guard (pseudo-term-alistp x)))
  (if (consp x)
      (cons `(equal ,(car (car x)) ,(cdr (car x)))
            (pseudo-term-alist-to-equalities (cdr x)))
    nil))

(defthm pseudo-term-listp-of-pseudo-term-alist-to-equalities
  (implies (force (pseudo-term-alistp x))
           (equal (pseudo-term-listp (pseudo-term-alist-to-equalities x))
                  t)))



(mutual-recursion
 (defun pseudo-term-substitute-alist (x alist)
   ;; Substitute a pseudo-term alist into a pseudo-term.  We've arbitrarily
   ;; chosen not to descend into lambda bodies.
   (declare (xargs :guard (and (pseudo-termp x)
                               (pseudo-term-alistp alist))))
   (let ((binding (assoc-equal x alist)))
     (cond ((consp binding)
            (cdr binding))
           ((atom x)
            x)
           ((equal (car x) 'quote)
            x)
           (t 
            (cons (car x) (pseudo-term-list-substitute-alist (cdr x) alist))))))
 (defun pseudo-term-list-substitute-alist (x alist)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (pseudo-term-alistp alist))))
   (if (consp x)
       (cons (pseudo-term-substitute-alist (car x) alist)
             (pseudo-term-list-substitute-alist (cdr x) alist))
     nil)))



(defun weaken-clause-with-each-term (terms clause)
  ;; Terms are a list of pseudo-terms, [t1, ..., tn]
  ;; We create the list of clauses, [t1::clause, ..., tn::clause]
  (declare (xargs :guard (and (pseudo-term-listp terms)
                              (pseudo-term-listp clause))))
  (if (consp terms)
      (cons (cons (car terms) clause)
            (weaken-clause-with-each-term (cdr terms) clause))
    nil))

(defthm pseudo-term-list-listp-of-weaken-clause-with-each-term
  (implies (and (force (pseudo-term-listp terms))
                (force (pseudo-term-listp clause)))
           (pseudo-term-list-listp (weaken-clause-with-each-term terms clause))))

(set-verify-guards-eagerness 0)

(defun equality-substitute-clause (clause alist state)
  (declare (xargs :guard (and (state-p state)
                              (pseudo-term-listp clause))
                  :stobjs state))
  (cond 
   ((not (pseudo-term-alistp alist))
    (ACL2::prog2$ 
     (ACL2::cw "equality-substitute-clause invoked with bad alist: ~x0~%" alist)
     (mv t nil state)))
   (t
    (value (cons
            ;; The clause resulting from the substitution.
            (pseudo-term-list-substitute-alist clause alist)
            ;; You also have to prove the clause resulting from the substitution.
            (weaken-clause-with-each-term 
             (pseudo-term-alist-to-equalities alist)
             clause))))))

(defun flag-pseudo-termp (flag x)
  (declare (xargs :guard t))
  (if (equal flag 'term)
      (cond ((atom x) (symbolp x))
            ((eq (car x) 'quote)
             (and (consp (cdr x))
                  (null (cdr (cdr x)))))
            ((not (true-listp x)) nil)
            ((not (flag-pseudo-termp 'list (cdr x))) nil)
            (t (or (symbolp (car x))
                   (and (true-listp (car x))
                        (equal (length (car x)) 3)
                        (eq (car (car x)) 'lambda)
                        (symbol-listp (cadr (car x)))
                        (flag-pseudo-termp 'term (caddr (car x)))
                        (equal (length (cadr (car x)))
                               (length (cdr x)))))))
    (cond ((atom x) (equal x nil))
          (t (and (flag-pseudo-termp 'term (car x))
                  (flag-pseudo-termp 'list (cdr x)))))))

(encapsulate 
 ()
 (local (defthm lemma
          (if (equal flag 'term)
              (equal (flag-pseudo-termp flag x)
                     (pseudo-termp x))
            (equal (flag-pseudo-termp flag x)
                   (pseudo-term-listp x)))
          :rule-classes nil))

 (defthm flag-pseudo-termp-of-term
   (equal (flag-pseudo-termp 'term x)
          (pseudo-termp x))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))
 
 (defthm flag-psueod-termp-of-list
   (equal (flag-pseudo-termp 'list x)
          (pseudo-term-listp x))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))



(encapsulate
 ()
 (local (defthm lemma1
          (implies (consp (assoc-equal x alist))
                   (member (list 'equal x (cdr (assoc-equal x alist)))
                           (pseudo-term-alist-to-equalities alist)))))
 
 (local (defthm lemma2
          (implies (and (and-list (evl-list x env))
                        (member a x))
                   (iff (evl a env)
                        t))))

 (local (defthm lemma3
          (implies (and (and-list (evl-list (pseudo-term-alist-to-equalities alist) env))
                        (consp (assoc-equal x alist)))
                   (iff (evl (list 'equal x (cdr (assoc-equal x alist))) env)
                        t))))

 (defthm evl-of-binding
   (implies (and (and-list (evl-list (pseudo-term-alist-to-equalities alist) env))
                 (consp (assoc-equal x alist)))
            (equal (evl (cdr (assoc-equal x alist)) env)
                   (evl x env)))))
  

(encapsulate
 ()
 (local (defthm lemma
          (if (equal flag 'term)
              (implies (and (pseudo-termp x)
                            (pseudo-term-alistp alist)
                            (and-list (evl-list (pseudo-term-alist-to-equalities alist) env)))
                       (equal (evl (pseudo-term-substitute-alist x alist) env)
                              (evl x env)))
            (implies (and (pseudo-term-listp x)
                          (pseudo-term-alistp alist)
                          (and-list (evl-list (pseudo-term-alist-to-equalities alist) env)))
                     (equal (evl-list (pseudo-term-list-substitute-alist x alist) env)
                            (evl-list x env))))
          :rule-classes nil
          :hints(("Goal"
                  :induct (flag-pseudo-termp flag x)
                  :do-not '(generalize fertilize)
                  :do-not-induct t))))

 (defthm evl-of-pseudo-term-substitute-alist-when-all-equal
   (implies (and (pseudo-termp x)
                 (pseudo-term-alistp alist)
                 (and-list (evl-list (pseudo-term-alist-to-equalities alist) env)))
            (equal (evl (pseudo-term-substitute-alist x alist) env)
                   (evl x env)))
   :hints(("Goal" :use ((:instance lemma (flag 'term))))))
 
 (defthm evl-of-pseudo-term-list-substitute-alist-when-all-equal
   (implies (and (pseudo-term-listp x)
                 (pseudo-term-alistp alist)
                 (and-list (evl-list (pseudo-term-alist-to-equalities alist) env)))
            (equal (evl-list (pseudo-term-list-substitute-alist x alist) env)
                   (evl-list x env)))
   :hints(("Goal" :use ((:instance lemma (flag 'list)))))))
                  
(defun repeat (x n)
  (declare (xargs :guard (natp n)))
  (if (zp n)
      nil
    (cons x (repeat x (- n 1)))))

(encapsulate
 ()
 (local (include-book "arithmetic/top" :dir :system))
 
 (defthm repeat-of-plus1
   (implies (force (natp n))
            (equal (repeat x (+ 1 n))
                   (cons x (repeat x n))))
   :hints(("Goal" :expand (repeat x (+ 1 n))))))

(defthm lemma
  (implies (not (or-list (evl-list clause env)))
           (iff-list (evl-list (disjoin-lst (weaken-clause-with-each-term terms clause)) env)
                     (evl-list terms env)))
  :hints(("Goal"
          :induct (len terms)
          :do-not '(generalize fertilize)
          :do-not-induct t)))

(defthm correctness-of-equality-substitute-clause
  (implies (and (pseudo-term-listp clause)
                (alistp env)
                (evl (conjoin-clauses (clauses-result (equality-substitute-clause clause alist state))) env))
           (evl (disjoin clause) env))
  :rule-classes :clause-processor
  :hints(("Goal" 
          :do-not-induct t
          :do-not '(generalize fertilize)))
  :otf-flg t)

; Here is an application contributed by Erik Reeber (which we make local so
; that it's not exported).

(local
 (progn

   (encapsulate
    (((f *) => *)
     ((g *) => *)
     ((p * *) => *))
    (local (defun f (x) x))
    (local (defun g (x) x))
    (local (defun p (x y) (declare (ignore x y)) t))
    (defthm p-axiom (p (g x) (g y))))

; Define must-succeed and must-fail macros.
   (local (include-book "make-event/eval" :dir :system))

   (must-fail ; illustrates why we need a hint
    (defthm p-thm 
      (implies (and (equal (f x) (g x)) 
                    (equal (f y) (g y))) 
               (p (f x) (f y)))))

   (defthm p-thm 
     (implies (and (equal (f x) (g x)) 
                   (equal (f y) (g y))) 
              (p (f x) (f y))) 
     :hints (("Goal"
              :clause-processor
              (:function
               equality-substitute-clause
               :hint
; The following is an alist with entries (old . new), where new is to be
; substituted for old.
               '(((f x) . (g x))
                 ((f y) . (g y)))))))
   ))

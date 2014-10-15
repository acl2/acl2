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
(include-book "basic")
(include-book "clean-clauses")
(include-book "if-lifting/lifted-termp")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



;; Definition of clause.aux-split
;;
;; Clause.aux-split is our main routine for splitting clauses.  We think of
;; todo and done together as a single input clause, (app todo done), and we
;; produce a list of clauses which whose conjunction is logically equivalent to
;; the input clause.  We search todo for three kinds of literals,
;;
;;   - (not (not x)),
;;   - (not (if a b c)), and
;;   - (if a b c),
;;
;; where each "not" should be understood to include the negative-termp variants
;; such as (iff x nil).  We scan the todo list for these kinds of literals, and
;; then apply the following reductions.
;;
;;   1. (aux-split [(not (not x)), ...] done) = (aux-split [x, ...] done)
;;
;;   2. (aux-split [(not (if a b c)), ...] done) =
;;        (app (aux-split [(not a),(not b),...] done)
;;             (aux-split [a,(not c),...] done)))
;;
;;   3. (aux-split [(if a b c), ...] done) =
;;        (app (aux-split [(not a),b...] done)
;;             (aux-split [a,c,...] done))
;;
;; To see that this terminates, we introduce the following count,
;;
;;   m(not x)    = 1 + m(x),
;;   m(if a b c) = 1 + m(a) + m(b) + m(c), and
;;   m(_)        = 1,
;;
;; and we sum the counts of the literals in todo.  This decreases with each
;; recursive call above:
;;
;;    (1) WTS: m(x) < m(not (not x))
;;         <-> m(x) < 1 + 1 + m(x)
;;         <-> 0 < 2
;;
;;   (2a) WTS: m(not a) + m(not b) < m(not (if a b c))
;;         <-> 1 + m(a) + 1 + m(b) < 1 + 1 + m(a) + m(b) + m(c)
;;         <-> 0 < m(c)
;;
;;   (2b) WTS: m(a) + m(not c) < m(not (if a b c))
;;         <-> m(a) + 1 + m(c) < 1 + m(a) + m(b) + m(c)
;;         <-> 0 < m(c)
;;
;;   (3a) WTS: m(not a) + m(c) < m(if a b c)
;;         <-> 1 + m(a) + m(c) < 1 + m(a) + m(b) + m(c)
;;         <-> 0 < m(b)
;;
;;   (3b) WTS: m(a) + m(c) < m(if a b c)
;;         <-> m(a) + m(c) < 1 + m(a) + m(b) + m(c)
;;         <-> 0 < 1 + m(c)

(defund clause.split-count (x)
  (declare (xargs :guard (logic.termp x)))
  (if (clause.negative-termp x)
      (+ 1 (clause.split-count (clause.negative-term-guts x)))
    (if (and (logic.functionp x)
             (equal (logic.function-name x) 'if)
             (equal (len (logic.function-args x)) 3))
        (+ 1 (+ (clause.split-count (first (logic.function-args x)))
                (+ (clause.split-count (second (logic.function-args x)))
                   (clause.split-count (third (logic.function-args x))))))
      1)))

(encapsulate
 ()
 (local (in-theory (enable clause.split-count)))

 (defthm natp-of-clause.split-count
   (equal (natp (clause.split-count x))
          t))

 (defthm |(< 0 (clause.split-count x))|
   (equal (< 0 (clause.split-count x))
          t))

 (defthm clause.split-count-when-clause.negative-termp
   (implies (clause.negative-termp x)
            (equal (clause.split-count x)
                   (+ 1 (clause.split-count (clause.negative-term-guts x))))))

 (defthm clause.split-count-when-if
   (implies (and (logic.functionp x)
                 (equal (logic.function-name x) 'if)
                 (equal (len (logic.function-args x)) 3)
                 (not (clause.negative-termp x)))
            (equal (clause.split-count x)
                   (+ 1 (+ (clause.split-count (first (logic.function-args x)))
                           (+ (clause.split-count (second (logic.function-args x)))
                              (clause.split-count (third (logic.function-args x))))))))))




(defund clause.split-count-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (if (consp x)
      (+ (clause.split-count (car x))
         (clause.split-count-list (cdr x)))
    0))

(encapsulate
 ()
 (defthm clause.split-count-list-when-not-consp
   (implies (not (consp x))
            (equal (clause.split-count-list x)
                   0))
   :hints(("Goal" :in-theory (enable clause.split-count-list))))

 (defthm clause.split-count-list-of-cons
   (equal (clause.split-count-list (cons a x))
          (+ (clause.split-count a)
             (clause.split-count-list x)))
   :hints(("Goal" :in-theory (enable clause.split-count-list))))

 (defthm natp-of-clause.split-count-list
   (equal (natp (clause.split-count-list x))
          t)
   :hints(("Goal" :induct (cdr-induction x)))))




(defund clause.aux-split-goal (todo done)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (logic.term-listp done)
                              (or (consp todo)
                                  (consp done)))))
  (cond ((and (consp todo)
              (consp done))
         (logic.por (clause.clause-formula todo)
                    (clause.clause-formula done)))
        ((consp todo)
         (clause.clause-formula todo))
        (t
         (clause.clause-formula done))))

(defthmd clause.aux-split-goal-when-not-consp-of-todo
   (implies (and (not (consp todo))
                 (force (consp done)))
            (equal (clause.aux-split-goal todo done)
                   (clause.clause-formula done)))
   :hints(("Goal" :in-theory (enable clause.aux-split-goal))))




(defund clause.aux-split-trivial-branchp (x y rest done)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp y)
                              (logic.term-listp rest)
                              (logic.term-listp done))))
  ;; As we split, we often introduce trivial clauses where a term is obvious or where
  ;; the new literals are the complements of other literals.  In these cases, we want
  ;; to stop splitting immediately, and just prove the goal formula for the branch.
  (or (clause.obvious-termp x)
      (clause.obvious-termp y)
      (let ((xbar (clause.complement-term x)))
        (or (equal xbar y)
            (memberp xbar rest)
            (memberp xbar done)))
      (let ((ybar (clause.complement-term y)))
        (or (memberp ybar rest)
            (memberp ybar done)))))

(defthm booleanp-of-clause.aux-split-trivial-branchp
  (equal (booleanp (clause.aux-split-trivial-branchp x y rest done))
         t)
  :hints(("Goal" :in-theory (enable clause.aux-split-trivial-branchp))))




(defund@ clause.aux-split-trivial-branch-bldr (x y rest done)
  (declare (xargs :guard (and (logic.termp x)
                              (logic.termp y)
                              (logic.term-listp rest)
                              (logic.term-listp done)
                              (clause.aux-split-trivial-branchp x y rest done))
                  :guard-hints (("Goal" :in-theory (enable
                                                    clause.aux-split-trivial-branchp)))))

  ;; Goal is to prove
  ;; (clause.aux-split-goal (cons x (cons y todo)) done)

  (let* ((xbar          (clause.complement-term x))
         (ybar          (clause.complement-term y))
         (todo          (cons x (cons y rest)))
         (todo-formulas (logic.term-list-formulas todo)))

    (cond ((clause.obvious-termp x)
           (if (consp done)
               (@derive
                ((!= X nil)                  (clause.obvious-term-bldr x))
                ((v X (v Y T1-Tn))           (build.multi-expansion @- todo-formulas))
                ((v (v X (v Y T1-Tn)) D1-Dm) (build.right-expansion @- (clause.clause-formula done))))
             (@derive
              ((!= X nil)                  (clause.obvious-term-bldr x))
              ((v X (v Y T1-Tn))           (build.multi-expansion @- todo-formulas)))))

          ((clause.obvious-termp y)
           (if (consp done)
               (@derive
                ((!= Y nil)                  (clause.obvious-term-bldr y))
                ((v X (v Y T1-Tn))           (build.multi-expansion @- todo-formulas))
                ((v (v X (v Y T1-Tn)) D1-Dm) (build.right-expansion @- (clause.clause-formula done))))
             (@derive
              ((!= Y nil)                  (clause.obvious-term-bldr y))
              ((v X (v Y T1-Tn))           (build.multi-expansion @- todo-formulas)))))

          ((or (equal xbar y) (memberp xbar rest))
           (if (consp done)
               (@derive
                ((v X (v Y T1-Tn))           (clause.complement-clause-bldr x todo))
                ((v (v X (v Y T1-Tn)) D1-Dm) (build.right-expansion @- (clause.clause-formula done))))
             (@derive
              ((v X (v Y T1-Tn)) (clause.complement-clause-bldr x todo)))))

          ((memberp xbar done)
           (@derive
            ((v X D1-Dm)                  (clause.complement-clause-bldr x (cons x done)))
            ((v X (v (v Y T1-Tn) D1-Dm))  (build.disjoined-left-expansion @- (clause.clause-formula (cons y rest))))
            ((v (v X (v Y T1-Tn)) D1-Dm)  (build.associativity @-))))

          ((memberp ybar rest)
           (if (consp done)
               (@derive
                ((v X (v Y T1-Tn))           (clause.complement-clause-bldr y todo))
                ((v (v X (v Y T1-Tn)) D1-Dm) (build.right-expansion @- (clause.clause-formula done))))
             (@derive
              ((v X (v Y T1-Tn)) (clause.complement-clause-bldr y todo)))))

          ((memberp ybar done)
           (if (consp rest)
               (@derive
                ((v Y D1-Dm)                  (clause.complement-clause-bldr y (cons y done)))
                ((v Y (v T1-Tn D1-Dm))        (build.disjoined-left-expansion @- (clause.clause-formula rest)))
                ((v (v Y T1-Tn) D1-Dm)        (build.associativity @-))
                ((v X (v (v Y T1-Tn) D1-Dm))  (build.expansion (logic.term-formula x) @-))
                ((v (v X (v Y T1-Tn)) D1-Dm)  (build.associativity @-)))
             (@derive
              ((v Y D1-Dm)        (clause.complement-clause-bldr y (cons y done)))
              ((v X (v Y D1-Dm))  (build.expansion (logic.term-formula x) @-))
              ((v (v X Y) D1-Dm)  (build.associativity @-)))))

          (t
           nil))))


(defobligations clause.aux-split-trivial-branch-bldr
  (clause.obvious-term-bldr
   build.multi-expansion
   build.right-expansion
   clause.complement-clause-bldr
   build.disjoined-left-expansion
   build.associativity
   build.expansion))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-split-trivial-branchp
                           clause.aux-split-trivial-branch-bldr
                           clause.aux-split-goal)))

 (defthm logic.appealp-of-clause.aux-split-trivial-branch-bldr
   (implies (force (and (logic.termp x)
                        (logic.termp y)
                        (logic.term-listp rest)
                        (logic.term-listp done)
                        (clause.aux-split-trivial-branchp x y rest done)))
            (equal (logic.appealp (clause.aux-split-trivial-branch-bldr x y rest done))
                   t)))

 (defthm logic.conclusion-of-clause.aux-split-trivial-branch-bldr
   (implies (force (and (logic.termp x)
                        (logic.termp y)
                        (logic.term-listp rest)
                        (logic.term-listp done)
                        (clause.aux-split-trivial-branchp x y rest done)))
            (equal (logic.conclusion (clause.aux-split-trivial-branch-bldr x y rest done))
                   (clause.aux-split-goal (cons x (cons y rest)) done))))

 (defthm@ logic.proofp-of-clause.aux-split-trivial-branch-bldr
   (implies (force (and (logic.termp x)
                        (logic.termp y)
                        (logic.term-listp rest)
                        (logic.term-listp done)
                        (clause.aux-split-trivial-branchp x y rest done)
                        ;; ---
                        (equal (cdr (lookup 'not atbl)) 1)
                        (equal (cdr (lookup 'equal atbl)) 2)
                        (equal (cdr (lookup 'iff atbl)) 2)
                        (equal (cdr (lookup 'if atbl)) 3)
                        (logic.term-atblp x atbl)
                        (logic.term-atblp y atbl)
                        (logic.term-list-atblp rest atbl)
                        (logic.term-list-atblp done atbl)
                        (@obligations clause.aux-split-trivial-branch-bldr)))
            (equal (logic.proofp (clause.aux-split-trivial-branch-bldr x y rest done) axioms thms atbl)
                   t))))





(defund clause.aux-split (todo done)
  (declare (xargs :guard (and (logic.term-listp todo)
                              (logic.term-listp done))
                  :verify-guards nil
                  :measure (clause.split-count-list todo)))
  (if (consp todo)
      (let* ((negativep (clause.negative-termp (car todo)))
             (guts      (if negativep (clause.negative-term-guts (car todo)) (car todo))))
        (cond

         ((and negativep (clause.negative-termp guts))
          ;; Cancel (not (not a))
          (clause.aux-split (cons (clause.negative-term-guts guts) (cdr todo)) done))

         ((and (logic.functionp guts)
               (equal (logic.function-name guts) 'if)
               (equal (len (logic.function-args guts)) 3))
          (let ((args (logic.function-args guts)))
            (if negativep
                ;; The first literal is (not (if a b c)).
                ;; New clause 1: (not a) v (not b) v rest
                ;; New clause 2: a v (not c) v rest
                (let ((a      (first args))
                      (not-a  (logic.function 'not (list (first args))))
                      (not-b  (logic.function 'not (list (second args))))
                      (not-c  (logic.function 'not (list (third args))))
                      (rest   (cdr todo)))
                  (let ((triv1 (clause.aux-split-trivial-branchp not-a not-b rest done))
                        (triv2 (clause.aux-split-trivial-branchp a not-c rest done)))
                    (cond ((and triv1 triv2)
                           nil)
                          (triv1
                           (clause.aux-split (cons a (cons not-c rest)) done))
                          (triv2
                           (clause.aux-split (cons not-a (cons not-b rest)) done))
                          (t
                           (revappend (clause.aux-split (cons not-a (cons not-b rest)) done)
                                      (clause.aux-split (cons a (cons not-c rest)) done))))))

              ;; The first literal is (if a b c).
              ;; New clause 1: (not a) v b v rest
              ;; New clause 2: a v c v rest
              (let ((a     (first args))
                    (not-a (logic.function 'not (list (first args))))
                    (b     (second args))
                    (c     (third args))
                    (rest  (cdr todo)))
                (let ((triv1 (clause.aux-split-trivial-branchp not-a b rest done))
                      (triv2 (clause.aux-split-trivial-branchp a c rest done)))
                  (cond ((and triv1 triv2)
                         nil)
                        (triv1
                         (clause.aux-split (cons a (cons c rest)) done))
                        (triv2
                         (clause.aux-split (cons not-a (cons b rest)) done))
                        (t
                         (revappend (clause.aux-split (cons not-a (cons b rest)) done)
                                    (clause.aux-split (cons a (cons c rest)) done)))))))))

         (t
          ;; We can't split this literal, but we'll normalize it to "(not x)" if it is
          ;; some other negative-termp variant of not.
          (clause.aux-split (cdr todo) (cons (if negativep
                                                 (logic.function 'not (list guts))
                                               (car todo))
                                             done)))))
    (list done)))

(encapsulate
 ()
 (local (in-theory (enable clause.aux-split)))

 (defthm true-listp-of-clause.aux-split
   (equal (true-listp (clause.aux-split todo done))
          t))

 ;; (defthm consp-of-clause.aux-split
 ;;    (equal (consp (clause.aux-split todo done))
 ;;           t))

 ;; (defthm clause.aux-split-under-iff
 ;;   (iff (clause.aux-split todo done)
 ;;        t))

 (defthm forcing-term-list-listp-of-clause.aux-split
   (implies (force (and (logic.term-listp todo)
                        (logic.term-listp done)))
            (equal (logic.term-list-listp (clause.aux-split todo done))
                   t)))

 (defthm forcing-term-list-list-atblp-of-clause.aux-split
   (implies (force (and (logic.term-listp todo)
                        (logic.term-list-atblp todo atbl)
                        (logic.term-list-atblp done atbl)
                        (equal (cdr (lookup 'not atbl)) 1)))
            (equal (logic.term-list-list-atblp (clause.aux-split todo done) atbl)
                   t)))

 (verify-guards clause.aux-split)

 (defthm forcing-cons-listp-of-clause.aux-split
   (implies (force (or (consp todo) (consp done)))
            (equal (cons-listp (clause.aux-split todo done))
                   t))))



;; We say that clause splitting is "complete" if the resulting clauses contain
;; only simple terms.  Clearly aux-split is not complete for all terms, because
;; it only looks for "if" expressions at the top of a literal.  So, even though
;; it would split (IF X (CONSP Y) (CONSP Z)), it would miss (CONSP (IF X Y Z)).
;; But aux-split is complete for all "lifted" terms, so we can combine our
;; clause.lift routine with aux-split to arrive at a complete routine for any
;; clause.
;;
;; The definition of lifted-termp does not line up well with aux-split because
;; of negative-termps, so we actually show that aux-split is complete for a
;; larger class of terms, the lifted-gutsp terms, which subsume the lifted
;; terms.

(defund clause.lifted-gutsp (x)
  (declare (xargs :guard (logic.termp x)))
  (if (clause.negative-termp x)
      (clause.lifted-gutsp (clause.negative-term-guts x))
    (if (and (logic.functionp x)
             (equal (logic.function-name x) 'if)
             (equal (len (logic.function-args x)) 3))
        (and (clause.lifted-gutsp (first (logic.function-args x)))
             (clause.lifted-gutsp (second (logic.function-args x)))
             (clause.lifted-gutsp (third (logic.function-args x))))
      (clause.simple-termp x))))

(defthm booleanp-of-clause.lifted-gutsp
  (equal (booleanp (clause.lifted-gutsp x))
         t)
  :hints(("Goal" :in-theory (enable clause.lifted-gutsp))))

(defthm forcing-clause.lifted-termp-of-clause.negative-term-guts-when-clause.lifted-termp
  (implies (and (clause.lifted-termp x)
                (force (clause.negative-termp x))
                (force (logic.termp x)))
           (equal (clause.lifted-termp (clause.negative-term-guts x))
                  t))
  :hints(("Goal" :in-theory (enable clause.negative-termp clause.negative-term-guts))))

;; (defthm clause.lifted-termp-when-bad-args-logic.functionp
;;   (implies (and (logic.functionp x)
;;                 (not (equal (len (logic.function-args x)) 3)))
;;            (equal (clause.lifted-termp x)
;;                   (clause.simple-term-listp (logic.function-args x))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 1))
;;   :hints(("Goal" :in-theory (enable clause.lifted-termp))))

(defthmd lemma-for-forcing-clause.lifted-gutsp-when-clause.lifted-termp
  (implies (not (logic.functionp x))
           (equal (clause.lifted-termp x)
                  (clause.simple-termp x)))
  :hints(("Goal" :induct (clause.lifted-termp-induction x))))

(defthm forcing-clause.lifted-gutsp-when-clause.lifted-termp
  (implies (and (clause.lifted-termp x)
                (force (logic.termp x)))
           (equal (clause.lifted-gutsp x)
                  t))
  :hints(("Goal"
          :in-theory (enable clause.lifted-gutsp
                             lemma-for-forcing-clause.lifted-gutsp-when-clause.lifted-termp))))


(deflist clause.lifted-guts-listp (x)
  (clause.lifted-gutsp x)
  :elementp-of-nil t
  :guard (logic.term-listp x))

(defthm forcing-clause.lifted-guts-listp-when-clause.lifted-term-listp
  (implies (and (clause.lifted-term-listp x)
                (force (logic.term-listp x)))
           (equal (clause.lifted-guts-listp x)
                  t))
  :hints(("Goal" :induct (cdr-induction x))))


(encapsulate
 ()
 (local (defthm lemma1
          (implies (and (clause.lifted-gutsp x)
                        (clause.negative-termp x))
                   (equal (clause.lifted-gutsp (clause.negative-term-guts x))
                          t))
          :hints(("Goal" :in-theory (enable clause.lifted-gutsp)))))

 (local (defthm lemma2
          (equal (clause.lifted-gutsp (logic.function 'not (list arg)))
                 (clause.lifted-gutsp arg))
          :hints(("Goal" :in-theory (enable clause.lifted-gutsp)))))

 (local (defthm lemma3
          (implies (and (clause.lifted-gutsp x)
                        (not (clause.negative-termp x))
                        (logic.functionp x)
                        (equal (logic.function-name x) 'if)
                        (equal (len (logic.function-args x)) 3))
                   (equal (clause.lifted-gutsp (first (logic.function-args x)))
                          t))
          :hints(("Goal" :expand (clause.lifted-gutsp x)))))

 (local (defthm lemma4
          (implies (and (clause.lifted-gutsp x)
                        (not (clause.negative-termp x))
                        (logic.functionp x)
                        (equal (logic.function-name x) 'if)
                        (equal (len (logic.function-args x)) 3))
                   (equal (clause.lifted-gutsp (second (logic.function-args x)))
                          t))
          :hints(("Goal" :expand (clause.lifted-gutsp x)))))

 (local (defthm lemma5
          (implies (and (clause.lifted-gutsp x)
                        (not (clause.negative-termp x))
                        (logic.functionp x)
                        (equal (logic.function-name x) 'if)
                        (equal (len (logic.function-args x)) 3))
                   (equal (clause.lifted-gutsp (third (logic.function-args x)))
                          t))
          :hints(("Goal" :expand (clause.lifted-gutsp x)))))

 (local (defthm lemma6
          (implies (and (clause.lifted-gutsp x)
                        (not (clause.negative-termp x))
                        (not (clause.simple-termp x)))
                   (and (equal (logic.functionp x) t)
                        (equal (logic.function-name x) 'if)
                        (equal (len (logic.function-args x)) 3)))
          :hints(("Goal" :expand (clause.lifted-gutsp x)))))

 (defthm clause.simple-term-list-listp-of-clause.aux-split-when-clause.lifted-guts-listp
   (implies (and (logic.term-listp todo)
                 (logic.term-listp done)
                 (clause.lifted-guts-listp todo)
                 (clause.simple-term-listp done))
            (equal (clause.simple-term-list-listp (clause.aux-split todo done))
                   t))
   :hints(("Goal"
           :in-theory (enable clause.aux-split)
           :induct (clause.aux-split todo done)))))

(defthm clause.simple-term-list-listp-of-clause.aux-split-when-clause.lifted-term-listp
  (implies (and (logic.term-listp todo)
                (logic.term-listp done)
                (clause.lifted-term-listp todo)
                (clause.simple-term-listp done))
           (equal (clause.simple-term-list-listp (clause.aux-split todo done))
                  t)))



;; (defthmd clause.aux-split-when-double-negative
;;   (implies (and (clause.negative-termp a)
;;                 (clause.negative-termp (clause.negative-term-guts a)))
;;            (equal (clause.aux-split (cons a x) done)
;;                   (clause.aux-split (cons (clause.negative-term-guts (clause.negative-term-guts a)) x) done)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (defthmd clause.aux-split-when-negative-1
;;   (implies (and (clause.negative-termp a)
;;                 (not (clause.negative-termp (clause.negative-term-guts a)))
;;                 (not (logic.functionp (clause.negative-term-guts a))))
;;            (equal (clause.aux-split (cons a x) done)
;;                   (clause.aux-split x (cons (logic.function 'not (list (clause.negative-term-guts a))) done))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (defthmd clause.aux-split-when-negative-2
;;   (implies (and (clause.negative-termp a)
;;                 (not (clause.negative-termp (clause.negative-term-guts a)))
;;                 (not (equal (logic.function-name (clause.negative-term-guts a)) 'if)))
;;            (equal (clause.aux-split (cons a x) done)
;;                   (clause.aux-split x (cons (logic.function 'not (list (clause.negative-term-guts a))) done))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (defthmd clause.aux-split-when-negative-3
;;   (implies (and (clause.negative-termp a)
;;                 (not (clause.negative-termp (clause.negative-term-guts a)))
;;                 (not (equal (len (logic.function-args (clause.negative-term-guts a))) 3)))
;;            (equal (clause.aux-split (cons a x) done)
;;                   (clause.aux-split x (cons (logic.function 'not (list (clause.negative-term-guts a))) done))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (defthmd clause.aux-split-when-negative-4
;;   (implies (and (clause.negative-termp a)
;;                 (not (clause.negative-termp (clause.negative-term-guts a)))
;;                 (logic.functionp (clause.negative-term-guts a))
;;                 (equal (logic.function-name (clause.negative-term-guts a)) 'if)
;;                 (equal (len (logic.function-args (clause.negative-term-guts a))) 3))
;;            (equal (clause.aux-split (cons a x) done)
;;                   (let ((args (logic.function-args (clause.negative-term-guts a))))
;;                     (let ((a      (first args))
;;                           (not-a  (logic.function 'not (list (first args))))
;;                           (not-b  (logic.function 'not (list (second args))))
;;                           (not-c  (logic.function 'not (list (third args))))
;;                           (rest   x))
;;                       (let ((part1  (if (clause.aux-split-trivial-branchp not-a not-b rest done)
;;                                         nil
;;                                       (clause.aux-split (cons not-a (cons not-b rest)) done)))
;;                             (part2 (if (clause.aux-split-trivial-branchp a not-c rest done)
;;                                        nil
;;                                      (clause.aux-split (cons a (cons not-c rest)) done))))
;;                         (cond ((and part1 part2)
;;                                (revappend part1 part2))
;;                               (part1 part1)
;;                               (t     part2)))))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (defthmd clause.aux-split-when-positive-1
;;   (implies (and (not (clause.negative-termp a))
;;                 (not (logic.functionp a)))
;;            (equal (clause.aux-split (cons a x) done)
;;                   (clause.aux-split x (cons a done))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (defthmd clause.aux-split-when-positive-2
;;   (implies (and (not (clause.negative-termp a))
;;                 (not (equal (logic.function-name a) 'if)))
;;            (equal (clause.aux-split (cons a x) done)
;;                   (clause.aux-split x (cons a done))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (defthmd clause.aux-split-when-positive-3
;;   (implies (and (not (clause.negative-termp a))
;;                 (not (equal (len (logic.function-args a)) 3)))
;;            (equal (clause.aux-split (cons a x) done)
;;                   (clause.aux-split x (cons a done))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (defthmd clause.aux-split-when-positive-4
;;   (implies (and (not (clause.negative-termp a))
;;                 (logic.functionp a)
;;                 (equal (logic.function-name a) 'if)
;;                 (equal (len (logic.function-args a)) 3))
;;            (equal (clause.aux-split (cons a x) done)
;;                   (let ((args (logic.function-args a)))
;;                     (let ((a     (first args))
;;                           (not-a (logic.function 'not (list (first args))))
;;                           (b     (second args))
;;                           (c     (third args))
;;                           (rest  x))
;;                       (let ((part1 (if (clause.aux-split-trivial-branchp not-a b rest done)
;;                                        nil
;;                                      (clause.aux-split (cons not-a (cons b rest)) done)))
;;                             (part2 (if (clause.aux-split-trivial-branchp a c rest done)
;;                                        nil
;;                                      (clause.aux-split (cons a (cons c rest)) done))))
;;                         (cond ((and part1 part2)
;;                                (revappend part1 part2))
;;                               (part1 part1)
;;                               (t     part2)))))))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (defthmd clause.aux-split-when-not-consp
;;   (implies (not (consp todo))
;;            (equal (clause.aux-split todo done)
;;                   (list done)))
;;   :rule-classes ((:rewrite :backchain-limit-lst 0))
;;   :hints(("Goal" :in-theory (enable clause.aux-split))))

;; (deftheory clause.aux-split-openers
;;   '(clause.aux-split-when-double-negative
;;     clause.aux-split-when-negative-1
;;     clause.aux-split-when-negative-1
;;     clause.aux-split-when-negative-2
;;     clause.aux-split-when-negative-3
;;     clause.aux-split-when-negative-4
;;     clause.aux-split-when-positive-1
;;     clause.aux-split-when-positive-2
;;     clause.aux-split-when-positive-3
;;     clause.aux-split-when-positive-4
;;     clause.aux-split-when-not-consp))




(definlined clause.simple-split (clause)
  (declare (xargs :guard (and (logic.term-listp clause)
                              (consp clause))))
  (clause.aux-split clause nil))

(defthm true-listp-of-clause.simple-split
  (equal (true-listp (clause.simple-split clause))
         t)
  :hints(("Goal" :in-theory (enable clause.simple-split))))

;; (defthm consp-of-clause.simple-split
;;   (equal (consp (clause.simple-split clause))
;;          t)
;;   :hints(("Goal" :in-theory (enable clause.simple-split))))

;; (defthm clause.simple-split-under-iff
;;   (iff (clause.simple-split clause)
;;        t)
;;   :hints(("Goal" :in-theory (enable clause.simple-split))))

(defthm forcing-term-list-listp-of-clause.simple-split
  (implies (force (logic.term-listp clause))
           (equal (logic.term-list-listp (clause.simple-split clause))
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-split))))

(defthm forcing-term-list-list-atblp-of-clause.simple-split
  (implies (force (and (logic.term-listp clause)
                       (logic.term-list-atblp clause atbl)
                       (equal (cdr (lookup 'not atbl)) 1)))
           (equal (logic.term-list-list-atblp (clause.simple-split clause) atbl)
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-split))))

(defthm forcing-cons-listp-of-clause.simple-split
  (implies (force (consp clause))
           (equal (cons-listp (clause.simple-split clause))
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-split))))

(defthm clause.simple-term-list-listp-of-clause.simple-split-when-clause.lifted-term-listp
  (implies (and (logic.term-listp clause)
                (clause.lifted-term-listp clause))
           (equal (clause.simple-term-list-listp (clause.simple-split clause))
                  t))
  :hints(("Goal" :in-theory (enable clause.simple-split))))

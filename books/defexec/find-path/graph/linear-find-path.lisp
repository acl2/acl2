; An Exercise in Graph Theory
; J Strother Moore

; This file is an ACL2 book.  To certify it, execute:
;
; (certify-book "linear-find-path")
;
; Read the paper to get the context.

; In this file, I define a linear version of find-path and prove that
; it is equivalent to find-path and thus satisfies the same
; specification.

; This is a pretty interesting exercise.  One issue dealt with is that
; the linear find-path is reflexive.

; I follow the standard approach of including an ``irrelevant'' test
; on the measure to admit a reflexive definitional equation.  Then I
; eliminate it and prove uniqueness (just as an example of handling
; reflexive definitions) before getting on with the real work of
; correctness.

; The correctness argument was sort of difficult.  I had to invent a
; few concepts to get it to go through.  The function returns two
; results.  The first is the answer as computed by find-path.  The
; other is an extended mark table.  I am only interested in proving
; the correctness of the first result.  But of course I have to prove
; stuff about the second too, since it is used in the recursion to
; compute the first.  The two results are thus linked and the key
; lemma, called step2 below, is a conjunction and the conjuncts have
; to be proved together.  To state the property of the modified mark
; table, I had to define the notion of a ``pathless'' extension of
; another mark table.

; ---------------------------------------------------------------------------
; Getting Started

(in-package "ACL2")

(include-book "find-path3")
(set-well-founded-relation e0-ord-<)

; ---------------------------------------------------------------------------
; Admission of linear-find-path

(defun markedp (node mt)
  (member node mt))

(defun mark (node mt)
  (cons node mt))

(defthm count-non-members-cons
  (<= (count-non-members x (cons n mt))
      (count-non-members x mt))
  :rule-classes :linear)


(defthm e0-ordinalp-measure
  (e0-ordinalp (measure c mt g)))

; The following lemma captures the gist of the argument that adding a
; non-node to the table still decreases the measure.

(defthm non-nodes-have-no-neighbors
  (implies (and (equal (count-non-members (all-nodes g) (cons e mt))
                       (count-non-members (all-nodes g) mt))
                (not (member e mt)))
           (equal (neighbors e g) nil)))

(defthm measure-decreases-1
  (implies (and (consp c)
                (not (markedp e mt)))
           (e0-ord-< (measure (neighbors e g)
                              (cons e mt)
                              g)
                     (measure c mt g))))

(defthm measure-decreases-2
  (implies (and (consp c)
                (subsetp mt new-mt))
           (e0-ord-< (measure (cdr c)
                              new-mt
                              g)
                     (measure c mt g))))

(in-theory (disable measure))

(defun linear-find-next-step (c stack b g mt)
  (declare (xargs :measure (measure c mt g)))
  (cond
   ((endp c) (mv 'failure mt))
   ((markedp (car c) mt)
    (linear-find-next-step (cdr c) stack b g mt))
   ((equal (car c) b)
    (mv (rev (cons b stack))
        mt))
   (t (mv-let (temp new-mt)
              (linear-find-next-step (neighbors (car c) g)
                                     (cons (car c) stack)
                                     b g
                                     (mark (car c) mt))
              (cond
               ((e0-ord-< (measure (cdr c) new-mt g)
                          (measure c mt g))
                (if (eq temp 'failure)
                    (linear-find-next-step (cdr c) stack b g new-mt)
                  (mv temp mt)))
               (t (mv 'impossible 'impossible)))))))

(defun linear-find-path (a b g)
  (cond ((equal a b) (list a))
        (t (mv-let (temp mt)
                   (linear-find-next-step (neighbors a g)
                                          (list a)
                                          b g
                                          (mark a nil))
                   (declare (ignore mt))
                   temp))))

; ---------------------------------------------------------------------------
; Eliminating the ``Irrelevant'' Test

; I prove that the e0-ord-< test above is always true.

(defthm transitivity-of-subsetp
  (implies (and (subsetp x y)
                (subsetp y z))
           (subsetp x z)))

; The key fact is that linear-find-next-step only extends the table:

(defthm linear-find-next-step-extends-mt
  (subsetp mt (mv-nth 1 (linear-find-next-step c stack b g mt))))

; Thus, by the transitivity of subsetp, we know that we can extend it
; twice, e.g., from mt, to (mark e mt) to the table returned by
; linear-find-next-step on (mark e mt).  We use the expanded version
; of mark since mark is enabled and just rewrites to cons.

(defthm linear-find-next-step-extends-mt-corollary-1
  (subsetp mt
           (mv-nth 1 (linear-find-next-step c stack b g (cons e mt))))
  :hints
  (("Goal"
    :in-theory (disable transitivity-of-subsetp)
    :use (:instance transitivity-of-subsetp
                    (x mt)
                    (y (cons e mt))
                    (z (mv-nth 1
                               (linear-find-next-step c stack b g
                                                      (cons e mt))))))))

; This lemma shows the test must be t.

(defthm generalized-test-is-always-t
  (implies (and (not (endp c))
                (subsetp mt new-mt))
           (e0-ord-< (measure (cdr c) new-mt g)
                     (measure c mt g)))
  :hints (("Goal" :in-theory (enable measure))))

(defthm test-is-always-t
  (implies (not (endp c))
           (e0-ord-<
            (measure (cdr c)
                     (mv-nth 1
                             (linear-find-next-step (neighbors (car c) g)
                                                    (cons (car c) stack)
                                                    b g
                                                    (mark (car c) mt)))
                     g)
            (measure c mt g))))

; ---------------------------------------------------------------------------
; Existence

(defthm existence
  (equal
   (linear-find-next-step c stack b g mt)
   (cond
    ((endp c) (mv 'failure mt))
    ((markedp (car c) mt)
     (linear-find-next-step (cdr c) stack b g mt))
    ((equal (car c) b)
     (mv (rev (cons b stack))
         mt))
    (t (mv-let (temp new-mt)
               (linear-find-next-step (neighbors (car c) g)
                                      (cons (car c) stack)
                                      b g
                                      (mark (car c) mt))
               (cond
                ((eq temp 'failure)
                 (linear-find-next-step (cdr c) stack b g new-mt))
                (t (mv temp mt)))))))
  :rule-classes
  ((:definition :controller-alist
                ((linear-find-next-step t nil nil t t)))))

; Added by Matt Kaufmann 3/25/06, after v2-9-4, in order to allow the proof of
; step2 (below) to go through as before:
(set-body linear-find-next-step linear-find-next-step)

; From here on, we'll let the existence rule be used as our only
; ``definition'' of linear-find-next-step.

(in-theory (disable (:definition linear-find-next-step)))

; ---------------------------------------------------------------------------
; Uniqueness

; Q: Why did I name this constrained function x-linear-find-next-step?
; A: So that the system's dumb heuristics for equality substitution
;    would use

;    (equal (x-linear-find-next-step ...) (linear-find-next-step ...))

;    left-to-right rather than right-to-left.  To use an explicitly
;    given equality hypothesis, it substitutes to eliminate the
;    lexicographically biggest term

(encapsulate
 (((x-linear-find-next-step * * * * *) => (mv * *)))
 (local
  (defun x-linear-find-next-step (c stack b g mt)
    (linear-find-next-step c stack b g mt)))
 (defthm x-constraint
   (equal (x-linear-find-next-step c stack b g mt)
          (cond
           ((endp c) (mv 'failure mt))
           ((markedp (car c) mt)
            (x-linear-find-next-step (cdr c) stack b g mt))
           ((equal (car c) b)
            (mv (rev (cons b stack))
                mt))
           (t (mv-let (temp new-mt)
                      (x-linear-find-next-step (neighbors (car c) g)
                                               (cons (car c) stack)
                                               b g
                                               (mark (car c) mt))
                      (cond
                       ((eq temp 'failure)
                        (x-linear-find-next-step (cdr c) stack b g new-mt))
                       (t (mv temp mt)))))))
   :rule-classes
   ((:definition
     :controller-alist ((x-linear-find-next-step t nil nil t t))))))

(defthm uniqueness
  (equal (x-linear-find-next-step c stack b g mt)
         (linear-find-next-step c stack b g mt))
  :rule-classes nil
  :hints (("Goal" :induct (linear-find-next-step c stack b g mt))))

; ---------------------------------------------------------------------------
; The Relation to find-next-step

; I will prove that linear-find-next-step is find-next-step.  My
; strategy is two-fold.  First, I will introduce an intermediate
; concept, namely find-next-step-avoiding, which finds a simple path
; while avoiding all nodes in a FIXED table.  I will prove that both
; find-next-step and linear-find-next-step are equal to this function.
; The second aspect of my strategy is that in proving the relationship
; between linear-find-next-step and the version that fixes the mark
; table, I will define a relationship between tables that allows one
; to be substituted for another without changing the answer.

; Here is the version of the algorithm with the fixed table.

(defun find-next-step-avoiding (c stack b g mt)
  (declare (xargs :measure (measure c stack g)))
  (cond ((endp c) 'failure)
        ((member (car c) stack)
         (find-next-step-avoiding (cdr c) stack b g mt))
        ((member (car c) mt)
         (find-next-step-avoiding (cdr c) stack b g mt))
        ((equal (car c) b) (rev (cons b stack)))
        (t (let ((temp (find-next-step-avoiding (neighbors (car c) g)
                                                (cons (car c) stack)
                                                b g mt)))
             (if (eq temp 'failure)
                 (find-next-step-avoiding (cdr c) stack b g mt)
               temp)))))

(defun find-path-avoiding (a b g mt)
  (cond ((equal a b)
         (if (member a mt)
             'failure
           (list a)))
        (t (find-next-step-avoiding (neighbors a g)
                                    (list a)
                                    b g mt))))

; It is easy to prove that find-next-step is equal to the version with
; a fixed table, provided the fixed table is a subset of the stack.
; This will be the case when we consider the top-level entry into
; find-next-step versus linear-find-next-step.

(defthm step1
  (implies (subsetp mt stack)
           (equal (find-next-step-avoiding c stack b g mt)
                  (find-next-step c stack b g))))

; Note: The rule above is a bad rewrite rule if it could fire, because
; it eliminates the intermediate concept and puts us back in the
; situation we'd be in had we not introduced find-next-step-avoiding!
; But it won't fire because we don't know the subsetp hypothesis in
; the uses below.

; So we're left with step2, to prove that linear-find-next-step
; is find-next-step-avoiding.

; The following lemmas were discovered by using The Method, but
; required a lot of thinking.  I probably worked on this for about
; 8-12 hours.  I am not sure because it happened over several days.

; This lemma allows us to remove from the mark table anything that is
; already in the stack.

(defthm find-next-step-avoiding-cons
  (implies (member e stack)
           (equal (find-next-step-avoiding c stack b g (cons e mt))
                  (find-next-step-avoiding c stack b g mt))))

; Here is the key relationship between mark tables.  The following
; concept checks that all the new elements of new-mt, i.e., the ones
; not already in mt, are in no simple path to b (relative to stack)
; avoiding mt.

(defun pathlessp (new-mt stack b g mt)
  (cond ((endp new-mt) t)
        ((or (member (car new-mt) stack)
             (member (car new-mt) mt)
             (and (not (equal (car new-mt) b))
                  (equal (find-next-step-avoiding (neighbors (car new-mt) g)
                                                  (cons (car new-mt) stack)
                                                  b g mt)
                         'failure)))
         (pathlessp (cdr new-mt) stack b g mt))
        (t nil)))

; The next main stop is the lemma pathless-mt-substitution, below,
; which says that if new-mt and mt are in the pathless relationship,
; then find-next-step-avoiding returns equal results on them.  The
; lemmas between here and there are just The Method lemmas.

(defthm pathless-mt-substitution-lemma1
  (implies (and (pathlessp new-mt stack b g mt)
                (member e new-mt)
                (not (member e stack))
                (not (member e mt)))
           (equal (find-next-step-avoiding (neighbors e g)
                                           (cons e stack)
                                           b g mt)
                  'failure)))

(defthm find-next-step-avoiding-stack-extension
  (implies (and (equal (find-next-step-avoiding c stack1 b g mt)
                       'failure)
                (consp stack1)
                (subsetp stack1 stack2))
           (equal (find-next-step-avoiding c stack2 b g mt)
                  'failure))
  :hints (("Goal" :induct
           (list (find-next-step-avoiding c stack1 b g mt)
                 (find-next-step-avoiding c stack2 b g mt)))))

(defthm pathless-mt-substitution-lemma2
  (implies (pathlessp new-mt stack b g mt)
           (pathlessp new-mt (cons e stack)
                      b g mt)))

(defthm pathless-mt-substitution-lemma3
  (implies (and (not (member b mt))
                (not (member b stack))
                (member b new-mt))
           (not (PATHLESSP NEW-MT STACK b G MT))))

; So here's the promised result:

(defthm pathless-mt-substitution
  (implies (and (pathlessp new-mt stack b g mt)
                (subsetp mt new-mt))
           (equal (find-next-step-avoiding c stack b g new-mt)
                  (find-next-step-avoiding c stack b g mt))))

; It is not very useful as a rewrite rule, because of the free mt.  I
; will have to instantiate it manually sometimes.  However, the
; following corollary can be coded up to catch a common case.

(defthm pathless-mt-substitution-corollary
  (implies (and (equal (find-next-step-avoiding c stack b g new-mt)
                       'failure)
                (pathlessp new-mt stack b g mt)
                (subsetp mt new-mt))
           (equal (find-next-step-avoiding c stack b g mt)
                  'failure)))

; Pathlessp has two interesting general properties:  It is transitive
; and reflexive.

(defthm trans-pathlessp
  (implies (and (pathlessp beta stack b g alpha)
                (pathlessp alpha stack b g mt)
                (subsetp mt alpha))
           (pathlessp beta stack b g mt))
  :hints (("Goal" :induct (pathlessp beta stack b g alpha))))

(defthm pathlessp-x-x
  (implies (subsetp mt1 mt2)
           (pathlessp mt1 stack b g mt2)))

; Another neat fact is that the portion of the stack in mt is
; irrelevant to the success or failure of the search.

(defthm find-next-step-avoiding-non-failure-normalizer
  (implies (subsetp stack mt)
           (equal
            (equal (find-next-step-avoiding c (append ext stack) b g mt)
                   'failure)
            (equal (find-next-step-avoiding c ext b g mt)
                   'failure)))
  :rule-classes nil)

; This allows us to normalize calls of find-next-step-avoiding (and
; thus also of pathlessp) to replace the already marked nodes in the
; stack by nil.

(defthm find-next-step-avoiding-non-failure-normalizer-corollary
  (implies (and (syntaxp (not (equal stack ''nil)))
                (not (member d mt))
                (subsetp stack mt))
           (equal (equal (find-next-step-avoiding c (cons d stack) b g mt)
                         'failure)
                  (equal (find-next-step-avoiding c (list d) b g mt)
                         'failure)))
  :hints (("Goal" :use
           (:instance find-next-step-avoiding-non-failure-normalizer
                      (ext (list d))))))

(defthm pathlessp-normalizer
  (implies (and (syntaxp (not (equal stack ''nil)))
                (subsetp stack mt))
           (equal (pathlessp alpha stack b g mt)
                  (pathlessp alpha nil b g mt))))

; We need one other lemma, a simple corollary of the observation that
; linear-find-next-step extends the mark table.

(defthm linear-find-next-step-extends-mt-corollary-2
  (implies (member e mt)
           (member e (mv-nth 1 (linear-find-next-step c stack b g mt))))
  :hints (("Goal"
           :use (:instance linear-find-next-step-extends-mt)
           :in-theory (disable linear-find-next-step-extends-mt))))

; Ok, so here is step2.

; This is sort of like a mutual recursion.  We have to prove
; simultaneously that the first result of linear-find-next-step is
; find-next-step-avoiding, and we have to prove that the second result
; admits no new paths.  We can't prove the first without knowing the
; second because we need to use the pathless-mt-substitution trick to
; take care of the outer recursive call.  We can't prove the second
; first because pathlessp checks find-next-step-avoiding but the
; induction hypothesis we have will be about linear-find-next-step.
; So we have to prove them together.

(defthm step2
  (implies (subsetp stack mt)
           (and (equal (car (linear-find-next-step c stack b g mt))
                       (find-next-step-avoiding c stack b g mt))
                (pathlessp (mv-nth 1
                                   (linear-find-next-step c stack b g mt))
                           stack b g mt)))
  :hints
  (("Goal" :induct (linear-find-next-step c stack b g mt))
   ("Subgoal *1/4.2''"
    :use
    (:instance pathless-mt-substitution
               (new-mt (MV-NTH 1
                               (LINEAR-FIND-NEXT-STEP (NEIGHBORS c1 G)
                                                      (CONS c1 STACK)
                                                      B G (CONS c1 MT))))
               (c c2)
               (stack stack)
               (mt  mt)))))

; And so here are the two main results.

(defthm linear-find-path-is-find-path
  (equal (linear-find-path a b g)
         (find-path a b g)))

(defthm spec-of-linear-find-path
  (implies (and (graphp g)
                (nodep a g)
                (nodep b g)
                (path-from-to p a b g))
           (path-from-to (linear-find-path a b g) a b g))
  :hints (("Goal" :in-theory (disable linear-find-path
                                      find-path
                                      path-from-to))))

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
(include-book "fast-urewrite")
(include-book "fast-cache")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)



(defconst *rw.fast-crewrite-flag-sigma*
  ;; Substitutions used to generate the fast flag function's definition.
  (list (cons '(rw.urewrite ?x ?iffp ?control ?n)
              '(rw.fast-urewrite ?x ?iffp ?control ?n))
        (cons '(rw.crewrite-core$ ?x)
              '(rw.fast-flag-crewrite 'term assms ?x nil nil cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :iffp ?iffp)
              '(rw.fast-flag-crewrite 'term assms ?x nil nil cache ?iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :rlimit ?rlimit :cache ?cache)
              '(rw.fast-flag-crewrite 'term assms ?x nil nil ?cache iffp blimit ?rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :cache ?cache)
              '(rw.fast-flag-crewrite 'term assms ?x nil nil ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :cache ?cache :assms ?assms)
              '(rw.fast-flag-crewrite 'term ?assms ?x nil nil ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :iffp ?iffp :blimit ?blimit :anstack ?anstack :cache ?cache)
              '(rw.fast-flag-crewrite 'term assms ?x nil nil ?cache ?iffp ?blimit rlimit ?anstack control))
        (cons '(rw.crewrite-core-list$ ?x :iffp ?iffp)
              '(rw.fast-flag-crewrite 'list assms ?x nil nil cache ?iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core-list$ ?x :cache ?cache)
              '(rw.fast-flag-crewrite 'list assms ?x nil nil ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rule$ ?x ?rules)
              '(rw.fast-flag-crewrite 'rule assms ?x ?rules nil cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rules$ ?x ?rules)
              '(rw.fast-flag-crewrite 'rules assms ?x ?rules nil cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rules$ ?x ?rules :cache ?cache)
              '(rw.fast-flag-crewrite 'rules assms ?x ?rules nil ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-match$ ?x ?rules ?sigmas)
              '(rw.fast-flag-crewrite 'match assms ?x ?rules ?sigmas cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-matches$ ?x ?rules ?sigmas)
              '(rw.fast-flag-crewrite 'matches assms ?x ?rules ?sigmas cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-matches$ ?x ?rules ?sigmas :cache ?cache)
              '(rw.fast-flag-crewrite 'matches assms ?x ?rules ?sigmas ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyp$ ?x ?rules ?sigmas)
              '(rw.fast-flag-crewrite 'hyp assms ?x ?rules ?sigmas cache t blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyps$ ?x ?rules ?sigmas)
              '(rw.fast-flag-crewrite 'hyps assms ?x ?rules ?sigmas cache t blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyps$ ?x ?rules ?sigmas :cache ?cache)
              '(rw.fast-flag-crewrite 'hyps assms ?x ?rules ?sigmas ?cache t blimit rlimit anstack control))))


(defconst *rw.fast-crewrite-noflag-sigma*
  ;; Substitutions used to generate the flagless :definition rules
  (list (cons '(rw.urewrite ?x ?iffp ?control ?n)
              '(rw.fast-urewrite ?x ?iffp ?control ?n))
        (cons '(rw.crewrite-core$ ?x)
              '(rw.fast-crewrite-core assms ?x cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :iffp ?iffp)
              '(rw.fast-crewrite-core assms ?x cache ?iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :rlimit ?rlimit :cache ?cache)
              '(rw.fast-crewrite-core assms ?x ?cache iffp blimit ?rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :cache ?cache)
              '(rw.fast-crewrite-core assms ?x ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :cache ?cache :assms ?assms)
              '(rw.fast-crewrite-core ?assms ?x ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core$ ?x :iffp ?iffp :blimit ?blimit :anstack ?anstack :cache ?cache)
              '(rw.fast-crewrite-core assms ?x ?cache ?iffp ?blimit rlimit ?anstack control))
        (cons '(rw.crewrite-core-list$ ?x :iffp ?iffp)
              '(rw.fast-crewrite-core-list assms ?x cache ?iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-core-list$ ?x :cache ?cache)
              '(rw.fast-crewrite-core-list assms ?x ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rule$ ?x ?rules)
              '(rw.fast-crewrite-try-rule assms ?x ?rules cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rules$ ?x ?rules)
              '(rw.fast-crewrite-try-rules assms ?x ?rules cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-rules$ ?x ?rules :cache ?cache)
              '(rw.fast-crewrite-try-rules assms ?x ?rules ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-match$ ?x ?rules ?sigmas)
              '(rw.fast-crewrite-try-match assms ?x ?rules ?sigmas cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-matches$ ?x ?rules ?sigmas)
              '(rw.fast-crewrite-try-matches assms ?x ?rules ?sigmas cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-try-matches$ ?x ?rules ?sigmas :cache ?cache)
              '(rw.fast-crewrite-try-matches assms ?x ?rules ?sigmas ?cache iffp blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyp$ ?x ?rules ?sigmas)
              '(rw.fast-crewrite-relieve-hyp assms ?x ?rules ?sigmas cache blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyps$ ?x ?rules ?sigmas)
              '(rw.fast-crewrite-relieve-hyps assms ?x ?rules ?sigmas cache blimit rlimit anstack control))
        (cons '(rw.crewrite-relieve-hyps$ ?x ?rules ?sigmas :cache ?cache)
              '(rw.fast-crewrite-relieve-hyps assms ?x ?rules ?sigmas ?cache blimit rlimit anstack control))))


(defconst *rw.fast-crewrite-list*
  ;; This is hacky, but we need to switch to ftraces here.
  (ACL2::jared-rewrite *rw.crewrite-list*
                       (list (cons '(cons term1-trace others-traces)
                                   '(rw.ftraces (cons (rw.ftrace->rhs term1-trace)
                                                      (rw.ftraces->rhses others-traces))
                                                (fast-merge (rw.ftrace->fgoals term1-trace)
                                                            (rw.ftraces->fgoals others-traces))))
                             (cons '(rw.cresult nil cache nil)
                                   '(rw.cresult (rw.ftraces nil nil) cache nil)))))


(defconst *rw.fast-crewrite-hyps*
  ;; This is hacky, but we need to switch to ftraces here.
  (ACL2::jared-rewrite *rw.crewrite-hyps*
                       (list (cons '(cons hyp1-trace others-traces)
                                   '(rw.ftraces (cons (rw.ftrace->rhs hyp1-trace)
                                                      (rw.ftraces->rhses others-traces))
                                                (fast-merge (rw.ftrace->fgoals hyp1-trace)
                                                            (rw.ftraces->fgoals others-traces))))
                             (cons '(rw.hypresult ?successp nil ?cache ?limitedp)
                                   '(rw.hypresult ?successp (rw.ftraces nil nil) ?cache ?limitedp)))))



(ACL2::make-event
 (let ((sigma (ACL2::append *rw.fast-cache-sigma*
                            *rw.fast-assms-sigma*
                            *rw.fast-traces-sigma*
                            *rw.fast-crewrite-flag-sigma*)))
   `(encapsulate
     ()
     (acl2::set-ignore-ok t)
     (defun rw.fast-flag-crewrite (flag ;; which mode we are in (we're really 8 mutually recursive functions)
                                   assms ;; the current assumptions
                                   x ;; the term we are rewriting (or the hyp we are relieving)
                                   rule[s] ;; the rule (or list of rules) we want to try
                                   sigma[s] ;; the sigma (or sigma list) we want to try (once we've already chosen a rule)
                                   cache ;; rewrite cache to avoid repeated relieve-hyps from match-free
                                   iffp ;; t if we can use iff rules, nil if we can only use equal rules
                                   blimit ;; limit on backchaining depth (how hard may we try to relieving hyps?)
                                   rlimit ;; limit on successful rewrites (how many rules can we successively apply?)
                                   anstack ;; the ancestors stack (used to control backchaining; see ancestors.lisp)
                                   control ;; the rewriter control object (stores rules, definitions, etc.; see controlp.lisp)
                                   )
       (declare (xargs :guard (and (rw.fast-assmsp assms)
                                   (rw.fast-cachep cache)
                                   (booleanp iffp)
                                   (natp blimit)
                                   (natp rlimit)
                                   (rw.anstackp anstack)
                                   (rw.controlp control)
                                   (cond ((equal flag 'term)
                                          (logic.termp x))
                                         ((equal flag 'list)
                                          (logic.term-listp x))
                                         ((equal flag 'match)
                                          (and (logic.termp x)
                                               (rw.rulep rule[s])
                                               (or (equal (rw.rule->equiv rule[s]) 'equal)
                                                   (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                               (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                               (logic.sigmap sigma[s])
                                               (submapp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])))
                                         ((equal flag 'matches)
                                          (and (logic.termp x)
                                               (rw.rulep rule[s])
                                               (or (equal (rw.rule->equiv rule[s]) 'equal)
                                                   (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                               (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                               (logic.sigma-listp sigma[s])
                                               (submap-of-eachp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])))
                                         ((equal flag 'rule)
                                          (and (logic.termp x)
                                               (rw.rulep rule[s])))
                                         ((equal flag 'rules)
                                          (and (logic.termp x)
                                               (rw.rule-listp rule[s])))
                                         ((equal flag 'hyp)
                                          (and (rw.hypp x)
                                               (rw.rulep rule[s])
                                               (logic.sigmap sigma[s])))
                                         (t
                                          (and (equal flag 'hyps)
                                               (rw.hyp-listp x)
                                               (rw.rulep rule[s])
                                               (logic.sigmap sigma[s])))))
                       :verify-guards nil
                       :measure (cond ((or (equal flag 'term)
                                           (equal flag 'list))
                                       (four-nats-measure rlimit (nfix blimit) 4 (rank x)))
                                      ((or (equal flag 'rule)
                                           (equal flag 'rules))
                                       (four-nats-measure rlimit (nfix blimit) 3 (rank rule[s])))
                                      ((or (equal flag 'match)
                                           (equal flag 'matches))
                                       (four-nats-measure rlimit (nfix blimit) 2 (rank sigma[s])))
                                      (t
                                       (four-nats-measure rlimit (nfix blimit) 1 (rank x))))
                       :hints (("Goal" :in-theory (disable (:executable-counterpart ACL2::force))))))
       (cond ((equal flag 'term)
              ,(ACL2::jared-rewrite *rw.crewrite-core* sigma))
             ((equal flag 'list)
              ,(ACL2::jared-rewrite *rw.fast-crewrite-list* sigma))
             ((equal flag 'rule)
              ,(ACL2::jared-rewrite *rw.crewrite-rule* sigma))
             ((equal flag 'rules)
              ,(ACL2::jared-rewrite *rw.crewrite-rules* sigma))
             ((equal flag 'match)
              ,(ACL2::jared-rewrite *rw.crewrite-match* sigma))
             ((equal flag 'matches)
              ,(ACL2::jared-rewrite *rw.crewrite-matches* sigma))
             ((equal flag 'hyp)
              ,(ACL2::jared-rewrite *rw.crewrite-hyp* sigma))
             (t
              ,(ACL2::jared-rewrite *rw.fast-crewrite-hyps* sigma)))))))




(defsection fast-invoke-macros

  (defmacro rw.fast-crewrite-core$ (term &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.fast-flag-crewrite 'term ,assms ,term nil nil ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.fast-crewrite-core ,assms ,term ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.fast-crewrite-core-list$ (term-list &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.fast-flag-crewrite 'list ,assms ,term-list nil nil ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.fast-crewrite-core-list ,assms ,term-list ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.fast-crewrite-try-rule$ (term rule &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.fast-flag-crewrite 'rule ,assms ,term ,rule nil ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.fast-crewrite-try-rule ,assms ,term ,rule ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.fast-crewrite-try-rules$ (term rules &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.fast-flag-crewrite 'rules ,assms ,term ,rules nil ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.fast-crewrite-try-rules ,assms ,term ,rules ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.fast-crewrite-try-match$ (term rule sigma &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.fast-flag-crewrite 'match ,assms ,term ,rule ,sigma ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.fast-crewrite-try-match ,assms ,term ,rule ,sigma ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.fast-crewrite-try-matches$ (term rule sigmas &key flagp (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.fast-flag-crewrite 'matches ,assms ,term ,rule ,sigmas ,cache ,iffp ,blimit ,rlimit ,anstack ,control)
      `(rw.fast-crewrite-try-matches ,assms ,term ,rule ,sigmas ,cache ,iffp ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.fast-crewrite-relieve-hyp$ (hyp rule sigma &key flagp (assms 'assms) (cache 'cache) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.fast-flag-crewrite 'hyp ,assms ,hyp ,rule ,sigma ,cache t ,blimit ,rlimit ,anstack ,control)
      `(rw.fast-crewrite-relieve-hyp ,assms ,hyp ,rule ,sigma ,cache ,blimit ,rlimit ,anstack ,control)))

  (defmacro rw.fast-crewrite-relieve-hyps$ (hyps rule sigma &key flagp (assms 'assms) (cache 'cache) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
    (declare (xargs :guard (booleanp flagp)))
    (if flagp
        `(rw.fast-flag-crewrite 'hyps ,assms ,hyps ,rule ,sigma ,cache t ,blimit ,rlimit ,anstack ,control)
      `(rw.fast-crewrite-relieve-hyps ,assms ,hyps ,rule ,sigma ,cache ,blimit ,rlimit ,anstack ,control))))




(defsection fast-irrelevant-argument-reduction

  ;; Some of the functions do not use all the arguments here, so we provide
  ;; reduction theorems to show which arguments are irrelevant.

 (local (in-theory (disable (:executable-counterpart ACL2::force))))

 (defthmd rw.fast-flag-crewrite-of-term-reduction
   (equal (rw.fast-flag-crewrite 'term assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-core$ x :flagp t))
   :hints(("Goal"
           :expand ((rw.fast-flag-crewrite 'term assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.fast-crewrite-core$ x :flagp t)))))

 (defthmd rw.fast-flag-crewrite-of-list-reduction
   (equal (rw.fast-flag-crewrite 'list assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-core-list$ x :flagp t))
   :hints(("Goal"
           :expand ((rw.fast-flag-crewrite 'list assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.fast-crewrite-core-list$ x :flagp t)))))

 (defthmd rw.fast-flag-crewrite-of-rule-reduction
   (equal (rw.fast-flag-crewrite 'rule assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-try-rule$ x rule[s] :flagp t))
   :hints(("Goal"
           :expand ((rw.fast-flag-crewrite 'rule assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.fast-crewrite-try-rule$ x rule[s] :flagp t)))))

 (defthmd rw.fast-flag-crewrite-of-rules-reduction
   (equal (rw.fast-flag-crewrite 'rules assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-try-rules$ x rule[s] :flagp t))
   :hints(("Goal"
           :expand ((rw.fast-flag-crewrite 'rules assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.fast-crewrite-try-rules$ x rule[s] :flagp t)))))

 (defthmd rw.fast-flag-crewrite-of-hyp-reduction
   (equal (rw.fast-flag-crewrite 'hyp assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s] :flagp t))
   :hints(("Goal"
           :expand ((rw.fast-flag-crewrite 'hyp assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s] :flagp t)))))

 (defthmd rw.fast-flag-crewrite-of-hyps-reduction
   (equal (rw.fast-flag-crewrite 'hyps assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s] :flagp t))
   :hints(("Goal"
           :expand ((rw.fast-flag-crewrite 'hyps assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
                    (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s] :flagp t))))))




(defsection fast-flag-wrapper-functions

  ;; We now introduce wrappers for the various functions inside the nest.

  (definlined rw.fast-crewrite-core (assms x cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.fast-assmsp assms)
                                (logic.termp x)
                                (rw.fast-cachep cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.fast-crewrite-core$ x :flagp t))

  (definlined rw.fast-crewrite-core-list (assms x cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.fast-assmsp assms)
                                (logic.term-listp x)
                                (rw.fast-cachep cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.fast-crewrite-core-list$ x :flagp t))

  (definlined rw.fast-crewrite-try-rule (assms x rule[s] cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.fast-assmsp assms)
                                (logic.termp x)
                                (rw.rulep rule[s])
                                (rw.fast-cachep cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.fast-crewrite-try-rule$ x rule[s] :flagp t))

  (definlined rw.fast-crewrite-try-rules (assms x rule[s] cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.fast-assmsp assms)
                                (logic.termp x)
                                (rw.rule-listp rule[s])
                                (rw.fast-cachep cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.fast-crewrite-try-rules$ x rule[s] :flagp t))

  (definlined rw.fast-crewrite-try-match (assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.fast-assmsp assms)
                                (logic.termp x)
                                (rw.rulep rule[s])
                                (or (equal (rw.rule->equiv rule[s]) 'equal)
                                    (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                (logic.sigmap sigma[s])
                                (submapp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])
                                (rw.fast-cachep cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.fast-crewrite-try-match$ x rule[s] sigma[s] :flagp t))

  (definlined rw.fast-crewrite-try-matches (assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.fast-assmsp assms)
                                (logic.termp x)
                                (rw.rulep rule[s])
                                (or (equal (rw.rule->equiv rule[s]) 'equal)
                                    (and iffp (equal (rw.rule->equiv rule[s]) 'iff)))
                                (not (equal 'fail (logic.patmatch (rw.rule->lhs rule[s]) x nil)))
                                (logic.sigma-listp sigma[s])
                                (submap-of-eachp (logic.patmatch (rw.rule->lhs rule[s]) x nil) sigma[s])
                                (rw.fast-cachep cache)
                                (booleanp iffp)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.fast-crewrite-try-matches$ x rule[s] sigma[s] :flagp t))

  (definlined rw.fast-crewrite-relieve-hyp (assms x rule[s] sigma[s] cache blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.fast-assmsp assms)
                                (rw.hypp x)
                                (rw.rulep rule[s])
                                (logic.sigmap sigma[s])
                                (rw.fast-cachep cache)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s] :flagp t))

  (definlined rw.fast-crewrite-relieve-hyps (assms x rule[s] sigma[s] cache blimit rlimit anstack control)
    (declare (xargs :guard (and (rw.fast-assmsp assms)
                                (rw.hyp-listp x)
                                (rw.rulep rule[s])
                                (logic.sigmap sigma[s])
                                (rw.fast-cachep cache)
                                (natp blimit)
                                (natp rlimit)
                                (rw.anstackp anstack)
                                (rw.controlp control))
                    :verify-guards nil))
    (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s] :flagp t)))




(defsection rw.fast-flag-crewrite-removal

  ;; We now prove the elimination rules for flag-crewrite to transform it into
  ;; calls of these wrapper functions.

 (defthm rw.fast-flag-crewrite-of-term
   (equal (rw.fast-flag-crewrite 'term assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-core$ x))
   :hints(("Goal"
           :in-theory (enable rw.fast-crewrite-core)
           :use ((:instance rw.fast-flag-crewrite-of-term-reduction)))))

 (defthm rw.fast-flag-crewrite-of-list
   (equal (rw.fast-flag-crewrite 'list assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-core-list$ x))
   :hints(("Goal"
           :in-theory (enable rw.fast-crewrite-core-list)
           :use ((:instance rw.fast-flag-crewrite-of-list-reduction)))))

 (defthm rw.fast-flag-crewrite-of-rule
   (equal (rw.fast-flag-crewrite 'rule assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-try-rule$ x rule[s]))
   :hints(("Goal"
           :in-theory (enable rw.fast-crewrite-try-rule)
           :use ((:instance rw.fast-flag-crewrite-of-rule-reduction)))))

 (defthm rw.fast-flag-crewrite-of-rules
   (equal (rw.fast-flag-crewrite 'rules assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-try-rules$ x rule[s]))
   :hints(("Goal"
           :in-theory (enable rw.fast-crewrite-try-rules)
           :use ((:instance rw.fast-flag-crewrite-of-rules-reduction)))))

 (defthm rw.fast-flag-crewrite-of-match
   (equal (rw.fast-flag-crewrite 'match assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-try-match$ x rule[s] sigma[s]))
   :hints(("Goal" :in-theory (enable rw.fast-crewrite-try-match))))

 (defthm rw.fast-flag-crewrite-of-matches
   (equal (rw.fast-flag-crewrite 'matches assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-try-matches$ x rule[s] sigma[s]))
   :hints(("Goal" :in-theory (enable rw.fast-crewrite-try-matches))))

 (defthm rw.fast-flag-crewrite-of-hyp
   (equal (rw.fast-flag-crewrite 'hyp assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s]))
   :hints(("Goal"
           :in-theory (enable rw.fast-crewrite-relieve-hyp)
           :use ((:instance rw.fast-flag-crewrite-of-hyp-reduction)))))

 (defthm rw.fast-flag-crewrite-of-hyps
   (equal (rw.fast-flag-crewrite 'hyps assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
          (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s]))
   :hints(("Goal"
           :in-theory (enable rw.fast-crewrite-relieve-hyps)
           :use ((:instance rw.fast-flag-crewrite-of-hyps-reduction))))))




(ACL2::make-event
 (let ((sigma (ACL2::append *rw.fast-cache-sigma*
                            *rw.fast-assms-sigma*
                            *rw.fast-traces-sigma*
                            *rw.fast-crewrite-noflag-sigma*)))
   `(encapsulate
     ()
     (ACL2::set-ignore-ok t)

     (defthmd definition-of-rw.fast-crewrite-core
       (equal (rw.fast-crewrite-core$ x)
              ,(ACL2::jared-rewrite *rw.crewrite-core* sigma))
       :rule-classes :definition
       :hints(("Goal"
               :use ((:instance rw.fast-flag-crewrite (flag 'term))))))

     (defthmd definition-of-rw.fast-crewrite-core-list
       (equal (rw.fast-crewrite-core-list$ x)
              ,(ACL2::jared-rewrite *rw.fast-crewrite-list* sigma))
       :rule-classes :definition
       :hints(("Goal" :use ((:instance rw.fast-flag-crewrite (flag 'list))))))

     (defthmd definition-of-rw.fast-crewrite-try-rule
       (equal (rw.fast-crewrite-try-rule$ x rule[s])
              ,(ACL2::jared-rewrite *rw.crewrite-rule* sigma))
       :rule-classes :definition
       :hints(("Goal" :use ((:instance rw.fast-flag-crewrite (flag 'rule))))))

     (defthmd definition-of-rw.fast-crewrite-try-rules
       (equal (rw.fast-crewrite-try-rules$ x rule[s])
              ,(ACL2::jared-rewrite *rw.crewrite-rules* sigma))
       :rule-classes :definition
       :hints(("Goal" :use ((:instance rw.fast-flag-crewrite (flag 'rules))))))

     (defthmd definition-of-rw.fast-crewrite-try-match
       (equal (rw.fast-crewrite-try-match$ x rule[s] sigma[s])
              ,(ACL2::jared-rewrite *rw.crewrite-match* sigma))
       :rule-classes :definition
       :hints(("Goal" :use ((:instance rw.fast-flag-crewrite (flag 'match))))))

     (defthmd definition-of-rw.fast-crewrite-try-matches
       (equal (rw.fast-crewrite-try-matches$ x rule[s] sigma[s])
              ,(ACL2::jared-rewrite *rw.crewrite-matches* sigma))
       :rule-classes :definition
       :hints(("Goal" :use ((:instance rw.fast-flag-crewrite (flag 'matches))))))

     (defthmd definition-of-rw.fast-crewrite-relieve-hyp
       (equal (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s])
              ,(ACL2::jared-rewrite *rw.crewrite-hyp* sigma))
       :rule-classes :definition
       :hints(("Goal" :use ((:instance rw.fast-flag-crewrite (flag 'hyp))))))

     (defthmd definition-of-rw.fast-crewrite-relieve-hyps
       (equal (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s])
              ,(ACL2::jared-rewrite *rw.fast-crewrite-hyps* sigma))
       :rule-classes :definition
       :hints(("Goal" :use ((:instance rw.fast-flag-crewrite (flag 'hyps)))))))))



(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-crewrite-core))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-crewrite-core-list))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-crewrite-try-rule))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-crewrite-try-rules))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-crewrite-try-match))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-crewrite-try-matches))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-crewrite-relieve-hyp))))
(ACL2::theory-invariant (not (ACL2::active-runep '(:definition rw.fast-crewrite-relieve-hyps))))





(defthm rw.fast-crewrite-core-list-when-not-consp
   (implies (not (consp x))
            (equal (rw.fast-crewrite-core-list$ x)
                   (rw.cresult (rw.ftraces nil nil) cache nil)))
   :hints(("Goal" :in-theory (enable definition-of-rw.fast-crewrite-core-list))))

(defthm rw.fast-crewrite-core-list-of-cons
   (equal (rw.fast-crewrite-core-list$ (cons a x))
          (let* ((term1-rw      (rw.fast-crewrite-core$ a))
                 (term1-trace   (rw.cresult->data term1-rw))
                 (term1-cache   (rw.cresult->cache term1-rw))
                 (term1-limited (rw.cresult->alimitedp term1-rw))
                 (others-rw      (rw.fast-crewrite-core-list$ x :cache term1-cache))
                 (others-traces  (rw.cresult->data others-rw))
                 (others-cache   (rw.cresult->cache others-rw))
                 (others-limited (rw.cresult->alimitedp others-rw)))
            (rw.cresult (rw.ftraces (cons (rw.ftrace->rhs term1-trace)
                                          (rw.ftraces->rhses others-traces))
                                    (fast-merge (rw.ftrace->fgoals term1-trace)
                                                (rw.ftraces->fgoals others-traces)))
                        others-cache
                        (or term1-limited others-limited))))
   :hints(("Goal" :in-theory (enable definition-of-rw.fast-crewrite-core-list))))

(defun rw.fast-crewrite-list-induction (assms x cache iffp blimit rlimit anstack control)
   (declare (xargs :verify-guards nil))
   (if (consp x)
       (rw.fast-crewrite-list-induction assms (cdr x)
                                        (rw.cresult->cache (rw.fast-crewrite-core$ (car x)))
                                        iffp blimit rlimit anstack control)
     (list assms x cache iffp blimit rlimit anstack control)))

(defmacro rw.fast-crewrite-list-induction$ (x &key (assms 'assms) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
   `(rw.fast-crewrite-list-induction ,assms ,x ,cache ,iffp ,blimit ,rlimit ,anstack ,control))

(defthm len-of-rw.ftraces->rhses-of-rw.cresult->data-of-rw.fast-crewrite-core-list$
  (equal (len (rw.ftraces->rhses (rw.cresult->data (rw.fast-crewrite-core-list$ x))))
         (len x))
  :hints(("Goal"
          :induct (rw.fast-crewrite-list-induction$ x)
          :in-theory (disable (:executable-counterpart ACL2::force)))))

(defthm rw.fast-crewrite-try-rules-when-not-consp
   (implies (not (consp rule[s]))
            (equal (rw.fast-crewrite-try-rules$ x rule[s])
                   (rw.cresult nil cache nil)))
   :hints(("Goal" :in-theory (enable definition-of-rw.fast-crewrite-try-rules))))

(defthm rw.fast-crewrite-try-rules-of-cons
   (equal (rw.fast-crewrite-try-rules$ x (cons rule rules))
          (let* ((rule1-rw      (rw.fast-crewrite-try-rule$ x rule))
                 (rule1-trace   (rw.cresult->data rule1-rw))
                 (rule1-cache   (rw.cresult->cache rule1-rw))
                 (rule1-limited (rw.cresult->alimitedp rule1-rw)))
            (if rule1-trace
                rule1-rw
              (let* ((others-rw      (rw.fast-crewrite-try-rules$ x rules :cache rule1-cache))
                     (others-trace   (rw.cresult->data others-rw))
                     (others-cache   (rw.cresult->cache others-rw))
                     (others-limited (rw.cresult->alimitedp others-rw)))
                (if others-trace
                    others-rw
                  (rw.cresult nil others-cache (or rule1-limited others-limited)))))))
   :hints(("Goal" :in-theory (enable definition-of-rw.fast-crewrite-try-rules))))

(defun rw.fast-crewrite-try-rules-induction (assms x rule[s] cache iffp blimit rlimit anstack control)
   (declare (xargs :verify-guards nil))
   (if (consp rule[s])
       (rw.fast-crewrite-try-rules-induction assms x (cdr rule[s])
                                        (rw.cresult->cache (rw.fast-crewrite-try-rule$ x (car rule[s])))
                                        iffp blimit rlimit anstack control)
     (list assms x rule[s] cache iffp blimit rlimit anstack control)))

(defmacro rw.fast-crewrite-try-rules-induction$ (x &key (assms 'assms) (rule[s] 'rule[s]) (cache 'cache) (iffp 'iffp) (blimit 'blimit) (rlimit 'rlimit) (anstack 'anstack) (control 'control))
   `(rw.fast-crewrite-try-rules-induction ,assms ,x ,rule[s] ,cache ,iffp ,blimit ,rlimit ,anstack ,control))

(defthm rw.fast-crewrite-try-matches-when-not-consp
   (implies (not (consp sigma[s]))
            (equal (rw.fast-crewrite-try-matches$ x rule[s] sigma[s])
                   (rw.cresult nil cache nil)))
   :hints(("Goal" :in-theory (enable definition-of-rw.fast-crewrite-try-matches))))

(defthm rw.fast-crewrite-try-matches-of-cons
   (equal (rw.fast-crewrite-try-matches$ x rule[s] (cons sigma sigmas))
          (let* ((match1-rw      (rw.fast-crewrite-try-match$ x rule[s] sigma))
                 (match1-trace   (rw.cresult->data match1-rw))
                 (match1-cache   (rw.cresult->cache match1-rw))
                 (match1-limited (rw.cresult->alimitedp match1-rw)))
            (if match1-trace
                match1-rw
              (let* ((others-rw      (rw.fast-crewrite-try-matches$ x rule[s] sigmas :cache match1-cache))
                     (others-trace   (rw.cresult->data others-rw))
                     (others-cache   (rw.cresult->cache others-rw))
                     (others-limited (rw.cresult->alimitedp others-rw)))
                (if others-trace
                    others-rw
                  (rw.cresult nil others-cache (or match1-limited others-limited)))))))
   :hints(("Goal" :in-theory (enable definition-of-rw.fast-crewrite-try-matches))))


(defthm rw.fast-crewrite-relieve-hyps-when-not-consp
   (implies (not (consp x))
            (equal (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s])
                   (rw.hypresult t (rw.ftraces nil nil) cache nil)))
   :hints(("Goal" :in-theory (enable definition-of-rw.fast-crewrite-relieve-hyps))))

(defthm rw.fast-crewrite-relieve-hyps-of-cons
   (equal (rw.fast-crewrite-relieve-hyps$ (cons a x) rule[s] sigma[s])
          (let* ((hyp1-rw      (rw.fast-crewrite-relieve-hyp$ a rule[s] sigma[s]))
                 (hyp1-trace   (rw.cresult->data hyp1-rw))
                 (hyp1-cache   (rw.cresult->cache hyp1-rw))
                 (hyp1-limited (rw.cresult->alimitedp hyp1-rw)))
            (if (not hyp1-trace)
                (rw.hypresult nil (rw.ftraces nil nil) hyp1-cache hyp1-limited)
              (let* ((others-rw       (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s] :cache hyp1-cache))
                     (others-successp (rw.hypresult->successp others-rw))
                     (others-traces   (rw.hypresult->traces others-rw))
                     (others-cache    (rw.hypresult->cache others-rw))
                     (others-limited  (rw.hypresult->alimitedp others-rw)))
                (if others-successp
                    (rw.hypresult t (rw.ftraces (cons (rw.ftrace->rhs hyp1-trace)
                                                      (rw.ftraces->rhses others-traces))
                                                (fast-merge (rw.ftrace->fgoals hyp1-trace)
                                                            (rw.ftraces->fgoals others-traces)))
                                  others-cache nil)
                  (rw.hypresult nil (rw.ftraces nil nil) others-cache others-limited))))))
   :hints(("Goal" :in-theory (enable definition-of-rw.fast-crewrite-relieve-hyps))))

(defthm booleanp-of-rw.hypresult->successp-of-rw.fast-crewrite-relieve-hyps
   (equal (booleanp (rw.hypresult->successp (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s])))
          t)
   :hints(("Goal"
           :in-theory (disable (:executable-counterpart ACL2::force))
           :use ((:instance definition-of-rw.fast-crewrite-relieve-hyps)))))




(local (deftheory my-disables-for-extra-speed
          '(consp-when-memberp-of-logic.sigmap
            consp-when-memberp-of-logic.sigmap-alt
            consp-when-memberp-of-logic.sigma-atblp
            consp-when-memberp-of-logic.sigma-atblp-alt
            consp-when-memberp-of-logic.arity-tablep
            consp-when-memberp-of-logic.arity-tablep-alt
            consp-when-memberp-of-logic.callmapp
            consp-when-memberp-of-logic.callmapp-alt
            consp-when-memberp-of-logic.callmap-atblp
            consp-when-memberp-of-logic.callmap-atblp-alt
            consp-when-memberp-of-rw.cachemapp
            consp-when-memberp-of-rw.cachemapp-alt
            consp-when-memberp-of-none-consp
            consp-when-memberp-of-none-consp-alt
            consp-when-memberp-of-cons-listp
            consp-when-memberp-of-cons-listp-alt

            same-length-prefixes-equal-cheap

            car-when-not-consp
            cdr-when-not-consp
            consp-when-natp-cheap
            forcing-logic.groundp-of-logic.substitute
            consp-when-logic.lambdap-cheap
            consp-when-logic.functionp-cheap
            consp-when-nonempty-subset-cheap
            consp-when-memberp-cheap
            logic.substitute-when-malformed-cheap
            logic.constant-listp-when-not-consp
            subsetp-when-not-consp
            subsetp-when-not-consp-two
            cons-listp-when-not-consp
            none-consp-when-not-consp
            forcing-logic.substitute-of-empty-sigma
            not-equal-when-less
            trichotomy-of-<
            natp-of-len-free
            transitivity-of-<
            transitivity-of-<-three
            transitivity-of-<-two
            less-completion-left
            less-of-one-right)))

(local (in-theory (disable my-disables-for-extra-speed)))

(local (in-theory (disable zp min)))


(defthms-flag
  :shared-hyp (force (and (rw.fast-assmsp assms)
                          (rw.controlp control)
                          (rw.fast-cachep cache)))
  :thms ((term forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.ftracep (rw.cresult->data (rw.fast-crewrite-core$ x)))
                               t)))
         (term forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.fast-cachep (rw.cresult->cache (rw.fast-crewrite-core$ x)))
                               t)))

         (list forcing-rw.ftracesp-of-rw.cresult->data-of-rw.fast-crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.ftracesp (rw.cresult->data (rw.fast-crewrite-core-list$ x)))
                               t)))
         (list forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.fast-cachep (rw.cresult->cache (rw.fast-crewrite-core-list$ x)))
                               t)))

         (rule forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-try-rule
               (implies (force (and (rw.cresult->data (rw.fast-crewrite-try-rule$ x rule[s]))
                                    (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.ftracep (rw.cresult->data (rw.fast-crewrite-try-rule$ x rule[s])))
                               t)))
         (rule forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-try-rule
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.fast-cachep (rw.cresult->cache (rw.fast-crewrite-try-rule$ x rule[s])))
                               t)))

         (rules forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-try-rules
                (implies (force (and (rw.cresult->data (rw.fast-crewrite-try-rules$ x rule[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.ftracep (rw.cresult->data (rw.fast-crewrite-try-rules$ x rule[s])))
                                t)))
         (rules forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-try-rules
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.fast-cachep (rw.cresult->cache (rw.fast-crewrite-try-rules$ x rule[s])))
                                t)))

         (match forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-try-match
                (implies (force (and (rw.cresult->data (rw.fast-crewrite-try-match$ x rule[s] sigma[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.ftracep (rw.cresult->data (rw.fast-crewrite-try-match$ x rule[s] sigma[s])))
                                t)))
         (match forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-try-match
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.fast-cachep (rw.cresult->cache (rw.fast-crewrite-try-match$ x rule[s] sigma[s])))
                                t)))

         (matches forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-try-matches
                  (implies (force (and (rw.cresult->data (rw.fast-crewrite-try-matches$ x rule[s] sigma[s]))
                                       (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (equal (rw.ftracep (rw.cresult->data (rw.fast-crewrite-try-matches$ x rule[s] sigma[s])))
                                  t)))
         (matches forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-try-matches
                  (implies (force (and (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (equal (rw.fast-cachep (rw.cresult->cache (rw.fast-crewrite-try-matches$ x rule[s] sigma[s])))
                                  t)))

         (hyp forcing-rw.ftracep-of-rw.cresult->data-of-rw.fast-crewrite-relieve-hyp
              (implies (force (and (rw.cresult->data (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                   (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.ftracep (rw.cresult->data (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s])))
                              t)))
         (hyp forcing-rw.fast-cachep-of-rw.cresult->cache-of-rw.fast-crewrite-relieve-hyp
              (implies (force (and (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.fast-cachep (rw.cresult->cache (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s])))
                              t)))

         (t forcing-rw.ftracesp-of-rw.hypresult->traces-of-rw.fast-crewrite-relieve-hyps
            (implies (force (and (rw.hypresult->successp (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                 (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.ftracesp (rw.hypresult->traces (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s])))
                            t)))
         (t forcing-rw.fast-cachep-of-rw.hypresult->cache-of-rw.fast-crewrite-relieve-hyps
            (implies (force (and (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.fast-cachep (rw.hypresult->cache (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s])))
                            t))))
  :hints (("Goal"
           :induct (rw.fast-flag-crewrite flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
           :expand ((:free (iffp rlimit) (rw.fast-crewrite-core$ x))
                    (:free (iffp)        (rw.fast-crewrite-try-rule$ x rule[s]))
                    (:free ()            (rw.fast-crewrite-try-match$ x rule[s] sigma[s]))
                    (:free (blimit)      (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s])))
           :in-theory (disable forcing-lookup-of-logic.function-name
                               forcing-lookup-of-logic.function-name-free)
           :do-not-induct t)))

(verify-guards rw.fast-flag-crewrite
               :hints(("Goal"
                       :in-theory (disable subsetp-of-logic.term-vars-and-domain-of-logic.patmatch)
                       :use ((:instance subsetp-of-logic.term-vars-and-domain-of-logic.patmatch
                                        (x (rw.rule->lhs rule[s]))
                                        (y x)
                                        (sigma nil))))))



(defthms-flag

  ;; I am giant!

  ;; This is a big theorem because we effectively have to prove everything at
  ;; once.  The induction scheme takes up almost 5,000 lines when ACL2 prints
  ;; it.  It splits into 60 inductive subgoals, some of which then split into
  ;; thousands of subcases.

  ;; But don't complain.  I did a lot of work to introduce these "fast image"
  ;; functions and to get the rewriters to perfectly line up in this way.  My
  ;; original plan was to introduce an image relation, e.g., ftrace is related
  ;; to trace if their rhses are the same and ftrace's fgoals are a superset of
  ;; trace's.  If I had done that, then you'd be looking at a merged induction
  ;; scheme that walked both definitions simultaneously, and it would be even
  ;; worse than the horrific mess below.

  ;; If something breaks, the best thing to do is immediately go to the
  ;; CONCLUSION of the goal that has arisen.  Typically, this has the form
  ;; (equal lhs rhs).  Do a compare-windows on lhs and rhs to figure out the
  ;; first place they differ, and then try to think of why the different parts
  ;; should rewrite to the same thing.  If instead the conclusion is just a
  ;; term or a (NOT x) term, then look for the "related" term (i.e., about
  ;; rw.assumptions-trace instead of rw.fast-assumptions-trace) among the hyps,
  ;; and see if some rewrite rule can connect the two.

  ;; If this doesn't work, you'll have to dig through the hyps.  If you start
  ;; at the bottom of the hyps, it usually has the basic information about what
  ;; the main assumptions are.  That's a good place to start, because the upper
  ;; hyps will contain the numerous inductive hyps that you don't really want
  ;; to look at.

  :shared-hyp (force (and (rw.assmsp assms)
                          (rw.controlp control)
                          (rw.cachep cache)))

  :thms ((term rw.trace-fast-image-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.trace-fast-image (rw.cresult->data (rw.crewrite-core$ x)))
                               (rw.cresult->data (rw.fast-crewrite-core$ x
                                                  :assms (rw.assms-fast-image assms)
                                                  :cache (rw.cache-fast-image cache))))))

         (term rw.cache-fast-image-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.cache-fast-image (rw.cresult->cache (rw.crewrite-core$ x)))
                               (rw.cresult->cache (rw.fast-crewrite-core$ x
                                                   :assms (rw.assms-fast-image assms)
                                                   :cache (rw.cache-fast-image cache))))))

         (term rw.cresult->alimitedp-of-rw.crewrite-core
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)))
                        (equal (rw.cresult->alimitedp (rw.crewrite-core$ x))
                               (rw.cresult->alimitedp (rw.fast-crewrite-core$ x
                                                       :assms (rw.assms-fast-image assms)
                                                       :cache (rw.cache-fast-image cache))))))



         (list rw.trace-list-fast-image-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.trace-list-fast-image (rw.cresult->data (rw.crewrite-core-list$ x)))
                               (rw.cresult->data (rw.fast-crewrite-core-list$ x
                                                  :assms (rw.assms-fast-image assms)
                                                  :cache (rw.cache-fast-image cache))))))

         (list rw.cache-fast-image-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.cache-fast-image (rw.cresult->cache (rw.crewrite-core-list$ x)))
                               (rw.cresult->cache (rw.fast-crewrite-core-list$ x
                                                   :assms (rw.assms-fast-image assms)
                                                   :cache (rw.cache-fast-image cache))))))

         (list rw.cresult->alimitedp-of-rw.crewrite-core-list
               (implies (force (and (logic.term-listp x)
                                    (booleanp iffp)))
                        (equal (rw.cresult->alimitedp (rw.crewrite-core-list$ x))
                               (rw.cresult->alimitedp (rw.fast-crewrite-core-list$ x
                                                       :assms (rw.assms-fast-image assms)
                                                       :cache (rw.cache-fast-image cache))))))



         (rule rw.crewrite-try-rule-under-iff
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (iff (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                             (rw.cresult->data (rw.fast-crewrite-try-rule$ x rule[s]
                                                :assms (rw.assms-fast-image assms)
                                                :cache (rw.cache-fast-image cache))))))

         (rule rw.trace-fast-image-of-rw.crewrite-try-rule
               (implies (force (and (rw.cresult->data (rw.crewrite-try-rule$ x rule[s]))
                                    (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.trace-fast-image (rw.cresult->data (rw.crewrite-try-rule$ x rule[s])))
                               (rw.cresult->data (rw.fast-crewrite-try-rule$ x rule[s]
                                                  :assms (rw.assms-fast-image assms)
                                                  :cache (rw.cache-fast-image cache))))))

         (rule rw.cache-fast-image-of-rw.crewrite-try-rule
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.cache-fast-image (rw.cresult->cache (rw.crewrite-try-rule$ x rule[s])))
                               (rw.cresult->cache (rw.fast-crewrite-try-rule$ x rule[s]
                                                   :assms (rw.assms-fast-image assms)
                                                   :cache (rw.cache-fast-image cache))))))

         (rule rw.cresult->alimitedp-of-rw.crewrite-try-rule
               (implies (force (and (logic.termp x)
                                    (booleanp iffp)
                                    (rw.rulep rule[s])))
                        (equal (rw.cresult->alimitedp (rw.crewrite-try-rule$ x rule[s]))
                               (rw.cresult->alimitedp (rw.fast-crewrite-try-rule$ x rule[s]
                                                       :assms (rw.assms-fast-image assms)
                                                       :cache (rw.cache-fast-image cache))))))



         (rules rw.crewrite-try-rules-under-iff
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (iff (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                              (rw.cresult->data (rw.fast-crewrite-try-rules$ x rule[s]
                                                 :assms (rw.assms-fast-image assms)
                                                 :cache (rw.cache-fast-image cache))))))

         (rules rw.trace-fast-image-of-rw.crewrite-try-rules
                (implies (force (and (rw.cresult->data (rw.crewrite-try-rules$ x rule[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.trace-fast-image (rw.cresult->data (rw.crewrite-try-rules$ x rule[s])))
                                (rw.cresult->data (rw.fast-crewrite-try-rules$ x rule[s]
                                                  :assms (rw.assms-fast-image assms)
                                                  :cache (rw.cache-fast-image cache))))))

         (rules rw.cache-fast-image-of-rw.crewrite-try-rules
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.cache-fast-image (rw.cresult->cache (rw.crewrite-try-rules$ x rule[s])))
                                (rw.cresult->cache (rw.fast-crewrite-try-rules$ x rule[s]
                                                    :assms (rw.assms-fast-image assms)
                                                    :cache (rw.cache-fast-image cache))))))

         (rules rw.cresult->alimitedp-of-rw.crewrite-try-rules
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rule-listp rule[s])))
                         (equal (rw.cresult->alimitedp (rw.crewrite-try-rules$ x rule[s]))
                                (rw.cresult->alimitedp (rw.fast-crewrite-try-rules$ x rule[s]
                                                        :assms (rw.assms-fast-image assms)
                                                        :cache (rw.cache-fast-image cache))))))



         (match rw.crewrite-try-match-under-iff
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (iff (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                              (rw.cresult->data (rw.fast-crewrite-try-match$ x rule[s] sigma[s]
                                                 :assms (rw.assms-fast-image assms)
                                                 :cache (rw.cache-fast-image cache))))))

         (match rw.trace-fast-image-of-rw.crewrite-try-match
                (implies (force (and (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                     (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.trace-fast-image (rw.cresult->data (rw.crewrite-try-match$ x rule[s] sigma[s])))
                                (rw.cresult->data (rw.fast-crewrite-try-match$ x rule[s] sigma[s]
                                                   :assms (rw.assms-fast-image assms)
                                                   :cache (rw.cache-fast-image cache))))))

         (match rw.cache-fast-image-of-rw.crewrite-try-match
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.cache-fast-image (rw.cresult->cache (rw.crewrite-try-match$ x rule[s] sigma[s])))
                                (rw.cresult->cache (rw.fast-crewrite-try-match$ x rule[s] sigma[s]
                                                    :assms (rw.assms-fast-image assms)
                                                    :cache (rw.cache-fast-image cache))))))

         (match rw.cresult->alimitedp-of-rw.crewrite-try-match
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigmap sigma[s])))
                         (equal (rw.cresult->alimitedp (rw.crewrite-try-match$ x rule[s] sigma[s]))
                                (rw.cresult->alimitedp (rw.fast-crewrite-try-match$ x rule[s] sigma[s]
                                                        :assms (rw.assms-fast-image assms)
                                                        :cache (rw.cache-fast-image cache))))))



         (matches rw.crewrite-try-matches-under-iff
                  (implies (force (and (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (iff (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                (rw.cresult->data (rw.fast-crewrite-try-matches$ x rule[s] sigma[s]
                                                   :assms (rw.assms-fast-image assms)
                                                   :cache (rw.cache-fast-image cache))))))

         (matches rw.trace-fast-image-of-rw.crewrite-try-matches
                  (implies (force (and (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                       (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (equal (rw.trace-fast-image (rw.cresult->data (rw.crewrite-try-matches$ x rule[s] sigma[s])))
                                  (rw.cresult->data (rw.fast-crewrite-try-matches$ x rule[s] sigma[s]
                                                     :assms (rw.assms-fast-image assms)
                                                     :cache (rw.cache-fast-image cache))))))

         (matches rw.cache-fast-image-of-rw.crewrite-try-matches
                  (implies (force (and (logic.termp x)
                                       (booleanp iffp)
                                       (rw.rulep rule[s])
                                       (logic.sigma-listp sigma[s])))
                           (equal (rw.cache-fast-image (rw.cresult->cache (rw.crewrite-try-matches$ x rule[s] sigma[s])))
                                  (rw.cresult->cache (rw.fast-crewrite-try-matches$ x rule[s] sigma[s]
                                                      :assms (rw.assms-fast-image assms)
                                                      :cache (rw.cache-fast-image cache))))))

         (matches rw.cresult->alimitedp-of-rw.crewrite-try-matches
                (implies (force (and (logic.termp x)
                                     (booleanp iffp)
                                     (rw.rulep rule[s])
                                     (logic.sigma-listp sigma[s])))
                         (equal (rw.cresult->alimitedp (rw.crewrite-try-matches$ x rule[s] sigma[s]))
                                (rw.cresult->alimitedp (rw.fast-crewrite-try-matches$ x rule[s] sigma[s]
                                                        :assms (rw.assms-fast-image assms)
                                                        :cache (rw.cache-fast-image cache))))))



         (hyp rw.crewrite-relieve-hyp-under-iff
              (implies (force (and (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (iff (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                            (rw.cresult->data (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s]
                                               :assms (rw.assms-fast-image assms)
                                               :cache (rw.cache-fast-image cache))))))

         (hyp rw.trace-fast-image-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                                   (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.trace-fast-image (rw.cresult->data (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
                              (rw.cresult->data (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s]
                                                 :assms (rw.assms-fast-image assms)
                                                 :cache (rw.cache-fast-image cache))))))

         (hyp rw.cache-fast-image-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.cache-fast-image (rw.cresult->cache (rw.crewrite-relieve-hyp$ x rule[s] sigma[s])))
                              (rw.cresult->cache (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s]
                                                  :assms (rw.assms-fast-image assms)
                                                  :cache (rw.cache-fast-image cache))))))

         (hyp rw.cresult->alimitedp-of-rw.crewrite-relieve-hyp
              (implies (force (and (rw.hypp x)
                                   (rw.rulep rule[s])
                                   (logic.sigmap sigma[s])))
                       (equal (rw.cresult->alimitedp (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                              (rw.cresult->alimitedp (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s]
                                                      :assms (rw.assms-fast-image assms)
                                                      :cache (rw.cache-fast-image cache))))))



         (t rw.hypresult->successp-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                            (rw.hypresult->successp (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s]
                                                     :assms (rw.assms-fast-image assms)
                                                     :cache (rw.cache-fast-image cache))))))

         (t rw.trace-list-fast-image-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hypresult->successp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                                 (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.trace-list-fast-image (rw.hypresult->traces (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
                            (rw.hypresult->traces (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s]
                                                   :assms (rw.assms-fast-image assms)
                                                   :cache (rw.cache-fast-image cache))))))

         (t rw.cache-fast-image-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.cache-fast-image (rw.hypresult->cache (rw.crewrite-relieve-hyps$ x rule[s] sigma[s])))
                            (rw.hypresult->cache (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s]
                                                  :assms (rw.assms-fast-image assms)
                                                  :cache (rw.cache-fast-image cache))))))

         (t rw.hypresult->alimitedp-of-rw.crewrite-relieve-hyps
            (implies (force (and (rw.hyp-listp x)
                                 (rw.rulep rule[s])
                                 (logic.sigmap sigma[s])))
                     (equal (rw.hypresult->alimitedp (rw.crewrite-relieve-hyps$ x rule[s] sigma[s]))
                            (rw.hypresult->alimitedp (rw.fast-crewrite-relieve-hyps$ x rule[s] sigma[s]
                                                      :assms (rw.assms-fast-image assms)
                                                      :cache (rw.cache-fast-image cache)))))))

  :hints (("Goal"
           :induct (rw.flag-crewrite flag assms x rule[s] sigma[s] cache iffp blimit rlimit anstack control)
           :expand ((:free (iffp rlimit) (rw.fast-crewrite-core$ x
                                                                 :assms (rw.assms-fast-image assms)
                                                                 :cache (rw.cache-fast-image cache)))
                    (:free (iffp)        (rw.fast-crewrite-try-rule$ x rule[s]
                                                                 :assms (rw.assms-fast-image assms)
                                                                 :cache (rw.cache-fast-image cache)))
                    (:free ()            (rw.fast-crewrite-try-match$ x rule[s] sigma[s]
                                                                 :assms (rw.assms-fast-image assms)
                                                                 :cache (rw.cache-fast-image cache)))
                    (:free (blimit)      (rw.fast-crewrite-relieve-hyp$ x rule[s] sigma[s]
                                                                 :assms (rw.assms-fast-image assms)
                                                                 :cache (rw.cache-fast-image cache)))
                    ;; ---
                    (:free (iffp rlimit) (rw.crewrite-core$ x))
                    (:free (iffp)        (rw.crewrite-try-rule$ x rule[s]))
                    (:free ()            (rw.crewrite-try-match$ x rule[s] sigma[s]))
                    (:free (blimit)      (rw.crewrite-relieve-hyp$ x rule[s] sigma[s]))
                    )
           :in-theory (e/d (rw.trace-fast-image-equivalence-lemmas
                            rw.fast-weakening-trace)
                           (forcing-lookup-of-logic.function-name
                            forcing-lookup-of-logic.function-name-free))
           :do-not-induct t
           )))



(defthm rw.ftrace->rhs-of-rw.fast-crewrite-core
  (implies (force (and (logic.termp x)
                       (booleanp iffp)
                       (rw.assmsp assms)
                       (rw.controlp control)
                       (rw.cachep cache)))
           (equal (rw.ftrace->rhs (rw.cresult->data (rw.fast-crewrite-core$ x
                                                     :assms (rw.assms-fast-image assms)
                                                     :cache (rw.cache-fast-image cache))))
                  (rw.trace->rhs (rw.cresult->data (rw.crewrite-core$ x)))))
  :hints(("Goal"
          :in-theory (disable rw.trace-fast-image-of-rw.crewrite-core)
          :use ((:instance rw.trace-fast-image-of-rw.crewrite-core)))))


#||

;; As in crewrite, this is no longer necessary...

(defund rw.aux-fast-crewrite (assms x cache iffp blimit rlimit control n)
  (declare (xargs :guard (and (rw.fast-assmsp assms)
                              (logic.termp x)
                              (rw.fast-cachep cache)
                              (rw.controlp control)
                              (booleanp iffp)
                              (natp blimit)
                              (natp rlimit)
                              (natp n))
                  :measure (nfix n)
                  :verify-guards nil))
  (let* ((pass1-rw    (rw.fast-crewrite-core assms x cache iffp blimit rlimit nil control))
         (pass1-trace (rw.cresult->data pass1-rw))
         (pass1-cache (rw.cresult->cache pass1-rw)))
    (cond ((equal x (rw.ftrace->rhs pass1-trace))
           ;; Originally, we instead checked if the method was 'fail.  But when
           ;; we started to develop fast-crewrite, we adopted the above approach
           ;; instead.
           ;;
           ;; This gives us a wonderful property: our rewriter never looks at
           ;; the method of a trace.  Because of this, we can omit the method
           ;; from fast-traces.  (The method is still needed for regular traces
           ;; because of the trace compilers.)
           ;;
           ;; This also allows further optimization.  For instance, the method
           ;; of (rw.transitivity-trace x y) might be 'fail or 'transitivity,
           ;; but to compute this we must have the lhs of x to compare against
           ;; the lhs of y.  By obviating the method computation, we can (1)
           ;; omit lhses from fast-traces entirely, and (2) eliminate the
           ;; overhead of these equality checks.
           pass1-trace)

          ((zp n)
           ;; We cannot further simplify becuase we have run out of steps.
           (ACL2::prog2$ (ACL2::cw "[rw.fast-crewrite] Warning: ran out of rewriting steps.~%")
                         pass1-trace))

          (t
           ;; Perhaps we can simplify it further?
           (rw.fast-transitivity-trace pass1-trace
                                       (rw.aux-fast-crewrite assms (rw.ftrace->rhs pass1-trace) pass1-cache iffp
                                                             blimit rlimit control (- n 1)))))))

(defthm rw.ftracep-of-rw.aux-fast-crewrite
  (implies (force (and (rw.fast-assmsp assms)
                       (rw.fast-cachep cache)
                       (rw.controlp control)
                       (booleanp iffp)
                       (logic.termp x)
                   ))
           (equal (rw.ftracep (rw.aux-fast-crewrite assms x cache iffp blimit rlimit control n))
                  t))
  :hints(("Goal" :in-theory (enable rw.aux-fast-crewrite))))

(defthm rw.trace-fast-image-of-rw.aux-crewrite
  (implies (force (and (logic.termp x)
                       (booleanp iffp)
                       (rw.assmsp assms)
                       (rw.cachep cache)
                       (rw.controlp control)))
           (equal (rw.trace-fast-image (rw.aux-crewrite assms x cache iffp blimit rlimit control n))
                  (rw.aux-fast-crewrite (rw.assms-fast-image assms)
                                        x
                                        (rw.cache-fast-image cache)
                                        iffp blimit rlimit control n)))
  :hints(("Goal" :in-theory (enable rw.aux-crewrite
                                    rw.aux-fast-crewrite))))


||#


(defund rw.fast-crewrite (assms x iffp blimit rlimit control n)
  (declare (xargs :guard (and (rw.fast-assmsp assms)
                              (logic.termp x)
                              (booleanp iffp)
                              (natp blimit)
                              (natp rlimit)
                              (rw.controlp control)
                              (natp n))
                  :verify-guards nil)
           (ignore n))
  ;; Old code:
  ;; (rw.aux-fast-crewrite assms x (rw.fast-empty-cache) iffp blimit rlimit control n))
  ;; New code:
  (let ((result (rw.fast-crewrite-core assms x (rw.fast-empty-cache) iffp blimit rlimit nil control)))
    (ACL2::prog2$
     (ACL2::flush-hons-get-hash-table-link (rw.cresult->cache result))
     (rw.cresult->data result))))

(defthm rw.ftracep-of-rw.fast-crewrite
  (implies (force (and (rw.fast-assmsp assms)
                       (rw.controlp control)
                       (booleanp iffp)
                       (logic.termp x)))
           (equal (rw.ftracep (rw.fast-crewrite assms x iffp blimit rlimit control n))
                  t))
  :hints(("Goal" :in-theory (enable rw.fast-crewrite))))

(defthm rw.trace-fast-image-of-rw.crewrite
  (implies (force (and (logic.termp x)
                       (booleanp iffp)
                       (rw.assmsp assms)
                       (rw.controlp control)))
           (equal (rw.trace-fast-image (rw.crewrite assms x iffp blimit rlimit control n))
                  (rw.fast-crewrite (rw.assms-fast-image assms)
                                    x iffp blimit rlimit control n)))
  :hints(("Goal" :in-theory (enable rw.crewrite
                                    rw.fast-crewrite))))

(defthm rw.ftrace->rhs-of-rw.fast-crewrite
  (implies (force (and (logic.termp x)
                       (booleanp iffp)
                       (rw.assmsp assms)
                       (rw.controlp control)))
           (equal (rw.ftrace->rhs (rw.fast-crewrite (rw.assms-fast-image assms) x iffp blimit rlimit control n))
                  (rw.trace->rhs (rw.crewrite assms x iffp blimit rlimit control n))))
  :hints(("Goal"
          :in-theory (disable rw.trace-fast-image-of-rw.crewrite)
          :use ((:instance rw.trace-fast-image-of-rw.crewrite)))))

(defthm rw.ftrace->fgoals-of-rw.fast-crewrite
  (implies (force (and (logic.termp x)
                       (booleanp iffp)
                       (rw.assmsp assms)
                       (rw.controlp control)))
           (equal (rw.ftrace->fgoals (rw.fast-crewrite (rw.assms-fast-image assms) x iffp blimit rlimit control n))
                  (rw.collect-forced-goals (rw.crewrite assms x iffp blimit rlimit control n))))
  :hints(("Goal"
          :in-theory (disable rw.trace-fast-image-of-rw.crewrite)
          :use ((:instance rw.trace-fast-image-of-rw.crewrite)))))

(verify-guards rw.fast-crewrite-core)
(verify-guards rw.fast-crewrite)

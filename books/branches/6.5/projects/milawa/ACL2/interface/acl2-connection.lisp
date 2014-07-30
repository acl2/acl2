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
(include-book "core")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


;; Goal checking
;;
;; Since our tactic harness is inside ACL2, we can ask ACL2 if it believes the
;; goals are true using (%check).  Of course, this will only work if all the
;; functions involved are already defined inside of ACL2.

(defun %check-goal (goal)
  (declare (xargs :mode :program))
  `(ACL2::make-event (ACL2::mv-let (erp val ACL2::state)
                                   (ACL2::thm (or ,@goal))
                                   (declare (ignore erp val))
                                   (ACL2::value '(ACL2::value-triple :invisible)))))

(defun %aux-check-goals (goals n)
  (declare (xargs :mode :program))
  (if (consp goals)
      (list* `(ACL2::value-triple (ACL2::cw "Checking goal ~x0~%" ',n))
             (%check-goal (car goals))
             (%aux-check-goals (cdr goals) (+ 1 n)))
    nil))

(defun %check-goals (goals)
  (declare (xargs :mode :program))
  `(ACL2::encapsulate () ,@(%aux-check-goals goals 1)))

(defmacro %check ()
  ;; Check if ACL2 believes the goals are theorems.
  `(ACL2::make-event (%check-goals (tactic.harness->goals (ACL2::w ACL2::state)))))



;; Autoadmitting Functions
;;
;; We can look up a function's definition in the ACL2 world, convert it into a
;; Milawa-usable form, and submit it as a Milawa definition.  This won't work
;; unless all the functions it calls are already in Milawa, etc., but it's
;; awfully handy.

(defun ACL2::get-untranslated-defun (name world)
  (declare (xargs :mode :program))
  (let* ((ev-world (ACL2::decode-logical-name name world)))
    (ACL2::access-event-tuple-form (ACL2::cddar ev-world))))

(defun ACL2::get-measure (name world)
  (declare (xargs :mode :program))
  (let* ((justification (acl2::fgetprop name 'acl2::justification nil world)))
    (and justification
         (ACL2::access ACL2::justification justification :measure))))

(defun find-syntax-defun (name syntax-defuns)
  (declare (xargs :mode :program))
  (if (consp syntax-defuns)
      (if (equal name (second (car syntax-defuns)))
          (car syntax-defuns)
        (find-syntax-defun name (cdr syntax-defuns)))
    nil))

(defun %autoadmit-fn (name world)
  (declare (xargs :mode :program))
  ;; What about :export support?  We should be looking for that instead.
  (let* ((syntax-defuns  (ACL2::get-syntax-defun-entries world))
         (this-defun     (find-syntax-defun name syntax-defuns))
         ;; (untranslated-defun (ACL2::get-untranslated-defun name world))
         ;; (real-name      (ACL2::deref-macro-name name world))
         (measure        (ACL2::get-measure name world))
         ;; (formals        (third untranslated-defun))
         (formals        (third this-defun))
         ;; (body           (car (ACL2::last untranslated-defun))))
         (body           (fourth this-defun)))
    (if measure
        `(defsection ,name
           (%defun ,name ,formals
                   ;; ,(ACL2::clean-up-body (annhialate-declarations body))
                   ,body
                   :measure ,measure)
           (local (%auto))
           (%admit))
      `(defsection ,name
         (%defun ,name ,formals
                 ;; ,(ACL2::clean-up-body (annhialate-declarations body)))
                 ,body)
         (%admit)))))

(defmacro %autoadmit (name)
  `(ACL2::make-event (%autoadmit-fn ',name (ACL2::w ACL2::state))))



;; Automatic "outside-in" rule creation
;;
;; The rule (car (cons x y)) = x is a perfect example of a good outside-in
;; rule because it lets us throw away "y" before we even look at it.  I go
;; ahead and generate an outside-in rule from ACL2 rules when:
;;
;;   1. The right-hand side "never increases a variable"
;;   2. There are no syntaxp restrictions, and
;;   3. There are no hypotheses.
;;
;; At one time I also prohibited rules that repeated a variable in their lhs,
;; such as (subsetp x x) = t, under the theory that we would want to give both
;; sides a chance to canonicalize first.  But since we're keeping the
;; inside-out version too, I think this is not really much of a problem.
;;
;; Criteria #1 is the main issue.  The whole point of outside-in rules is that
;; they'll allow us to avoid rewriting parts of terms by throwing away some
;; variable that they matched.  And we don't want to introduce duplicates,
;; e.g., (foo x y (bar x z)) = (baz z z) is probably a bad outside-in rule
;; since if "z" is large then we might have blown up the term considerably.
;; Maybe it makes sense to break this rule when we "know" that z is usually
;; small, but for automatic outside-in rule introduction, I'm not bothering
;; with that.
;;
;; At one time, I also require that at least one variable was decreased.  But
;; now I don't require this, since it allows rules like (iff x nil) = (not x)
;; to be made outside-rules, which I think probably helps canonicalize things.
;;
;; Criteria #2 is in place because often syntaxp rules are used to break
;; canonical forms, e.g., to left-associate (+ a (+ b c)) when a,b are
;; constants.  We think it's unlikely that they'll be constants before we
;; rewrite them.  Moreover, it seems like a reasonable expectation on the
;; part of the syntaxp writer is that their matches are already in
;; canonical form.
;;
;; Criteria #3 is probably overly restrictive.  Basically we don't want to
;; introduce huge complicated hyps by instantiating their variables with big
;; expressions.  It might pay off to investigate relaxing this somewhat,
;; especially given our caching mechanism.

(defthm forcing-mapp-of-clean-update
  (implies (force (mapp map))
           (equal (mapp (clean-update key val map))
                  t))
  :hints(("Goal" :in-theory (e/d (clean-update)
                                 (rw.theory-mapp-of-clean-update)))))

(defund rw.flag-count-variables (flag x acc)
  ;; Create a map from variable names to their number of occurrences in a term,
  ;; x.
  (declare (xargs :guard (and (if (equal flag 'term)
                                  (logic.termp x)
                                (logic.term-listp x))
                              (mapp acc))
                  :verify-guards nil))
  (if (equal flag 'term)
      (cond ((logic.constantp x) acc)
            ((logic.variablep x) (clean-update x (+ 1 (cdr (lookup x acc))) acc))
            ((logic.functionp x) (rw.flag-count-variables 'list (logic.function-args x) acc))
            ((logic.lambdap x)   (rw.flag-count-variables 'list (logic.lambda-actuals x) acc))
            (t acc))
    (if (consp x)
        (rw.flag-count-variables 'list (cdr x)
                                 (rw.flag-count-variables 'term (car x) acc))
      acc)))

(defthm forcing-mapp-of-rw.flag-count-variables
  (implies (force (mapp acc))
           (equal (mapp (rw.flag-count-variables flag x acc))
                  t))
  :hints(("Goal" :in-theory (enable rw.flag-count-variables))))

(verify-guards rw.flag-count-variables)

(definlined rw.count-variables (x)
  (declare (xargs :guard (logic.termp x)))
  (rw.flag-count-variables 'term x nil))

(definlined rw.count-variables-list (x)
  (declare (xargs :guard (logic.term-listp x)))
  (rw.flag-count-variables 'list x nil))

(defthm mapp-of-rw.count-variables
  (equal (mapp (rw.count-variables x))
         t)
  :hints(("Goal" :in-theory (enable rw.count-variables))))

(defund rw.no-count-increases-aux (dom x y)
  ;; For all the keys listed in domain, is the corresponding value in y never
  ;; greater than the corresponding value in x?  I.e., "did no variables increase?"
  (declare (xargs :guard (and (mapp x)
                              (mapp y))))
  (if (consp dom)
      (and (<= (cdr (lookup (car dom) y))
               (cdr (lookup (car dom) x)))
           (rw.no-count-increases-aux (cdr dom) x y))
    t))

(definlined rw.no-count-increases (x y)
  ;; For all keys in x, is the corresponding value in y never greater than the
  ;; corresponding value in x?
  (declare (xargs :guard (and (mapp x)
                              (mapp y))))
  (rw.no-count-increases-aux (fast-domain$ x nil) x y))

(defund rw.some-count-decreases-aux (dom x y)
  ;; For some key listed in domain, is the corresponding value in y smaller
  ;; than the corresponding value in x?  I.e., "did some variable decrease?"
  (declare (xargs :guard (and (mapp x)
                              (mapp y))))
  (if (consp dom)
      (or (< (cdr (lookup (car dom) y))
             (cdr (lookup (car dom) x)))
          (rw.some-count-decreases-aux (cdr dom) x y))
    nil))

(definlined rw.some-count-decreases (x y)
  (declare (xargs :guard (and (mapp x)
                              (mapp y))))
  (rw.some-count-decreases-aux (fast-domain$ x nil) x y))

(defund rw.looks-good-for-outside-inp (rule)
  ;; Would we like rule to be an outside-in rule as well?
  (declare (xargs :guard (rw.rulep rule)))
  (and (equal (rw.rule->type rule) 'inside)
       (not (rw.rule->syntax rule))
       (not (rw.rule->hyps rule))
       (let ((lhsmap (rw.count-variables (rw.rule->lhs rule)))
             (rhsmap (rw.count-variables (rw.rule->rhs rule))))
         (and (subsetp (domain rhsmap) (domain lhsmap)) ;; no new vars please
              ;; we don't require this anymore.
              ;; (rw.some-count-decreases lhsmap rhsmap) not any more.
              (rw.no-count-increases lhsmap rhsmap)))))









;; Translating Rewrite Rules
;;
;; Our first step is to convert the rule's hypotheses into hypp's for Milawa.
;; This is somewhat involved:
;;
;;   (1) ACL2 embeds "force" inside the term; we have a separate field in the
;;       hypp structure for this.
;;   (2) Some ACL2 hyps are syntaxp hyps; we do not consider these to be hyps
;;       and store them in a separate part of the rule.
;;   (3) ACL2 embeds the backchain limits for the hyps in a separate list,
;;       while we store them inside each hyp.
;;
;; We may also need to create additional syntaxp hyps from the loop-stoppers
;; of a rule.

(defun make-force-list (x)
  (declare (xargs :mode :program))
  ;; We are given a list of acl2-hyps as terms.  We create tuples of the form
  ;; (forcep term) as follows:
  ;;    (force a) --> (t a)
  ;;    a         --> (nil a)
  (if (consp x)
      (let ((term (car x)))
        (if (and (consp term)
                 (equal (car term) 'ACL2::force))
            (cons (list t (second term))
                  (make-force-list (cdr x)))
          (cons (list nil term)
                (make-force-list (cdr x)))))
    nil))

(defun make-syntax-list (x)
  (declare (xargs :mode :program))
  ;; X is a list of (forcep term) tuples.  We create tuples of the form
  ;; (syntaxp forcep term) as follows:
  ;;   (forcep (syntaxp a)) => (t   forcep a*)
  ;;   (forcep a)           => (nil forcep a)
  ;; Where a* is the "corrected" version of a.  That is, a might include
  ;; calls of ACL2::quotep, which does not exist in Milawa and must be
  ;; replaced with MILAWA::logic.constantp.
  (if (consp x)
      (let* ((entry  (car x))
             (forcep (first entry))
             (term   (second entry)))
        (if (and (consp term)
                 (equal (car term) 'ACL2::synp))
            ;; The hyp is (synp vars form (quote term))
            (let* ((syn-term   (second (fourth term)))
                   (fix-quotep (ACL2::subst 'logic.constantp 'ACL2::quotep syn-term)))
              (cons (list t forcep fix-quotep)
                    (make-syntax-list (cdr x))))
          ;; This isn't a syntax hyp.
          (cons (list nil forcep term)
                (make-syntax-list (cdr x)))))
    nil))

(defun insert-backchain-limits (x blimits)
  (declare (xargs :mode :program))
  ;; X is a list of (syntaxp forcep term) tuples
  ;; Blimits is the :backchain-limit-lst from the ACL2 rule
  ;; We add the blimit to each hyp, creating tuples of the form (blimit syntaxp forcep term)
  ;; Each blimit is either nil (for no limit) or a number.
  (if (consp x)
      (cons (cons (car blimits) (car x))
            (insert-backchain-limits (cdr x) (cdr blimits)))
    nil))

(defun collect-semantic-hyps (x)
  (declare (xargs :mode :program))
  ;; X is a list of (limit syntaxp forcep term) tuples.  We build the hypp structures for all
  ;; of the non-syntaxp hyps.
  (if (consp x)
      (let ((limit   (first (car x)))
            (syntaxp (second (car x)))
            (forcep  (third (car x)))
            (term    (fourth (car x))))
        (if syntaxp
            (collect-semantic-hyps (cdr x))
          (cons (%hyp-fn term (if forcep 'weak nil) limit)
                (collect-semantic-hyps (cdr x)))))
    nil))

(defun collect-syntax-hyps (x)
  (declare (xargs :mode :program))
  ;; X is a list of (limit syntaxp forcep term) tuples.  We collect only the
  ;; terms from all the entries with valid syntaxp pairs.
  (if (consp x)
      (let ((syntaxp (second (car x)))
            (term    (fourth (car x))))
        (if syntaxp
            (cons term
                  (collect-syntax-hyps (cdr x)))
          (collect-syntax-hyps (cdr x))))
    nil))

(defun create-loop-stoppers (stoppers)
  (declare (xargs :mode :program))
  ;; Stoppers are a list of (x y . fns) objects.  We create a list of
  ;; (logic.term-< y x) entries.
  (if (consp stoppers)
      (let ((x (first (car stoppers)))
            (y (second (car stoppers))))
        (cons (logic.function 'logic.term-< (list y x))
              (create-loop-stoppers (cdr stoppers))))
    nil))

(defun create-rule-from-rewrite-entry (name entry)
  (declare (xargs :mode :program))
  ;; We return (enabledp . milawa-rule) for an ACL2 rewrite rule entry.
  (let* ((hyps                (third (lookup :hyps entry)))
         (lhs                 (third (lookup :lhs entry)))
         (rhs                 (third (lookup :rhs entry)))
         (equiv               (second (lookup :equiv entry)))
         (backchain-limit-lst (second (lookup :backchain-limit-lst entry)))
         (loop-stopper        (second (lookup :loop-stopper entry)))
         (enabledp            (second (lookup :enabledp entry)))
         (hypmap              (insert-backchain-limits (make-syntax-list (make-force-list hyps))
                                                       backchain-limit-lst))
         (milawa-hyps         (collect-semantic-hyps hypmap))
         (syntax              (revappend (create-loop-stoppers loop-stopper)
                                         (collect-syntax-hyps hypmap))))
    (cons enabledp (%rule-fn name 'inside milawa-hyps lhs rhs equiv syntax))))





;; Translating Rule-Classes Nil Rules
;;

(defun annhialate-forces (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (if (and (equal (first x) 'ACL2::force)
               (tuplep 2 x))
          (annhialate-forces (second x))
        (cons (annhialate-forces (car x))
              (annhialate-forces (cdr x))))
    x))

(defun create-rule-from-rule-classes-nil (name entry)
  (declare (xargs :mode :program))
  ;; We return (enabledp . milawa-rule) for an ACL2 :rule-classes nil entry.
  (let* ((thm (annhialate-forces (third (lookup :theorem entry)))))
    (cond ((equal (car thm) 'implies)
           ;; We know implies is boolean, so we can cheat and use equal as the
           ;; equivalence relation.  This turned out to be better than parsing
           ;; out the hyps separately.
           (cons nil (%rule-fn name
                               'manual ; "manual" rules are our equivalent of ACL2's rule-classes nil
                               nil ; hyps
                               thm ; lhs is the whole theorem
                               ''t ; rhs is t
                               'equal ; equiv is equal
                               nil)))
          ((memberp (car thm) '(equal iff))
           (cons nil (%rule-fn name
                               'manual
                               nil          ; hyps
                               (second thm) ; lhs
                               (third thm)  ; rhs
                               (first thm)  ; equiv
                               nil)))       ; syntax
          (t
           (cons nil (%rule-fn name
                               'manual
                               nil
                               thm
                               ''t
                               'iff
                               nil))))))

(defun create-rule-from-acl2 (name ACL2::state)
  ;; Returns (enabledp . milawa-rule) or throws an error.
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let ((info-entries (ACL2::info-fn name ACL2::state)))
    (if (not (and (tuplep 1 info-entries)
                  (car info-entries)))
        (ACL2::er hard 'create-rule-from-acl2
                  "Something seems to be wrong with ~x0.~%~
                   Its info-entry is: ~x1.~%"
                  name info-entries)
      (let* ((entry (car info-entries))
             (class (first (cdr (lookup :class entry)))))
        (cond ((equal class :rewrite)
               (create-rule-from-rewrite-entry name entry))
              ((equal class nil)
               (create-rule-from-rule-classes-nil name entry))
              (t
               (ACL2::er hard 'create-rule-from-acl2 "Don't know how to handle rule-classes ~x0.~%" class)))))))



(defmacro %autorule (name)
  `(ACL2::make-event `(%prove ',(cdr (create-rule-from-acl2 ',name ACL2::state)))))

(defun autoprove-fn (name hints ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((rule+    (create-rule-from-acl2 name ACL2::state))
         (enabledp (car rule+))
         (rule     (cdr rule+)))
    `(defsection ,name
       (%prove ',rule)
       (local (ACL2::progn ,@hints))
       (local (%auto))
       (%qed)
       ,@(if enabledp
             `((%enable default ,name))
           nil)
       ,@(if (rw.looks-good-for-outside-inp rule)
             (let ((new-name (ACL2::mksym '[OUTSIDE] (rw.rule->name rule))))
               `((%raw-add-rule
                  (%rule ,new-name
                         :type   outside
                         :hyps   ,(rw.rule->hyps rule)
                         :lhs    ,(rw.rule->lhs rule)
                         :rhs    ,(rw.rule->rhs rule)
                         :equiv  ,(rw.rule->equiv rule)
                         :syntax ,(rw.rule->syntax rule)))
                 ,@(if enabledp
                       `((%enable default ,new-name))
                     nil)))
           nil))))


(defmacro %autoprove (name &rest hints)
  `(ACL2::make-event (autoprove-fn ',name ',hints ACL2::state)))





(defmacro %autoinduct (name &rest args)
  ;; Try inducting as suggested by the definition of the function <name>.
  ;; You can also rename the arguments, e.g.,
  ;;   (%autoinduct cdr-induction y)
  ;; Will try "cdr-induction on y" instead of "cdr-induction on x", which is the
  ;; default since the argument to cdr-induction is x.
  `(local (ACL2::make-event (%autoinduct-fn ',name ',args (ACL2::w ACL2::state)))))

(defun pair-formals-with-calls (formals calls)
  ;; Calls are a list of function calls, e.g., ((foo a b) (foo c d) (foo e f)), and formals
  ;; are the names of the formals, e.g., (x y).  We're going to turn these into substitution
  ;; lists, e.g., ((x . a) (y . b)), ((x . c) (y . d)), etc.
  (declare (xargs :mode :program))
  (if (consp calls)
      (cons (list2-list formals (logic.function-args (car calls)))
            (pair-formals-with-calls formals (cdr calls)))
    nil))

(defun acl2-tests-and-calls-to-induct-pairs (formals x)
  ;; X is a list of tests-and-calls produced by acl2's induction-machine-for-fn function.  We
  ;; need to walk through it and turn it into a list of conditions and substitutions.
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((tests (ACL2::access ACL2::tests-and-calls (car x) :tests))
            (calls (ACL2::access ACL2::tests-and-calls (car x) :calls)))
        (cons (list (cond ((and (consp tests)
                                (consp (cdr tests)))
                           (cons 'and tests))
                          ((consp tests)
                           (car tests))
                          (t
                           (ACL2::er hard 'acl2-tests-and-calls-to-induct-pairs
                                     "A tests-and-calls entry had no tests!~%")))
                    (pair-formals-with-calls formals calls))
              (acl2-tests-and-calls-to-induct-pairs formals (cdr x))))
    nil))

(defun %autoinduct-fn (name args world)
  (declare (xargs :mode :program))
  (let* ((syntax-defuns  (ACL2::get-syntax-defun-entries world))
         (this-defun     (find-syntax-defun name syntax-defuns))
         (measure        (ACL2::get-measure name world))
         (formals        (third this-defun))
         (body           (logic.translate (fourth this-defun)))
         (args*          (or args formals)))
    (cond ((not measure)
           (ACL2::er hard '%autoinduct-fn "The function ~x0 doesn't seem to have a measure.~%" name))
          ((not (same-lengthp args* formals))
           (ACL2::er hard '%autoinduct-fn "Wrong number of arguments provided.  ~x0 takes ~x1 arguments.~%"
                     name (len formals)))
          (t
           (let* ((args-sigma    (fast-pair-lists$ formals args* nil))
                  (body/sigma    (logic.substitute body args-sigma))
                  (measure/sigma (logic.substitute measure args-sigma))
                  (tests-and-calls (ACL2::induction-machine-for-fn (list name) body/sigma
                                                                   ;; In 3.5, ruler-extenders were added.  For
                                                                   ;; 3.4 compatibility we only sometimes add them.
                                                                   #-v3-4 nil)))
             `(%induct ,measure/sigma
                       ,@(acl2-tests-and-calls-to-induct-pairs args* tests-and-calls)))))))




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

; Jared: what's this file for?  It's not certifiable, so I'm
; renaming it to a .lsp extension for Make compatibility
(error "is anyone using this?  If so please remove this message.")

#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#|===========================================================================|#
;; adviser-definitions.lisp
;; John D. Powell
(in-package "ADVISER")

;;
;; This file isolates adviser definitions and types. The file currently
;; contains the following ACL2 constructs as they occur in the adviser book:
;; - defun
;; - defund
;; - defstub
;; - defchoose
;; - defthm
;; - in-theory
;;

(defun rewriting-goal-lit (mfc state)
  "Ensure that we are rewriting a goal, i.e., not backchaining."
  (declare (xargs :stobjs state)
           (ignore state))
  (null (mfc-ancestors mfc)))

(defun rewriting-conc-lit (term mfc state)
  "Ensure that we are writing a conclusion, not a hypothesis."
  (declare (xargs :stobjs state)
           (ignore state))
  (let ((clause (mfc-clause mfc)))
    (member-equal term (last clause))))

(defun aux-symbols (n acc)
  "Generate symbols and accumulate them onto acc."
  (declare (xargs :mode :program))
  (if (zp n)
      acc
    (aux-symbols (1- n) (cons (intern-in-package-of-symbol
                               (concatenate 'string "X"
                                            (coerce (explode-atom n 10) 'string))
                               'defthm)
                              acc))))
;; A valid pick a point rule is of the following form:
;;
;; (defadvice name
;;   (implies (hyps)
;;            (conclusion (arg1) (arg2) ... (argN)))
;;   :rule-classes (:pick-a-point :driver foo))
;;
;; Where hyps and each arg are encapsulated functions of no arguments, and
;; where foo is some defthm which proves exactly this implication for those
;; constrained functions.
;;
;; We check the syntactical validity of the form with the following functions.

(defun pick-a-point-term-syntax-ok-p1 (x)
  "Check that ((arg1) (arg2) ... (argN)) are function symbols of no arguments."
  (declare (xargs :mode :program))
  (if (atom x)
      (null x)
    (and (true-listp (car x))
         (equal (len (car x)) 1)
         (symbolp (first (car x)))
         (pick-a-point-term-syntax-ok-p1 (cdr x)))))

(defun pick-a-point-term-syntax-ok-p (term)
  "Check that (implies (hyps) (conclusion ...)) is syntactically ok."
  (declare (xargs :mode :program))
  (and (true-listp term)
       (equal (len term) 3)
       (equal (first term) 'implies)
       (let ((hypothesis (second term))
             (conclusion (third term)))
         (and (true-listp hypothesis)
              (equal (len hypothesis) 1)
              (symbolp (first hypothesis))
              (true-listp conclusion)
              (consp conclusion)
              (cond ((eq (car conclusion) 'not)
                     (let ((conclusion (cadr conclusion)))
                       (and (<= 2 (len conclusion))
                            (symbolp (car conclusion))
                            (pick-a-point-term-syntax-ok-p1
                             (cdr conclusion)))))
                    (t
                     (and (<= 2 (len conclusion))
                          (symbolp (car conclusion))
                          (pick-a-point-term-syntax-ok-p1
                           (cdr conclusion)))))))))


(defun pick-a-point-rule-classes-syntax-ok-p (x)
  "Check that the rule classes are syntactically ok."
  (declare (xargs :mode :program))
  (and (true-listp x)
       (= (length x) 3)
       (eq (first x) :pick-a-point)
       (eq (second x) :driver)
       (symbolp (third x))))

(defun pick-a-point-rule-syntax-check (name term rule-classes)
  "Check that a pick a point rule satisfies all syntactic requirements."
  (declare (xargs :mode :program))
  (cond ((not (symbolp name))
         (cw "~%Rule name must be a symbol, but it is ~x0.~%"
             name))
        ((not (pick-a-point-term-syntax-ok-p term))
         (cw "~%Term must be of the form:~%~%   ~
               (implies (hyps) ~%          ~
                        (conclusion (arg1) (arg2) ... (argN)))~%~%~
              Or else of the form:~%~%   ~
               (implies (hyps) ~%          ~
                        (not (conclusion (arg1) (arg2) ... (argN))))~%~%~
              But instead, the term is:~%~%   ~x0~%"
             term))
        ((not (pick-a-point-rule-classes-syntax-ok-p rule-classes))
         (cw "~%:pick-a-point rules must have :rule-classes ~
              of the form:~%~%   ~
               (:rule-classes :driver <thm>)~%~%
              Where <thm> is the name of some generic theorem of the same ~
              form.  But, the rule classes here are of the form: ~%~%   ~x0~%"
              rule-classes))
        (t t)))

(defun pick-a-point-rule-parser (name term rule-classes)
  "Take from a pick-a-point rule the name, function, theorem, hyps, and
   args, and return them as an alist."
  (declare (xargs :mode :program))
  ;; Note: we assume that x is a syntactically well formed rule before
  ;; this function is called.
  (let* ((hypothesis (second term))
         (conclusion (third term))
         (negatedp   (if (eq (car conclusion) 'not)
                         t
                       nil))
         (function   (if negatedp
                         (first (cadr conclusion))
                       (first conclusion)))
         (args       (if negatedp
                         (rest (cadr conclusion))
                       (rest conclusion))))
    (list (cons :class :pick-a-point)
          (cons :name name)
          (cons :negatedp negatedp)
          (cons :function function)
          (cons :trigger (symbol-fns::join-symbols
                          function
                          "ADVISER-"
                          (symbol-name function)
                          "-TRIGGER"))
          (cons :driver (third rule-classes))
          (cons :hyps (first hypothesis))
          (cons :args (pairlis$ (symbols (len args))
                                args)))))

(defun pick-a-point-rule-installer (parsed-rule)
  "Take a parsed rule and install it into the table, and set up the trigger."
  (declare (xargs :mode :program))
  (let* ((name (cdr (assoc :name parsed-rule)))
         (function (cdr (assoc :function parsed-rule)))
         (trigger (cdr (assoc :trigger parsed-rule)))
         (args (cdr (assoc :args parsed-rule)))
         (negatedp (cdr (assoc :negatedp parsed-rule))))
  `(encapsulate
    ()

    ;; First create a new trigger that will be used as the target for this
    ;; rule.
    (defund ,trigger ,(strip-cars args)
      (declare (xargs :verify-guards nil))
      (,function ,@(strip-cars args)))

    ;; Next we create a theorem that rewrites function to our trigger in the
    ;; appropriate circumstances.
    (defthm ,name
      (implies (and (syntaxp (rewriting-goal-lit mfc state))
                    (syntaxp (rewriting-conc-lit
                              ,(if negatedp
                                   `(list 'not (list ',function ,@(strip-cars args)))
                                 `(list ',function ,@(strip-cars args)))
                              mfc state)))
               (equal (,function ,@(strip-cars args))
                      (,trigger ,@(strip-cars args))))
      :hints(("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                '((:definition ,trigger))))))

    ;; Finally we add our pattern to the pick a point rules database.
    (table adviser-table :pick-a-point-rules
           (let ((rules (pick-a-point-rules world)))
             (ACL2::rebalance-symbol-btree
              (ACL2::symbol-btree-update ',trigger
                                         ',parsed-rule
                                         rules))))
  )))

(defun pick-a-point-rule-defadvice (name term rule-classes)
  (declare (xargs :mode :program))
  (if (pick-a-point-rule-syntax-check name term rule-classes)
      (pick-a-point-rule-installer
       (pick-a-point-rule-parser name term rule-classes))
    nil))






;; Computing Pick a Point Hints
;;
;; Now, what we are going to do next is create a computed hint that will look
;; for instances of a trigger, and if it sees one, we will try to provide a
;; functional instantiation hint.  Our computed hint function is called as ACL2
;; is working to simplify terms, and it is allowed to examine the current
;; clause.
;;
;; Terminology: A clause is a list of disjuncts, e.g.,
;;
;;   (a ^ b ^ ...) => P  is  (~a v ~b v ... v P)
;;   (a v b v ...) => P  is  subgoal1: (~a v P), sg2: (~b v P), ...
;;
;; The disjuncts are each terms, e.g., (foo x y).
;;
;; Our first step is to see if our hint should even be applied to this clause.
;; We should only give a hint if we see one of our triggers (i.e., if a hint
;; tagging rule has fired).
;;
;; We check for the existence of our triggers using the following function,
;; (pick-a-point-trigger-harvester clause rules acc-lit acc-rule).
;;
;;   Clause is the current clause we are processing.
;;   Rules is the database of pick a point rules (a btree).
;;   Acc-lit is an accumulator that stores the matching clauses.
;;   Acc-rule is an accumulator that stores the matching rules.
;;
;; We look for known triggers and if we find any, we add the literal to the
;; acc-lit accumulator, and we add the corresponding rule to the acc-rule
;; accumulator.  Hence, the nth element of each accumulator corresponds to the
;; nth element of the other.  We return both accumulators.

(defun pick-a-point-trigger-harvester (clause rules acc-lit acc-rule)
  (declare (xargs :mode :program))
  (if (endp clause)
      (mv acc-lit acc-rule)
    (let* ((literal (car clause))
           ;; DAG : Added "guard" checking code to protect functions
           (matchsym (if (consp literal)
                         (if (and (equal (car literal) 'not)
                                  (consp (cdr literal))
                                  (consp (cadr literal)))
                             (caadr literal)
                           (car literal))
                       nil)))
      (let ((match (and
                    ;; Eric and Doug added this check, since we got an error
                    ;; when matchsym was a lambda expression:
                    (symbolp matchsym)
                    (ACL2::symbol-btree-lookup matchsym rules))))
        (pick-a-point-trigger-harvester
         (cdr clause)
         rules
         (if match (cons literal acc-lit) acc-lit)
         (if match (cons match acc-rule) acc-rule))))))



;; If we find any matches, we need to provide appropriate hints.  To do this,
;; we need to provide values for the hypotheses and arguments.
;;
;; In order to compute the hypotheses, we first remove from the clause all of
;; our trigger terms.  This is easy to do, we can just take the
;; set-difference-equal of the clause with the acc-lit accumulator found above.
;;
;; Once that is done, the remaining literals should become hypotheses.  Suppose
;; that the original conjecture was (a ^ b ^ ...) => P.  Then, we will have the
;; clause (~a v ~b v ... v P), i.e., ((not a) (not b) ... P).  Suppose P was
;; our trigger term, so we remove it from the clause leaving us with ((not a)
;; (not b) ...).  What we need to do is recover the original hypotheses, namely
;; (a ^ b ^ ...).  To do this, we will negate each literal and then and them
;; together, which will create the the term (and a b ...), which was our
;; original hypotheses!

(defun negate-literals (literals)
  (declare (xargs :mode :program))
  (if (endp literals)
      nil
    (if (equal (caar literals) 'not)
        ;; don't create ugly double not's
        (cons (second (car literals))
              (negate-literals (cdr literals)))
      (cons (list 'not (car literals))
            (negate-literals (cdr literals))))))

(defun andify-literals (literals)
  (declare (xargs :mode :program))
  (if (endp literals)
      ;; the "and" of nothing is "t"
      t
    (if (endp (cdr literals))
        ;; don't create ugly and's of singletons
        (car literals)
      (cons 'and literals))))

;; Here's an example:
;;
;; ADVISER !>(andify-literals
;;  (negate-literals '((foo x)
;;                     (foo y)
;;                     (not (foo a))
;;                     (not (foo b)))))
;; (AND (NOT (FOO X))
;;      (NOT (FOO Y))
;;      (FOO A)
;;      (FOO B))



;; Now that we can handle the hypotheses, we're ready to be able to build our
;; actual hints.  We do this with build-hint.  Build-hint expects to receive
;; as arguments the matching literal and rule, and the hypotheses that were
;; build using the above strategy.
;;
;; Rule is expected to be a parsed rule, which means that it is an alist of
;; components.  We need to build a functional instance hint.  The theorem
;; to instantiate is stored in :driver.  The name of the generic hypotheses
;; function is stored in :hyps.  We also need to provide instantiations for
;; each of the arguments.  The names of these functions are in order in the
;; strip-cdrs of :args.

(defun make-functional-instance-pairs (arg-names actuals)
  (declare (xargs :mode :program))
  (if (endp arg-names)
      nil
    (cons `(,(car arg-names)
            (lambda () ,(car actuals)))
          (make-functional-instance-pairs (cdr arg-names)
                                          (cdr actuals)))))

(defun build-hint (literal rule hyps)
  (declare (xargs :mode :program))
  (let ((driver      (cdr (assoc :driver rule)))
        (hyps-name   (cdr (assoc :hyps rule)))
        (arg-names   (strip-cars (strip-cdrs (cdr (assoc :args rule)))))
        (actuals     (if (equal (car literal) 'not)
                         (rest (cadr literal))
                       (rest literal))))
    `(:functional-instance ,driver
      (,hyps-name (lambda () ,hyps))
      ,@(make-functional-instance-pairs arg-names actuals))))

(defun build-hints (literals rules hyps acc)
  (declare (xargs :mode :program))
  (if (endp literals)
      acc
    (build-hints (cdr literals)
                 (cdr rules)
                 hyps
                 (cons (build-hint (car literals)
                                   (car rules)
                                   hyps)
                       acc))))
(defun get-thms (rules)
  (declare (xargs :mode :program))
  (if (endp rules)
      nil
    (cons (cdr (assoc :driver (car rules)))
          (get-thms (cdr rules)))))

(defun get-names (rules)
  (declare (xargs :mode :program))
  (if (endp rules)
      nil
    (cons (cdr (assoc :name (car rules)))
          (get-names (cdr rules)))))

(defun build-expand-hint (literals)
  (declare (xargs :mode :program))
  (if (endp literals)
      nil
    (let ((lit (first literals)))
      (if (equal (car lit) 'not)
          (cons (cadr lit)
                (build-expand-hint (rest literals)))
        (cons lit (build-expand-hint (rest literals)))))))

; Slight modification by Matt Kaufmann for ACL2 Version 3.3:
;   "Fixed a bug in handling of computed hints related to the
;    stable-under-simplificationp parameter (see *note COMPUTED-HINTS::)."
; The bug in Versions 3.2 and before was that a computed hint firing when
; stable-under-simplificationp took us back to the preprocess ledge of the
; waterfall, where :use hints aren't applied.  So the original combination of
; :use and :expand generated by the following function caused only the
; application of the :expand hint; the :use hint was left alone and then
; applied to the next subgoal.  With the fix, we can create that same behavior
; by judicious use of the :computed-hint-replacement feature, so that the
; :expand hint continues to be applied first.
(defun pick-a-point-suggester (id clause world)
  (declare (xargs :mode :program))
  (let ((rules (pick-a-point-rules world)))
    (if (null rules)
        nil
      (mv-let (literals rules)
              (pick-a-point-trigger-harvester clause rules nil nil)
              (if (null literals)
                  nil
                (let* ((others (set-difference-equal clause literals))
                       (hyps (andify-literals
                              (negate-literals others)))
                       (hints `(:computed-hint-replacement
                                ('(:computed-hint-replacement
                                   ((adviser-default-hint id clause world stable-under-simplificationp))
                                   :use ,(build-hints literals rules hyps nil)))
                                :expand ,(build-expand-hint literals))))
                  (prog2$ (cw *pick-a-point-message*
                              (get-thms rules)
                              (get-names rules)
                              (list (ACL2::string-for-tilde-@-clause-id-phrase id)
                                    hints))
                          hints)))))))

(defun adviser-default-hint (id clause world stable)
  (declare (xargs :mode :program))
  (if (not stable)
      nil
    (or (pick-a-point-suggester id clause world)
        nil)))

;; Some primitive tests.  First we set up a predicate to check that all
;; elements of a list are not integerp's.  We then create a membership based
;; strategy to show this.

(defun all-not-integerp (x)
  (if (consp x)
      (if (integerp (car x))
          nil
        (all-not-integerp (cdr x)))
    t))

(defthm integerp-when-member-of-all-not-integerp
  (implies (and (all-not-integerp x)
                (member a x))
           (not (integerp a))))


;; We also introduce a predicate that test whether or not a list contains some
;; member which is an integer, and a membership based strategy for proving that
;; some list satisfies some-integerp.

(defun some-integerp (x)
  (if (consp x)
      (if (integerp (car x))
          t
        (some-integerp (cdr x)))
    nil))

(defthm integerp-when-member-of-not-some-integerp
  (implies (and (not (some-integerp x))
                (member a x))
           (not (integerp a))))

;; We can now conclude, without inducting over the definitions of
;; all-not-integerp and some-integerp, that these ideas are actually opposites
;; of one another.

(in-theory (disable all-not-integerp some-integerp))

(defthm lemma1
  (implies (all-not-integerp x)
           (not (some-integerp x))))

(defthm lemma2
  (implies (not (some-integerp x))
           (all-not-integerp x)))

(defthm conclusion
  (equal (some-integerp x)
         (not (all-not-integerp x))))




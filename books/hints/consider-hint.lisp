; Copyright (C) 2013, ForrestHunt, Inc.
; Written by J Strother Moore (some years before that)
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(include-book "huet-lang-algorithm")
(include-book "merge-hint")
(program)
(set-state-ok t)

; Essay on the Design of Consider Hints

; [Note that this is NOT the similarly titled Essay on the
; Implementation of Consider Hint Processing!]

; :hints (("Goal" ...
;                 :CONSIDER
;                 ((<name>
;                   [:pattern <term> | :lhs ]
;                   [:target  <term> | :conclusion ]
;                   [:instance <var-substn>]
;                   [:functional-instance <fn-substn>]
;                  )
;                  ...)
;                 ...)

; The new hint will use second-order matching to compute a relevant
; instantiation of <name> and that instantiation is added as a hypothesis,
; as when we supply :USE hints.

; The value of the :consider hint denotes a list of
; ``considerations.''

; The user-level form of a consideration is

;                 (<name>
;                  [:pattern <term> | :lhs ]
;                  [:target  <term> | :conclusion | :clause]
;                  [:instance <var-substn>]
;                  [:functional-instance <fn-substn>)]
;                  )
; or just <name>.

; We describe below some conventions for abbreviating a list of
; considerations.

; The :pattern specifies the pat used in second order matching.  It is
; either a term or the keyword :lhs.  The latter means ``use the lhs
; of the conclusion of <name>.''  If :pattern is not specified, it
; defaults to :lhs.

; The :target specifies the concrete term to match.  If it is
; :conclusion, we SEARCH through the conclusion of the subgoal clause
; for the first match of :pattern.  If it is :clause, we SEARCH
; through the clause, from last literal to the first literal, for the
; first match of :pattern.  If :target is :term, we use term and we
; don't search, we just match against term itself.  If :target is not
; specified, it defaults to :clause.

; :Instance and :functional-instance specify substitutions in the
; usual form that users write them, e.g., lists of doublets.  The
; first is a var-to-term substitution, the second is a
; function-symbol-to-function substitution.  They are combined into a
; mixed substitution that is used by the second order pattern matcher
; as the starting substitution.  That substitution must be extended in
; the match.  This is a way to limit the possible matches.

; If either substitution is not specified, it defaults to nil.

; If no keywords are specified, all default as described.

; We must decide how to handle user-level input that denotes a list of
; considerations.  For example, if the user writes :consider h-thm it
; means :consider (h-thm).  If the user writes :consider (h-thm
; :pattern ...) it means :consider ((h-thm :pattern ...)).  But if the
; user writes :consider (h-thm g-thm) it means just that: h-thm and
; g-thm are two considerations.  See coerce-consideration-list.
;
; Translation-Time Processing: We check that <name> is a named
; formula.  Each <term> is translated.  If :lhs is written, we replace
; it by the translated lhs of the named formula, so :lhs will NEVER
; appear in a translated :consider hint.  If :conclusion or :clause is
; written, we leave it as written, since we cannot resolve it until we
; see the goal clause.  The two substitutions are combined at
; translate-time into a single psubst.

; Prove-Time Processing: Most of the work on :consider hints occurs at
; prove-time, when we use second order matching between the :pattern
; and the :target term of the subgoal clause to generate a list of
; substitutions.  We rank the substitutions by syntactic criteria and
; choose the most highly ranked substitutions and produce the
; corresponding lemma instance, lmi.  We do this for each of the
; consideration items listed.  We are supposed to use one of the lmi's
; from each of the items.  So we use all-picks to convert what is
; essentially a conjunction of disjuncts to a disjunction of
; conjuncts.  Each list of lmi's is now an UNtranslated :USE hint and
; we will search for the first one that works.  To do that, we convert
; each of these automatically generated :USE hints into internal form
; (analogous to the translation-time processing of :USE hints, but
; done in the waterfall without state), and then successively replace
; the :CONSIDER hint by the :USE hints and proceed.

; We anticipate that users might ultimately wish to see ALL of the
; candidate substitutions generated.  After all, we choose only the
; most highly ranked ones and our rankings are entirely syntactic.  We
; could have preserved all that information and included it in our
; normal output, but we decided that was too complicated and verbose.
; Instead, we expect to implement a diagnostic feature like
; show-all-matches that takes two terms, or a clause and consider
; item, and prints all of the matches.

(defrec consideration
  (name          ; name of a formula
   pattern       ; a translated term to use as the pattern
   target        ; a translated term or the symbol :conclusion or :clause
   psubst0       ; a psubst to seed hld's match
   user-level)   ; user-level input giving rise to this
  nil)

(defun listify-consideration-lst (arg)

; We disambiguate arg into a list of user-level considerations.  That
; is, all we're doing is resolving the question of whether arg is a
; single consideration or a list of them.  We know arg is not nil.  If
; this function returns nil, it means we could not disambiguate arg.
; The elements of the disambiguated arg are still in external,
; user-level form!  This function does not translate.

; Illustrative cases:
; arg                       value
; h-thm                     (h-thm)
; (h-thm)                   (h-thm)
; (h-thm :pattern ...)      ((h-thm :pattern ...))
; (h-thm x ...)             (h-thm x ...)

  (cond
   ((atom arg)
    (list arg))
   ((not (true-listp arg)) nil)
   ((null (cdr arg))
    arg)
   ((and (symbolp (car arg))
         (keywordp (cadr arg)))
    (list arg))
   (t arg)))


(defun get-lhs (term ctx wrld state)
  (let ((lst (unprettyify term))) ; pair = (hyps . concl)
    (cond
     ((equal (length lst) 1)
      (mv-let (equiv lhs0 lhs rhs ttree)
              (interpret-term-as-rewrite-rule1
               (remove-lambdas (cdr (car lst)))
               t ; equiv-ok
               (ens state)
               wrld)
              (declare (ignore equiv lhs0 rhs ttree))
              (value lhs)))
     (t (er soft ctx
            "We cannot determine the :lhs of a formula because it ~
             flattens to more than one clause.")))))

(defun translate-consideration1 (name lst ctx wrld state)
  (cond
   ((not (and (symbolp name)
              (formula name nil wrld)
              (true-listp lst)
              (evenp (length lst))
              (subsetp (evens lst)
                       '(:pattern :target
                                  :instance
                                  :functional-instance))))
    (er soft ctx
        "A :CONSIDER hint element should be a list consisting of an ~
         event name followed by a list of even length containing ~
         alternating keys and values, with the keys :PATTERN, ~
         :TARGET, :INSTANCE, and :FUNCTIONAL-INSTANCE being legal. ~
         Your hint element ~x0 is ill-formed!"
        (cons name lst)))
   (t (er-let*
        ((pattern
          (let ((temp (assoc-keyword :pattern lst)))
            (cond ((and temp (not (eq (cadr temp) :lhs)))
                   (translate (cadr temp)
                              t t t ctx wrld state))
                  (t (get-lhs (formula name nil wrld) ctx wrld state)))))
         (target
          (let ((temp (assoc-keyword :target lst)))
            (cond ((null temp) (value :clause))
                  ((or (eq (cadr temp) :conclusion)
                       (eq (cadr temp) :clause))
                   (value (cadr temp)))
                  (t (translate (cadr temp)
                                t t t ctx wrld state)))))
         (var-alist
          (translate-substitution (cadr (assoc-keyword :instance lst))
                                  ctx wrld state))
         (fn-alist
          (translate-functional-substitution
           (cadr (assoc-keyword :functional-instance lst))
           ctx wrld state)))
        (value
         (make consideration
               :name name
               :pattern pattern
               :target  target
               :psubst0
               (convert-var-and-fn-alists-to-psubst var-alist
                                                    fn-alist
                                                    wrld)
               :user-level (cons name lst)))))))

(defun translate-consideration (x ctx wrld state)
  (cond
   ((atom x)
    (translate-consideration1 x nil ctx wrld state))
   (t (translate-consideration1 (car x) (cdr x) ctx wrld state))))

(defun translate-consider-hint1 (lst ctx wrld state)

; Each element of lst is to be treated as a consideration.  We translate
; each into a consideration record.
  (cond
   ((endp lst) (value nil))
   (t (er-let*
        ((c (translate-consideration (car lst) ctx wrld state))
         (rest (translate-consider-hint1 (cdr lst) ctx wrld state)))
        (value (cons c rest))))))

(defun translate-consider-hint (arg ctx wrld state)

; This function either causes an error or returns (as the value component of
; an error/value/state triple) a list of consideration records.
; See the Essay on the Design of Consider Hints.

  (cond
   ((null arg)
    (er soft ctx
        "Empty :CONSIDER hints are illegal."))
   (t (let ((lst (listify-consideration-lst arg)))
        (cond
         ((null lst)
          (er soft ctx "The value of a :CONSIDER hint must be a symbol ~
                       or a true-list and ~x0 is neither." arg))
         (t (translate-consider-hint1 lst ctx wrld state)))))))

(defxdoc consideration
  :parents (hints)
  :short "An object indicating that some instantiation is relevant."

  :long "<p>Considerations are the objects one provides as part of
@(':consider') @(see hints).  The most convenient form of a consideration is
simply the name of a lemma.  The system will then search for a relevant
instantiation of the left-hand side of the conclusion of that lemma inside the
specified goal clause, starting with the last literal.  The system uses a
heuristically modified version of the Huet-Lang second-order pattern matching
algorithm and, in general, produces instantiations of both variable symbols and
constrained function symbols in the lemma.  If an instance is found, the
consideration is turned into a @(see lemma-instance) and @(':use')d.</p>

<p>For example, suppose the following theorem has been proved:</p>

@({
    (defthm map-h-append
      (implies (and (true-listp x)
                    (true-listp y))
               (equal (map-h-append (append x y))
                      (append (map-h x) (map-h y))))
      :rule-classes nil)
})

<p>and suppose @('map-h') is a defined function involving some constrained
function symbol @('h').  Then the consideration @('map-h-append') attached to a
clause identifier will cause the system to find the identified clause and
search through it for an instance and/or functional instance of
@('(map-h-append (append x y))') and to add that (functional) instance as a
hypothesis when it finds it.  If no instance is found, an error is signaled.
The more elaborate form of a consideration allows you to specify what is used
as the pattern and where that pattern is searched for in the clause.</p>

<p>The most general form of a consideration is</p>

@({
   (name
    :pattern             pterm   ; term or :lhs
    :target              tterm   ; term or :conclusion or :clause
    :instance            vsubst  ; variable substitution
    :functional-instance fsubst) ; functional substitution
})

<p>where @('name') is the name of a previously proved theorem, @('pterm') is
either a term or the keyword @(':lhs'), @('tterm') is either a term or the
keyword @('conclusion') or the keyword @(':clause'), @('vsubst') is a variable
substitution as might be given in an @(':instance'), e.g., @('((x (rev
a)) (y (sort b)))'), and @('fsubst') is a functional substitution as might be
given in a @(':functional-instance'), e.g., @('((map-h sumer))').</p>

<p>If @('pterm') is a term, that term is used as the pattern we try to
instantiate.  If @('pterm') is the keyword @(':lhs'), the left-hand side of the
conclusion of @('name') is used as the pattern.  If no @(':pattern') is
specified, @(':lhs') is used by default.</p>

<p>If @('tterm') is a term, that term is matched against the pattern to
generate the instantiation.  If @('tterm') is @(':conclusion'), a match of the
pattern is searched for in the conclusion of the specified subgoal clause.  If
@('tterm') is @(':clause'), a match of the pattern is searched for in the
entire subgoal clause, starting with the conclusion and searching backwards
toward the first hypothesis.  The search is outer-most first, left-to-right
recursive descent.  The first subterm of the target producing a match of the
pattern stops the search and generates the instantiation.  Note that if
@('tterm') is given explicitly, no search occurs.  Note also that because we
cannot do the search until we know what the subgoal clause is, the work for
this hint -- the Huet-Lang second-order matching algorithm -- cannot commence
until the indicated subgoal arises.</p>

<p>The substitutions produced by second-order matching are what we called
``mixed substitutions'' by which we mean a given substitution will substitute
both for variable symbols and hereditarily constrained function symbols.  The
effect, however, is the same as</p>

@({
  (:INSTANCE (:FUNCTIONAL-INSTANCE name (fn1 (lambda ...)) ...)
             (var1 term1)
             ...).
})

<p>Second-order matching typically produces a plethora of such substitutions.
We rule many out on heuristic grounds.  Thus, our heuristic modification of the
Huet-Lang algorithm makes it incomplete.  Still, it is typical for a lot of
substitutions to be found and the system selects some to pursue in an
DISJUNCTIVE way.  That is, it takes each of the ``winning'' substitutions and
generates a @(':use') hint for each of them separately to see if any one of
them will prove the indicated subgoal.</p>

<p>It is frequently necessary to give the matcher a ``hint'' to limit its
consideration of all possible substitutions.  The @('vsubst') and @('fsubst')
are treated as ``seed'' substitutions.  Any computed instance is an extension
of the two seeds.  That is, the variable pairs in the mixed substitutions
extend @('vsubst') and the functional pairs in the mixed substitutions extend
@('fsubst').  Both @('vsubst') and @('fsubst') default to @('nil').</p>")

; --------------
; Essay on the Implementation of Consider Hint Processing

; We are about to start dealing with the conversion of considerations
; to :use hints.  A use hint is a list of lemma instances and in our
; case each is of the form (:instance (:functional-instance ...) ...).

; Let temp be (:consider . (consideration1
; ... considerationn)), where each consideration is a record of that
; type.  Naively, each consideration generates a lemma instance and we
; conjoin them all together across the n considerations.

; But less naively, each considerationi may generate multiple lemma
; instances (because of the multiplicity of functional instantiations
; produced by second order matching).  Thus, the list of n
; considerations represents a conjunction of disjunctions.  If
; consideration1 generates u1,1 ... u1,k1, where each u is a lemma
; instance, then we have (and (or u1,1 ... u1,k1) (or u2,1 ... u2,k2)
; ...) and we want a disjunction of conjunctions: (or (and u1,1 u2,1
; ...) (and u1,1 u2,2 ...) ...).  This transformation to DNF form is
; just performed by all-picks.  Thus, we get k1*k2*... disjunctions,
; each of which represents a conjunction of lemma instances.  But a
; conjunction of lemma instances is a :USE hint.  Thus we ultimately
; produce a hint of the form

; :OR ((:USE (u1,1 u2,1 ...)) (:USE (u1,1 u2,2 ...)) ...)

; We go back and forth between the internal and external form of
; substitutions in this code, so we need these two functions.

(defun convert-pairs-to-doublets (alist)

; Alist is of the form ((key . val) ...) and we convert it to the form
; ((key val) ...)

  (cond ((endp alist) nil)
        (t (cons (list (car (car alist)) (cdr (car alist)))
                 (convert-pairs-to-doublets (cdr alist))))))

(defun convert-doublets-to-pairs (substn)

; Substn is of the form ((key val) ...) and we convert it to the form
; ((key . val) ...)

  (cond ((endp substn) nil)
        (t (cons (cons (car (car substn)) (cadr (car substn)))
                 (convert-doublets-to-pairs (cdr substn))))))

; We now develop the code that converts a consideration to an lmi.

; Here is the function that searches for the first (second order)
; match of pat in term extending psubst0.

(mutual-recursion

(defun hld-sweep (pat term psubst0 n wrld)
  (cond
   ((variablep term) nil)
   ((fquotep term) nil)
   (t (or (hld pat term psubst0 nil nil n wrld)
          (hld-sweep-lst pat (fargs term) psubst0 n wrld)))))

(defun hld-sweep-lst (pat term-lst psubst0 n wrld)
  (cond
   ((endp term-lst) nil)
   (t (or (hld-sweep pat (car term-lst) psubst0 n wrld)
          (hld-sweep-lst pat (cdr term-lst) psubst0 n wrld))))))

(defun prettyify-substn (functionalp substn wrld)

; Substn is a list of pairs of the form (var term) or (fn function),
; where functionap = nil for the former and t for the latter.  We
; untranslate it into the external form (var term') or (fn function'),
; where term' and function' are the untranslated versions of the term
; or function.

  (cond ((endp substn) nil)
        (t (cons (list (car (car substn))
                       (if functionalp
                           (if (symbolp (cadr (car substn)))
                               (cadr (car substn))
                             (make-lambda (lambda-formals (cadr (car substn)))
                                          (untranslate
                                           (lambda-body (cadr (car substn)))
                                           nil
                                           wrld)))
                         (untranslate (cadr (car substn)) nil wrld)))
                 (prettyify-substn functionalp
                                   (cdr substn)
                                   wrld)))))

(defun prettyify-lmi (lmi wrld)
  (cond ((atom lmi) lmi)
        ((eq (car lmi) :instance)
         (list* :INSTANCE
                (prettyify-lmi (cadr lmi) wrld)
                (prettyify-substn nil (cddr lmi) wrld)))
        ((eq (car lmi) :functional-instance)
         (list* :FUNCTIONAL-INSTANCE
                (prettyify-lmi (cadr lmi) wrld)
                (prettyify-substn t (cddr lmi) wrld)))
        ((eq (car lmi) :theorem)
         (list :theorem
               (untranslate (cadr lmi) t wrld)))
        (t lmi)))

(defun prettyify-lmi-lst (lmi-lst wrld)
  (cond ((endp lmi-lst) nil)
        (t (cons (prettyify-lmi (car lmi-lst) wrld)
                 (prettyify-lmi-lst (cdr lmi-lst) wrld)))))

(defun convert-mixed-subst-to-lmi (name thm mixed-subst wrld)
  (mv-let
   (var-alist initial-fn-alist)
   (strip-mixed-subst mixed-subst)
   (mv-let (fn-alist inverse-subst)
           (rename-free-vars-in-fn-substitution thm initial-fn-alist wrld)
           `(:INSTANCE
             (:FUNCTIONAL-INSTANCE
              ,name
              ,@(convert-pairs-to-doublets fn-alist))
             ,@(convert-pairs-to-doublets var-alist)
             ,@inverse-subst))))

(defun convert-mixed-substs-to-lmi-lst (name thm mixed-substs wrld)
  (cond
   ((endp mixed-substs) nil)
   (t (cons (convert-mixed-subst-to-lmi name thm (car mixed-substs) wrld)
            (convert-mixed-substs-to-lmi-lst name thm
                                             (cdr mixed-substs) wrld)))))

#|
(defun prettyify-ranked-mixed-substs (name thm ranked-mixed-substs wrld)
  (cond
   ((endp ranked-mixed-substs)
    nil)
   (t (cons (list (car (car ranked-mixed-substs))
                  (prettyify-lmi
                   (convert-mixed-subst-to-lmi name thm
                                               (cdr (car ranked-mixed-substs))
                                               wrld)
                   wrld))
            (prettyify-ranked-mixed-substs name thm
                                           (cdr ranked-mixed-substs)
                                           wrld)))))
|#


(defun collect-high-ranking-mixed-substs (ranked-mixed-substs)

; Each element of lst is of the form (rank . mixed-subst) and the list
; is ordered descending by rank.  We collect the mixed-substs with
; highest rank.  Note that we do not collect the ranks.

  (cond ((endp ranked-mixed-substs)
         nil)
        ((endp (cdr ranked-mixed-substs))
         (list (cdr (car ranked-mixed-substs))))
        ((equal (car (car ranked-mixed-substs))
                (car (cadr ranked-mixed-substs)))
         (cons (cdr (car ranked-mixed-substs))
               (collect-high-ranking-mixed-substs (cdr ranked-mixed-substs))))
        (t (list (cdr (car ranked-mixed-substs))))))

(defun convert-consideration-to-lmi-lst
  (cl consideration wrld all-flg ctx state)

; Note: The name in a user-level consideration denotes the
; UN-normalized formula, not the normalized formula.  That is because
; we do pattern matching on the formula and we want to use the pattern
; the user wrote, not its normalization.  The :USE hint generated will
; use the normalized version of the instantiated formula, of course.

; Note: In the hld sweeps below we limit the rewrite repetition to 1.
; That is, we will apply all known rewrite rules to every argument and
; recursively rewrite the resulting intermediate terms.  But we will
; not rewrite those.  That is (f (g '1)) might be rewritten to (f (g
; '2)), by applying a rule to (g '1), and then that might be rewritten
; to (h (g '2)), by applying a rule to (f (g '2)).  But we don't ever
; try to rewrite (h (g '2)).  If you want that to happen, change
; (certain of) the 1's to 2's below.

; We print and signal an error or return (value lmi-lst) where lmi-lst
; is the list of the highest ranking automatically-computed lmi's as
; might have been typed by a user in a :USE hint.

; Warning: The lmis we return are prettyified, so the terms in them
; are now untranslated!  We return such things so that if the user
; activates show-custom-keyword-hint-expansion he sees pretty
; substitutions.

  (let* ((name (access consideration consideration :name))
         (thm (formula name nil wrld))
         (pat (access consideration consideration :pattern))
         (psubst0 (access consideration consideration :psubst0))
         (ans (cond
               ((eq (access consideration consideration :target)
                    :conclusion)
                (hld-sweep pat (car (last cl)) psubst0 1 wrld))
               ((eq (access consideration consideration :target)
                    :clause)
                (hld-sweep-lst pat (reverse cl) psubst0 1 wrld))
               (t (hld pat
                       (access consideration consideration :target)
                       psubst0 nil nil 1 wrld))))
         (mixed-substs (if all-flg ans
                         (collect-high-ranking-mixed-substs ans))))
    (cond
     (ans
      (value
       (prettyify-lmi-lst
        (convert-mixed-substs-to-lmi-lst name thm mixed-substs wrld)
        wrld)))
     (t (er soft ctx
            "We were unable to compute a second-order instantiation ~
             matching the pattern ~x0 with the target ~x1, as ~
             directed by your :CONSIDER hint.~#2~[~/  The ~x1 in ~
             question is ~x3.~]"
            pat
            (access consideration consideration :target)
            (if (or (eq (access consideration consideration :target)
                        :conclusion)
                    (eq (access consideration consideration :target)
                        :clause))
                1 0)
            (cond
             ((eq (access consideration consideration :target)
                  :conclusion)
              (car (last cl)))
             ((eq (access consideration consideration :target)
                  :clause)
              (reverse cl))
             (t nil)))))))

; Here is how we convert a list of considerations to a list of
; lmi-lsts.

(defun convert-considerations-to-lmi-lst-lst
  (cl considerations wrld ctx state)

; We convert a list of considerations into a list of lmi lists.  We
; always choose only the highest ranking substitutions.  We return (mv
; erp val).  If erp is t, val is an error msg.  Else, val is a list of
; lmi lists.  Don't be fooled by the messiness below.  This is just
; a simple map and collect, handling the error pairs appropriately.

  (cond
   ((endp considerations)
    (value nil))
   (t
    (er-let*
      ((lmi-lst
        (convert-consideration-to-lmi-lst cl (car considerations) wrld nil
                                          ctx state))
       (lmi-lst-lst
        (convert-considerations-to-lmi-lst-lst cl (cdr considerations) wrld
                                               ctx state)))
      (value (cons lmi-lst lmi-lst-lst))))))

; The code above converts a list of consideration records into a list of
; lists of lemma instances in the form a user could have written them,
; e.g., each lmi looks like (:instance (:functional-instance name ...)
; ...).

; If consideration1 generates u1,1 ... u1,k1, where each u is a lemma
; instance, then we have (and (or u1,1 ... u1,k1) (or u2,1 ... u2,k2)
; ...) and we turn that into a disjunction of conjunctions: (or (and
; u1,1 u2,1 ...) (and u1,1 u2,2 ...) ...).  Thus, we get
; k1*k2*... disjunctions, each of which represents a :USE hint with
; multiple (conjoined) lemma instances in it.

(defun dnf-size (cnf)

; Let cnf be a list of buckets.  Suppose we choose one element from
; each bucket, in all possible ways, as with all-picks.  E.g.,
; (all-picks '((a1 a2) (b1 b2 b3) (c1 c2)) nil) = '((a1 b1 c1) (a2 b1
; c1) ...).  How many combinations are there?

  (cond ((endp cnf) 1)
        (t (* (len (car cnf)) (dnf-size (cdr cnf))))))

(defun convert-considerations-to-dnf (cl considerations wrld ctx state)

; Suppose the first item in considerations generates the lmi-lst (u1,1
; ... u1,k1), where each u is a lemma instance.  And suppose the rest
; generate analogously indexed lmi's.  Then we have a conjunction of
; disjunctions (we get to use each lemma but have multiple choices for
; how):

; (and (or u1,1 ... u1,k1) (or u2,1 ... u2,k2) ...)

; We want a disjunction of conjunctions:

; (or (and u1,1 u2,1 ...) (and u1,1 u2,2 ...) ...).

; Thus, we get k1*k2*... disjunctions, each of which represents a :USE
; hint with multiple (conjoined) lemma instances in it.  If we think
; there are too many combinations, we cause an error.

  (er-let* ((cnf
             (convert-considerations-to-lmi-lst-lst cl considerations wrld
                                                    ctx state)))
    (cond
     ((< 100 (dnf-size cnf))
      (er soft ctx
          "There are ~x0 combinations of substitutions ~
                 suggested by your :consider hint.  We abort when ~
                 there are more than 100.  Sorry."
          (dnf-size cnf)))
     (t (value (all-picks cnf nil))))))

; So now we have a disjunction of conjunctions of lmi's, or, put
; another way, we have disjunction of :USE hints in the form a user
; might have written them, ((:instance (:functional-instance ...) ...)
; ...).


(defun map-list (x lst)

; With apologies to the much more useful maplist!

  (cond ((endp lst) nil)
        (t (cons (list x (car lst))
                 (map-list x (cdr lst))))))

(defun process-considerations (val cl wrld ctx state)

; We use second-order matching to convert the given untranslated
; considerations into an :OR hint of :USE hints.  We either print and
; signal an error or we return an error triple whose value is
; a hint segment to splice in instead of :CONSIDER val.

; Our answer is the list containing the segment:

; :OR ((:USE (u1,1 u2,1 ...)) ...)

; Note that this can generate a singleton :OR.  But we do that on
; purpose because :OR takes the responsibility for printing the
; generated hints.

; We only consider the highest ranked substitutions generated for each
; consider item.  We choose one such substitution for each item, in
; all possible ways, producing a disjunctive split.

; See the Essay on the Implementation of Consider Hint Processing.

  (er-let* ((considerations
             (translate-consider-hint val ctx wrld state))
            (lmi-lst-lst
             (convert-considerations-to-dnf cl considerations wrld
                                            ctx state)))
    (value (cond ((and (consp lmi-lst-lst)
                       (null (cdr lmi-lst-lst)))
                  (list :USE (car lmi-lst-lst)))
                 (t (list :OR (map-list :USE lmi-lst-lst)))))))

(defun put-assoc-keyword (key val keyword-alist)
  (cond
   ((endp keyword-alist)
    (list key val))
   ((eq key (car keyword-alist))
    (cons key (cons val (cddr keyword-alist))))
   (t (cons (car keyword-alist)
            (cons (cadr keyword-alist)
                  (put-assoc-keyword key val (cddr keyword-alist)))))))

(defun consider-hint-generator (val keyword-alist clause world ctx state)
  (er-let* ((or-seg (process-considerations val clause world ctx state)))
    (value
     (put-assoc-keyword
      :merge t
      (splice-keyword-alist
       :consider or-seg
       (splice-keyword-alist
        :merge nil
        keyword-alist))))))

(defun consider-hint-checker (val world ctx state)

; Just to make it obvious that the checker does not actually yeild
; translated considerations (even though it does indeed translate
; them), we define this function.

  (er-let* ((temp (translate-consider-hint val ctx world state)))
    (value nil)))

(defmacro add-consider-hint ()
  '(progn
     (add-merge-hint)
     (add-custom-keyword-hint :consider
                              (consider-hint-generator val keyword-alist
                                                       clause
                                                       world ctx state)
                              :checker
                              (consider-hint-checker val world ctx state))))

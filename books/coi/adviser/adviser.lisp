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

;; adviser.lisp
;; Jared Davis

(in-package "ADVISER")
(include-book "misc/symbol-btree" :dir :system)
(include-book "../symbol-fns/symbol-fns")
(include-book "xdoc/top" :dir :system)
(defmacro defxdoc (&rest args)
  `(acl2::defxdoc ,@args))

; The following legacy doc strings were replaced Nov. 2014 by
; auto-generated defxdoc forms below.

;(defdoc Adviser
; ":Doc-Section Adviser

;  a extensible hint suggestion daemon~/

;  Adviser is a a hint computation service.  When the adviser book is loaded,
;  this service is installed into the ACL2 world as a default hint.  This
;  service is consulted when goals becomes stable under simplification during
;  your proof attempts.  In other words, before destructor elimination,
;  generalization, and so forth are tried, the theorem prover will now first
;  consult the Adviser service and see if any hints is available.  ~/

;  When the Adviser is consulted, it examines the goal that ACL2 is stuck on
;  and checks to see if it can give any suggestions.  To make these
;  suggestions, Adviser consults its own database of rules.  These rules are
;  kept in a new ACL2 ~il[table] that Adviser manages, and efficiently stored
;  using the btree library that comes with ACL2 (see
;  books/misc/symbol-btree.lisp).

;  This database oriented approach has two advantages.  First, users can extend
;  Adviser's knowledge by adding new rules, without having to understand the
;  tricky details of how computed hints work.  (These rules are added through a
;  new event called ~il[adviser::defadvice], which intentionally looks a lot
;  like defthm).  Second, by using a database of triggers, a single pass over
;  each goal is sufficient to determine if advice is necessary.  In contrast,
;  if everyone created their own computed hints, we would have multiple passes
;  over the same goal.

;  ~l[adviser::defadvice] for information on adding rules to Adviser.")

;(defdoc defadvice
; ":Doc-Section Adviser

; adds a rule to the Adviser database~/

; ~bv[]
; General Form:
; (defadvice rule-name term
;   :rule-classes rule-classes)
; ~ev[]

; where ~c[name] is a new symbolic name ~l[name], ~c[term] is a term alleged to
; be a useful piece of advice, and ~c[rule-classes] describe the type of advice
; being added and when to suggest hints of this nature.~/

; When Adviser is first loaded, no rules are installed in its database, so it
; will never suggest any hints.  To make Adviser useful, rules must be added to
; it using defadvice.  In principle, many types of advice could be added to the
; Adviser service, and in the future other classes of advice might be added.
; But, for now, the only understood rule class is :pick-a-point.

; ~l[adviser::pick-a-point] for documentation and examples about :pick-a-point
; rules.")

;(defdoc pick-a-point
; ":Doc-Section Adviser

; make some :pick-a-point rules~/

; ~bv[]
; Example:
; (defadvice subbag-by-multiplicity
;   (implies (bag-hyps)
;            (subbagp (subbag) (superbag))))
; ~ev[]~/
;
; I described how the pick-a-point method can be useful for proving subsets in
; the 2004 ACL2 Workshop Paper: Finite Set Theory based on Fully Ordered Lists.
; Essentially, the idea is to you should be able to prove (subset x y) by just
; knowing that forall a, (in a x) implies (in a y).  Since writing that paper,
; I have found the pick a point method to be widely useful in other contexts
; that involve extending a predicate to some data structure.

; Often we will have some simple predicate, say ~c[integerp], which we will
; want to extend over some datastructure, say a list.  The result is a new,
; recursively defined predicate, say ~c[all-integerp].  Of course, it should be
; obvious that if every member of the list satisfies ~c[integerp], then the
; entire list satisfies ~c[all-integerp].  But, we can't write a :rewrite rule
; such as:

; ~bv[]
;   (equal (all-integerp x)
;          (forall a (implies (member a x) (integerp a))))
; ~ev[]

; Because all of the variables in our :rewrite rules must be universally
; quantified.  The :pick-a-point rules in Adviser are designed to make exactly
; this kind of reduction.  As an example, I'll now elaborate on how to set up
; such a reduction for ~c[all-integerp].  You will find that many other ideas,
; such as subsets, subtree, subbag relations, and so forth, are basically just
; copies of this idea.

; We begin with our definition of all-integerp.  (We do not use integer-listp
; because it requires its argument to be a true-listp.)

; ~bv[]
; (defun all-integerp (x)
;   (if (consp x)
;       (and (integerp (car x))
;            (all-integerp (cdr x)))
;     t))
; ~ev[]

; Our first task is to write our ``forall'' statement as a constraint theorem
; about encapsulated functions.  Becuase we are quantifying over all ``a'', it
; will be a variable in this constrained theorem.  However, since ``x'' is not
; being quantified, we will create a constrained function for it.  For reasons
; we will explain later, we will also have one more constrianed function called
; ``hyps''.  In all, we come up with the following encapsulate:

; ~bv[]
; (encapsulate
;  (((intlist-hyps) => *)
;   ((intlist-list) => *))
;  (local (defun intlist-hyps () nil))
;  (local (defun intlist-list () nil))
;  (defthm intlist-constraint
;    (implies (and (intlist-hyps)
;                  (member intlist-element (intlist-list)))
;             (integerp intlist-element))
;    :rule-classes nil))
; ~ev[]

; Our next goal is to prove that, given this constraint, it must be the case
; that (integer-listp (intlist-list)) is true.  The proof is not entirely
; straightforward, but follows the same script each time.  Basically, we first
; set up a ``badguy'' function that will go through and find an element that
; violates our constraint if one exists.  We show that the badguy finds such
; an element whenever ``all-integerp'' is not satisifed.  Then, we just use
; the instance of our constraint to show that all-integerp must be true for
; (intlist-list).

; ~bv[]
; (local (defun badguy (x)
;          (if (endp x)
;              nil
;            (if (integerp (car x))
;                (badguy (cdr x))
;              (car x)))))
;
; (local (defthm badguy-works
;          (implies (not (all-integerp x))
;                   (and (member (badguy x) x)
;                        (not (integerp (badguy x)))))))

; (defthm intlist-by-membership-driver
;   (implies (intlist-hyps)
;            (all-integerp (intlist-list)))
;   :rule-classes nil
;   :hints((\"Goal\"
;           :use (:instance intlist-constraint
;                           (intlist-element (badguy (intlist-list)))))))
; ~ev[]
;
; At this point, we have essentially shown ACL2 that ``all-integerp`` can
; be shown as long as we can show our constraint is true.  The missing step
; is for ACL2 to actually try this approach for us.  But we can't write a
; rewrite rule that says ``try to functionally instantiate this theorem
; whenever you are trying to prove (all-integerp x).''

; That's where Adviser comes in.  We just give it the following rule:

; ~bv[]
; (ADVISER::defadvice intlist-by-membership
;   (implies (intlist-hyps)
;            (all-integerp (intlist-list)))
;   :rule-classes (:pick-a-point :driver intlist-by-membership-driver))
; ~ev[]

; Because we used defadvice, rather than defthm, this rule is for Adviser
; to add to its database.  Adviser will set up a new trigger for
; all-integerp, and whenever it sees that trigger as the target that we
; are trying to prove, it will functionally instantiate the driver theorem.
; We can now conduct membership based proofs of all-integerp.

; For example, in the following script we can prove that (all-integerp (rev x))
; exactly when (all-integerp x) without inducting over either function,
; because we can just consider membership.

; ~bv[]
; (defthm equal-of-booleans-rewrite
;   (implies (and (booleanp x)
;                 (booleanp y))
;            (equal (equal x y)
;                   (iff x y)))
;   :rule-classes ((:rewrite :backchain-limit-lst 0)))

; (defthm member-of-all-integerp-1
;   (implies (and (member a x)
;                 (all-integerp x))
;            (integerp a)))

; (defthm member-of-all-integerp-2
;   (implies (and (all-integerp x)
;                 (not (integerp a)))
;            (not (member a x))))

; (in-theory (disable all-integerp))

; (defund rev (x)
;   (if (endp x)
;       x
;     (append (rev (cdr x))
;             (list (car x)))))

; (defthm member-of-rev
;   (iff (member a (rev x))
;        (member a x))
;   :hints((\"Goal\" :in-theory (enable rev))))

; (encapsulate
;  ()

;  (local (defthm lemma1
;           (implies (all-integerp x)
;                    (all-integerp (rev x)))))
;
;  (local (defthm lemma2
;           (implies (all-integerp (rev x))
;                    (all-integerp x))
;           :hints((\"Subgoal 1\" :use (:instance member-of-all-integerp-1
;                                                 (a intlist-element)
;                                                 (x (rev x)))))))

;  (defthm all-integerp-of-rev
;    (equal (all-integerp (rev x))
;           (all-integerp x)))
;  )
; ~ev[]")

(defxdoc adviser::adviser
  :parents (adviser::adviser)
  :short "A extensible hint suggestion daemon"
  :long "<p>Adviser is a a hint computation service.  When the adviser book is
 loaded, this service is installed into the ACL2 world as a default hint.  This
 service is consulted when goals becomes stable under simplification during
 your proof attempts.  In other words, before destructor elimination,
 generalization, and so forth are tried, the theorem prover will now first
 consult the Adviser service and see if any hints is available.</p>

 <p>When the Adviser is consulted, it examines the goal that ACL2 is stuck on
 and checks to see if it can give any suggestions.  To make these suggestions,
 Adviser consults its own database of rules.  These rules are kept in a new
 ACL2 @(see table) that Adviser manages, and efficiently stored using the btree
 library that comes with ACL2 (see books/misc/symbol-btree.lisp).</p>

 <p>This database oriented approach has two advantages.  First, users can
 extend Adviser's knowledge by adding new rules, without having to understand
 the tricky details of how computed hints work.  (These rules are added through
 a new event called @(see adviser::defadvice), which intentionally looks a lot
 like defthm).  Second, by using a database of triggers, a single pass over
 each goal is sufficient to determine if advice is necessary.  In contrast, if
 everyone created their own computed hints, we would have multiple passes over
 the same goal.</p>

 <p>See @(see adviser::defadvice) for information on adding rules to
 Adviser.</p>")

(defxdoc adviser::defadvice
  :parents (adviser::adviser)
  :short "Adds a rule to the Adviser database"
  :long "@({
  General Form:
  (defadvice rule-name term
    :rule-classes rule-classes)
 })

 <p>where @('name') is a new symbolic name See @(see acl2::name), @('term') is a term
 alleged to be a useful piece of advice, and @('rule-classes') describe the
 type of advice being added and when to suggest hints of this nature.</p>

 <p>When Adviser is first loaded, no rules are installed in its database, so it
 will never suggest any hints.  To make Adviser useful, rules must be added to
 it using defadvice.  In principle, many types of advice could be added to the
 Adviser service, and in the future other classes of advice might be added.
 But, for now, the only understood rule class is :pick-a-point.</p>

 <p>See @(see adviser::pick-a-point) for documentation and examples about
 :pick-a-point rules.</p>")

(defxdoc adviser::pick-a-point
  :parents (adviser::adviser)
  :short "Make some :pick-a-point rules"
  :long "@({
  Example:
  (defadvice subbag-by-multiplicity
    (implies (bag-hyps)
             (subbagp (subbag) (superbag))))
 })

 <p>I described how the pick-a-point method can be useful for proving subsets
 in the 2004 ACL2 Workshop Paper: Finite Set Theory based on Fully Ordered
 Lists.  Essentially, the idea is to you should be able to prove (subset x y)
 by just knowing that forall a, (in a x) implies (in a y).  Since writing that
 paper, I have found the pick a point method to be widely useful in other
 contexts that involve extending a predicate to some data structure.</p>

 <p>Often we will have some simple predicate, say @('integerp'), which we will
 want to extend over some datastructure, say a list.  The result is a new,
 recursively defined predicate, say @('all-integerp').  Of course, it should be
 obvious that if every member of the list satisfies @('integerp'), then the
 entire list satisfies @('all-integerp').  But, we can't write a :rewrite rule
 such as:</p>

 @({
    (equal (all-integerp x)
           (forall a (implies (member a x) (integerp a))))
 })

 <p>Because all of the variables in our :rewrite rules must be universally
 quantified.  The :pick-a-point rules in Adviser are designed to make exactly
 this kind of reduction.  As an example, I'll now elaborate on how to set up
 such a reduction for @('all-integerp').  You will find that many other ideas,
 such as subsets, subtree, subbag relations, and so forth, are basically just
 copies of this idea.</p>

 <p>We begin with our definition of all-integerp.  (We do not use integer-listp
 because it requires its argument to be a true-listp.)</p>

 @({
  (defun all-integerp (x)
    (if (consp x)
        (and (integerp (car x))
             (all-integerp (cdr x)))
      t))
 })

 <p>Our first task is to write our ``forall'' statement as a constraint theorem
 about encapsulated functions.  Becuase we are quantifying over all ``a'', it
 will be a variable in this constrained theorem.  However, since ``x'' is not
 being quantified, we will create a constrained function for it.  For reasons
 we will explain later, we will also have one more constrianed function called
 ``hyps''.  In all, we come up with the following encapsulate:</p>

 @({
  (encapsulate
   (((intlist-hyps) => *)
    ((intlist-list) => *))
   (local (defun intlist-hyps () nil))
   (local (defun intlist-list () nil))
   (defthm intlist-constraint
     (implies (and (intlist-hyps)
  		   (member intlist-element (intlist-list)))
  	      (integerp intlist-element))
     :rule-classes nil))
 })

 <p>Our next goal is to prove that, given this constraint, it must be the case
 that (integer-listp (intlist-list)) is true.  The proof is not entirely
 straightforward, but follows the same script each time.  Basically, we first
 set up a ``badguy'' function that will go through and find an element that
 violates our constraint if one exists.  We show that the badguy finds such an
 element whenever ``all-integerp'' is not satisifed.  Then, we just use the
 instance of our constraint to show that all-integerp must be true for
 (intlist-list).</p>

 @({
  (local (defun badguy (x)
           (if (endp x)
               nil
             (if (integerp (car x))
                 (badguy (cdr x))
               (car x)))))

  (local (defthm badguy-works
           (implies (not (all-integerp x))
                    (and (member (badguy x) x)
                         (not (integerp (badguy x)))))))

  (defthm intlist-by-membership-driver
    (implies (intlist-hyps)
             (all-integerp (intlist-list)))
    :rule-classes nil
    :hints((\"Goal\"
            :use (:instance intlist-constraint
                            (intlist-element (badguy (intlist-list)))))))
 })

 <p>

 At this point, we have essentially shown ACL2 that ``all-integerp`` can be
 shown as long as we can show our constraint is true.  The missing step is for
 ACL2 to actually try this approach for us.  But we can't write a rewrite rule
 that says ``try to functionally instantiate this theorem whenever you are
 trying to prove (all-integerp x).''</p>

 <p>That's where Adviser comes in.  We just give it the following rule:</p>

 @({
  (ADVISER::defadvice intlist-by-membership
    (implies (intlist-hyps)
             (all-integerp (intlist-list)))
    :rule-classes (:pick-a-point :driver intlist-by-membership-driver))
 })

 <p>Because we used defadvice, rather than defthm, this rule is for Adviser to
 add to its database.  Adviser will set up a new trigger for all-integerp, and
 whenever it sees that trigger as the target that we are trying to prove, it
 will functionally instantiate the driver theorem.  We can now conduct
 membership based proofs of all-integerp.</p>

 <p>For example, in the following script we can prove that (all-integerp (rev
 x)) exactly when (all-integerp x) without inducting over either function,
 because we can just consider membership.</p>

 @({
  (defthm equal-of-booleans-rewrite
    (implies (and (booleanp x)
                  (booleanp y))
             (equal (equal x y)
                    (iff x y)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm member-of-all-integerp-1
    (implies (and (member a x)
                  (all-integerp x))
             (integerp a)))

  (defthm member-of-all-integerp-2
    (implies (and (all-integerp x)
                  (not (integerp a)))
             (not (member a x))))

  (in-theory (disable all-integerp))

  (defund rev (x)
    (if (endp x)
        x
      (append (rev (cdr x))
              (list (car x)))))

  (defthm member-of-rev
    (iff (member a (rev x))
         (member a x))
    :hints((\"Goal\" :in-theory (enable rev))))

  (encapsulate
   ()

   (local (defthm lemma1
            (implies (all-integerp x)
                     (all-integerp (rev x)))))

   (local (defthm lemma2
            (implies (all-integerp (rev x))
                     (all-integerp x))
            :hints((\"Subgoal 1\" :use (:instance member-of-all-integerp-1
                                                  (a intlist-element)
                                                  (x (rev x)))))))

   (defthm all-integerp-of-rev
     (equal (all-integerp (rev x))
            (all-integerp x)))
   )
 })

 ")

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

(defun rewriting-any-lit (term mfc state)
  "Rewrite any appearance in the goal"
  (declare (xargs :stobjs state)
	   (ignore state))
  (let ((clause (mfc-clause mfc)))
    (member-equal term clause)))

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

(defmacro symbols (n)
  "Generate a list of symbols, ACL2::X1 through ACL2::Xn."
  `(aux-symbols ,n nil))

;; Rules are stored in the following table.  You can add your own rule classes
;; by adding an extra table command for each class.

(table adviser-table :pick-a-point-rules nil)



;; ----------------------------------------------------------------------------
;;
;;                          Pick a Point Rules
;;
;; ----------------------------------------------------------------------------


;; Pick a point rules are stored in the :pick-a-point-rules entry of the
;; adviser-table, which is a btree.  We can access this btree using the
;; following function.

(defun pick-a-point-rules (world)
  (declare (xargs :guard (and (plist-worldp world)
                              (alistp (table-alist 'adviser-table world)))))
  (cdr (assoc-eq :pick-a-point-rules (table-alist 'adviser-table world))))





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
	 (name-any (symbol-fns::join-symbols name name '-any))
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

    ;; Next we create a theorem that rewrites function to our trigger in
    ;; any appropriate circumstance.  This may rewrite terms from the
    ;; hypothesis .. which may be undesirable .. so for now we disable it.
    (defthmd ,name-any
      (implies (and (syntaxp (rewriting-goal-lit mfc state))
                    (syntaxp (rewriting-any-lit
			      ,(if negatedp
                                   `(list 'not (list ',function ,@(strip-cars args)))
                                 `(list ',function ,@(strip-cars args)))
			      mfc state)))
               (equal (,function ,@(strip-cars args))
                      (,trigger ,@(strip-cars args))))
      :hints(("Goal" :in-theory (union-theories (theory 'minimal-theory)
                                                '((:definition ,trigger))))))

    ;; Next we create a theorem that rewrites function to our trigger in more
    ;; appropriate circumstances .. when the term is the conclusion of the goal.
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

(defconst *pick-a-point-message*
  "~|~%[Adviser]: We suspect this conjecture should be proven by functional ~
  instantiation of the following, generic theorems: ~x0.  We only make this ~
  suggestion because of following triggering rules: ~x1.  If you do not want ~
  to use functional instantiation here, you should disable these triggering ~
  rules.~%~%  We provide the following hint: ~%~%~x2~%")

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
		       (use   `(:use ,(build-hints literals rules hyps nil)))
                       (hints `(:computed-hint-replacement
                                ('(:computed-hint-replacement
                                   ((adviser-default-hint id clause world stable-under-simplificationp)) ; ',(current-theory :here)))
                                   ,@use))
				;;:in-theory (disable ,@(get-names rules))
                                :expand ,(build-expand-hint literals))))
                  (prog2$ (cw *pick-a-point-message*
                              (get-thms rules)
                              (get-names rules)
                              (list (ACL2::string-for-tilde-@-clause-id-phrase id) use))
                          hints)))))))

(defun adviser-default-hint (id clause world stable) ;; theory)
  (declare (xargs :mode :program))
  (if (not stable)
      nil
;;     (if theory
;; 	`(:computed-hint-replacement
;; 	  ((adviser-default-hint id clause world stable-under-simplificationp 'nil))
;; 	  :expand nil
;; 	  :in-theory ',theory)
      (or (pick-a-point-suggester id clause world)
	  nil)))

(add-default-hints!
 '((adviser-default-hint id clause world stable-under-simplificationp))) ;; 'nil)))





;; ----------------------------------------------------------------------------
;;
;;                           The Defadvice Macro
;;
;; ----------------------------------------------------------------------------

(defconst *supported-rule-classes*
  '(:pick-a-point))

(defmacro defadvice (name term &key rule-classes)
  (if (and (consp rule-classes)
           (member (car rule-classes) *supported-rule-classes*))
      (case (car rule-classes)
        (:pick-a-point
         (pick-a-point-rule-defadvice name term rule-classes))
        (otherwise
         (er hard 'defadvice
             ":rule-classes ~x0 is allegedly supported, but has not ~
             been implemented!~%" (car rule-classes))))
    (er hard 'defadvice
        ":rule-classes must be a list, e.g., (:pick-a-point :driver thm), ~
        but is ~x0.~%" rule-classes)))

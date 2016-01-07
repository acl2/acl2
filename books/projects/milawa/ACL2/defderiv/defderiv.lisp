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
(include-book "context")
(include-book "latex")
(set-verify-guards-eagerness 2)
(set-case-split-limitations nil)
(set-well-founded-relation ord<)
(set-measure-function rank)


(acl2::defttag acl2::open-output-channel!)

(defun dd.open-output-channel (filename type ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (ACL2::mv-let (channel ACL2::state)
    (ACL2::open-output-channel! filename type ACL2::state)
    (ACL2::prog2$
      (or channel
          (ACL2::er ACL2::hard? 'dd.open-output-channel
                    "Failed to open file ~x0 for output." filename))
      (ACL2::mv channel ACL2::state))))



;; Derivation cost estimation.
;;
;; We maintain a table that includes cost estimates for simple builders.
;; Initially we say that the "price" of each primitive builder is 1, and that
;; each given costs 0.  Then, given a derivation, we can try to sum the costs
;; associated with each step.  If all the costs are defined, we will have
;; successfully made an estimate.

(ACL2::table milawa 'builder-costs
             '((@given . 0)
               (build.axiom . 1)
               (build.theorem . 1)
               (build.propositional-schema . 1)
               (build.cut . 1)
               (build.contraction . 1)
               (build.expansion . 1)
               (build.associativity . 1)
               (build.instantiation . 1)
               (build.functional-equality . 1)
               (build.beta-reduction . 1)
               (build.base-eval . 1)))

(defun dd.get-builder-costs (wrld)
  (declare (xargs :mode :program))
  (cdr (lookup 'builder-costs (ACL2::table-alist 'milawa wrld))))

(defun dd.estimate-cost-of-lines (lines wrld)
  (declare (xargs :mode :program))
  (if (consp lines)
      (let* ((justification (second (car lines)))
             (lookup        (cdr (lookup (first justification) (dd.get-builder-costs wrld)))))
        (and lookup
             (+ lookup (dd.estimate-cost-of-lines (cdr lines) wrld))))
    0))




(defun dd.all-deriv-local-axioms (x)
  (declare (xargs :mode :program))
  (cond ((not (consp x))
         x)
        ((equal (car x) '@derive)
         (dd.deriv-local-axioms (cdr x)))
        (t
         (app (dd.all-deriv-local-axioms (car x))
              (dd.all-deriv-local-axioms (cdr x))))))

(defun dd.all-deriv-local-theorems (x)
  (declare (xargs :mode :program))
  (cond ((not (consp x))
         x)
        ((equal (car x) '@derive)
         (dd.deriv-local-theorems (cdr x)))
        (t
         (app (dd.all-deriv-local-theorems (car x))
              (dd.all-deriv-local-theorems (cdr x))))))

(defun dd.all-deriv-inherited-axioms (x wrld)
  (declare (xargs :mode :program))
  (cond ((not (consp x))
         x)
        ((equal (car x) '@derive)
         (dd.deriv-inherited-axioms (cdr x) wrld))
        (t
         (app (dd.all-deriv-inherited-axioms (car x) wrld)
              (dd.all-deriv-inherited-axioms (cdr x) wrld)))))

(defun dd.all-deriv-inherited-theorems (x wrld)
  (declare (xargs :mode :program))
  (cond ((not (consp x))
         x)
        ((equal (car x) '@derive)
         (dd.deriv-inherited-theorems (cdr x) wrld))
        (t
         (app (dd.all-deriv-inherited-theorems (car x) wrld)
              (dd.all-deriv-inherited-theorems (cdr x) wrld)))))






;; (defderiv <name>
;;   :derive <formula>
;;   :from   <multi-patterns>
;;   :proof  <deriv>)
;;
;; Defderiv allows us to introduce a simple derivation using matching and
;; @derive style lines.


(defun dd.defderiv-formals (from)
  ;; We analyze the :from <multi-patterns> section and extract all the paths.
  ;; We expect that each path is a simple variable.  These variables become the
  ;; inputs to our builder function.
  (declare (xargs :mode :program))
  (if (consp from)
      (let ((path (second (car from))))
        (if (not (logic.variablep path))
            (ACL2::er ACL2::hard 'dd.defderiv-formals
                      "All paths in defderiv :from multi-patterns must be variables.~%")
          (cons path (dd.defderiv-formals (cdr from)))))
    nil))

(defun dd.count-proofs (x)
  ;; X is the :from <multi-patterns> object.
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((type (first (car x))))
        (if (equal type 'proof)
            (+ 1 (dd.count-proofs (cdr x)))
          (dd.count-proofs (cdr x))))
    0))

(defun dd.build-subproofs-matching-code (x path)
  ;; X is the :from <multi-patterns> object.  We write code to check that a list of
  ;; subproofs match the proofs in these patterns.  This code will be given to a new
  ;; @match.  So, for example, we write:
  ;;
  ;;   (proof (car subproofs) pattern-1)
  ;;   (proof (car (cdr subproofs)) pattern-2)
  ;;   ...
  ;;   (proof (car (cdr (cdr ...))) pattern-N)
  ;;
  ;; Path is just an accumulator which begins with "subproofs", then "(cdr subproofs)",
  ;; etc.
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((type (first (car x)))
            (pattern (third (car x))))
        (cond ((equal type 'proof)
               (cons `(proof (car ,path) ,pattern)
                     (dd.build-subproofs-matching-code (cdr x) `(cdr ,path))))
              ((or (equal type 'term)
                   (equal type 'formula))
               (dd.build-subproofs-matching-code (cdr x) path))
              (t
               ;; I think constant is not a valid option anymore.  It's handled by
               ;; where instead.
               (ACL2::er ACL2::hard 'dd.build-subproofs-matching-code
                         "Invalid entry ~x0.~%" (car x)))))
    nil))

(defun dd.build-subproofs-witness-code (x path)
  ;; X is the :from <multi-patterns> object.  Our job is to provide an argument list
  ;; that can be used to instantiate a call of this builder, using the provable
  ;; witnesses for its subproofs.  For example,
  ;;
  ;;  :from ((term a [term-pattern])
  ;;         (proof b [proof-pattern-b])
  ;;         (formula c [formula-pattern])
  ;;         (proof d [proof-pattern-d]))
  ;;  --->
  ;;
  ;;   (  (@term [term-pattern])
  ;;      (logic.provable-witness (logic.conclusion (car subproofs)) axioms thms atbl)
  ;;      (@formula [formula-pattern])
  ;;      (logic.provable-witness (logic.conclusion (car (cdr subproofs))) axioms thms atbl)  )
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((type (first (car x)))
            (pattern (third (car x))))
        (cond ((equal type 'term)
               (cons `(@term ,pattern)
                     (dd.build-subproofs-witness-code (cdr x) path)))
              ((equal type 'formula)
               (cons `(@formula ,pattern)
                     (dd.build-subproofs-witness-code (cdr x) path)))
              ((equal type 'proof)
               (cons `(logic.provable-witness (logic.conclusion (car ,path)) axioms thms atbl)
                     (dd.build-subproofs-witness-code (cdr x) `(cdr ,path))))
              (t
               ;; I think constant is not a valid option anymore.  It's handled by where
               ;; instead.
               (ACL2::er ACL2::hard 'dd.build-subproofs-witness-code
                         "Invalid entry ~x0.~%" (car x)))))
    nil))

(defun dd.names-of-subproofs (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (let ((type (first (car x)))
            (name (second (car x))))
        (if (equal type 'proof)
            (cons name (dd.names-of-subproofs (cdr x)))
          (dd.names-of-subproofs (cdr x))))
    nil))

(defun dd.defderiv-extra-guards (from)
  ;; These are the hyps we add to @match for the logic.appealp
  ;; theorem, the conclusion theorem, and for the function's guards.
  (declare (xargs :mode :program))
  (if (consp from)
      (let ((type (first (car from)))
            (path (second (car from))))
        (cond ((equal type 'term)
               (cons `(logic.termp ,path)
                     (dd.defderiv-extra-guards (cdr from))))
               ((equal type 'formula)
               (cons `(logic.formulap ,path)
                     (dd.defderiv-extra-guards (cdr from))))
              ((equal type 'proof)
               (cons `(logic.appealp ,path)
                     (dd.defderiv-extra-guards (cdr from))))
              ((equal type 'constant)
               (dd.defderiv-extra-guards (cdr from)))
              (t
               (ACL2::er ACL2::hard 'dd.defderiv-extra-guards
                         "Invalid entry ~x0~%" (car from)))))
    nil))

(defun dd.defderiv-extra-guards-atbl (from)
  ;; These are the hyps we add to @match for the logic.appeal-atblp theorem.
  (declare (xargs :mode :program))
  (if (consp from)
      (let ((type (first (car from)))
            (path (second (car from))))
        (cond ((equal type 'term)
               (cons `(logic.termp ,path)
                     (cons `(logic.term-atblp ,path atbl)
                           (dd.defderiv-extra-guards-atbl (cdr from)))))
              ((equal type 'formula)
               (cons `(logic.formulap ,path)
                     (cons `(logic.formula-atblp ,path atbl)
                           (dd.defderiv-extra-guards-atbl (cdr from)))))
              ((equal type 'proof)
               (cons `(logic.appealp ,path)
                     (cons `(logic.appeal-atblp ,path atbl)
                           (dd.defderiv-extra-guards-atbl (cdr from)))))
              ((equal type 'constant)
               (dd.defderiv-extra-guards-atbl (cdr from)))
              (t
               (ACL2::er ACL2::hard 'dd.defderiv-extra-guards-atbl
                         "Invalid entry ~x0~%" (car from)))))
    nil))

(defun dd.defderiv-extra-guards-proofp (from)
  ;; These are the guards we add to @match for the logic.proofp theorem.
  (declare (xargs :mode :program))
  (if (consp from)
      (let ((type (first (car from)))
            (path (second (car from))))
        (cond ((equal type 'term)
               (cons `(logic.termp ,path)
                     (cons `(logic.term-atblp ,path atbl)
                           (dd.defderiv-extra-guards-proofp (cdr from)))))
              ((equal type 'formula)
               (cons `(logic.formulap ,path)
                     (cons `(logic.formula-atblp ,path atbl)
                           (dd.defderiv-extra-guards-proofp (cdr from)))))
              ((equal type 'proof)
               (cons `(logic.appealp ,path)
                     (cons `(logic.proofp ,path axioms thms atbl)
                           (dd.defderiv-extra-guards-proofp (cdr from)))))
              ((equal type 'constant)
               (dd.defderiv-extra-guards-proofp (cdr from)))
              (t
               (ACL2::er ACL2::hard 'dd.defderiv-extra-guards-proofp
                         "Invalid entry ~x0~%" (car from)))))
    nil))




;; For the recognizer, we need to do arity checks on any new formulas or terms that have
;; been supplied.

(defun dd.defderiv-atbl-checks-for-okp (from)
  (declare (xargs :mode :program))
  (if (consp from)
      (let ((type (first (car from)))
            ;(path (second (car from)))
            (pat  (third (car from))))
        (cond ((equal type 'term)
               (cons `(logic.term-atblp (@term ,pat) atbl)
                     (dd.defderiv-atbl-checks-for-okp (cdr from))))
              ((equal type 'formula)
               (cons `(logic.formula-atblp (@formula ,pat) atbl)
                     (dd.defderiv-atbl-checks-for-okp (cdr from))))
              (t
               (dd.defderiv-atbl-checks-for-okp (cdr from)))))
    nil))


;; We can probably eventually automate the minimum atbl requirements for the
;; logic.appealp and logic.proofp theorems, but for now we will just have the user supply
;; it as an atbl fragment, i.e., ((if . 3) (equal . 2)), etc.

(defun dd.minatbl-to-checks (minatbl)
  (declare (xargs :mode :program))
  (if (consp minatbl)
      (let ((fn (car (car minatbl)))
            (arity (cdr (car minatbl))))
        (cons `(equal (cdr (lookup ',fn atbl)) ,arity)
              (dd.minatbl-to-checks (cdr minatbl))))
    nil))


;; We save some information for bootstrapping in the info-for-%defderiv table.
(ACL2::table milawa 'info-for-%defderiv nil)

(defun dd.get-info-for-%defderiv (world)
  (declare (xargs :mode :program))
  (cdr (lookup 'info-for-%defderiv (ACL2::table-alist 'milawa world))))

(defun dd.defderiv-fn (name from derive where proof minatbl highlevel-override wrld)
  (declare (xargs :mode :program))
  (let* ((formals              (dd.defderiv-formals from))
         (extra-guards         (dd.defderiv-extra-guards from))
         (extra-guards-proofp  (dd.defderiv-extra-guards-proofp from))
         (local-axioms         (dd.all-deriv-local-axioms proof))
         (local-theorems       (dd.all-deriv-local-theorems proof))
         (all-axioms           (cdr (lookup name (dd.get-builder-axioms wrld))))
         (all-theorems         (cdr (lookup name (dd.get-builder-theorems wrld))))
         (atbl-checks          (dd.minatbl-to-checks minatbl))
         (name-okp             (ACL2::mksym name '-okp))
         (name-high            (ACL2::mksym name '-high)))
    `(encapsulate
      ()
      ;; We begin by introducing the proof builder and proving the theorems about
      ;; it conclusion, appeal-ness, and proof-ness.
      (encapsulate
       ()
       ,@(if (or local-axioms local-theorems)
             `((local (in-theory (enable ,@(strip-firsts local-axioms)
                                         ,@(strip-firsts local-theorems)))))
           nil)

       (defund@ ,name ,formals
         (declare (xargs :guard (and ,@extra-guards
                                     (@match ,@from)
                                     ,@where)))
         ,proof)

       (in-theory (disable (:executable-counterpart ,name)))

       (local (in-theory (enable ,name)))

       (defthm@ ,(ACL2::mksym name '-under-iff)
         (iff (,name ,@formals)
              t)
         :hints(("Goal" :in-theory (disable (:executable-counterpart acl2::force)))))

       (defthm@ ,(ACL2::mksym 'forcing-logic.appealp-of- name)
         (implies (force (and ,@extra-guards
                              (@match ,@from)
                              ,@where))
                  (equal (logic.appealp (,name ,@formals))
                         t)))

       (defthm@ ,(ACL2::mksym 'forcing-logic.conclusion-of- name)
         (implies (force (and ,@extra-guards
                              (@match ,@from)
                              ,@where))
                  (equal (logic.conclusion (,name ,@formals))
                         (@formula ,derive)))
         :rule-classes ((:rewrite :backchain-limit-lst 0)))

       (defthm@ ,(ACL2::mksym 'forcing-logic.proofp-of- name)
         (implies (force (and ,@extra-guards-proofp
                              (@match ,@from)
                              ,@atbl-checks
                              ,@(dd.make-members all-axioms 'axioms)
                              ,@(dd.make-members all-theorems 'thms)
                              ,@where))
                  (equal (logic.proofp (,name ,@formals) axioms thms atbl)
                         t))))

       (@context
        (@expand ((proof x ,derive))
                 (ACL2::table milawa 'info-for-%defderiv
                              (cons (list ',name
                                          ',local-axioms
                                          ',local-theorems
                                          ',(dd.build-subproofs-witness-code from '(logic.subproofs x))
                                          )
                                    (dd.get-info-for-%defderiv ACL2::world)))))

      ;; Now we introduce a recognizer for these kinds of steps.
       ;; we should do a better job of avoiding atbl if we can
      (defund@ ,name-okp (x atbl)
        (declare (xargs :guard (and (logic.appealp x)
                                    (logic.arity-tablep atbl)))
                 (ACL2::ignorable atbl))
        (let ((method     (logic.method x))
              (conclusion (logic.conclusion x))
              (subproofs  (logic.subproofs x))
              (extras     (logic.extras x)))
          (and (equal method ',name)
               (equal extras nil)
               (equal (len subproofs) ,(dd.count-proofs from))
               (@match (formula conclusion ,derive)
                       ,@(dd.build-subproofs-matching-code from 'subproofs))
               ,@(dd.defderiv-atbl-checks-for-okp from)
               ,@where)))

      (local (in-theory (enable ,name-okp)))

      (defthm ,(ACL2::mksym 'booleanp-of- name-okp)
        (equal (booleanp (,name-okp x atbl))
               t)
        :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

      (defthm ,(ACL2::mksym name-okp '-of-logic.appeal-identity)
        (equal (,name-okp (logic.appeal-identity x) atbl)
               (,name-okp x atbl))
        :hints(("Goal" :in-theory (disable (:executable-counterpart ACL2::force)))))

      (encapsulate
       ()
       (local (in-theory (e/d (backtracking-logic.formula-atblp-rules)
                              (forcing-logic.formula-atblp-rules
                               forcing-lookup-of-logic.function-name-free
                               forcing-logic.term-list-atblp-of-logic.function-args
                               ))))

       (defthmd@ ,(ACL2::mksym 'lemma-1-for-soundness-of- name-okp)
         (@expand ((proof x ,derive)) ;; so we can match vars in the conclusion
                  (implies (and (,name-okp x atbl)
                                (logic.appealp x)
                                ;; NEW: we don't assume it's an formula-atbl.
                                ;; (logic.formula-atblp (logic.conclusion x) atbl)
                                (logic.formula-list-atblp (logic.strip-conclusions (logic.subproofs x)) atbl)
                                (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl))
                           (equal (logic.conclusion (,name ,@(dd.build-subproofs-witness-code from '(logic.subproofs x))))
                                  (logic.conclusion x)))))

       (defthmd@ ,(ACL2::mksym 'lemma-2-for-soundness-of- name-okp)
         (@expand ((proof x ,derive)) ;; so we can match vars in the conclusion
                  (implies (and (,name-okp x atbl)
                                (logic.appealp x)
                                ;; NEW: we don't assume it's an formula-atbl.
                                ;; (logic.formula-atblp (logic.conclusion x) atbl)
                                (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                                ,@atbl-checks
                                ,@(dd.make-members all-axioms 'axioms)
                                ,@(dd.make-members all-theorems 'thms))
                           (equal (logic.proofp
                                   (,name ,@(dd.build-subproofs-witness-code from '(logic.subproofs x)))
                                   axioms thms atbl)
                                  t)))))

      (defthm@ ,(ACL2::mksym 'forcing-soundness-of- name-okp)
        (@expand ((proof x ,derive)) ;; so we can match vars in the conclusion
                 (implies (and (,name-okp x atbl)
                               (force (and (logic.appealp x)
                                           ;; NEW: we don't assume it's an formula-atbl.
                                           ;;(logic.formula-atblp (logic.conclusion x) atbl)
                                           (logic.provable-listp (logic.strip-conclusions (logic.subproofs x)) axioms thms atbl)
                                           ,@atbl-checks
                                           ,@(dd.make-members all-axioms 'axioms)
                                           ,@(dd.make-members all-theorems 'thms))))
                          (equal (logic.provablep (logic.conclusion x) axioms thms atbl)
                                 t)))
        :hints(("Goal"
                :in-theory (enable ,(ACL2::mksym 'lemma-1-for-soundness-of- name-okp)
                                   ,(ACL2::mksym 'lemma-2-for-soundness-of- name-okp))
                :use (:instance forcing-logic.provablep-when-logic.proofp
                                (x (,name ,@(dd.build-subproofs-witness-code from '(logic.subproofs x))))))))

      ;; We finally introduce the corresponding high-level builder.

      (defund@ ,name-high ,formals
        (declare (xargs :guard (and ,@extra-guards
                                    (@match ,@from)
                                    ,@where)))
        ,(or highlevel-override
             `(logic.appeal ',name
                            (@formula ,derive)
                            (list ,@(dd.names-of-subproofs from))
                            nil)))

      )))





;; LaTeX support for Derivations

(defconst *dd.max-summary-width* (dd.inches-to-twips 5))
(defconst *dd.max-derive-line-width* (dd.inches-to-twips (acl2::+ 3 3/4)))
(defconst *dd.justify-width* (dd.inches-to-twips 5/4))

(defconst *dd.bldr-name-always-replace*
  ;; Replacements to builder names which are always applied
  (list (cons (dd.explode "pequal")           (dd.explode "$=$"))
        (cons (dd.explode "not pequal")       (dd.explode "$\\neq$"))
        (cons (dd.explode "not =")            (dd.explode "$\\neq$"))
        (cons (dd.explode "not $=$")          (dd.explode "$\\neq$"))
        (cons (dd.explode "nega")             (dd.explode "1hide"))
        (cons (dd.explode "neg")              (dd.explode "$\\neg$"))
        (cons (dd.explode "$\\neg$ $\\neg$")  (dd.explode "$\\neg\\neg$"))
        (cons (dd.explode " bldr")            (dd.explode ""))
        (cons (dd.explode "build.")           (dd.explode ""))
        (cons (dd.explode "tactic.")          (dd.explode ""))
        (cons (dd.explode "clause.")          (dd.explode ""))
        (cons (dd.explode "rw.")              (dd.explode ""))
        (cons (dd.explode "1hide")            (dd.explode "nega"))))

(defconst *dd.bldr-name-maybe-replace*
  ;; Replacements to builder names which are only applied if we want to shorten the name
  (list (cons (dd.explode "disjoined")         (dd.explode "dj."))
        (cons (dd.explode "theorem")           (dd.explode "th."))
        (cons (dd.explode "axiom")             (dd.explode "ax."))
        (cons (dd.explode "associativity")     (dd.explode "assoc."))
        (cons (dd.explode "negative")          (dd.explode "neg."))
        (cons (dd.explode "transitivity of")   (dd.explode "trans."))
        (cons (dd.explode "transitivity")      (dd.explode "trans."))
        (cons (dd.explode "reflexivity of")    (dd.explode "refl."))
        (cons (dd.explode "reflexivity")       (dd.explode "refl."))
        (cons (dd.explode "commutativity of")  (dd.explode "comm."))
        (cons (dd.explode "commutativity")     (dd.explode "comm."))
        (cons (dd.explode "commute")           (dd.explode "comm."))
        (cons (dd.explode "left")              (dd.explode "l."))
        (cons (dd.explode "right")             (dd.explode "r."))
        (cons (dd.explode "modus ponens 2")    (dd.explode "mp2"))
        (cons (dd.explode "modus ponens")      (dd.explode "mp"))
        (cons (dd.explode "propositional")     (dd.explode "prop."))
        (cons (dd.explode "normalize")           (dd.explode "norm."))
        (cons (dd.explode "contraction")         (dd.explode "contr."))
        (cons (dd.explode "implications")        (dd.explode "imp."))
        (cons (dd.explode "implies")             (dd.explode "imp."))
        (cons (dd.explode "equal")               (dd.explode "eq."))
        (cons (dd.explode "specialcase")         (dd.explode "sp."))
        (cons (dd.explode "substitute")          (dd.explode "sub."))
        (cons (dd.explode "lemma")               (dd.explode "lm."))
        (cons (dd.explode "two")                 (dd.explode "2"))
        (cons (dd.explode "not nil and nil")     (dd.explode "nnil, nil"))
        (cons (dd.explode "not nil and not nil") (dd.explode "nnil, nnil"))
        (cons (dd.explode "nil and nil")         (dd.explode "nil, nil"))
        (cons (dd.explode "nil and not nil")     (dd.explode "nil, nnil"))
        (cons (dd.explode "not nil")             (dd.explode "nnil"))
        (cons (dd.explode "expansion")           (dd.explode "exp."))
        (cons (dd.explode " when")                (dd.explode ","))
        (cons (dd.explode "from")                (dd.explode "fr."))
        (cons (dd.explode "by args")             (dd.explode "args"))
        ))

(defconst *dd.cross-patterns*
  ;; Replacements to cross-references
  (list (cons (dd.explode "*1a, *1b, *1c") (dd.explode "*1abc"))
        (cons (dd.explode "*2a, *2b, *2c") (dd.explode "*2abc"))
        (cons (dd.explode "*1a, *1b") (dd.explode "*1ab"))
        (cons (dd.explode "*1a, *1b") (dd.explode "*1ab"))))

(defun dd.cat-separator-between-strings (strings sep) ;; => string
  ;; Insert a separator between each string in a list
  (declare (xargs :mode :program))
  (if (consp strings)
      (if (consp (cdr strings))
          (dd.cat (car strings)
                  sep
                  (dd.cat-separator-between-strings (cdr strings) sep))
        (car strings))
    ""))

(defun dd.char-list-replace (old new char-list) ;; => char list
  ;; Replace all character occurrences
  (declare (xargs :mode :program))
  (if (consp char-list)
      (cons (if (equal (car char-list) old)
                new
              (car char-list))
            (dd.char-list-replace old new (cdr char-list)))
    nil))

(defun dd.char-list-replace-char-list (old new char-list) ;; => char list
  ;; Replace all substring occurrences
  (declare (xargs :mode :program))
  (if (prefixp old char-list)
      (app new
           (dd.char-list-replace-char-list old new (ACL2::nthcdr (len old) char-list)))
    (if (consp char-list)
        (cons (car char-list)
              (dd.char-list-replace-char-list old new (cdr char-list)))
      nil)))

(defun dd.char-list-replace-patterns (char-list patterns) ;; => char list
  ;; Replace all substring occurrences specified in a table
  (declare (xargs :mode :program))
  (if (consp patterns)
      (dd.char-list-replace-patterns (dd.char-list-replace-char-list (car (car patterns))
                                                                     (cdr (car patterns))
                                                                     char-list)
                                     (cdr patterns))
    char-list))

(defun dd.name-estimate-twips (x)
  ;; Estimate how long a builder name will be
  (declare (xargs :mode :program))
  (if (consp x)
      (if (equal (car x) #\$)
          (cond ((prefixp (dd.explode "$=$") x)
                 (+ *dd.equal-width*
                    (dd.name-estimate-twips (ACL2::nthcdr 3 x))))
                ((prefixp (dd.explode "$\\neq$") x)
                 (+ *dd.neq-width*
                    (dd.name-estimate-twips (ACL2::nthcdr 6 x))))
                ((prefixp (dd.explode "$\\neg$") x)
                 (+ *dd.neg-width*
                    (dd.name-estimate-twips (ACL2::nthcdr 6 x))))
                ((prefixp (dd.explode "$\\neg\\neg$") x)
                 (+ (+ *dd.neg-width* *dd.neg-width*)
                    (dd.name-estimate-twips (ACL2::nthcdr 10 x))))
                (t
                 (ACL2::er hard 'dd.name-estimate-twips "Unusual math mode encountered. ~x0~%" x)))
        (+ (dd.normal-twips (car x))
           (dd.name-estimate-twips (cdr x))))
    0))

(defun dd.name-autotruncate (char-list patterns twips) ;; => char list
  ;; Successively try applying patterns until the name is short enough
  (declare (xargs :mode :program))
  (if (consp patterns)
      (if (<= (dd.name-estimate-twips char-list) twips)
          char-list
        (dd.name-autotruncate (dd.char-list-replace-char-list (car (car patterns)) (cdr (car patterns)) char-list)
                              (cdr patterns)
                              twips))
    char-list))

(defun dd.bldr-name (x twips) ;; => string
  (declare (xargs :mode :program))
  (let* ((name-chars      (dd.explode (ACL2::string-downcase (ACL2::symbol-name x))))
         (erase-dashes    (dd.char-list-replace #\- #\Space name-chars))
         (erase-opening-@ (if (equal (car erase-dashes) #\@)
                              (cdr erase-dashes)
                            erase-dashes))
         (apply-pats      (dd.char-list-replace-patterns erase-opening-@ *dd.bldr-name-always-replace*))
         (auto-shorten    (dd.name-autotruncate apply-pats *dd.bldr-name-maybe-replace* twips))
         (fix-case        (cons (ACL2::char-upcase (car auto-shorten))
                                (cdr auto-shorten))))
    fix-case))



(defun dd.extract-proofs-from-multipatterns (x) ;; => (proof path pat) list
  (declare (xargs :mode :program))
  (if (consp x)
      (if (equal (car (car x)) 'proof)
          (cons (car x) (dd.extract-proofs-from-multipatterns (cdr x)))
        (dd.extract-proofs-from-multipatterns (cdr x)))
    nil))

(defun dd.defderiv-latex-summary (from derive where) ;; => string
  (declare (xargs :mode :program))
  (let ((types (strip-firsts from)))
    (if (and (not (consp where))
             (not (memberp 'constant types)))
        ;; This is a simple derivation involving only proofs, terms, and formulas
        ;; which are not further restricted by where clauses and none of which are
        ;; required to be constants.  We'll just build one of the table-style rules:
        ;;  hyp1
        ;;  ...
        ;;  hypN
        ;; --------------------
        ;;  conclusion
        (let* ((proof-tuples   (dd.extract-proofs-from-multipatterns from))
               (proof-patterns (strip-thirds proof-tuples))
               (boxed-hyps     (dd.latex-autobox-formulas proof-patterns *dd.max-summary-width*))
               (boxed-concl    (dd.latex-autobox-formula derive *dd.max-summary-width*)))
          (dd.cat "\\begin{tabular}{l}" *dd.nl*
                  (if (consp proof-tuples)
                      (dd.cat-separator-between-strings boxed-hyps (dd.cat " \\\\ " *dd.nl*))
                    "")
                  " \\\\ " *dd.nl*
                  "\\hline" *dd.nl*
                  boxed-concl *dd.nl*
                  "\\end{tabular}" *dd.nl*))
      "Bozo: Implement non-simple summaries")))

(defun dd.find-last-derive (x) ;; => (@derive ...)
  (declare (xargs :mode :program))
  (if (consp x)
      (if (equal (car x) '@derive)
          (or (dd.find-last-derive (cdr x))
              x)
        (or (dd.find-last-derive (cdr x))
            (dd.find-last-derive (car x))))
    nil))

(defun dd.get-deriv-lines (proof)
  ;; We try to find the very last (@derive ...) in an object, which should be the most
  ;; general one in a derivation.
  (declare (xargs :mode :program))
  (let ((derivation (dd.find-last-derive proof)))
    (if (not derivation)
        (ACL2::er hard 'dd.get-deriv-lines "Unable to find an @derive in the proof.~%")
      (cdr derivation))))

(defun dd.flatten (x)
  (declare (xargs :mode :program))
  (if (consp x)
      (app (dd.flatten (car x))
           (dd.flatten (cdr x)))
    (list x)))

(defun dd.intersection (x y)
  (declare (xargs :mode :program))
  (if (consp x)
      (if (memberp (car x) y)
          (cons (car x) (dd.intersection (cdr x) y))
        (dd.intersection (cdr x) y))
    nil))

(defun dd.symbol-name-list (x) ;; => string list
  (declare (xargs :mode :program))
  (if (consp x)
      (cons (ACL2::string-downcase (ACL2::symbol-name (car x)))
            (dd.symbol-name-list (cdr x)))
    nil))

(defun dd.latex-justification (justify names) ;; => string
  (declare (xargs :mode :program))
  (let* ((cross-refs  (remove-all nil (dd.intersection (dd.flatten (cdr justify)) names)))
         (cross-text  (if cross-refs
                          (dd.cat " " (dd.cat-separator-between-strings (dd.symbol-name-list cross-refs) ", "))
                        ""))
         (cross-text  (dd.name-autotruncate (dd.explode cross-text) *dd.cross-patterns* 0))
         (cross-twips (dd.name-estimate-twips (dd.explode cross-text)))
         (raw-name    (if (memberp (first justify) '(build.theorem build.axiom))
                          ;; (build.axiom (axiom-blah-blah)) or (build.theorem (theorem-blah-blah))
                          (car (second justify))
                        (first justify)))
         (bldr-name   (dd.bldr-name raw-name (- *dd.justify-width* cross-twips)))
         (needs-linkp (not (memberp raw-name '(@given propositional-schema cut contraction expansion associativity
                                                      instantiation functional-equality beta-reduction base-eval)))))
    (if needs-linkp
        (dd.cat "\\hyperlink{" (ACL2::string-downcase (ACL2::symbol-name raw-name)) "}{" bldr-name "}" cross-text)
      (dd.cat bldr-name cross-text))))

(defun dd.latex-deriv-line (line formula-width names) ;; => string
  (declare (xargs :mode :program))
  (let ((formula (first line))
        (jusify  (second line))
        (name    (third line)))
    (dd.cat (dd.latex-autobox-formula formula formula-width)
            " & "
            (dd.latex-justification jusify names)
            " & "
            (if name
                (dd.cat "(" (ACL2::string-downcase (ACL2::symbol-name name)) ")")
              ""))))

(defun dd.latex-deriv-lines (lines formula-width names) ;; => string
  (declare (xargs :mode :program))
  (if (consp lines)
      (dd.cat (dd.latex-deriv-line (car lines) formula-width names)
              (if (consp (cdr lines)) "" "\\qedhere")
              " \\\\ " *dd.nl*
              (dd.latex-deriv-lines (cdr lines) formula-width names))
    ""))

(defun dd.defderiv-latex-derivation (lines) ;; => string
  (declare (xargs :mode :program))
  (let* ((formulas      (strip-firsts lines))
         (names         (strip-thirds lines))
         (desired-width (dd.latex-formulas-max-desired-width formulas (- *dd.max-derive-line-width* *dd.overestimate-padding*)))
         (derivs-width  (+ desired-width *dd.overestimate-padding*)))
    (dd.latex-deriv-lines lines derivs-width names)))



(defconst *dd.hypercommand-patterns*
  (list (cons (dd.explode "build.") (dd.explode ""))
        (cons (dd.explode ".")      (dd.explode ""))
        (cons (dd.explode "-")      (dd.explode ""))
        (cons (dd.explode "1")      (dd.explode "one"))
        (cons (dd.explode "2")      (dd.explode "two"))
        (cons (dd.explode "3")      (dd.explode "three"))
        (cons (dd.explode "4")      (dd.explode "four"))
        (cons (dd.explode "5")      (dd.explode "five"))
        (cons (dd.explode "6")      (dd.explode "six"))
        (cons (dd.explode "7")      (dd.explode "seven"))
        (cons (dd.explode "8")      (dd.explode "eight"))
        (cons (dd.explode "9")      (dd.explode "nine"))
        (cons (dd.explode "0")      (dd.explode "zero"))))

(defun dd.hypercommand (internal-name)
  (declare (xargs :mode :program))
  (dd.implode
   (app (dd.explode "\\DR")
        (STR::char-list-replace-patterns (dd.explode internal-name)
                                         *dd.hypercommand-patterns*))))

(defun dd.defderiv-latex (name from derive where proof minatbl ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state)
           (ignore minatbl))
  (let* ((internal-name (ACL2::string-downcase (ACL2::symbol-name name)))
         (print-name    (dd.bldr-name name *dd.max-summary-width*))
         (filename      (dd.cat "defderiv-" internal-name ".tex"))
         (cost          (cdr (lookup name (dd.get-builder-costs (ACL2::w ACL2::state)))))
         (derivation    (dd.cat "\\begin{derivedrule}{\\hypertarget{" internal-name "}" "{" print-name "}}" *dd.nl*
                                "\\index{Derived rules!" print-name "}" *dd.nl*

                                ;; Important: keep this all one one line (i.e., no *dd.nl*)
                                "%\\newcommand{" (dd.hypercommand internal-name) "}[1][" print-name "]"
                                   "{\\hyperlink{" internal-name "}{#1}}"
                                ;; /Important

                                *dd.nl* *dd.nl*
                                (dd.defderiv-latex-summary from derive where)
                                "\\begin{proof}[Derivation]"
                                (if cost
                                    (dd.cat " (" (dd.implode (ACL2::explode-atom cost 10)) ")")
                                  "")
                                ;"\\mbox{} "
                                *dd.nl* *dd.nl*
                                "\\noindent "
                                "\\begin{longtable}{lll}" *dd.nl*
                                (dd.defderiv-latex-derivation (dd.get-deriv-lines proof)) *dd.nl*
                                "\\end{longtable}"
                                "\\end{proof}" *dd.nl*
                                "\\bigskip" *dd.nl*
                                "\\end{derivedrule}" *dd.nl* *dd.nl*))
         (sfilename     (dd.cat "defsummary-" internal-name ".tex"))
         (scontents     (dd.cat "\\begin{derivedrule}{\\hyperlink{" internal-name "}{" print-name "}}" *dd.nl*
                                "\\index{Derived rules!" print-name "}" *dd.nl* *dd.nl*
                                (dd.defderiv-latex-summary from derive where)
                                "\\end{derivedrule}" *dd.nl* *dd.nl*)))
    (ACL2::mv-let (channel ACL2::state)
                  (dd.open-output-channel (dd.cat "autodoc/" filename) :character ACL2::state)
                  (let* ((ACL2::state (ACL2::princ$ derivation channel ACL2::state))
                         (ACL2::state (ACL2::close-output-channel channel ACL2::state))
                         (ACL2::state (dd.write-fn (dd.cat "\\input{" filename "}" *dd.nl*) ACL2::state)))
                    (ACL2::mv-let (channel ACL2::state)
                                  (dd.open-output-channel (dd.cat "autodoc/" sfilename) :character ACL2::state)
                                  (let* ((ACL2::state (ACL2::princ$ scontents channel ACL2::state))
                                         (ACL2::state (ACL2::close-output-channel channel ACL2::state)))
                                    ACL2::state))))))


(defmacro defderiv (name &key from derive where proof minatbl highlevel-override)
  `(ACL2::progn
    ;; Axiom computation for the builder-axioms table.
    (ACL2::table milawa 'builder-axioms
                 (update ',name
                         (app (dd.all-deriv-local-axioms ',proof)
                              (dd.all-deriv-inherited-axioms ',proof ACL2::world))
                         (dd.get-builder-axioms ACL2::world)))
    ;; Theorem computation for builder-theorems table.
    (ACL2::table milawa 'builder-theorems
                 (update ',name
                         (app (dd.all-deriv-local-theorems ',proof)
                              (dd.all-deriv-inherited-theorems ',proof ACL2::world))
                         (dd.get-builder-theorems ACL2::world)))
    ;; Cost computation for builder-costs table.
    (ACL2::table milawa 'builder-costs
                 (update ',name
                         (dd.estimate-cost-of-lines (dd.get-deriv-lines ',proof) ACL2::world)
                         (dd.get-builder-costs ACL2::world)))
    ;; Builder introduction
    (ACL2::make-event
     (dd.defderiv-fn ',name ',from ',derive ',where ',proof ',minatbl ',highlevel-override (ACL2::w ACL2::state)))
    ;; LaTeX printing
    (local (ACL2::make-event
            (let ((ACL2::state (dd.defderiv-latex ',name ',from ',derive ',where ',proof ',minatbl ACL2::state)))
              (ACL2::mv nil '(ACL2::value-triple ',name) ACL2::state))))))




(defun dd.deftheorem-fn (name derive proof minatbl wrld)
  (declare (xargs :mode :program))
  (let* ((name-proof     (ACL2::mksym name '-proof))
         (local-axioms   (dd.all-deriv-local-axioms proof))
         (local-theorems (dd.all-deriv-local-theorems proof))
         (all-axioms     (app local-axioms (dd.all-deriv-inherited-axioms proof wrld)))
         (all-theorems   (app local-theorems (dd.all-deriv-inherited-theorems proof wrld))))
    (cond ((dd.context-gather proof)
           (ACL2::er ACL2::hard 'deftheorem
                     "deftheorem proof illegally mentions context variables: ~x0~%"
                     (dd.context-gather proof)))
          (t
           `(encapsulate
             ()
             (ACL2::set-inhibit-warnings "theory")

             (local (in-theory (ACL2::executable-counterpart-theory :here)))

             (defund@ ,name ()
               (declare (xargs :guard t))
               (@formula ,derive))

             (defund@ ,name-proof ()
               (declare (xargs :guard t))
               ,proof)

             (defthm ,(ACL2::mksym 'logic.formulap-of- name)
               (equal (logic.formulap (,name))
                      t))

             (defthm ,(ACL2::mksym 'conclusion-of- name-proof)
               (equal (logic.conclusion (,name-proof))
                      (,name)))

             (defthm ,(ACL2::mksym 'logic.proofp-of- name-proof)
               (equal (logic.proofp (,name-proof)
                                    (list ,@all-axioms)
                                    (list ,@all-theorems)
                                    ',minatbl)
                      t))

             (in-theory (disable (:executable-counterpart ,name)
                                 (:executable-counterpart ,name-proof))))))))


(defun dd.deftheorem-latex (name derive proof minatbl ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state)
           (ignore minatbl))
  (let* ((internal-name (ACL2::string-downcase (ACL2::symbol-name name)))
         (print-name    (dd.bldr-name name *dd.max-summary-width*))
         (print-name    (if (prefixp (ACL2::coerce "Theorem " 'ACL2::list) print-name)
                            (let ((chop (restn (ACL2::length "Theorem ") print-name)))
                              (cons (ACL2::char-upcase (car chop))
                                    (cdr chop)))
                          print-name))
         (filename      (dd.cat internal-name ".tex"))
         (sfilename     (dd.cat "summary-" internal-name ".tex"))
         (derivation    (dd.cat "\\begin{formalthm}{\\hypertarget{" internal-name "}" "{" print-name "}}" *dd.nl*
                                "\\index{Formal theorems!" print-name "}" *dd.nl*
                                ;"\\mbox{} \\\\"
                                *dd.nl* *dd.nl*
                                (dd.latex-autobox-formula derive *dd.max-summary-width*)
                                "\\begin{proof}[Proof]"
                                ;"\\mbox{} "
                                *dd.nl* *dd.nl*
                                "\\noindent "
                                "\\begin{longtable}{lll}" *dd.nl*
                                (dd.defderiv-latex-derivation (dd.get-deriv-lines proof)) *dd.nl*
                                "\\end{longtable}"
                                "\\end{proof}" *dd.nl*
                                "\\bigskip" *dd.nl*
                                "\\end{formalthm}" *dd.nl* *dd.nl*))
         (scontents     (dd.cat "\\begin{formalthm}{\\hyperlink{" internal-name "}" "{" print-name "}}" *dd.nl*
                                "\\index{Formal theorems!" print-name "}" *dd.nl* *dd.nl*
                                (dd.latex-autobox-formula derive *dd.max-summary-width*) *dd.nl* *dd.nl*
                                "\\end{formalthm}" *dd.nl* *dd.nl* *dd.nl*)))
    (ACL2::mv-let (channel ACL2::state)
                  (dd.open-output-channel (dd.cat "autodoc/" filename) :character ACL2::state)
                  (let* ((ACL2::state (ACL2::princ$ derivation channel ACL2::state))
                         (ACL2::state (ACL2::close-output-channel channel ACL2::state))
                         (ACL2::state (dd.write-fn (dd.cat "\\input{" filename "}" *dd.nl*) ACL2::state)))
                    (ACL2::mv-let (channel ACL2::state)
                                  (dd.open-output-channel (dd.cat "autodoc/" sfilename) :character ACL2::state)
                                  (let* ((ACL2::state (ACL2::princ$ scontents channel ACL2::state))
                                         (ACL2::state (ACL2::close-output-channel channel ACL2::state)))
                                    ACL2::state))))))

(defun dd.deftheorem-dump (name full-proof ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((internal-name (ACL2::string-downcase (ACL2::symbol-name name)))
         (filename      (dd.cat "proofs/" internal-name ".proof")))
    (ACL2::mv-let (channel ACL2::state)
                  (dd.open-output-channel filename :character ACL2::state)
     (ACL2::mv-let (col ACL2::state)
                   (ACL2::fmt1! "~f0~%" (list (cons #\0 full-proof)) 0 channel ACL2::state nil)
                   (declare (ignore col))
       (ACL2::close-output-channel channel ACL2::state)))))

;; Every time we call deftheorem we store a (thmname . proof-function-name)
;; pair into the defthm registry table.  We use this table to dump out all the
;; theorems we've proven at the start of bootstrapping.

(ACL2::table milawa 'deftheorem-registry nil)

(defun dd.get-deftheorem-registry (wrld)
  (declare (xargs :mode :program))
  (cdr (lookup 'deftheorem-registry (ACL2::table-alist 'milawa wrld))))

(defmacro deftheorem (name &key derive proof minatbl)
  `(ACL2::progn
    ;; Theorem Introduction
    (ACL2::make-event
     (dd.deftheorem-fn ',name ',derive ',proof ',minatbl (ACL2::w ACL2::state)))
    ;; LaTeX Printing of the Derivation
    (local (ACL2::make-event
            (let ((ACL2::state (dd.deftheorem-latex ',name ',derive ',proof ',minatbl ACL2::state)))
              (ACL2::mv nil '(ACL2::value-triple ',name) ACL2::state))))
    ;; Print the proof to a file
    (local (ACL2::make-event
            (let ((ACL2::state (dd.deftheorem-dump ',name ,(list (ACL2::mksym name '-proof)) ACL2::state)))
              (ACL2::mv nil '(ACL2::value-triple ',name) ACL2::state))))
    ;; Write the entry to the table.
    (ACL2::table milawa 'deftheorem-registry
                 (update ',name ',(ACL2::mksym name '-proof)
                         (dd.get-deftheorem-registry ACL2::world)))))






(ACL2::table milawa 'defax-table nil)

(defun dd.get-defax-table (wrld)
  (declare (xargs :mode :program))
  (cdr (lookup 'defax-table (ACL2::table-alist 'milawa wrld))))


(mutual-recursion
 (defun dd.term-functions-and-arities (x acc)
   (declare (xargs :mode :program))
   (if (or (equal x t)
           (equal x nil)
           (natp x)
           (logic.constantp x)
           (logic.variablep x)
           (not (consp x))
           (equal (first x) '?))
       acc
     (let ((arity (len (cdr x)))
           (entry (lookup (first x) acc)))
       (if entry
           (if (equal (cdr entry) arity)
               (dd.term-list-functions-and-arities (cdr x) acc)
             (ACL2::er hard 'dd.term-functions-and-arities "Arity mismatch for ~x0.~%" (first x)))
         (dd.term-list-functions-and-arities (cdr x) (update (first x) arity acc))))))
 (defun dd.term-list-functions-and-arities (x acc)
   (declare (xargs :mode :program))
   (if (consp x)
       (dd.term-list-functions-and-arities
        (cdr x)
        (dd.term-functions-and-arities (car x) acc))
     acc)))

(defun dd.formula-functions-and-arities (x acc)
  (declare (xargs :mode :program))
  (if (not (consp x))
      acc
    (cond ((or (equal (first x) '=)
               (equal (first x) '!=))
           (dd.term-functions-and-arities (second x)
                                          (dd.term-functions-and-arities (third x) acc)))
          ((equal (first x) '!)
           (dd.formula-functions-and-arities (second x) acc))
          ((equal (first x) 'v)
           (dd.formula-functions-and-arities (second x)
                                             (dd.formula-functions-and-arities (third x) acc)))
          (t nil))))

(defun dd.extract-minatbl-from-formula (x)
  (declare (xargs :mode :program))
  (remove-duplicates (dd.formula-functions-and-arities x nil)))




(defun defax-fn (name body)
  (declare (xargs :mode :program))
  (let ((atbl-checks (dd.minatbl-to-checks (dd.extract-minatbl-from-formula body))))
    `(encapsulate
      ()
      (defund@ ,name ()
        (declare (xargs :guard t))
        (@formula ,body))

      (in-theory (disable (:executable-counterpart ,name)))

      (defthm ,(ACL2::mksym 'logic.formulap-of- name)
        (equal (logic.formulap (,name))
               t)
      :hints(("Goal" :in-theory (enable ,name))))

      (defthm ,(ACL2::mksym 'blah-logic.formula-atblp-of- name)
        (implies (force (and ,@atbl-checks))
                 (equal (logic.formula-atblp (,name) atbl)
                        t))
        :hints(("Goal" :in-theory (enable ,name)))))))

(defmacro defax (name body)
  `(ACL2::progn
    (ACL2::make-event (defax-fn ',name ',body))
    (ACL2::table milawa 'defax-table
                 (cons ',name (dd.get-defax-table ACL2::world)))))

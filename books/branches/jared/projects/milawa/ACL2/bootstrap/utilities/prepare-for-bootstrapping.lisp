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
(set-well-founded-relation ord<)
(set-measure-function rank)

(include-book
 ;; I break this include-book up to ruin the Makefile's scanner, so that we are
 ;; not trying to find the file "book-thms.mtime" in the ACL2 distribution
 "xdoc/book-thms" :dir :system)


;; Fix inlining status of NOT.
(ACL2::table ACL2::milawa 'ACL2::functions-to-inline
             (cons 'not
                   (ACL2::get-functions-to-inline ACL2::world)))


(defun find-acl2-rules-that-exist-in-milawa (acl2thms milawarules)
  (declare (xargs :mode :program))
  (if (consp acl2thms)
      (let ((lookup (rw.rule-list-lookup (car acl2thms) milawarules)))
        (if lookup
            (cons lookup
                  (find-acl2-rules-that-exist-in-milawa (cdr acl2thms) milawarules))
          (find-acl2-rules-that-exist-in-milawa (cdr acl2thms) milawarules)))
    nil))

(defun %list-missing-rules (filename ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let* ((world     (ACL2::w ACL2::state))
         (acl2-thms (difference (ACL2::theorems-introduced-in filename ACL2::state)
                                '(ACL2::ACL2-ASG-PACKAGE
                                  ACL2::ACL2-AGP-PACKAGE
                                  ACL2::ACL2-CRG-PACKAGE
                                  ACL2::U-PACKAGE)))
         (mlw-thms  (find-acl2-rules-that-exist-in-milawa acl2-thms (tactic.harness->allrules world))))
    (difference acl2-thms
                (rw.rule-list-names mlw-thms))))

(defmacro %ensure-exactly-these-rules-are-missing (filename &rest rules)
  `(ACL2::make-event (ensure-exactly-these-rules-are-missing-fn ,filename ',rules ACL2::state)))

(defun ensure-exactly-these-rules-are-missing-fn (filename expected-missing ACL2::state)
  (declare (xargs :mode :program :stobjs ACL2::state))
  (let ((actually-missing (%list-missing-rules filename ACL2::state)))
    (if (and (subsetp actually-missing expected-missing)
             (subsetp expected-missing actually-missing))
        `(ACL2::value-triple :invisible)
      (ACL2::er hard
                'ensure-exactly-these-rules-are-missing
                "~%~%Incorrect missing rules for ~s0.~%~%~
                  We thought these rules would not be missing:~%  ~&1.~%~%~
                  We thought these rules would be missing, but they are present:~%  ~&2.~%~%"
                filename
                (difference actually-missing expected-missing)
                (difference expected-missing actually-missing)))))



;; BOZO put this somewhere sensible

(defun compact-anstack (x)
  (if (consp x)
      (cons (list (first (car x))
                  (rw.rule-list-names (fourth (car x))))
            (compact-anstack (cdr x)))
    nil))

(defmacro trace-ancestors ()
  `(ACL2::trace! (rw.ancestors-check :entry (list (first acl2::arglist)
                                                  (rw.rule-list-names (second acl2::arglist))
                                                  (compact-anstack (third acl2::arglist))))))




;; prepare-for-bootstrapping.lisp
;;
;; This file is used to get the system ready to do bootstrapping.  It is in
;; charge of initializing all of the variables in the tactic harness.  This is
;; where we do all of the messy hacks we need so that the rest of the
;; bootstrapping process can be done in a principled way.  There is nothing
;; very intellectually stimulating here, it's just a bunch of details that need
;; to be taken care of before we can begin in earnest.






#|| We don't do this any more --- syndefs are gone.

;; 1.  Loading definitions for use in :syntax restrictions.
;;
;; Some of our rewrite rules use :syntax restrictions to limit their
;; application.  For example, we use a rewrite rule to orient (equal x y) so
;; that x < y in the term order.  This rule simply commutes (equal y x) to
;; (equal x y), and a :syntax restriction requires that y is bigger than x
;; before the rule is applied.
;;
;; We want to introduce this rule, and other rules using concepts such as
;; the term order, constantp, etc., long before the term order itself is
;; introduced.  Our tactic harness keeps a list of "syntax definitions"
;; which are used for this purpose.  Since these definitions are only used
;; heuristically (to decide whether or not to apply a rule), there are no
;; soundness issues to be concerned with.
;;
;; The file syntax-defuns.lisp, which is automatically generated by our make
;; system (using our custom "defun" event and some various modifications in
;; the ACL2/utilities and ACL2/logic directories), will have the current list
;; of definitions for us to add to the syntax definitions list.  We load them
;; in at this time.

;; (defun annhialate-time$ (x)
;;   (declare (xargs :mode :program))
;;   (if (consp x)
;;       (if (and (equal (car x) 'ACL2::time$)
;;                (equal (len x) 2))
;;           (annhialate-time$ (second x))
;;         (cons (annhialate-time$ (car x))
;;               (annhialate-time$ (cdr x))))
;;     x))

;; (ACL2::make-event
;;  `(ACL2::progn ,@(acl2::time$
;;                   (fast-rev
;;                    (annhialate-time$
;;                     (ACL2::get-syntax-defun-entries (ACL2::w ACL2::state)))))))

||#




;; 2.  Adding the rank, ordp, and ord< functions.
;;
;; The functions rank, ordp, and ord< are not among our base functions, but
;; they cannot be admitted in the ordinary manner.  This is because they are
;; recursive, hence admitting them requires that we prove they terminate.  But
;; the termination proofs will mention the functions rank, ordp, and ord<,
;; which cannot be mentioned until rank, ordp, and ord< are admitted.  We
;; therefore reach in and forcibly make their definitions available to the
;; system by adding them to the arity table, definitions list, and syntax
;; definitions list.  (They are also added as axioms in part 3.)

(ACL2::table tactic-harness 'atbl
             (ACL2::list* '(rank . 1)
                          '(ordp . 1)
                          '(ord< . 2)
                          (tactic.harness->atbl ACL2::world)))

(ACL2::table tactic-harness 'world
             (change-tactic.world-wrapper (tactic.harness->world ACL2::world)
                                          :defs
                                          (ACL2::list* (definition-of-rank)
                                                       (definition-of-ordp)
                                                       (definition-of-ord<)
                                                       (tactic.harness->defs ACL2::world))))




;; 3.  Adding the symbolic axioms.
;;
;; In the file ACL2/build/axioms.lisp, we introduced our symbolic axioms using
;; the special defax command.  Each such axiom is noted in the defax registry,
;; so we can read this registry in order to introduce all of our axioms at this
;; time.  This way, you just need to add your new axioms in the
;; ACL2/build/axioms.lisp file as defax'es, and they will be automatically
;; available to the system.

(defun aux-introduce-all-defaxes (registry)
  (declare (xargs :mode :program))
  (if (consp registry)
      (let ((axiom-name (car registry)))
        (cons `(%axiom (,axiom-name))
              (aux-introduce-all-defaxes (cdr registry))))
    nil))

(defun introduce-all-defaxes (world)
  (declare (xargs :mode :program))
  (let ((registry (fast-rev (dd.get-defax-table world))))
    `(ACL2::progn ,@(aux-introduce-all-defaxes registry))))

(ACL2::make-event (introduce-all-defaxes (ACL2::w ACL2::state)))




;; 4. Adding the "deftheorem" theorems.
;;
;; Our builder functions make use of several theorems introduced by the
;; "deftheorem" event throughout our files.  Like defax, deftheorem remembers
;; which theorems it has introduced by adding them to a registry.  We are now
;; going to read in all of these theorems and prove them.
;;
;; This is a somewhat delicate process.
;;
;;    - Some of the theorems mention the functions "iff" and "not" which have
;;      not yet been introduced.  So, we will need to introduce these functions
;;      before loading all the deftheorems.
;;
;;    - To introduced "iff" and "not", we need to have the following theorems
;;      available (to convert the axiom into a theorem corresponding to the
;;      associated rule)
;;         1. theorem-substitute-into-not-pequal
;;         2. theorem-not-t-or-not-nil
;;
;;    - But fortunately these theorems do not mention iff or not, so we are
;;      able to complete the process pretty easily.

(defmacro check-deftheorem (name)
  `(ACL2::progn
    (local (ACL2::make-event (let ((proof-okp (%theorem-check ',name
                                                              (,name)
                                                              (,(ACL2::mksym name '-proof))
                                                              ACL2::state)))
                               (acl2::prog2$
                                (acl2::cw ";; proof-okp = ~x0.~%" proof-okp)
                                '(ACL2::value-triple :invisible)))))
    (local (acl2::value-triple (acl2::cw "check-deftheorem calling %raw-add-theorem~%")))
    (%raw-add-theorem ,name (,name))))

(check-deftheorem theorem-substitute-into-not-pequal)
(check-deftheorem theorem-not-t-or-not-nil)

(defsection not
  ;; Essay on how "not" is handled.
  ;;
  ;; There are many variants of "not", such as (if x nil t), (equal x nil), and
  ;; so forth.  We have chosen to use (not x) as our canonical form.  It seems
  ;; like the simplest of these alternatives, since it has only a single
  ;; argument.
  ;;
  ;; Our conditional rewriter has a special case for handling not, which ensures
  ;; that x is always rewritten under IFF.  We also have a special case so that
  ;; (if x nil t) will be canonicalized to (not x).  The other variants can be
  ;; canonicalized with rewrite rules.
  ;;
  ;; Because of our special cases, regular rewrite rules (including definitions)
  ;; are never attempted when simplifying (not x).  Hence, it doesn't matter if
  ;; "not" is enabled or disabled, its definition will not be expanded in either
  ;; case.  I've chosen to leave it disabled just as a reminder that it won't be
  ;; used.  Rewrite rules should never target "not", because they would never be
  ;; used.  Of course, rules like (booleanp (not x)) are fine.
  (%defun not (x)
          (if x nil t))
  (%admit))

(defsection iff
  (%defun iff (x y)
          (if x (if y t nil) (if y nil t)))
  (%admit)
  (%enable default iff))

(defun aux-introduce-all-deftheorems (registry)
  (declare (xargs :mode :program))
  (if (consp registry)
      (let ((theorem-name (car (car registry))))
        (if (memberp theorem-name '(theorem-substitute-into-not-pequal theorem-not-t-or-not-nil))
            ;; Skip the theorems we've already introduced.
            (aux-introduce-all-deftheorems (cdr registry))
          (cons `(check-deftheorem ,theorem-name)
                (aux-introduce-all-deftheorems (cdr registry)))))
    nil))

(defun introduce-all-deftheorems (world)
  (declare (xargs :mode :program))
  ;; The registry entries are in the reverse order of how they were added, so we
  ;; reverse them to recover the original order they were added.
  (let ((registry (fast-rev (dd.get-deftheorem-registry world))))
    `(ACL2::progn ,@(aux-introduce-all-deftheorems registry))))

(ACL2::make-event (introduce-all-deftheorems (ACL2::w ACL2::state)))



;; 5. Adding "implies"
;;
;; Most of our functions are defined in our ACL2 scripts.  However, we cannot
;; redefine implies, because ACL2's defthm command is expecting its theorems to
;; have the form (ACL2::implies ... (equal lhs rhs)).  We correct for this now.

(defsection implies
  (%defun implies (x y)
          (if x (if y t nil) t))
  (%admit)
  (%enable default implies))



;; 7. Adding rules which are "deeply" part of ACL2

(defsection reflexivity-of-equal
  (%prove (%rule reflexivity-of-equal
                 :lhs (equal x x)
                 :rhs t))
  (%use (build.theorem (theorem-reflexivity-of-equal)))
  (%cleanup)
  (%qed)
  (%enable default reflexivity-of-equal))

(defsection symmetry-of-equal
  (%prove (%rule symmetry-of-equal
                 :lhs (equal x y)
                 :rhs (equal y x)
                 :syntax ((logic.term-< y x))))
  (%use (build.theorem (theorem-symmetry-of-equal)))
  (%cleanup)
  (%qed)
  (%enable default symmetry-of-equal))

(defsection equal-of-t-and-equal
  (%prove (%rule equal-of-t-and-equal
                 :lhs (equal t (equal x y))
                 :rhs (equal x y)))
  (%use (build.theorem (theorem-equal-of-equal-and-t)))
  (%urewrite default)
  (%cleanup)
  (%qed)
  (%enable default equal-of-t-and-equal))

(defsection consp-of-cons
  (%prove (%rule consp-of-cons
                 :lhs (consp (cons x y))
                 :rhs t))
  (%use (build.axiom (axiom-consp-of-cons)))
  (%cleanup)
  (%qed)
  (%enable default consp-of-cons))




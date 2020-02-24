; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (August 2nd 2016)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/basic/inductions" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "centaur/fty/baselists" :dir :system)

(include-book "hint-interface")
(include-book "hint-please")
(include-book "../config")

(defsection Smtlink-process-user-hint
  :parents (verified)
  :short "Functionalities for processing user hints given to Smtlink. User
  hints will be merged with (smt-hint)."

  ;; --------------------------------------------------------

  ;; Example:
  ;; :hints (("Goal"
  ;;          :clause-processor
  ;;          (SMT::smtlink clause
  ;;                        '(:functions ((f0 :formals ((a0 rationalp))
  ;;                                          :returns (r0 rationalp :hints (:use ((:instance returns-lemma))))
  ;;                                          :level 1
  ;;                                          :guard ((> a0 0) :hints (:use ((:instance guard-lemma))))
  ;;                                          :more-returns (((> r0 0) :hints (:use ((:instance more-lemma)))))))
  ;;                          :hypotheses (((> a b) :hints (:use ((:instance lemma)))))
  ;;                          :main-hint (:use ((:instance thm1)))
  ;;                          :fty (...)
  ;;                          :int-to-rat nil
  ;;                          :smt-fname ""
  ;;                          :rm-file t
  ;;                          :smt-solver-params (...)))))

  ;; Types:
  ;; hints-syntax-p/fix
  ;; hypothesis-syntax-p/fix
  ;; hypothesis-lst-syntax-p/fix
  ;; argument-syntax-p/fix
  ;; argument-lst-syntax-p/fix
  ;; function-option-syntax-p/fix
  ;; function-option-lst-syntax-p/fix
  ;; function-syntax-p/fix
  ;; function-lst-syntax-p/fix
  ;; smt-solver-params-p/fix
  ;; smtlink-hint-syntax-p/fix
  )

(defsection hints-syntax
  :parents (Smtlink-process-user-hint)

  (define hints-syntax-p ((term t))
    :parents (hints-syntax)
    :returns (syntax-good? booleanp)
    :short "Recognizer for hints-syntax."
    (true-listp term))

  (define hints-syntax-fix ((term hints-syntax-p))
    :parents (hints-syntax)
    :returns (fixed-term hints-syntax-p)
    :short "Fixing function for a hints-sytnax-p."
    (mbe :logic (if (hints-syntax-p term) term nil)
         :exec term))

  (encapsulate ()
    (local (in-theory (enable hints-syntax-fix)))
    (deffixtype hints-syntax
      :pred  hints-syntax-p
      :fix   hints-syntax-fix
      :equiv hints-syntax-equiv
      :define t
      :forward t
      :topic hints-syntax-p))
  )

(defsection hypothesis-lst-syntax
  :parents (Smtlink-process-user-hint)

  (define hypothesis-syntax-p ((term t))
    :parents (hypothesis-lst-syntax)
    :returns (syntax-good? booleanp)
    :short "Recognizer for hypothesis-syntax."
    (or (and (atom term)
             (equal term nil))
        ;; Without hints
        (and (true-listp term)
             (car term) (not (cdr term))
             (pseudo-termp (car term)))
        ;; With hints
        (and (true-listp term)
             (car term) (cadr term) (not (cdddr term))
             (pseudo-termp (car term))
             (equal (cadr term) ':hints)
             (hints-syntax-p (caddr term))))
    ///
    (defthm true-listp-of-caddr
      (implies
       (and (consp term)
            (consp (cdr term))
            (true-listp (cddr term))
            (equal (+ 2 (len (cddr term))) 3)
            (pseudo-termp (car term))
            (equal (cadr term) :hints)
            (hints-syntax-p (caddr term)))
       (true-listp (caddr term)))
      :hints (("Goal" :in-theory (enable hints-syntax-p)))))

  (define hypothesis-syntax-fix ((term hypothesis-syntax-p))
    :parents (hypothesis-lst-syntax)
    :returns (fixed-term hypothesis-syntax-p)
    :short "Fixing function for a hypothesis-syntax-p."
    (mbe :logic (if (hypothesis-syntax-p term) term nil)
         :exec term))

  (encapsulate ()
    (local (in-theory (enable hypothesis-syntax-fix)))
    (deffixtype hypothesis-syntax
      :pred  hypothesis-syntax-p
      :fix   hypothesis-syntax-fix
      :equiv hypothesis-syntax-equiv
      :define t
      :forward t
      :topic hypothesis-syntax-p)
    )

  (define hypothesis-lst-syntax-p ((term t))
    :parents (hypothesis-lst-syntax)
    :returns (syntax-good? booleanp)
    :short "Recognizer for hypothesis-lst-syntax."
    (b* (((if (atom term)) (equal term nil))
         ((cons first rest) term))
      (and (hypothesis-syntax-p first)
           (hypothesis-lst-syntax-p rest))))

  (define hypothesis-lst-syntax-fix ((term hypothesis-lst-syntax-p))
    :parents (hypothesis-lst-syntax)
    :returns (fixed-term hypothesis-lst-syntax-p
                         :hints (("Goal"
                                  :in-theory (enable hypothesis-lst-syntax-p))))
    :guard-hints (("Goal" :in-theory (enable hypothesis-syntax-fix
                                             hypothesis-lst-syntax-p hypothesis-lst-syntax-fix)))
    :short "Fixing function for a hypothesis-lst-syntax-p."
    (mbe :logic (if (consp term)
                    (cons (hypothesis-syntax-fix (car term))
                          (hypothesis-lst-syntax-fix (cdr term)))
                  nil)
         :exec term))

  (encapsulate ()
    (local (in-theory (enable hypothesis-lst-syntax-fix)))
    (deffixtype hypothesis-lst-syntax
      :pred  hypothesis-lst-syntax-p
      :fix   hypothesis-lst-syntax-fix
      :equiv hypothesis-lst-syntax-equiv
      :define t
      :forward t
      :topic hypothesis-lst-syntax-p))
  )

(defsection argument-lst-syntax
  :parents (Smtlink-process-user-hint)

  (define smt-typep ((term t))
    :parents (argument-lst-syntax)
    :returns (valid-type? booleanp)
    :short "Types allowed in Smtlink."
    ;; (if (assoc-equal term *SMT-uninterpreted-types*)
    ;;     t nil)
    (symbolp term)
    )

  (define argument-syntax-p ((term t))
    :parents (argument-lst-syntax)
    :returns (syntax-good? booleanp)
    :short "Recognizer for argument-syntax."
    (or (and (atom term)
             (equal term nil))
        ;; Just the name
        (and (true-listp term)
             (car term) (not (cdr term))
             (symbolp (car term)))
        ;; The name and the type/guard
        (and (true-listp term)
             (car term) (cadr term) (not (cddr term))
             (symbolp (car term))
             (smt-typep (cadr term)))
        ;; The name, the type and the :hints
        (and (true-listp term)
             (car term) (cadr term) (not (cddddr term)) 
             (symbolp (car term))
             (smt-typep (cadr term))
             (equal ':hints (caddr term))
             (hints-syntax-p (cadddr term)))))

  (define argument-syntax-fix ((term argument-syntax-p))
    :parents (argument-lst-syntax)
    :returns (fixed-term argument-syntax-p)
    :short "Fixing function for argument-syntax-p."
    (mbe :logic (if (argument-syntax-p term) term nil)
         :exec term))

  (encapsulate ()
    (local (in-theory (enable argument-syntax-fix)))
    (deffixtype argument-syntax
      :pred  argument-syntax-p
      :fix   argument-syntax-fix
      :equiv argument-syntax-equiv
      :define t
      :forward t
      :topic argument-syntax-p))

  (define argument-lst-syntax-p ((term t))
    :parents (argument-lst-syntax)
    :short "Recognizer for argument-lst-syntax."
    :returns (syntax-good? booleanp)
    (b* (((if (atom term)) (equal term nil))
         ((cons first rest) term))
      (and (argument-syntax-p first)
           (argument-lst-syntax-p rest))))

  (define argument-lst-syntax-fix ((term argument-lst-syntax-p))
    :parents (argument-lst-syntax)
    :short "Fixing function for argument-lst-syntax."
    :returns (fixed-term argument-lst-syntax-p
                         :hints (("Goal"
                                  :in-theory (enable argument-lst-syntax-p))))
    :guard-hints (("Goal"
                   :in-theory (enable argument-lst-syntax-fix argument-syntax-fix argument-lst-syntax-p)))
    (mbe :logic (if (consp term)
                    (cons (argument-syntax-fix (car term))
                          (argument-lst-syntax-fix (cdr term)))
                  nil)
         :exec term))

  (encapsulate ()
    (local (in-theory (enable argument-lst-syntax-fix)))
    (deffixtype argument-lst-syntax
      :pred  argument-lst-syntax-p
      :fix   argument-lst-syntax-fix
      :equiv argument-lst-syntax-equiv
      :define t
      :forward t
      :topic argument-lst-syntax-p))
  )

(defsection true-set-equiv-relation
  :parents (Smtlink-process-user-hint)

  (define true-set-equiv ((list1 true-listp) (list2 true-listp))
    :parents (true-set-equiv-relation)
    :returns (p booleanp)
    (if (equal (true-listp list1) (true-listp list2))
        (acl2::set-equiv list1 list2)
      nil)
    ///
    (more-returns
     (p (implies p (acl2::set-equiv list1 list2))
        :name set-equiv-if-true-set-equiv)
     (p (implies p
                 (and (subsetp list1 list2 :test 'equal)
                      (subsetp list2 list1 :test 'equal)))
        :name subsetp-if-true-set-equiv)
     (p (implies p (equal (true-listp list1) (true-listp list2)))
        :name true-set-equiv-is-for-true-lists)))

  (defequiv true-set-equiv
    :hints (("Goal" :in-theory (enable true-set-equiv))))
  (in-theory (disable (:type-prescription true-set-equiv)))
  )

(defsection function-syntax
  :parents (Smtlink-process-user-hint)

  (defconst *function-options*
    '((:formals . argument-lst-syntax-p)
      (:returns . argument-lst-syntax-p)
      (:level . natp)
      (:guard . hypothesis-syntax-p)
      (:more-returns . hypothesis-lst-syntax-p)))

  (defconst *function-option-names*
    (strip-cars *function-options*))

  (defconst *function-option-types*
    (remove-duplicates-equal (strip-cdrs *function-options*)))

  (define function-option-type-p ((option-type t))
    :parents (function-syntax)
    :returns (syntax-good? booleanp)
    :short "Recoginizer for function-option-type."
    (if (member-equal option-type *function-option-types*) t nil))

  (define function-option-type-fix ((option-type function-option-type-p))
    :parents (function-syntax)
    :returns (fixed-option-type function-option-type-p
                                :hints (("Goal" :in-theory (enable
                                                            function-option-type-p ))))
    :short "Fixing function for function-option-type."
    (mbe :logic (if (function-option-type-p option-type) option-type 'natp)
         :exec option-type))

  (defsection function-option-name-list
    :parents (function-syntax)

    (define function-option-name-p ((option-name t))
      :parents (function-option-name-list)
      :returns (syntax-good? booleanp)
      :short "Recoginizer for an function-option-name."
      (if (member-equal option-name *function-option-names*) t nil))

    ;; This default value ':formals will generate a list of options with
    ;; the same value. This violates the constraint that options should be
    ;; distinctive. But that's alright, since we never expect option-fix's logic
    ;; formula to ever get used. Proved guards ensure it.
    (define function-option-name-fix ((option-name function-option-name-p))
      :parents (function-option-name-list)
      :returns (fixed-option-name function-option-name-p)
      :short "Fixing function for option."
      (mbe :logic (if (function-option-name-p option-name) option-name ':formals)
           :exec option-name))

    (encapsulate ()
      (local (in-theory (enable function-option-name-fix)))
      (deffixtype function-option-name
        :pred  function-option-name-p
        :fix   function-option-name-fix
        :equiv function-option-name-equiv
        :define t
        :forward t
        :topic function-option-name-p)

      (deflist function-option-name-lst
        :elt-type function-option-name
        :true-listp t))

    (defthm function-option-name-fix-preserves-member
      (implies (member x used :test 'equal)
               (member (function-option-name-fix x)
                       (function-option-name-lst-fix used) :test 'equal)))

    (defthm function-option-name-lst-fix-preserves-subsetp
      (implies (subsetp used-1 used-2 :test 'equal)
               (subsetp (function-option-name-lst-fix used-1)
                        (function-option-name-lst-fix used-2)
                        :test 'equal))
      :hints(("Goal" :in-theory (e/d (subsetp-equal)))))

    (defthm function-option-name-lst-fix-preserves-set-equiv
      (implies (acl2::set-equiv used-1 used-2)
               (acl2::set-equiv
                (function-option-name-lst-fix used-1)
                (function-option-name-lst-fix used-2)))
      :hints (("Goal" :in-theory (enable acl2::set-equiv)))
      :rule-classes(:congruence))

    (defthm function-option-name-lst-p-and-member
      (implies (and (member x used)
                    (not (function-option-name-p x)))
               (not (function-option-name-lst-p used)))
      :hints(("Goal" :in-theory (enable function-option-name-lst-p))))

    (defthm function-option-name-lst-p--monotonicity
      (implies (and (equal (true-listp used-1) (true-listp used-2))
                    (subsetp used-1 used-2 :test 'equal)
                    (function-option-name-lst-p used-2))
               (function-option-name-lst-p used-1))
      :hints(("Goal" :in-theory (enable function-option-name-lst-p))))

    (defthm function-option-name-lst-p--congruence
      (implies (true-set-equiv used-1 used-2)
               (equal (function-option-name-lst-p used-1)
                      (function-option-name-lst-p used-2)))
      :hints(("Goal" :cases ((function-option-name-lst-p used-1)
                             (function-option-name-lst-p used-2))))
      :rule-classes(:congruence)))


  ;; The conditions in eval-type should go along with *function-options*
  (define eval-function-option-type ((option-type function-option-type-p) (term t))
    :parents (function-syntax)
    :returns (type-correct? booleanp)
    :short "Evaluating types for function option body."
    (b* ((option-type (function-option-type-fix option-type)))
      (case option-type
        (argument-lst-syntax-p (argument-lst-syntax-p term))
        (natp (natp term))
        (hypothesis-syntax-p (hypothesis-syntax-p term))
        (t (hypothesis-lst-syntax-p term)))))

  (define function-option-syntax-p ((term t) (used function-option-name-lst-p))
    :parents (function-syntax)
    :guard-hints (("Goal"
                   :in-theory (enable function-option-syntax-p function-option-name-p
                                      eval-function-option-type function-option-name-lst-p)))
    :returns (mv (ok booleanp)
                 (new-used function-option-name-lst-p
                           :hints (("Goal" :in-theory (enable function-option-name-lst-p function-option-name-p)))))
    :short "Recoginizer for function-option-syntax."
    (b* ((used (function-option-name-lst-fix used))
         ((unless (true-listp term)) (mv nil used))
         ((unless (consp term)) (mv t used))
         ((unless (and (car term) (cdr term) (not (cddr term)))) (mv nil used))
         ((cons option body-lst) term)
         ((unless (function-option-name-p option)) (mv nil used))
         (option-type (cdr (assoc-equal option *function-options*))))
      (mv (and (not (member-equal option used))
               (eval-function-option-type option-type (car body-lst)))
          (cons option used)))
    ///
    (more-returns
     (ok (implies (and (subsetp used-1 used :test 'equal) ok)
                  (mv-nth 0 (function-option-syntax-p term used-1)))
         :name function-option-syntax-p--monotonicity.ok
         )
     (ok (implies (acl2::set-equiv used-1 used)
                  (equal (mv-nth 0 (function-option-syntax-p term used-1))
                         ok))
         :name function-option-syntax-p--ok-congruence.ok
         :hints(("Goal"
                 :in-theory (disable function-option-syntax-p
                                     function-option-syntax-p--monotonicity.ok
                                     booleanp-of-function-option-syntax-p.ok)
                 :use((:instance function-option-syntax-p--monotonicity.ok
                                 (used-1 used-1) (used used) (term term))
                      (:instance function-option-syntax-p--monotonicity.ok
                                 (used-1 used) (used used-1) (term term))
                      (:instance booleanp-of-function-option-syntax-p.ok
                                 (used used-1) (term term))
                      (:instance booleanp-of-function-option-syntax-p.ok
                                 (used used) (term term)))))
         :rule-classes (:congruence))
     (new-used (implies (and (subsetp used-1 used :test 'equal) ok)
                        (subsetp
                         (mv-nth 1 (function-option-syntax-p term used-1))
                         new-used
                         :test 'equal))
               :name function-option-syntax-p--monotonicity.new-used)
     (new-used (implies (and term ok)
                        (equal new-used
                               (cons (car term) (function-option-name-lst-fix used))))
               :name function-option-syntax-p--new-used-when-ok)))

  (define function-option-lst-syntax-p-helper ((term t) (used function-option-name-lst-p))
    :parents (function-syntax)
    :returns (ok booleanp)
    :short "Helper for function-option-lst-syntax-p."
    (b* (((unless (true-listp term)) nil)
         ((unless term) t)
         ((unless (cdr term)) nil)
         ((list* first second rest) term)
         ((mv res new-used) (function-option-syntax-p (list first second)
                                                      used)))
      (and res (function-option-lst-syntax-p-helper rest new-used)))
    ///
    ;; These seem like they should be more-returns theorems, but
    ;; when I try that, ACL2 fails miserably.
    (defthm function-option-lst-syntax-p-helper--monotonicity
      (implies (and (subsetp used-1 used :test 'equal)
                    (function-option-lst-syntax-p-helper term used))
               (function-option-lst-syntax-p-helper term used-1)))

    (defthm function-option-lst-syntax-p-helper--congruence
      (b* ((ok (function-option-lst-syntax-p-helper term used)))
        (implies (acl2::set-equiv used-1 used)
                 (equal (function-option-lst-syntax-p-helper term used-1) ok)))
      :rule-classes(:congruence))

    ;; (more-returns
    ;;  (ok
    ;;   (implies (and (subsetp used-1 used :test 'equal) ok)
    ;;            (function-option-lst-syntax-p-helper term used-1))
    ;;   :name function-option-lst-syntax-p-helper--monotonicity))

    ;; (more-returns
    ;;  (ok
    ;;    (implies (acl2::set-equiv used-1 used)
    ;;             (equal (function-option-lst-syntax-p-helper term used-1) ok))
    ;;    :rule-classes(:congruence)
    ;;    :name function-option-lst-syntax-p-helper--congruence)

    (defthm function-option-lst-syntax-p-helper--head
      (implies (and (function-option-lst-syntax-p-helper term used) term)
               (and (<= 2 (len term))
                    (function-option-syntax-p (list (car term) (cadr term))
                                              used))))

    (encapsulate ()
      (local
       (defthm lemma-16
         (implies (and (function-option-name-lst-p used)
                       (function-option-name-p new-opt)
                       (function-option-lst-syntax-p-helper term (cons new-opt used)))
                  (function-option-lst-syntax-p-helper term used))
         :hints(("Goal"
                 :in-theory (disable
                             function-option-lst-syntax-p-helper--monotonicity)
                 :use((:instance function-option-lst-syntax-p-helper--monotonicity
                                 (used-1 used) (used (cons new-opt used))
                                 (term term))))))
       )

      (defthm function-option-lst-syntax-p-helper-preserve
        (implies (and (function-option-lst-syntax-p-helper term nil)
                      (consp term))
                 (function-option-lst-syntax-p-helper (cddr term)
                                                      nil))
        :hints (("Goal"
                 :in-theory (disable lemma-16)
                 :expand ((function-option-lst-syntax-p-helper term nil)
                          (function-option-syntax-p (list (car term) (cadr term))
                                                    nil))
                 :use ((:instance lemma-16
                                  (term (cddr term))
                                  (new-opt (car term))
                                  (used nil)))))))
    )

  (define function-option-lst-syntax-p ((term t))
    :parents (function-syntax)
    :returns (syntax-good? booleanp)
    :short "Recogizer for function-option-lst-syntax"
    (function-option-lst-syntax-p-helper term nil))

  (define function-option-lst-syntax-fix ((term function-option-lst-syntax-p))
    :parents (function-syntax)
    :returns (fixed-term function-option-lst-syntax-p)
    :short "Recogizer for function-option-lst-syntax"
    (mbe :logic (if (function-option-lst-syntax-p term) term nil)
         :exec term)
    ///
    (more-returns
     (fixed-term
      (implies (function-option-lst-syntax-p term)
               (equal fixed-term term))
      :hints(("Goal" :expand (function-option-lst-syntax-fix term)))
      :name
      function-option-lst-syntax-fix-when-function-option-lst-syntaxp)))

  (encapsulate ()
    (local (in-theory (enable function-option-lst-syntax-fix)))

    (deffixtype function-option-lst-syntax
      :pred  function-option-lst-syntax-p
      :fix   function-option-lst-syntax-fix
      :equiv function-option-lst-syntax-equiv
      :define t
      :forward t
      :topic function-option-lst-syntax-p))

  (encapsulate ()
    (local (defthm lemma1
             (implies (and (function-option-lst-syntax-p term) term)
                      (and (mv-nth 0 (function-option-syntax-p
                                      (list (car term) (cadr term)) nil))
                           (consp (cdr term))
                           (function-option-lst-syntax-p (cddr term))
                           (true-listp term)))
             :hints(("Goal"
                     :expand((function-option-lst-syntax-p term)
                             (function-option-lst-syntax-p-helper term nil)
                             (function-option-lst-syntax-p (cddr term)))))))

    (local (defthmd lemma2
             (implies (and (mv-nth 0 (function-option-syntax-p term nil)) term)
                      (and (member-equal (car term) *function-option-names*)
                           (or (and (equal (cdr (assoc-equal (car term) *function-options*)) 'argument-lst-syntax-p)
                                    (argument-lst-syntax-p (cadr term)))
                               (and (equal (cdr (assoc-equal (car term) *function-options*)) 'natp)
                                    (natp (cadr term)))
                               (and (equal (cdr (assoc-equal (car term) *function-options*)) 'hypothesis-syntax-p)
                                    (hypothesis-syntax-p (cadr term)))
                               (and (equal (cdr (assoc-equal (car term) *function-options*)) 'hypothesis-lst-syntax-p)
                                    (hypothesis-lst-syntax-p (cadr term))))))
             :hints(("Goal" :expand((function-option-syntax-p term nil)
                                    (:free (option-type) (eval-function-option-type
                                                          option-type (cadr term)))
                                    (function-option-name-p (car term)))))))

    (defthm everything-about-function-option-lst-syntax-p
      (implies (and (function-option-lst-syntax-p term) term)
               (let* ((opt (car term)) (val (cadr term)) (rest (cddr term))
                      (option-type (cdr (assoc-equal opt *function-options*))))
                 (and (true-listp term)
                      (consp (cdr term))
                      (equal (function-option-lst-syntax-fix term) term)
                      (function-option-lst-syntax-p rest)
                      (member-equal opt *function-option-names*)
                      (member-equal option-type *function-option-types*)
                      (implies (equal option-type 'argument-lst-syntax-p)
                               (argument-lst-syntax-p val))
                      (implies (equal option-type 'natp)
                               (and (integerp val) (<= 0 val)))
                      (implies (equal option-type 'hypothesis-syntax-p)
                               (hypothesis-syntax-p val))
                      (implies (equal option-type 'hypothesis-lst-syntax-p)
                               (hypothesis-lst-syntax-p val)))))
      :hints(("Goal"
              :in-theory (disable lemma2)
              :use((:instance lemma2 (term (list (car term) (cadr term))))))))
    )

  (define function-syntax-p ((term t))
    :parents (function-syntax)
    :returns (syntax-good? booleanp)
    :short "Recognizer for function-syntax."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) t)
         ((cons fname function-options) term))
      ;; It's probably possible to check existence of function?
      ;; Currently not doing such check, since it will require passing state.
      (and (symbolp fname)
           (function-option-lst-syntax-p function-options))))

  (define function-syntax-fix ((term function-syntax-p))
    :parents (function-syntax)
    :returns (fixed-term function-syntax-p)
    :short "Fixing function for function-syntax-p"
    (mbe :logic (if (function-syntax-p term) term nil)
         :exec term))

  (encapsulate ()
    (local (in-theory (enable function-syntax-fix)))
    (deffixtype function-syntax
      :pred  function-syntax-p
      :fix   function-syntax-fix
      :equiv function-syntax-equiv
      :define t
      :forward t
      :topic function-syntax-p))

  (define function-lst-syntax-p ((term t))
    :parents (function-syntax)
    :returns (syntax-good? booleanp)
    :short "Recognizer for function-lst-syntax"
    (b* (((if (atom term)) (equal term nil))
         ((cons first rest) term))
      (and (function-syntax-p first)
           (function-lst-syntax-p rest))))

  (define function-lst-syntax-fix ((term function-lst-syntax-p))
    :parents (function-syntax)
    :returns (fixed-term function-lst-syntax-p
                         :hints (("Goal" :in-theory (enable
                                                     function-lst-syntax-p))))
    :short "Fixing function for function-lst-syntax-fix"
    :guard-hints (("Goal" :in-theory (enable function-lst-syntax-fix
                                             function-syntax-fix function-lst-syntax-p function-syntax-p)))
    (mbe :logic (if (consp term)
                    (cons (function-syntax-fix (car term))
                          (function-lst-syntax-fix (cdr term)))
                  nil)
         :exec term))

  (encapsulate ()
    (local (in-theory (enable function-lst-syntax-fix)))
    (deffixtype function-lst-syntax
      :pred  function-lst-syntax-p
      :fix   function-lst-syntax-fix
      :equiv function-lst-syntax-equiv
      :define t
      :forward t
      :topic function-lst-syntax-p))

  (in-theory (disable ;; set-equiv-if-true-set-equiv
              ;; subsetp-if-true-set-equiv
              ;; true-set-equiv-is-for-true-lists
              function-option-name-fix-preserves-member
              function-option-name-lst-fix-preserves-subsetp
              function-option-name-lst-fix-preserves-set-equiv
              function-option-name-lst-p-and-member
              function-option-name-lst-p--monotonicity
              function-option-name-lst-p--congruence
              function-option-syntax-p--monotonicity.ok
              function-option-syntax-p--ok-congruence.ok
              function-option-syntax-p--monotonicity.new-used
              function-option-syntax-p--new-used-when-ok
              function-option-lst-syntax-p-helper--monotonicity
              function-option-lst-syntax-p-helper--congruence
              function-option-lst-syntax-p-helper--head
              function-option-lst-syntax-p-helper-preserve
              function-option-lst-syntax-fix-when-function-option-lst-syntaxp
              ))
  )

(defsection smt-solver-params
  :parents (Smtlink-process-user-hint)

  (define smt-solver-params-p ((term t))
    :parents (smt-solver-params)
    :returns (syntax-good? booleanp)
    :short "Recognizer for smt-solver-params."
    (true-listp term))

  (define smt-solver-params-fix ((term smt-solver-params-p))
    :parents (smt-solver-params)
    :returns (fixed-term smt-solver-params-p
                         :hints (("Goal" :in-theory (enable smt-solver-params-p))))
    :short "Fixing function for smt-solver-params."
    (mbe :logic (if (smt-solver-params-p term) term (true-list-fix term))
         :exec term))

  (encapsulate ()
    (local (in-theory (enable smt-solver-params-fix)))
    (deffixtype smt-solver-params
      :pred  smt-solver-params-p
      :fix   smt-solver-params-fix
      :equiv smt-solver-params-equiv
      :define t
      :forward t
      :topic smt-solver-params-p))
  )

(defsection smtlink-hint-syntax
  :parents (Smtlink-process-user-hint)

  (defconst *smtlink-options*
    '((:functions . function-lst-syntax-p)
      (:hypotheses . hypothesis-lst-syntax-p)
      (:main-hint . hints-syntax-p)
      (:abstract . symbol-listp)
      (:fty . symbol-listp)
      (:int-to-rat . booleanp)
      (:smt-fname . stringp)
      (:smt-dir . stringp)
      (:rm-file . booleanp)
      (:smt-solver-params . smt-solver-params-p)
      ;; internal parameter
      (:custom-p . booleanp)
      (:wrld-len . natp)))

  (defconst *smtlink-option-names*
    (strip-cars *smtlink-options*))

  (defconst *smtlink-option-types*
    (remove-duplicates-equal (strip-cdrs *smtlink-options*)))

  (define smtlink-option-type-p ((option-type t))
    :parents (smtlink-hint-syntax)
    :returns (syntax-good? booleanp)
    :short "Recoginizer for smtlink-option-type."
    (if (member-equal option-type *smtlink-option-types*) t nil))

  (define smtlink-option-type-fix ((opttype smtlink-option-type-p))
    :parents (smtlink-hint-syntax)
    :returns (fixed-opttype smtlink-option-type-p
                            :hints (("Goal" :in-theory (enable
                                                        smtlink-option-type-p))))
    :short "Fixing function for smtlink-option-type."
    (mbe :logic (if (smtlink-option-type-p opttype) opttype 'function-lst-syntax-p)
         :exec opttype))

  (define smtlink-option-name-p ((option-name t))
    :parents (smtlink-hint-syntax)
    :returns (syntax-good? booleanp)
    :short "Recoginizer for an smtlink-option-name."
    (if (member-equal option-name *smtlink-option-names*) t nil))

  (define smtlink-option-name-fix ((option smtlink-option-name-p))
    :parents (smtlink-hint-syntax)
    :returns (fixed-smtlink-option-name smtlink-option-name-p)
    :short "Fixing function for smtlink-option-name."
    (mbe :logic (if (smtlink-option-name-p option) option ':functions)
         :exec option))

  (encapsulate ()
    (local (in-theory (enable smtlink-option-name-fix)))
    (deffixtype smtlink-option-name
      :pred  smtlink-option-name-p
      :fix   smtlink-option-name-fix
      :equiv smtlink-option-name-equiv
      :define t
      :forward t
      :topic smtlink-option-name-p)

    (deflist smtlink-option-name-lst
      :parents (smtlink-option-name-p)
      :elt-type smtlink-option-name
      :true-listp t))

  (defthm smtlink-option-name-fix-preserves-member
    (implies (member x used :test 'equal)
             (member (smtlink-option-name-fix x)
                     (smtlink-option-name-lst-fix used) :test 'equal)))

  (defthm smtlink-option-name-lst-fix-preserves-subsetp
    (implies (subsetp used-1 used-2 :test 'equal)
             (subsetp (smtlink-option-name-lst-fix used-1)
                      (smtlink-option-name-lst-fix used-2)
                      :test 'equal))
    :hints(("Goal" :in-theory (e/d (subsetp-equal)))))

  (defthm smtlink-option-name-lst-fix-preserves-set-equiv
    (implies (acl2::set-equiv used-1 used-2)
             (acl2::set-equiv
              (smtlink-option-name-lst-fix used-1)
              (smtlink-option-name-lst-fix used-2)))
    :hints (("Goal" :in-theory (enable acl2::set-equiv)))
    :rule-classes(:congruence))

  (defthm smtlink-option-name-lst-p-and-member
    (implies (and (member x used)
                  (not (smtlink-option-name-p x)))
             (not (smtlink-option-name-lst-p used)))
    :hints(("Goal" :in-theory (enable smtlink-option-name-lst-p))))

  (defthm smtlink-option-name-lst-p--monotonicity
    (implies (and (equal (true-listp used-1) (true-listp used-2))
                  (subsetp used-1 used-2 :test 'equal)
                  (smtlink-option-name-lst-p used-2))
             (smtlink-option-name-lst-p used-1))
    :hints(("Goal" :in-theory (enable smtlink-option-name-lst-p))))

  (defthm smtlink-option-name-lst-p--congruence
    (implies (true-set-equiv used-1 used-2)
             (equal (smtlink-option-name-lst-p used-1)
                    (smtlink-option-name-lst-p used-2)))
    :hints(("Goal" :cases ((smtlink-option-name-lst-p used-1)
                           (smtlink-option-name-lst-p used-2))))
    :rule-classes(:congruence))

  (define eval-smtlink-option-type ((option-type smtlink-option-type-p) (term t))
    :parents (smtlink-hint-syntax)
    :returns (type-correct? booleanp)
    :short "Evaluating types for smtlink option body."
    (case option-type
      (function-lst-syntax-p (function-lst-syntax-p term))
      (hypothesis-lst-syntax-p (hypothesis-lst-syntax-p term))
      (hints-syntax-p (hints-syntax-p term))
      (symbol-listp (symbol-listp term))
      (booleanp (booleanp term))
      (stringp (stringp term))
      (smt-solver-params-p (smt-solver-params-p term))
      (custom-p (booleanp term))
      (t (natp term))))

  (define smtlink-option-syntax-p ((term t) (used smtlink-option-name-lst-p))
    :parents (smtlink-hint-syntax)
    :returns (mv (ok booleanp)
                 (new-used smtlink-option-name-lst-p
                           :hints (("Goal" :in-theory (enable smtlink-option-name-lst-p smtlink-option-name-p)))))
    :short "Recoginizer for smtlink-option-syntax."
    :guard-hints (("Goal" :in-theory (enable smtlink-option-syntax-p smtlink-option-name-p
                                             eval-smtlink-option-type smtlink-option-name-lst-p)))
    (b* ((used (smtlink-option-name-lst-fix used))
         ((unless (true-listp term)) (mv nil used))
         ((if (equal term nil)) (mv t used))
         ((unless (and (car term) (cdr term) (not (cddr term)))) (mv nil used))
         ((cons option body-lst) term)
         ((unless (smtlink-option-name-p option)) (mv nil used))
         (option-type (cdr (assoc-equal option *smtlink-options*))))
      (mv (and (not (member-equal option used))
               (eval-smtlink-option-type option-type (car body-lst)))
          (cons option used)))
    ///
    (more-returns
     (ok (implies (and (subsetp used-1 used :test 'equal) ok)
                  (mv-nth 0 (smtlink-option-syntax-p term used-1)))
         :name smtlink-option-syntax-p--monotonicity.ok
         )
     (ok (implies (acl2::set-equiv used-1 used)
                  (equal (mv-nth 0 (smtlink-option-syntax-p term used-1))
                         ok))
         :name smtlink-option-syntax-p--ok-congruence.ok
         :hints(("Goal"
                 :in-theory (disable smtlink-option-syntax-p
                                     smtlink-option-syntax-p--monotonicity.ok
                                     booleanp-of-smtlink-option-syntax-p.ok)
                 :use((:instance smtlink-option-syntax-p--monotonicity.ok
                                 (used-1 used-1) (used used) (term term))
                      (:instance smtlink-option-syntax-p--monotonicity.ok
                                 (used-1 used) (used used-1) (term term))
                      (:instance booleanp-of-smtlink-option-syntax-p.ok
                                 (used used-1) (term term))
                      (:instance booleanp-of-smtlink-option-syntax-p.ok
                                 (used used) (term term)))))
         :rule-classes (:congruence))
     (new-used (implies (and (subsetp used-1 used :test 'equal) ok)
                        (subsetp
                         (mv-nth 1 (smtlink-option-syntax-p term used-1))
                         new-used
                         :test 'equal))
               :name smtlink-option-syntax-p--monotonicity.new-used)
     (new-used (implies (and term ok)
                        (equal new-used
                               (cons (car term) (smtlink-option-name-lst-fix used))))
               :name smtlink-option-syntax-p--new-used-when-ok)))

  (define smtlink-hint-syntax-p-helper ((term t) (used smtlink-option-name-lst-p))
    :parents (smtlink-hint-syntax)
    :returns (syntax-good? booleanp)
    :short "Helper function for smtlink-hint-syntax-p."
    (b* (((unless (true-listp term)) nil)
         ((if (atom term)) (equal term nil))
         ((unless (cdr term)) nil)
         ((list* first second rest) term)
         ((mv res new-used) (smtlink-option-syntax-p (list first second) used)))
      (and res (smtlink-hint-syntax-p-helper rest new-used)))
    ///
    (defthm smtlink-hint-syntax-p-helper--monotonicity
      (implies (and (subsetp used-1 used :test 'equal)
                    (smtlink-hint-syntax-p-helper term used))
               (smtlink-hint-syntax-p-helper term used-1)))

    (defthm smtlink-hint-syntax-p-helper--congruence
      (b* ((ok (smtlink-hint-syntax-p-helper term used)))
        (implies (acl2::set-equiv used-1 used)
                 (equal (smtlink-hint-syntax-p-helper term used-1) ok)))
      :rule-classes(:congruence))

    (encapsulate ()
      (local
       (defthm lemma-16
         (implies (and (smtlink-option-name-lst-p used)
                       (smtlink-option-name-p new-opt)
                       (smtlink-hint-syntax-p-helper term (cons new-opt used)))
                  (smtlink-hint-syntax-p-helper term used))
         :hints(("Goal"
                 :in-theory (disable
                             smtlink-hint-syntax-p-helper--monotonicity)
                 :use((:instance smtlink-hint-syntax-p-helper--monotonicity
                                 (used-1 used) (used (cons new-opt used))
                                 (term term))))))
       )

      (defthm smtlink-hint-syntax-p-helper-preserve
        (implies (and (smtlink-hint-syntax-p-helper term nil)
                      (consp term))
                 (smtlink-hint-syntax-p-helper (cddr term)
                                               nil))
        :hints (("Goal"
                 :in-theory (disable lemma-16)
                 :expand ((smtlink-hint-syntax-p-helper term nil)
                          (smtlink-option-syntax-p (list (car term) (cadr term))
                                                   nil))
                 :use ((:instance lemma-16
                                  (term (cddr term))
                                  (new-opt (car term))
                                  (used nil))))))))

  (define smtlink-hint-syntax-p ((term t))
    :parents (smtlink-hint-syntax)
    :returns (syntax-good? booleanp)
    :short "Recognizer for smtlink-hint-syntax."
    (smtlink-hint-syntax-p-helper term nil))

  ;; Strange fixing function.
  (define smtlink-hint-syntax-fix ((term smtlink-hint-syntax-p))
    :parents (smtlink-hint-syntax)
    :short "Fixing function for smtlink-hint-syntax."
    :returns (fixed-smtlink-hint-syntax smtlink-hint-syntax-p)
    (mbe :logic (if (smtlink-hint-syntax-p term) term nil)
         :exec term)
    ///
    (more-returns
     (fixed-smtlink-hint-syntax
      (implies (smtlink-hint-syntax-p term)
               (equal fixed-smtlink-hint-syntax term))
      :hints(("Goal" :expand (smtlink-hint-syntax-p term)))
      :name
      smtlink-hint-syntax-fix-when-smtlink-hint-syntax-p)))

  (encapsulate ()
    (local (defthm lemma1
             (implies (and (smtlink-hint-syntax-p term) term)
                      (and (mv-nth 0 (smtlink-option-syntax-p
                                      (list (car term) (cadr term)) nil))
                           (consp (cdr term))
                           (smtlink-hint-syntax-p (cddr term))
                           (true-listp term)))
             :hints(("Goal"
                     :expand((smtlink-hint-syntax-p term)
                             (smtlink-hint-syntax-p-helper term nil)
                             (smtlink-hint-syntax-p (cddr term)))))))

    (local (defthmd lemma2
             (implies (and (mv-nth 0 (smtlink-option-syntax-p term nil)) term)
                      (and (member-equal (car term) *smtlink-option-names*)
                           (or (and (equal (cdr (assoc-equal (car term) *smtlink-options*)) 'function-lst-syntax-p)
                                    (function-lst-syntax-p (cadr term)))
                               (and (equal (cdr (assoc-equal (car term) *smtlink-options*)) 'hypothesis-lst-syntax-p)
                                    (hypothesis-lst-syntax-p (cadr
                                                              term)))
                               (and (equal (cdr (assoc-equal (car term) *smtlink-options*)) 'symbol-listp)
                                    (symbol-listp (cadr term)))
                               (and (equal (cdr (assoc-equal (car term) *smtlink-options*)) 'hints-syntax-p)
                                    (hints-syntax-p (cadr term)))
                               (and (equal (cdr (assoc-equal (car term) *smtlink-options*)) 'booleanp)
                                    (booleanp (cadr term)))
                               (and (equal (cdr (assoc-equal (car term) *smtlink-options*)) 'stringp)
                                    (stringp (cadr term)))
                               (and (equal (cdr (assoc-equal (car term) *smtlink-options*)) 'smt-solver-params-p)
                                    (smt-solver-params-p (cadr term)))
                               (and (equal (cdr (assoc-equal (car term) *smtlink-options*)) 'natp)
                                    (natp (cadr term))))))
             :hints(("Goal" :expand((smtlink-option-syntax-p term nil)
                                    (:free (option-type) (eval-smtlink-option-type
                                                          option-type (cadr term)))
                                    (smtlink-option-name-p (car term)))))))

    (defthm everything-about-smtlink-syntax-p
      (implies (and (smtlink-hint-syntax-p term) term)
               (let* ((opt (car term)) (val (cadr term)) (rest (cddr term))
                      (option-type (cdr (assoc-equal opt *smtlink-options*))))
                 (and (true-listp term)
                      (consp (cdr term))
                      (equal (smtlink-hint-syntax-fix term) term)
                      (smtlink-hint-syntax-p rest)
                      (member-equal opt *smtlink-option-names*)
                      (member-equal option-type *smtlink-option-types*)
                      (implies (equal option-type 'function-lst-syntax-p)
                               (function-lst-syntax-p val))
                      (implies (equal option-type 'hypothesis-lst-syntax-p)
                               (hypothesis-lst-syntax-p val))
                      (implies (equal option-type 'hints-syntax-p)
                               (hints-syntax-p val))
                      (implies (equal option-type 'symbol-listp)
                               (symbol-listp val))
                      (implies (equal option-type 'booleanp)
                               (booleanp val))
                      (implies (equal option-type 'stringp)
                               (stringp val))
                      (implies (equal option-type 'smt-solver-params-p)
                               (smt-solver-params-p val))
                      (implies (equal option-type 'custom-p)
                               (booleanp val))
                      (implies (equal option-type 'natp)
                               (natp val)))))
      :hints(("Goal"
              :in-theory (disable lemma2)
              :use((:instance lemma2 (term (list (car term) (cadr term))))))))
    )

  (encapsulate ()
    (local (in-theory (enable smtlink-hint-syntax-fix)))
    (deffixtype smtlink-hint-syntax
      :pred  smtlink-hint-syntax-p
      :fix   smtlink-hint-syntax-fix
      :equiv smtlink-hint-syntax-equiv
      :define t
      :forward t
      :topic smtlink-hint-syntax-p))

  (in-theory (disable smtlink-option-name-fix-preserves-member
                      smtlink-option-name-lst-fix-preserves-subsetp
                      smtlink-option-name-lst-fix-preserves-set-equiv
                      smtlink-option-name-lst-p-and-member
                      smtlink-option-name-lst-p--monotonicity
                      smtlink-option-name-lst-p--congruence

                      smtlink-option-syntax-p--monotonicity.ok
                      smtlink-option-syntax-p--ok-congruence.ok
                      smtlink-option-syntax-p--monotonicity.new-used
                      smtlink-option-syntax-p--new-used-when-ok

                      smtlink-hint-syntax-p-helper--monotonicity
                      smtlink-hint-syntax-p-helper--congruence

                      smtlink-hint-syntax-p-helper-preserve

                      smtlink-hint-syntax-fix-when-smtlink-hint-syntax-p
                      ))
  )

;; -------------------------------------------------------------------------

(defsection process-smtlink-hints
  :parents (Smtlink-process-user-hint)

  (define make-merge-formals-helper ((content argument-lst-syntax-p))
    :parents (process-smtlink-hints)
    :returns (decls decl-listp)
    :short "Adding user defined formals to overwrite what's already in smt-func."
    :measure (len content)
    :hints (("Goal" :in-theory (enable argument-lst-syntax-fix)))
    :guard-hints (("Goal" :in-theory (enable argument-lst-syntax-fix
                                             argument-lst-syntax-p
                                             argument-syntax-fix
                                             argument-syntax-p
                                             smt-typep
                                             hints-syntax-p)))
    (b* ((content (argument-lst-syntax-fix content))
         ((unless (consp content)) nil)
         ((cons first rest) content)
         ((list* argname type & hints) first)
         (new-formal (make-decl :name argname
                                :type (make-hint-pair :thm type
                                                      :hints hints))))
      (cons new-formal (make-merge-formals-helper rest))))

  (define remove-duplicate-from-decl-list ((decls decl-listp) (seen symbol-listp))
    :parents (process-smtlink-hints)
    :returns (simple-decls decl-listp)
    :short "Remove shadowed decls from decl-list"
    :measure (len decls)
    (b* ((decls (decl-list-fix decls))
         ((unless (consp decls)) nil)
         ((cons first rest) decls)
         ((decl d) first)
         (seen? (member-equal d.name seen))
         ((if seen?) (remove-duplicate-from-decl-list rest seen)))
      (cons first (remove-duplicate-from-decl-list rest (cons d.name seen)))))

  (define make-merge-formals ((content argument-lst-syntax-p) (smt-func func-p))
    :parents (process-smtlink-hints)
    :returns (func func-p)
    :short "Adding user defined formals to overwrite what's already in smt-func."
    (b* ((new-formals (make-merge-formals-helper content))
         ((func f) smt-func)
         (all-formals
          (remove-duplicate-from-decl-list (append new-formals f.formals)
                                           nil)))
      (change-func f :formals all-formals)))

  (define make-merge-returns-helper ((content argument-lst-syntax-p))
    :parents (process-smtlink-hints)
    :returns (decls decl-listp)
    :short "Adding user defined returns to overwrite what's already in smt-func."
    :measure (len content)
    :hints (("Goal" :in-theory (enable argument-lst-syntax-fix)))
    :guard-hints (("Goal" :in-theory (enable argument-lst-syntax-fix
                                             argument-lst-syntax-p
                                             argument-syntax-p
                                             argument-syntax-fix
                                             hints-syntax-p
                                             smt-typep
                                             )))
    (b* ((content (argument-lst-syntax-fix content))
         ((unless (consp content)) nil)
         ((cons first rest) content)
         ((cons argname (cons type (cons & hints))) first)
         (new-return (make-decl :name argname
                                :type (make-hint-pair :thm type
                                                      :hints (car hints)))))
      (cons new-return (make-merge-returns-helper rest))))

  (define make-merge-returns ((content argument-lst-syntax-p) (smt-func func-p))
    :parents (process-smtlink-hints)
    :returns (func func-p)
    :short "Adding user defined returns to overwrite what's already in smt-func."
    (b* ((new-return (make-merge-returns-helper content))
         ((func f) smt-func)
         (all-returns
          (remove-duplicate-from-decl-list (append new-return f.returns)
                                           nil)))
      (change-func f :returns all-returns)))

  (define make-merge-guard ((content hypothesis-syntax-p) (smt-func func-p))
    :parents (process-smtlink-hints)
    :returns (func func-p)
    :short "Adding user defined guard to smt-func."
    :guard-hints (("Goal"
                   :in-theory (enable hypothesis-syntax-fix hypothesis-syntax-p)))
    (b* ((content (hypothesis-syntax-fix content))
         (smt-func (func-fix smt-func))
         ((cons thm (cons & hints-lst)) content)
         (hints (car hints-lst))
         (new-guard (make-hint-pair :thm thm :hints hints)))
      (change-func smt-func :guard new-guard)))


  (define make-merge-more-returns ((content hypothesis-lst-syntax-p)
                                   (smt-func func-p))
    :parents (process-smtlink-hints)
    :returns (func func-p)
    :short "Adding user-defined more-return theorems."
    :measure (len content)
    :hints (("Goal" :in-theory (enable hypothesis-lst-syntax-fix)))
    :guard-hints (("Goal" :in-theory (enable hypothesis-lst-syntax-p
                                             hypothesis-lst-syntax-fix
                                             hypothesis-syntax-p
                                             hypothesis-syntax-fix)))
    (b* ((content (hypothesis-lst-syntax-fix content))
         (smt-func (func-fix smt-func))
         ((func f) smt-func)
         ((unless (consp content)) smt-func)
         ((cons first rest) content)
         ((cons thm (cons & hints-lst)) first)
         (hints (car hints-lst))
         (new-more-return (make-hint-pair :thm thm :hints hints))
         (new-func (change-func smt-func
                                :more-returns (cons new-more-return f.more-returns))))
      (make-merge-more-returns rest new-func)))

  ;; Bozo:
  ;; This implementation is potentially slow because of the threading of smt-func
  ;; all the way while at the same time updating it.
  (define make-merge-function-option-lst ((fun-opt-lst function-option-lst-syntax-p)
                                          (smt-func func-p))
    :parents (process-smtlink-hints)
    :returns (func func-p)
    :short "Add option information into func."
    :measure (len fun-opt-lst)
    :hints (("Goal" :in-theory (enable function-option-lst-syntax-fix)))
    :guard-hints (("Goal" :in-theory (disable
                                      everything-about-function-option-lst-syntax-p)
                   :use((:instance everything-about-function-option-lst-syntax-p
                                   (term fun-opt-lst)))))
    (b* ((fun-opt-lst (function-option-lst-syntax-fix fun-opt-lst))
         (smt-func (func-fix smt-func))
         ((unless (consp fun-opt-lst)) smt-func)
         ((cons option (cons content rest)) fun-opt-lst)
         (new-func (case option
                     (:formals (make-merge-formals content smt-func))
                     (:returns (make-merge-returns content smt-func))
                     (:level (change-func smt-func :expansion-depth content))
                     (:guard (make-merge-guard content smt-func))
                     (:more-returns (make-merge-more-returns content smt-func)))))
      (make-merge-function-option-lst rest new-func)))


  (define make-merge-function ((func function-syntax-p) (smt-func func-p))
    :parents (process-smtlink-hints)
    :returns (func func-p)
    :short "Function for generating func-p of a single function hint."
    :guard-hints (("Goal" :in-theory (enable function-syntax-fix function-syntax-p)))
    (b* ((func (function-syntax-fix func))
         ((cons fun-name fun-opt-lst) func)
         (name fun-name))
      (make-merge-function-option-lst fun-opt-lst
                                      (change-func smt-func :name name))))

  (define merge-functions ((content function-lst-syntax-p) (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Merging function hints into smt-hint."
    :measure (len content)
    :hints (("Goal" :in-theory (enable function-lst-syntax-fix)))
    :guard-hints (("Goal" :in-theory (enable function-lst-syntax-fix
                                             function-lst-syntax-p
                                             function-syntax-p
                                             function-syntax-fix)))
    (b* ((hint (smtlink-hint-fix hint))
         (content (function-lst-syntax-fix content))
         ((unless (consp content)) hint)
         ((cons first rest) content)
         (name (car first))
         ((smtlink-hint h) hint)
         (exist? (hons-get name h.fast-functions))
         (smt-func (if exist? (cdr exist?) (make-func)))
         (new-func-lst (cons (make-merge-function first smt-func) h.functions))
         (new-hint (change-smtlink-hint hint :functions new-func-lst)))
      (merge-functions rest new-hint)))

  (define make-merge-hypothesis ((hypo hypothesis-syntax-p))
    :parents (process-smtlink-hints)
    :returns (hp hint-pair-p)
    :short "Generate a hint-pair for hypo"
    :guard-hints (("Goal" :in-theory (enable hypothesis-syntax-p hypothesis-syntax-fix hints-syntax-p)))
    (b* ((hypo (hypothesis-syntax-fix hypo))
         ((list* thm & rest) hypo))
      (make-hint-pair :thm thm
                      :hints (car rest))))

  (define merge-hypothesis ((content hypothesis-lst-syntax-p)
                            (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Merge hypothesis into hint"
    :measure (len content)
    :hints (("Goal" :in-theory (enable hypothesis-lst-syntax-fix)))
    :guard-hints (("Goal" :in-theory (enable hypothesis-lst-syntax-p hypothesis-lst-syntax-fix)))
    (b* ((hint (smtlink-hint-fix hint))
         (content (hypothesis-lst-syntax-fix content))
         ((unless (consp content)) hint)
         ((cons first rest) content)
         ((smtlink-hint h) hint)
         (new-hypo-lst (cons (make-merge-hypothesis first) h.hypotheses))
         ;; It might be better to first generate the list of merging hypotheses
         ;; and then append the old lst after them. Not sure which one takes less
         ;; time, because I'm not sure about time complexity of
         ;; change-smtlink-hint. Append might be expensive, too.
         (new-hint (change-smtlink-hint hint :hypotheses new-hypo-lst)))
      (merge-hypothesis rest new-hint)))

  (define merge-main-hint ((content hints-syntax-p)
                           (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Merge main-hint"
    :guard-hints (("Goal"
                   :in-theory (enable hints-syntax-p)))
    (b* ((hint (smtlink-hint-fix hint))
         (content (hints-syntax-fix content))
         (new-hint (change-smtlink-hint hint :main-hint content)))
      new-hint))

  (define set-abstract-types ((content symbol-listp)
                              (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "set fty types"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :abs content)))
      new-hint))

  (define set-fty-types ((content symbol-listp)
                         (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "set fty types"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :fty content)))
      new-hint))

  (define set-int-to-rat ((content booleanp)
                          (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Set :int-to-rat based on user hint."
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :int-to-rat content)))
      new-hint))

  (define set-fname ((content stringp) (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Set :smt-fname."
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :smt-fname content)))
      new-hint))

  (define set-smt-dir ((content stringp)
                       (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Set :smt-dir"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :smt-dir content)))
      new-hint))

  (define set-rm-file ((content booleanp)
                       (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Set :rm-file"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :rm-file content)))
      new-hint))

  (define set-custom-p ((content booleanp)
                        (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Set :custom-p"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :custom-p content)))
      new-hint))

  (define set-wrld-len ((content natp)
                        (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Set :wrld-fn-len"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :wrld-fn-len content)))
      new-hint))

  (define set-smt-solver-params ((content smt-solver-params-p)
                                 (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (new-hint smtlink-hint-p)
    :short "Set :smt-params"
    :guard-hints (("Goal"
                   :in-theory (enable smt-solver-params-p smt-solver-params-fix)))
    (b* ((hint (smtlink-hint-fix hint))
         (content (smt-solver-params-fix content))
         (new-hint (change-smtlink-hint hint :smt-params content)))
      new-hint))

  (define combine-hints ((user-hint smtlink-hint-syntax-p)
                         (hint smtlink-hint-p))
    :parents (process-smtlink-hints)
    :returns (combined-hint smtlink-hint-p)
    :hints (("Goal" :in-theory (enable smtlink-hint-syntax-fix)))
    :measure (len user-hint)
    :short "Combining user-hints into smt-hint."
    :guard-hints (("Goal"
                   :in-theory (e/d (smtlink-hint-syntax-fix
                                    smtlink-hint-syntax-p smtlink-hint-syntax-p-helper)
                                   (everything-about-smtlink-syntax-p
                                    smtlink-hint-syntax-p-helper-preserve))
                   :use ((:instance everything-about-smtlink-syntax-p (term user-hint))
                         (:instance smtlink-hint-syntax-p-helper-preserve))))
    (b* ((hint (smtlink-hint-fix hint))
         (user-hint (smtlink-hint-syntax-fix user-hint))
         ((unless (consp user-hint)) hint)
         ((cons option (cons second rest)) user-hint)
         ((smtlink-hint h) hint)
         (fast-funcs (make-alist-fn-lst h.functions))
         (new-hint (case option
                     (:functions (with-fast-alist fast-funcs
                                   (merge-functions second
                                                    (change-smtlink-hint
                                                     hint
                                                     :fast-functions fast-funcs))))
                     (:hypotheses (merge-hypothesis second hint))
                     (:main-hint (merge-main-hint second hint))
                     (:abstract (set-abstract-types second hint))
                     (:fty (set-fty-types second hint))
                     (:int-to-rat (set-int-to-rat second hint))
                     (:smt-fname (set-fname second hint))
                     (:smt-dir (set-smt-dir second hint))
                     (:rm-file (set-rm-file second hint))
                     (:custom-p (set-custom-p second hint))
                     (:smt-solver-params (set-smt-solver-params second hint))
                     (t (set-wrld-len second hint)))))
      (combine-hints rest new-hint)))

  (define process-hint ((cl pseudo-term-listp) (user-hint t))
    :parents (process-smtlink-hints)
    :returns (subgoal-lst pseudo-term-list-listp)
    (b* ((cl (pseudo-term-list-fix cl))
         ((unless (smtlink-hint-syntax-p user-hint))
          (prog2$ (cw "User provided Smtlink hint can't be applied because of ~
    syntax error in the hints: ~q0Therefore proceed without Smtlink...~%" user-hint)
                  (list cl)))
         (combined-hint (combine-hints user-hint (smt-hint)))
         (next-cp (cdr (assoc-equal 'process-hint *SMT-architecture*)))
         ((if (null next-cp)) (list cl))
         (cp-hint `(:clause-processor (,next-cp clause ',combined-hint)))
         (subgoal-lst (cons `(hint-please ',cp-hint) cl)))
      (list subgoal-lst)))
  )

;; ------------------------------------------------------------------------
;;     Run translate-cmp on terms to generate translated terms
(defsection translate-cmp-smtlink
  :parents (Smtlink-process-user-hint)

  (define wrld-fn-len ((state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* ((world (w state)))
      (len (remove-duplicates-eq
            (strip-cadrs (universal-theory :here))))))

  (define trans-hypothesis ((val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* (((unless (and (true-listp val)
                       (car val)))
          val)
         ((mv err term)
          (acl2::translate-cmp (car val) t t nil 'Smtlink-process-user-hint->trans-hypothesis
                               (w state) (acl2::default-state-vars t)))
         ((when err)
          (er hard? 'Smtlink-process-user-hint->trans-hypothesis "Error ~
    translating form: ~q0" (car val))))
      `(,term ,@(cdr val))))

  (define trans-guard ((val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (trans-hypothesis val state))

  (define trans-more-returns ((val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* (((unless (true-listp val)) val)
         ((unless (consp val)) val)
         ((cons first rest) val)
         (new-first (trans-hypothesis first state)))
      (cons new-first (trans-more-returns rest state))))

  (define trans-argument ((val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* (((unless (and (true-listp val)
                       (car val) (cadr val)))
          val)
         ((list* name type rest) val)
         (to-be-trans `(,type ,name))
         ((mv err term)
          (acl2::translate-cmp to-be-trans t t nil 'Smtlink-process-user-hint->trans-hypothesis
                               (w state) (acl2::default-state-vars t)))
         ((when err)
          (er hard? 'Smtlink-process-user-hint->trans-argument "Error ~
    translating form: ~q0" to-be-trans)))
      `(,name ,(car term) ,@rest)))

  (define trans-formals ((val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* (((unless (true-listp val)) val)
         ((unless (consp val)) val)
         ((cons first rest) val)
         (new-first (trans-argument first state)))
      (cons new-first (trans-formals rest state))))

  (define trans-returns ((val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* (((unless (true-listp val)) val)
         ((unless (consp val)) val)
         ((cons first rest) val)
         (new-first (trans-argument first state)))
      (cons new-first (trans-formals rest state))))

  (define trans-func-option ((opt t) (val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (cond ((equal opt ':formals) (trans-formals val state))
          ((equal opt ':returns) (trans-returns val state))
          ((equal opt ':guard) (trans-guard val state))
          ((equal opt ':more-returns) (trans-more-returns val state))
          (t val)))

  (define trans-function ((val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* (((unless (and (true-listp val) (consp val)))
          val)
         ((list* first second rest) val)
         (new-second (trans-func-option first second state))
         (new-functions `(,first ,new-second ,@(trans-function rest state))))
      new-functions))

  (define trans-functions ((val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* (((unless (true-listp val)) val)
         ((unless (consp val)) val)
         ((cons first rest) val)
         ((cons fname options) first)
         (new-first `(,fname ,@(trans-function options state))))
      (cons new-first (trans-functions rest state))))

  (define trans-hypotheses ((val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* (((unless (true-listp val)) val)
         ((unless (consp val)) val)
         ((cons first rest) val)
         (new-first (trans-hypothesis first state)))
      (cons new-first (trans-hypotheses rest state))))

  (define trans-hint-option ((opt t) (val t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (cond ((equal opt ':functions) (trans-functions val state))
          ((equal opt ':hypotheses) (trans-hypotheses val state))
          ((equal opt ':wrld-len)
           (er hard?
               'Smtlink-process-user-hint->trans-hint-option
               "User trying to access internal parameter ~
                wrld-len!"))
          (t val)))

  (define trans-hint ((hint t) (state))
    :parents (translate-cmp-smtlink)
    :mode :program
    (b* (((unless (true-listp hint)) hint)
         (wrld-len (wrld-fn-len state))
         ((if (atom hint)) `(:wrld-len ,wrld-len))
         ((unless (cdr hint)) hint)
         ((list* first second rest) hint)
         (new-second (trans-hint-option first second state))
         (new-hint `(,first ,new-second ,@(trans-hint rest state))))
      new-hint))
  )

;; ------------------------------------------------------------
;;         Prove correctness of clause processor
;;

;; -----------------------------------------------------------------
;;       Define evaluators
(defsection process-hint-clause-processor
  :parents (Smtlink-process-user-hint)

  (defevaluator ev-process-hint ev-lst-process-hint
    ((not x) (if x y z) (hint-please hint)))

  (def-join-thms ev-process-hint)

  (encapsulate ()
    (local (in-theory (enable process-hint)))

    (defthm correctness-of-process-hint
      (implies (and (pseudo-term-listp cl)
                    (alistp b)
                    (ev-process-hint
                     (conjoin-clauses (process-hint cl hint))
                     b))
               (ev-process-hint (disjoin cl) b))
      :rule-classes :clause-processor))

  ;; Smtlink is a macro that generates a clause processor hint. This clause
  ;;   processor hint generates a clause, with which a new smt-hint is attached.
  ;;   This new smt-hint combines user given hints with defattach hints.
  ;; A computed hint will be waiting to take the clause and hint for clause
  ;;   expansion and transformation.
  (defmacro Smtlink (clause hint)
    `(process-hint ,clause (trans-hint ',hint state)))

  (defmacro Smtlink-custom (clause hint)
    `(process-hint ,clause (trans-hint ',(append hint '(:custom-p t)) state)))

  ;; Adding :smtlink as a custom :hints option
  (add-custom-keyword-hint :smtlink
                           (pprogn
                            (fms "~%Using clause-processor Smtlink~%"
                                 nil *standard-co* state nil)
                            (value
                             (acl2::splice-keyword-alist
                              :smtlink
                              `(:clause-processor (smtlink clause ,acl2::val))
                              acl2::keyword-alist))))

  ;; Adding :smtlink-custom as a custom :hints option
  (add-custom-keyword-hint :smtlink-custom
                           (pprogn
                            (fms "~%Using clause-processor Smtlink (customized)~%"
                                 nil *standard-co* state nil)
                            (value
                             (acl2::splice-keyword-alist
                              :smtlink-custom
                              `(:clause-processor (smtlink-custom clause ,acl2::val))
                              acl2::keyword-alist))))
  )

;; Copyright (C) 2015, University of British Columbia
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
(include-book "centaur/fty/top" :dir :system)

(include-book "smt-hint-table")
(include-book "hint-please")
(include-book "basics")
(include-book "evaluator")
(include-book "../config")

(defsection Smtlink-process-user-hint
  :parents (verified)
  :short "Functionalities for processing user hints given to Smtlink. User
  hints will be merged with (smt-hint)."

  ;; --------------------------------------------------------

;; Example:
;; :hints (("Goal"
;;          :smtlink
;;          (:functions
;;           ((f0 :formals ((a0 rationalp))
;;                :returns
;;                ((r0 rationalp
;;                     :name rationalp-of-f0))
;;                :expansion-depth 1
;;                :guard ((> a0 0)
;;                        :name a0->-0 <or>
;;                        :hints (:use ((:instance guard-lemma))))
;;                :more-returns
;;                (((> r0 0)
;;                  :name r0->-0 <or> :hints (:use ((:instance more-lemma)))))))
;;           :types
;;           ((integer-list
;;             :recognizer integer-listp
;;             :fixer integer-list-fix
;;             :fixer-when-recognizer-thm integer-list-fix-when-integer-listp
;;             :kind (:list
;;                    :cons
;;                    (:constructor
;;                     (integer-list-cons :return-type integer-list-p
;;                                        :type-thm (:name ... :hints ...))
;;                     :destructors
;;                     ((integer-list-car :return-type integerp
;;                                        :type-thm (:name ...)
;;                                        :destructor-thm (:name ...))
;;                      (integer-list-cdr ...)))
;;                    :nil-kind
;;                    (:constructor
;;                     (integer-list-nil :return-type ...
;;                                       :type-thm (:name ... :hints ...))))
;;             (:abstract)
;;             (:prod
;;              :constructor ()
;;              :destructors (() () ...))
;;             (:sum
;;              :kind-fn integer-list-kind
;;              :kind1
;;              (:constructor (...)
;;               :destructors (() () ...))
;;              :kind2
;;               (:constructor (...)
;;                :destructors (() () ...)))
;;             (:option
;;              :some
;;              (:constructor ()
;;               :destructor ())
;;              :none
;;              (:constructor ()))
;;            (...)
;;            ...)
;;           :hypotheses (((> a b) :hints (:use ((:instance lemma)))))
;;           :rm-file t
;;           :smt-dir ""
;;           :smt-fname ""
;;           :int-to-rat nil
;;           :use-uninterpreted t
;;           :under-induct nil
;;           :global-hint nil
;;           :wrld-fn-len 0
;;           :custom-p nil
;;           )))

  ;; A few note for :name of hint-pair:
  ;; A :name represents the name of the theorem. This theorem when
  ;; instantiated can be used as a conjunction of the hypotheses and this can
  ;; be proved using meta-extract, so no additional subgoals will be generated.
  ;; When a :hints used, it gives an ACL2 hint that can help with the proof of
  ;; the generated subgoal.
  ;;
  ;; In principal, Smtlink returns the minimal number of subgoals, therefore
  ;; :name should be in most cases the only one that's useful. I'm keeping
  ;; :hints in case we do need it in some cases.
  ;;
  ;; When both :name and :hints exist, :name is preferred.
  ;;

  ;; TODO: implement use-uninterpreted and under-induct options
  ;; TODO: I will write macros for this file if I've got time.
  )

(defsection hints-syntax
  :parents (Smtlink-process-user-hint)

  (define hints-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for hints-syntax."
    (true-listp term)
    ///
    (more-returns
     (syntax-good?
      (implies syntax-good? (true-listp term))
      :name true-listp-of-hints-syntax-p)))

  (easy-fix hints-syntax nil)
  )

(defsection hypothesis-lst-syntax
  :parents (Smtlink-process-user-hint)

  (define hypothesis-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for hypothesis-syntax."
    (or (and (atom term)
             (equal term nil))
        ;; Without hints
        (and (true-listp term)
             (car term) (not (cdr term))
             (pseudo-termp (car term)))
        ;; With name
        (and (true-listp term)
             (car term) (cadr term) (not (cdddr term))
             (pseudo-termp (car term))
             (equal (cadr term) ':name)
             (symbolp (caddr term)))
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
      :hints (("Goal" :in-theory (enable hints-syntax-p))))
    )

  (easy-fix hypothesis-syntax nil)

  (deflist hypothesis-lst-syntax
    :pred hypothesis-lst-syntax-p
    :elt-type hypothesis-syntax-p
    :true-listp t)
)

(defsection argument-lst-syntax
  :parents (Smtlink-process-user-hint)

  (define smt-typep ((term t))
    :enabled t
    :returns (valid-type? booleanp)
    :short "Should be a smtlink fixtype. This is just a syntax check, so it
    only need to be a symbol."
    (symbolp term))

  (define argument-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "recognizer for argument-syntax."
    (or (and (atom term)
             (equal term nil))
        ;; just the name
        (and (true-listp term)
             (car term) (not (cdr term))
             (symbolp (car term)))
        ;; the name and the type/guard
        (and (true-listp term)
             (car term) (cadr term) (not (cddr term))
             (symbolp (car term))
             (smt-typep (cadr term)))
        ;; the name, the type and the theorem
        ;; For formals, no such theorem exists;
        ;; For returns, such theorem exists
        (and (true-listp term)
             (car term) (cadr term) (not (cddddr term))
             (symbolp (car term))
             (smt-typep (cadr term))
             (equal ':name (caddr term))
             (symbolp (cadddr term)))
        ))

  (easy-fix argument-syntax nil)

  (deflist argument-lst-syntax
    :elt-type argument-syntax-p
    :pred argument-lst-syntax-p
    :true-listp t)
  )

(defthm symbol-list-fix-preserve-member-equal
  (implies (and (consp x)
                (member-equal (car x) y))
           (member-equal (symbol-fix (car x))
                         (symbol-list-fix y)))
  :hints (("Goal"
           :in-theory (enable symbol-list-fix member-equal))))

(defthm symbol-list-fix-preserve-subsetp-equal
  (implies (subsetp x y :test 'equal)
           (subsetp (symbol-list-fix x) (symbol-list-fix y) :test 'equal))
  :hints (("Goal"
           :in-theory (enable symbol-list-fix subsetp-equal))))

(defsection function-option-syntax
  :parents (function-syntax)

  (define function-option-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for function-option-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>function-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            ;; TODO: I didn't check for distinct formals.
            (:formals (argument-lst-syntax-p second))
            (:returns (argument-lst-syntax-p second))
            (:expansion-depth (natp second))
            (:guard (hypothesis-syntax-p second))
            (:more-returns (hypothesis-lst-syntax-p second))
            (t (er hard? 'process=>function-option-syntax-p-helper
                   "Smtlink-hint function hint option doesn't include: ~p0.
                       They are :formals, :returns, :expansion-depth, :guard, and
                       :more-returns.~%" first)))))
      (and first-ok
           (function-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and (symbol-listp used) ok (consp term))
                  (and (not (member-equal (car term) used))
                       (consp (cdr term))
                       (implies (equal (car term) :formals)
                                (argument-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :returns)
                                (argument-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :expansion-depth)
                                (natp (cadr term)))
                       (implies (equal (car term) :guard)
                                (hypothesis-syntax-p (cadr term)))
                       (implies (equal (car term) :more-returns)
                                (hypothesis-lst-syntax-p (cadr term)))))
         :name definition-of-function-option-syntax-p-helper)
     (ok (implies (and (symbol-listp used) ok (consp term))
                  (or (equal (car term) :formals)
                      (equal (car term) :returns)
                      (equal (car term) :guard)
                      (equal (car term) :more-returns)
                      (equal (car term) :expansion-depth)))
         :name option-of-function-option-syntax-p-helper))
    (defthm monotonicity-of-function-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (function-option-syntax-p-helper term used))
               (function-option-syntax-p-helper term used-1)))
    )

  (defthm monotonicity-of-function-option-syntax-p-helper-corollary
    (implies (function-option-syntax-p-helper term used)
             (function-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-function-option-syntax-p-helper)
             :use ((:instance monotonicity-of-function-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define function-option-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for function-option-syntax."
    (function-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :formals)
                                (argument-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :returns)
                                (argument-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :expansion-depth)
                                (natp (cadr term)))
                       (implies (equal (car term) :guard)
                                (hypothesis-syntax-p (cadr term)))
                       (implies (equal (car term) :more-returns)
                                (hypothesis-lst-syntax-p (cadr term)))))
         :name definition-of-function-option-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-function-option-syntax-p-helper)
                  :use ((:instance
                         definition-of-function-option-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term)
                       (not (equal (car term) :expansion-depth))
                       (not (equal (car term) :formals))
                       (not (equal (car term) :returns))
                       (not(equal (car term) :guard)))
                  (equal (car term) :more-returns))
         :name option-of-function-option-syntax-p
         :hints (("Goal"
                  :in-theory (disable option-of-function-option-syntax-p-helper)
                  :use ((:instance
                         option-of-function-option-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term))
                  (function-option-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (function-option-syntax-p-helper term nil)))
         :name monotonicity-of-function-option-syntax-p)
     ))

  (easy-fix function-option-syntax nil)
  )

(defsection function-syntax
  :parents (Smtlink-process-user-hint)

  (define function-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for function-syntax."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) t)
         ((cons fname function-options) term))
      (and (symbolp fname)
           (function-option-syntax-p function-options))))

  (easy-fix function-syntax nil)

  (deflist function-lst-syntax
    :elt-type function-syntax-p
    :pred function-lst-syntax-p
    :true-listp t)
  )

(defsection type-function-syntax
  :parents (kind-syntax)

  (define type-thm-syntax-p-helper ((term t)
                                    (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for type-thm-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>type-thm-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:name (symbolp second))
            (:hints (hints-syntax-p second))
            (t (er hard? 'process=>type-thm-syntax-p-helper
                   "Smtlink-hint type-thm-syntax option doesn't include:
                    ~p0. They are :name, and :hints~%" first)))))
      (and first-ok
           (type-thm-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (not (member-equal (car term) used))
                       (implies (equal (car term) :name)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :hints)
                                (hints-syntax-p (cadr term)))))
         :name definition-of-type-thm-syntax-p-helper
         :hints (("Goal"
                  :expand (type-thm-syntax-p-helper term used))))
     (ok (implies (and ok (consp term) (symbol-listp used)
                       (not (equal (car term) :name)))
                  (equal (car term) :hints))
         :name option-of-type-thm-syntax-p-helper
         :hints (("Goal"
                  :expand (type-thm-syntax-p-helper term used)))))
     (defthm monotonicity-of-type-thm-syntax-p-helper
       (implies (and (subsetp used-1 used :test 'equal)
                     (type-thm-syntax-p-helper term used))
                (type-thm-syntax-p-helper term used-1)))
     )

  (defthm monotonicity-of-type-thm-syntax-p-helper-corollary
    (implies (type-thm-syntax-p-helper term used)
             (type-thm-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-type-thm-syntax-p-helper)
             :use ((:instance monotonicity-of-type-thm-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define type-thm-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for type-thm-syntax-p."
    (type-thm-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :name)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :hints)
                                (hints-syntax-p (cadr term)))))
         :name definition-of-type-thm-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-type-thm-syntax-p-helper)
                  :use ((:instance
                         definition-of-type-thm-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term)
                       (not (equal (car term) :name)))
                  (equal (car term) :hints))
         :name option-of-type-thm-syntax-p
         :hints (("Goal"
                  :in-theory (disable option-of-type-thm-syntax-p-helper)
                  :use ((:instance
                         option-of-type-thm-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term))
                  (type-thm-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (type-thm-syntax-p-helper term nil)))
         :name monotonicity-of-type-thm-syntax-p)
     ))

  (easy-fix type-thm-syntax nil)

  (define type-function-option-syntax-p-helper ((term t)
                                                (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for type-function-option-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>type-function-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:return-type (symbolp second))
            (:type-thm (type-thm-syntax-p second))
            (:destructor-thm (type-thm-syntax-p second))
            (t (er hard? 'process=>type-function-option-syntax-p-helper
                   "Smtlink-hint type-function-option-syntax option doesn't
                    include: ~p0. They are :return-type, :type-thm, and
                    :destructor-thm.~%" first)))))
      (and first-ok
           (type-function-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (not (member-equal (car term) used))
                       (implies (equal (car term) :return-type)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :type-thm)
                                (type-thm-syntax-p (cadr term)))
                       (implies (equal (car term) :destructor-thm)
                                (type-thm-syntax-p (cadr term)))))
         :name definition-of-type-function-option-syntax-p-helper
         :hints (("Goal"
                  :expand (type-function-option-syntax-p-helper term used))))
     (ok (implies (and ok (consp term) (symbol-listp used)
                       (not (equal (car term) :return-type))
                       (not (equal (car term) :type-thm)))
                  (equal (car term) :destructor-thm))
         :name option-of-type-function-option-syntax-p-helper
         :hints (("Goal"
                  :expand (type-function-option-syntax-p-helper term used)))))
    (defthm monotonicity-of-type-function-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (type-function-option-syntax-p-helper term used))
               (type-function-option-syntax-p-helper term used-1))))

  (defthm monotonicity-of-type-function-option-syntax-p-helper-corollary
    (implies (type-function-option-syntax-p-helper term used)
             (type-function-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-type-function-option-syntax-p-helper)
             :use ((:instance monotonicity-of-type-function-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define type-function-option-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for type-function-option-syntax-p."
    (type-function-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :return-type)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :type-thm)
                                (type-thm-syntax-p (cadr term)))
                       (implies (equal (car term) :destructor-thm)
                                (type-thm-syntax-p (cadr term)))))
         :name definition-of-type-function-option-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-type-function-option-syntax-p-helper)
                  :use ((:instance
                         definition-of-type-function-option-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term)
                       (not (equal (car term) :return-type))
                       (not (equal (car term) :type-thm)))
                  (equal (car term) :destructor-thm))
         :name option-of-type-function-option-syntax-p
         :hints (("Goal"
                  :in-theory (disable option-of-type-function-option-syntax-p-helper)
                  :use ((:instance
                         option-of-type-function-option-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term))
                  (type-function-option-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (type-function-option-syntax-p-helper term nil)))
         :name monotonicity-of-type-function-option-syntax-p)))

  (easy-fix type-function-option-syntax nil)

  (define type-function-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for type-function-syntax-p."
    (b* (((unless (consp term)) nil)
         ((cons name options) term))
      (and (symbolp name)
           (type-function-option-syntax-p options))))

  (easy-fix type-function-syntax '(:abstract))

  (deflist type-function-list-syntax
    :elt-type type-function-syntax-p
    :true-listp t)
  )

(defsection kind-syntax
  :parents (type-syntax)

  ;; abstract-kind
  (define abstract-kind-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for abstract-kind-syntax."
    (null term))

  (easy-fix abstract-kind-syntax nil)

  ;; array-kind
  (define array-kind-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for array-kind-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>array-kind-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:store (symbolp second))
            (:select (symbolp second))
            (:k (symbolp second))
            (:key-type (symbolp second))
            (:val-type (symbolp second))
            (:array-thm (type-thm-syntax-p second))
            (t (er hard? 'process=>array-kind-syntax-p-helper
                   "Smtlink-hint array-kind option doesn't include: ~p0.
                       They are :store, :select, :k, :key-type, :val-type, and
                       :array-thm.~%" first)))))
      (and first-ok
           (array-kind-syntax-p-helper rest (cons first used)))))

  (define array-kind-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for array-kind-syntax."
    (array-kind-syntax-p-helper term nil))

  (easy-fix array-kind-syntax nil)

  ;; prod-option
  (define prod-option-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for prod-option-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>prod-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:constructor (type-function-syntax-p second))
            (:destructors (type-function-list-syntax-p second))
            (t (er hard? 'process=>prod-option-syntax-p-helper
                   "Smtlink-hint prod-option doesn't include: ~p0.
                       They are :constructor, and :field-accessors.~%"
                   first)))))
      (and first-ok
           (prod-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (not (member-equal (car term) used))
                       (implies (equal (car term) :constructor)
                                (type-function-syntax-p (cadr term)))
                       (implies (equal (car term) :destructors)
                                (type-function-list-syntax-p (cadr term)))))
         :name definition-of-prod-option-syntax-p-helper
         :hints (("Goal"
                  :expand (prod-option-syntax-p-helper term used))))
     (ok (implies (and ok (consp term) (symbol-listp used)
                       (not (equal (car term) :constructor)))
                  (equal (car term) :destructors))
         :name option-of-prod-option-syntax-p-helper
         :hints (("Goal"
                  :expand (prod-option-syntax-p-helper term used)))))
    (defthm monotonicity-of-prod-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (prod-option-syntax-p-helper term used))
               (prod-option-syntax-p-helper term used-1))))

  (defthm monotonicity-of-prod-option-syntax-p-helper-corollary
    (implies (prod-option-syntax-p-helper term used)
             (prod-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-prod-option-syntax-p-helper)
             :use ((:instance monotonicity-of-prod-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define prod-kind-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for prod-kind-syntax."
    (prod-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :constructor)
                                (type-function-syntax-p (cadr term)))
                       (implies (equal (car term) :destructors)
                                (type-function-list-syntax-p (cadr term)))))
         :name definition-of-prod-kind-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-prod-option-syntax-p-helper)
                  :use ((:instance
                         definition-of-prod-option-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term)
                       (not (equal (car term) :constructor)))
                  (equal (car term) :destructors))
         :name option-of-prod-kind-syntax-p
         :hints (("Goal"
                  :in-theory (disable option-of-prod-option-syntax-p-helper)
                  :use ((:instance
                         option-of-prod-option-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term))
                  (prod-kind-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (prod-option-syntax-p-helper term nil)))
         :name monotonicity-of-prod-kind-syntax-p)))

  (easy-fix prod-kind-syntax nil)

  ;; list-kind
  (define list-kind-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for list-kind-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>list-kind-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:cons (prod-kind-syntax-p second))
            (:nil-kind (prod-kind-syntax-p second))
            (t (er hard? 'process=>list-kind-syntax-p-helper
                   "Smtlink-hint list-kind option doesn't include: ~p0.
                       They are :cons, and :nil-kind.~%"
                   first)))))
      (and first-ok
           (list-kind-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (not (member-equal (car term) used))
                       (implies (equal (car term) :cons)
                                (prod-kind-syntax-p (cadr term)))
                       (implies (equal (car term) :nil-kind)
                                (prod-kind-syntax-p (cadr term)))))
         :name definition-of-list-kind-syntax-p-helper
         :hints (("Goal"
                  :expand (list-kind-syntax-p-helper term used))))
     (ok (implies (and ok (consp term) (symbol-listp used)
                       (not (equal (car term) :cons)))
                  (equal (car term) :nil-kind))
         :name option-of-list-kind-syntax-p-helper
         :hints (("Goal"
                  :expand (list-kind-syntax-p-helper term used)))))
    (defthm monotonicity-of-list-kind-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (list-kind-syntax-p-helper term used))
               (list-kind-syntax-p-helper term used-1))))

  (defthm monotonicity-of-list-kind-syntax-p-helper-corollary
    (implies (list-kind-syntax-p-helper term used)
             (list-kind-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-list-kind-syntax-p-helper)
             :use ((:instance monotonicity-of-list-kind-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define list-kind-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for list-kind-syntax."
    (list-kind-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :cons)
                                (prod-kind-syntax-p (cadr term)))
                       (implies (equal (car term) :nil-kind)
                                (prod-kind-syntax-p (cadr term)))))
         :name definition-of-list-kind-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-list-kind-syntax-p-helper)
                  :use ((:instance
                         definition-of-list-kind-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term)
                       (not (equal (car term) :cons)))
                  (equal (car term) :nil-kind))
         :name option-of-list-kind-syntax-p
         :hints (("Goal"
                  :in-theory (disable option-of-list-kind-syntax-p-helper)
                  :use ((:instance
                         option-of-list-kind-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term))
                  (list-kind-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (list-kind-syntax-p-helper term nil)))
         :name monotonicity-of-list-kind-syntax-p)))

  (easy-fix list-kind-syntax nil)

  ;; option-kind
  (define option-kind-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for option-kind-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>option-kind-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:some (prod-kind-syntax-p second))
            (:none (prod-kind-syntax-p second))
            (t (er hard? 'process=>option-kind-syntax-p-helper
                   "Smtlink-hint option-kind option doesn't include: ~p0.
                       They are :some, and :none.~%"
                   first)))))
      (and first-ok
           (option-kind-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (not (member-equal (car term) used))
                       (implies (equal (car term) :some)
                                (prod-kind-syntax-p (cadr term)))
                       (implies (equal (car term) :none)
                                (prod-kind-syntax-p (cadr term)))))
         :name definition-of-option-kind-syntax-p-helper
         :hints (("Goal"
                  :expand (option-kind-syntax-p-helper term used))))
     (ok (implies (and ok (consp term) (symbol-listp used)
                       (not (equal (car term) :some)))
                  (equal (car term) :none))
         :name option-of-option-kind-syntax-p-helper
         :hints (("Goal"
                  :expand (option-kind-syntax-p-helper term used)))))
    (defthm monotonicity-of-option-kind-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (option-kind-syntax-p-helper term used))
               (option-kind-syntax-p-helper term used-1))))

  (defthm monotonicity-of-option-kind-syntax-p-helper-corollary
    (implies (option-kind-syntax-p-helper term used)
             (option-kind-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-option-kind-syntax-p-helper)
             :use ((:instance monotonicity-of-option-kind-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define option-kind-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for option-kind-syntax."
    (option-kind-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :some)
                                (prod-kind-syntax-p (cadr term)))
                       (implies (equal (car term) :none)
                                (prod-kind-syntax-p (cadr term)))))
         :name definition-of-option-kind-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-option-kind-syntax-p-helper)
                  :use ((:instance
                         definition-of-option-kind-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term)
                       (not (equal (car term) :some)))
                  (equal (car term) :none))
         :name option-of-option-kind-syntax-p
         :hints (("Goal"
                  :in-theory (disable option-of-option-kind-syntax-p-helper)
                  :use ((:instance
                         option-of-option-kind-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term))
                  (option-kind-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (option-kind-syntax-p-helper term nil)))
         :name monotonicity-of-option-kind-syntax-p)))

  (easy-fix option-kind-syntax nil)

  ;; sum-kind
  (define sum-kind-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for sum-kind-syntax-p."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>sum-kind-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (cond ((equal first :kind-fn) (symbolp second))
                ((symbolp first) (prod-kind-syntax-p second))
                (t (er hard? 'process=>sum-kind-syntax-p-helper
                       "Smtlink-hint sum-kind option doesn't include: ~p0.
                       They are :kind-fn, and tags.~%"
                       first)))))
      (and first-ok
           (sum-kind-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (not (member-equal (car term) used))
                       (implies (equal (car term) :kind-fn)
                                (symbolp (cadr term)))
                       (implies (and (symbolp (car term))
                                     (not (equal (car term) :kind-fn)))
                                (prod-kind-syntax-p (cadr term)))))
         :name definition-of-sum-kind-syntax-p-helper
         :hints (("Goal"
                  :expand (sum-kind-syntax-p-helper term used))))
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (symbolp (car term)))
         :name option-of-sum-kind-syntax-p-helper
         :hints (("Goal"
                  :expand (sum-kind-syntax-p-helper term used)))))
    (defthm monotonicity-of-sum-kind-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (sum-kind-syntax-p-helper term used))
               (sum-kind-syntax-p-helper term used-1))))

  (defthm monotonicity-of-sum-kind-syntax-p-helper-corollary
    (implies (sum-kind-syntax-p-helper term used)
             (sum-kind-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-sum-kind-syntax-p-helper)
             :use ((:instance monotonicity-of-sum-kind-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define sum-kind-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for sum-kind-syntax."
    (sum-kind-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :kind-fn)
                                (symbolp (cadr term)))
                       (implies (and (symbolp (car term))
                                     (not (equal (car term) :kind-fn)))
                                (prod-kind-syntax-p (cadr term)))))
         :name definition-of-sum-kind-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-sum-kind-syntax-p-helper)
                  :use ((:instance
                         definition-of-sum-kind-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term))
                  (symbolp (car term)))
         :name option-of-sum-kind-syntax-p
         :hints (("Goal"
                  :in-theory (disable option-of-sum-kind-syntax-p-helper)
                  :use ((:instance
                         option-of-sum-kind-syntax-p-helper
                         (used nil))))))
     (ok (implies (and ok (consp term))
                  (sum-kind-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (sum-kind-syntax-p-helper term nil)))
         :name monotonicity-of-sum-kind-syntax-p)))

  (easy-fix sum-kind-syntax nil)

  ;; kind syntax
  (define kind-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for kind-syntax."
    (b* (((unless (consp term)) nil)
         ((cons kind options) term))
      (case kind
        (:abstract (abstract-kind-syntax-p options))
        (:array (array-kind-syntax-p options))
        (:prod (prod-kind-syntax-p options))
        (:sum (sum-kind-syntax-p options))
        (:list (list-kind-syntax-p options))
        (:option (option-kind-syntax-p options))
        (t (er hard? 'process=>kind-syntax-p
               "Smtlink-hint kind-syntax option doesn't include: ~p0.
                       They are :abstract, :list, :array, :prod, :option, and
                       :sum.~%" kind))))
    ///
    (more-returns
     (ok
      (implies ok
               (and (consp term)
                    (implies (equal (car term) :abstract)
                             (abstract-kind-syntax-p (cdr term)))
                    (implies (equal (car term) :array)
                             (array-kind-syntax-p (cdr term)))
                    (implies (equal (car term) :prod)
                             (prod-kind-syntax-p (cdr term)))
                    (implies (equal (car term) :sum)
                             (sum-kind-syntax-p (cdr term)))
                    (implies (equal (car term) :list)
                             (list-kind-syntax-p (cdr term)))
                    (implies (equal (car term) :option)
                             (option-kind-syntax-p (cdr term)))))
      :name definition-of-kind-syntax-p)
     (ok (implies (and ok
                       (not (equal (car term) :abstract))
                       (not (equal (car term) :array))
                       (not (equal (car term) :prod))
                       (not (equal (car term) :list))
                       (not (equal (car term) :option)))
                  (equal (car term) :sum))
         :name option-of-kind-syntax-p))
    )

  (easy-fix kind-syntax '(:abstract))
  )

(defsection type-option-syntax
  :parents (type-syntax)

  (define type-option-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper type for type-option-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>type-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:recognizer (symbolp second))
            (:fixer (symbolp second))
            (:fixer-when-recognizer-thm (symbolp second))
            (:kind (kind-syntax-p second))
            (t (er hard? 'process=>type-option-syntax-p-helper
                   "Smtlink-hint type option doesn't include: ~p0.
                       They are :recognizer, :fixer,
                       :fixer-when-recognizer-thm, and :kind.~%" first)))))
      (and first-ok
           (type-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :recognizer)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :fixer)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :fixer-when-recognizer-thm)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :kind)
                                (kind-syntax-p (cadr term)))))
         :hints (("Goal"
                  :expand (type-option-syntax-p-helper term used)))
         :name definition-of-type-option-syntax-p-helper)
     (ok (implies (and (and ok (consp term) (symbol-listp used))
                       (not (equal (car term) :recognizer))
                       (not (equal (car term) :fixer))
                       (not (equal (car term) :fixer-when-recognizer-thm)))
                  (equal (car term) :kind))
         :hints (("Goal"
                  :expand (type-option-syntax-p-helper term used)))
         :name option-of-type-option-syntax-p-helper))
    (defthm monotonicity-of-type-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (type-option-syntax-p-helper term used))
               (type-option-syntax-p-helper term used-1))))

  (defthm monotonicity-of-type-option-syntax-p-helper-corollary
    (implies (type-option-syntax-p-helper term used)
             (type-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-type-option-syntax-p-helper)
             :use ((:instance monotonicity-of-type-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define type-option-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for type-option-syntax."
    (type-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :recognizer)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :fixer)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :fixer-when-recognizer-thm)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :kind)
                                (kind-syntax-p (cadr term)))))
         :name definition-of-type-option-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :recognizer))
                       (not (equal (car term) :fixer))
                       (not (equal (car term) :fixer-when-recognizer-thm)))
                  (equal (car term) :kind))
         :name option-of-type-option-syntax-p)
     (ok (implies (and ok (consp term))
                  (type-option-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (type-option-syntax-p-helper term nil)))
         :name monotonicity-of-type-option-syntax-p)))

  (easy-fix type-option-syntax nil)
  )

(defsection type-syntax
  :parents (Smtlink-process-user-hint)

  (define type-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for type-syntax."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) t)
         ((cons tname type-options) term))
      (and (symbolp tname)
           (type-option-syntax-p type-options))))

  (easy-fix type-syntax nil)

  (deflist type-lst-syntax
    :elt-type type-syntax-p
    :pred type-lst-syntax-p
    :true-listp t)
  )

(defsection int-to-rat-syntax
  :parents (Smtlink-process-user-hint)

  (define int-to-rat-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for int-to-rat-syntax."
    (or (booleanp term)
        (symbol-listp term))
    ///
    (more-returns
     (syntax-good?
      (implies syntax-good?
               (or (booleanp term)
                   (symbol-listp term)))
      :name definition-of-int-to-rat-syntax-p)))

  (easy-fix int-to-rat-syntax nil)
  )

(defsection smtlink-hint-syntax
  :parents (Smtlink-process-user-hint)

  (define smtlink-hint-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper smtlink for smtlink-hint-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>smtlink-hint-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:functions (function-lst-syntax-p second))
            (:types (type-lst-syntax-p second))
            (:hypotheses (hypothesis-lst-syntax-p second))
            (:rm-file (booleanp second))
            (:smt-dir (stringp second))
            (:smt-fname (stringp second))
            (:int-to-rat (int-to-rat-syntax-p second))
            (:use-uninterpreted (booleanp second))
            (:under-induct (symbolp second))
            (:global-hint (symbolp second))
            (:custom-p (booleanp second))
            (:wrld-fn-len (natp second))
            (t (er hard? 'process=>smtlink-hint-syntax-p-helper
                   "Smtlink-hint option doesn't include: ~p0.
                       They are :functions, :types, :hypotheses, :rm-file,
                       :smt-dir, :smt-fname, :int-to-rat, :use-uninterpreted,
                       :under-induct, and :global-hint.~%" first)))))
      (and first-ok
           (smtlink-hint-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :functions)
                                (function-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :types)
                                (type-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :hypotheses)
                                (hypothesis-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :rm-file)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :smt-dir)
                                (stringp (cadr term)))
                       (implies (equal (car term) :smt-fname)
                                (stringp (cadr term)))
                       (implies (equal (car term) :int-to-rat)
                                (int-to-rat-syntax-p (cadr term)))
                       (implies (equal (car term) :use-uninterpreted)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :under-induct)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :global-hint)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :custom-p)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :wrld-fn-len)
                                (natp (cadr term)))))
         :hints (("Goal"
                  :expand (smtlink-hint-syntax-p-helper term used)))
         :name definition-of-smtlink-hint-syntax-p-helper)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :functions))
                       (not (equal (car term) :types))
                       (not (equal (car term) :hypotheses))
                       (not (equal (car term) :rm-file))
                       (not (equal (car term) :smt-dir))
                       (not (equal (car term) :smt-fname))
                       (not (equal (car term) :int-to-rat))
                       (not (equal (car term) :use-uninterpreted))
                       (not (equal (car term) :under-induct))
                       (not (equal (car term) :global-hint))
                       (not (equal (car term) :custom-p)))
                  (equal (car term) :wrld-fn-len))
         :hints (("Goal"
                  :expand (smtlink-hint-syntax-p-helper term used)))
         :name option-of-smtlink-hint-syntax-p-helper))
    (defthm monotonicity-of-smtlink-hint-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (smtlink-hint-syntax-p-helper term used))
               (smtlink-hint-syntax-p-helper term used-1))))

  (defthm monotonicity-of-smtlink-hint-syntax-p-helper-corollary
    (implies (smtlink-hint-syntax-p-helper term used)
             (smtlink-hint-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-smtlink-hint-syntax-p-helper)
             :use ((:instance monotonicity-of-smtlink-hint-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define smtlink-hint-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for smtlink-hint-syntax."
    (smtlink-hint-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :functions)
                                (function-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :types)
                                (type-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :hypotheses)
                                (hypothesis-lst-syntax-p (cadr term)))
                       (implies (equal (car term) :rm-file)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :smt-dir)
                                (stringp (cadr term)))
                       (implies (equal (car term) :smt-fname)
                                (stringp (cadr term)))
                       (implies (equal (car term) :int-to-rat)
                                (int-to-rat-syntax-p (cadr term)))
                       (implies (equal (car term) :use-uninterpreted)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :under-induct)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :global-hint)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :custom-p)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :wrld-fn-len)
                                (natp (cadr term)))))
         :name definition-of-smtlink-hint-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :functions))
                       (not (equal (car term) :types))
                       (not (equal (car term) :hypotheses))
                       (not (equal (car term) :rm-file))
                       (not (equal (car term) :smt-dir))
                       (not (equal (car term) :smt-fname))
                       (not (equal (car term) :int-to-rat))
                       (not (equal (car term) :use-uninterpreted))
                       (not (equal (car term) :under-induct))
                       (not (equal (car term) :global-hint))
                       (not (equal (car term) :custom-p)))
                  (equal (car term) :wrld-fn-len))
         :name option-of-smtlink-hint-syntax-p)
     (ok (implies (and ok (consp term))
                  (smtlink-hint-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (smtlink-hint-syntax-p-helper term nil)))
         :name monotonicity-of-smtlink-hint-syntax-p)))

  (easy-fix smtlink-hint-syntax nil)
  )

;; -------------------------------------------------------------------------
;; (defsection process-smtlink-hints
;;   :parents (Smtlink-process-user-hint)

(local (in-theory (disable symbol-listp
                           pseudo-term-listp
                           true-list-listp
                           pseudo-term-listp-of-symbol-listp
                           pseudo-term-listp-of-cdr-of-pseudo-termp
                           acl2::pseudo-lambdap-of-car-when-pseudo-termp
                           acl2::symbol-listp-of-cdr-when-symbol-listp
                           symbolp-of-fn-call-of-pseudo-termp
                           acl2::true-listp-of-car-when-true-list-listp
                           acl2::pseudo-term-listp-cdr)))

  (define construct-argument-list ((content argument-lst-syntax-p))
    :returns (decls decl-list-p)
    :short "Translate arguments into smtlink-hint structure."
    :measure (len content)
    :guard-hints (("Goal" :in-theory (e/d (argument-syntax-p
                                           smt-typep)
                                          ())))
    (b* ((content (argument-lst-syntax-fix content))
         ((unless (consp content)) nil)
         ((cons first rest) content)
         ((list argname type & thm-name) first)
         (new-formal (make-decl :name argname
                                :type (make-hint-pair :thm `(,type ,argname)
                                                      :name thm-name))))
      (cons new-formal (construct-argument-list rest))))

  (define construct-hypothesis ((content hypothesis-syntax-p))
    :returns (hypo hint-pair-p)
    :short "Translate one hypothesis into smtlink-hint structure."
    :guard-hints (("Goal" :in-theory (enable hypothesis-syntax-p)))
    (b* ((content (hypothesis-syntax-fix content))
         ((list thm tag hints/thm-name) content)
         (new-hypo (if (equal tag :name)
                       (make-hint-pair :thm thm :name hints/thm-name)
                     (make-hint-pair :thm thm :hints hints/thm-name))))
      new-hypo))

  (define construct-hypothesis-list ((content hypothesis-lst-syntax-p))
    :returns (hypos hint-pair-list-p)
    :short "Translate a list of hypotheses into smtlink-hint structure."
    :measure (len content)
    (b* ((content (hypothesis-lst-syntax-fix content))
         ((unless (consp content)) nil)
         ((cons first rest) content)
         (new-hypo (construct-hypothesis first)))
      (cons new-hypo (construct-hypothesis-list rest))))

  (define construct-function-option-lst ((fun-opt-lst function-option-syntax-p)
                                        (smt-func smt-function-p))
    :returns (func smt-function-p)
    :short "Add option information into func."
    :measure (len fun-opt-lst)
    :hints (("Goal" :in-theory (enable function-option-syntax-fix)))
    (b* ((fun-opt-lst (function-option-syntax-fix fun-opt-lst))
         (smt-func (smt-function-fix smt-func))
         ((unless (consp fun-opt-lst)) smt-func)
         ((list* option content rest) fun-opt-lst)
         (new-smt-func
          (case option
            (:expansion-depth (change-smt-function smt-func :expansion-depth content))
            (:formals (change-smt-function
                       smt-func
                       :formals (construct-argument-list content)))
            (:returns (change-smt-function
                       smt-func
                       :returns (construct-argument-list content)))
            (:guard (change-smt-function
                     smt-func
                     :guard (construct-hypothesis content)))
            (:more-returns (change-smt-function
                            smt-func
                            :more-returns (construct-hypothesis-list content))))))
      (construct-function-option-lst rest new-smt-func)))

  (define construct-function ((func function-syntax-p))
    :returns (new-func smt-function-p)
    :short "Function for generating func-p of a single function hint."
    :guard-hints (("Goal" :in-theory (enable function-syntax-fix function-syntax-p)))
    (b* ((func (function-syntax-fix func))
         ((cons name fun-opt-lst) func))
      (construct-function-option-lst fun-opt-lst
                                     (make-smt-function :name name))))

  (define merge-functions ((content function-lst-syntax-p)
                           (hint smtlink-hint-p))
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
         ((smtlink-hint h) hint)
         (new-func-lst (cons (construct-function first) h.functions))
         (new-hint (change-smtlink-hint h :functions new-func-lst)))
      (merge-functions rest new-hint)))

;; construct types
(define construct-type-thm-options ((content type-thm-syntax-p)
                                    (tt type-thm-p))
  :returns (new-tt type-thm-p)
  :measure (len content)
  :hints (("Goal" :in-theory (enable type-thm-syntax-fix)))
  (b* ((content (type-thm-syntax-fix content))
       (tt (type-thm-fix tt))
       ((unless (consp content)) tt)
       ((list* first second rest) content)
       (new-tt
        (case first
          (:name (change-type-thm tt :name second))
          (:hints (change-type-thm tt :hints second)))))
    (construct-type-thm-options rest new-tt)))

(define construct-type-thm ((content type-thm-syntax-p))
  :returns (new-tt type-thm-p)
  (construct-type-thm-options content (make-type-thm)))

(define construct-type-function-option-list ((content type-function-option-syntax-p)
                                             (tf type-function-p))
  :returns (new-tf type-function-p)
  :measure (len content)
  :hints (("Goal" :in-theory (enable type-function-option-syntax-fix)))
  (b* ((content (type-function-option-syntax-fix content))
       (tf (type-function-fix tf))
       ((unless (consp content)) tf)
       ((list* first second rest) content)
       (new-tf
        (case first
          (:return-type (change-type-function tf :return-type second))
          (:type-thm
           (change-type-function tf
                                 :type-of-function-thm
                                 (construct-type-thm second)))
          (:destructor-thm
           (change-type-function tf
                                 :destructor-of-constructor-thm
                                 (construct-type-thm second))))))
    (construct-type-function-option-list rest new-tf)))

(define construct-type-function ((content type-function-syntax-p)
                                 (acc symbol-listp))
  :returns (mv (new-tf type-function-p)
               (new-acc symbol-listp
                        :hints (("Goal"
                                 :in-theory (enable type-function-syntax-fix
                                                    type-function-syntax-p)))))
  :guard-hints (("Goal"
                 :in-theory (enable type-function-syntax-p)))
  (b* ((content (type-function-syntax-fix content))
       (acc (symbol-list-fix acc))
       ((cons name options) content)
       ((if (member-equal name acc))
        (mv (make-type-function)
            (er hard? 'process=>construct-type-function
                "Redefinition of function ~p0" name))))
    (mv (construct-type-function-option-list
         options
         (make-type-function :name name))
        (cons name acc))))

(define construct-type-function-list ((content type-function-list-syntax-p)
                                      (acc symbol-listp))
  :returns (mv (new-lst type-function-list-p)
               (new-acc symbol-listp))
  :measure (len content)
  :guard-hints (("Goal"
                 :in-theory (enable type-function-syntax-p)))
  (b* ((content (type-function-list-syntax-fix content))
       (acc (symbol-list-fix acc))
       ((unless (consp content)) (mv nil acc))
       ((cons first rest) content)
       ((mv first-fn new-acc)
        (construct-type-function first acc))
       ((mv rest-fn fin-acc)
        (construct-type-function-list rest new-acc)))
    (mv (cons first-fn rest-fn)
        fin-acc)))

  (define construct-array-kind ((content array-kind-syntax-p)
                                (smt-type-array smt-type-p))
    :returns (new-array smt-type-p)
    :guard (equal (smt-type-kind smt-type-array) :array)
    :irrelevant-formals-ok t
    :ignore-ok t
    (smt-type-fix smt-type-array))

  (define construct-prod-kind ((content prod-kind-syntax-p)
                               (prod prod-p)
                               (acc symbol-listp))
    :returns (mv (new-prod prod-p)
                 (new-acc symbol-listp))
    :measure (len content)
    :hints (("Goal"
             :in-theory (enable prod-kind-syntax-fix)))
    (b* ((content (prod-kind-syntax-fix content))
         (acc (symbol-list-fix acc))
         (prod (prod-fix prod))
         ((unless (consp content)) (mv prod acc))
         ((list* first second rest) content)
         ((mv new-prod new-acc)
          (case first
            (:constructor
             (b* (((mv constructor-fn new-acc)
                   (construct-type-function second acc)))
               (mv (change-prod prod :constructor constructor-fn)
                   new-acc)))
            (:destructors
             (b* (((mv destructor-fns new-acc)
                   (construct-type-function-list second acc)))
               (mv (change-prod prod :destructors destructor-fns)
                   new-acc)))
            (t (mv prod acc)))))
      (construct-prod-kind rest new-prod new-acc)))

;; difference prods can have the functions of the same name!!!
  (define construct-sum-kind ((content sum-kind-syntax-p)
                              (smt-type-sum smt-type-p)
                              (acc symbol-listp))
    :returns (mv (new-sum smt-type-p)
                 (new-acc symbol-listp))
    :guard (equal (smt-type-kind smt-type-sum) :sum)
    :measure (len content)
    :hints (("Goal"
             :in-theory (enable sum-kind-syntax-fix)))
    (b* ((content (sum-kind-syntax-fix content))
         (acc (symbol-list-fix acc))
         (smt-type-sum (smt-type-fix smt-type-sum))
         ((unless (consp content)) (mv smt-type-sum acc))
         ((list* first second rest) content)
         ((if (member-equal first acc))
          (prog2$ (er hard? 'process=>construct-sum-kind
                      "Redefining kind ~q0" first)
                  (mv (make-smt-type-abstract) nil)))
         ((smt-type-sum s) smt-type-sum)
         ((mv new-type new-acc)
          (case first
            (:kind-fn (mv (change-smt-type-sum s :kind-fn second)
                          acc))
            (t
             (b* (((mv new-prod &)
                   (construct-prod-kind second (make-prod :kind first) nil)))
               (mv (change-smt-type-sum s :prods (cons new-prod s.prods))
                   (cons first acc)))))))
      (construct-sum-kind rest new-type new-acc))
    )

(define construct-list-kind ((content list-kind-syntax-p)
                             (smt-type-list smt-type-p))
  :returns (new-list smt-type-p)
  :guard (equal (smt-type-kind smt-type-list) :sum)
  :measure (len content)
  :hints (("Goal" :in-theory (enable list-kind-syntax-fix)))
  (b* ((content (list-kind-syntax-fix content))
       (smt-type-list (smt-type-fix smt-type-list))
       ((unless (consp content)) smt-type-list)
       ((list* first second rest) content)
       ((smt-type-sum s) smt-type-list)
       (new-type
        (case first
          (:cons (b* (((mv new-prod &)
                       (construct-prod-kind second (make-prod :kind first) nil)))
                   (change-smt-type-sum s :prods (cons new-prod s.prods))))
          (:nil-kind (b* (((mv new-prod &)
                           (construct-prod-kind second (make-prod :kind first) nil)))
                       (change-smt-type-sum s :prods (cons new-prod s.prods)))))))
    (construct-list-kind rest new-type))
  )

(define construct-option-kind ((content option-kind-syntax-p)
                               (smt-type-option smt-type-p))
  :returns (new-option smt-type-p)
  :guard (equal (smt-type-kind smt-type-option) :sum)
  :measure (len content)
  :hints (("Goal" :in-theory (enable option-kind-syntax-fix)))
  (b* ((content (option-kind-syntax-fix content))
       (smt-type-option (smt-type-fix smt-type-option))
       ((unless (consp content)) smt-type-option)
       ((list* first second rest) content)
       ((smt-type-sum s) smt-type-option)
       (new-type
        (case first
          (:some (b* (((mv new-prod &)
                       (construct-prod-kind second (make-prod :kind first) nil)))
                   (change-smt-type-sum s :prods (cons new-prod s.prods))))
          (:none (b* (((mv new-prod &)
                       (construct-prod-kind second (make-prod :kind first) nil)))
                   (change-smt-type-sum s :prods (cons new-prod s.prods)))))))
    (construct-option-kind rest new-type)))

  (define construct-kind ((content kind-syntax-p))
    :returns (new-kind smt-type-p)
    (b* ((content (kind-syntax-fix content))
         ((cons kind options) content))
      (case kind
       (:abstract (make-smt-type-abstract))
       (:array
        (construct-array-kind options (make-smt-type-array)))
       (:prod
        (b* (((mv new-prod &)
              (construct-prod-kind options (make-prod) nil)))
          (make-smt-type-sum :kind-fn nil
                             :prods (list new-prod))))
       (:sum
        (b* (((mv new-type &)
              (construct-sum-kind options (make-smt-type-sum) nil)))
          new-type))
       (:list
        (construct-list-kind options (make-smt-type-sum)))
       (:option
        (construct-option-kind options (make-smt-type-sum))))))

  (define construct-type-option-lst ((type-opt-lst type-option-syntax-p)
                                     (smt-type smt-fixtype-p))
    :returns (new-type smt-fixtype-p)
    :short "Add option information into smt-type."
    :measure (len type-opt-lst)
    :hints (("Goal" :in-theory (enable type-option-syntax-fix)))
    (b* ((type-opt-lst (type-option-syntax-fix type-opt-lst))
         (smt-type (smt-fixtype-fix smt-type))
         ((unless (and (consp type-opt-lst) (consp (cdr type-opt-lst)))) smt-type)
         ((list* option content rest) type-opt-lst)
         (new-smt-type
          (case option
            (:recognizer (change-smt-fixtype smt-type :recognizer content))
            (:fixer (change-smt-fixtype smt-type :fixer content))
            (:fixer-when-recognizer-thm
             (change-smt-fixtype
              smt-type :fixer-when-recognizer-thm
              (make-type-thm :name content)))
            (:kind (change-smt-fixtype
                    smt-type
                    :kind (construct-kind content))))))
      (construct-type-option-lst rest new-smt-type)))

  (define construct-type ((type type-syntax-p))
    :returns (new-type smt-fixtype-p)
    :guard-hints (("Goal"
                   :in-theory (enable type-syntax-p)))
    (b* ((type (type-syntax-fix type))
         ((cons name type-opt-lst) type))
      (construct-type-option-lst type-opt-lst
                                (make-smt-fixtype :name name))))

  (define merge-types ((content type-lst-syntax-p)
                       (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :measure (len content)
    :short "Merging type hints into smt-hint."
    (b* ((hint (smtlink-hint-fix hint))
         (content (type-lst-syntax-fix content))
         ((unless (consp content)) hint)
         ((cons first rest) content)
         ((smtlink-hint h) hint)
         (new-type-lst (cons (construct-type first) h.types))
         (new-hint (change-smtlink-hint h :types new-type-lst)))
      (merge-types rest new-hint)))

  (define merge-hypotheses ((content hypothesis-lst-syntax-p)
                            (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Merging type hints into smt-hint."
    :measure (len content)
    (b* ((content (hypothesis-lst-syntax-fix content))
         (hint (smtlink-hint-fix hint))
         ((smtlink-hint h) hint)
         ((unless (consp content)) h)
         ((cons first rest) content)
         (new-hypo (construct-hypothesis first))
         (new-hypo-lst (cons new-hypo h.hypotheses))
         (new-hint (change-smtlink-hint h :hypotheses new-hypo-lst)))
      (merge-hypotheses rest new-hint)))

  (define set-rm-file ((content booleanp)
                       (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :rm-file"
    (b* ((hint (smtlink-hint-fix hint))
         ((smtlink-hint h) hint)
         (new-cnf (change-smt-config h.configurations :rm-file content))
         (new-hint (change-smtlink-hint hint :configurations new-cnf)))
      new-hint))

  (define set-smt-dir ((content stringp)
                       (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :smt-dir"
    (b* ((hint (smtlink-hint-fix hint))
         ((smtlink-hint h) hint)
         (new-cnf (change-smt-config h.configurations :smt-dir content))
         (new-hint (change-smtlink-hint hint :configurations new-cnf)))
      new-hint))

  (define set-fname ((content stringp) (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :smt-fname."
    (b* ((hint (smtlink-hint-fix hint))
         ((smtlink-hint h) hint)
         (new-cnf (change-smt-config h.configurations :smt-fname content))
         (new-hint (change-smtlink-hint hint :configurations new-cnf)))
      new-hint))

  (define set-int-to-rat ((content int-to-rat-syntax-p)
                          (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :int-to-rat based on user hint."
    :guard-hints (("Goal"
                   :in-theory (disable definition-of-int-to-rat-syntax-p)
                   :use ((:instance definition-of-int-to-rat-syntax-p
                                    (term content)))))
    (b* ((hint (smtlink-hint-fix hint))
         (content (int-to-rat-syntax-fix content))
         (new-int-to-rat
          (if (booleanp content)
              (make-int-to-rat-switch :okp content)
            (make-int-to-rat-symbol-list :lst content)))
         (new-hint (change-smtlink-hint hint :int-to-rat new-int-to-rat)))
      new-hint))

  (define set-smt-cnf ((content booleanp)
                       (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :smt-cnf"
    (b* ((hint (smtlink-hint-fix hint))
         (smt-cnf (if content (custom-smt-cnf) (default-smt-cnf)))
         ((smtlink-hint h) hint)
         (new-cnf (change-smt-config h.configurations :smt-cnf smt-cnf))
         (new-hint (change-smtlink-hint hint :configurations new-cnf)))
      new-hint))

  (define set-use-uninterpreted ((content booleanp)
                                 (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :use-uninterpreted"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :use-uninterpreted content)))
      new-hint))

  (define set-under-induct ((content symbolp)
                            (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :under-induct"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :under-induct content)))
      new-hint))

  (define set-global-hint ((content symbolp)
                           (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :short "Set :global-hint"
    (b* ((hint (smtlink-hint-fix hint))
         (new-hint (change-smtlink-hint hint :global-hint content)))
      new-hint))

(define set-wrld-len ((content natp)
                      (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Set :global-hint"
  (b* ((hint (smtlink-hint-fix hint))
       (new-hint (change-smtlink-hint hint :wrld-fn-len content)))
    new-hint))

  (define combine-hints ((user-hint smtlink-hint-syntax-p)
                         (hint smtlink-hint-p))
    :returns (combined-hint smtlink-hint-p)
    :hints (("Goal" :in-theory (enable smtlink-hint-syntax-fix)))
    :measure (len user-hint)
    :short "Combining user-hints into smt-hint."
    (b* ((hint (smtlink-hint-fix hint))
         (user-hint (smtlink-hint-syntax-fix user-hint))
         ((unless (consp user-hint)) hint)
         ((list* option second rest) user-hint)
         (new-hint (case option
                     (:functions (merge-functions second hint))
                     (:types (merge-types second hint))
                     (:hypotheses (merge-hypotheses second hint))
                     (:rm-file (set-rm-file second hint))
                     (:smt-dir (set-smt-dir second hint))
                     (:smt-fname (set-fname second hint))
                     (:int-to-rat (set-int-to-rat second hint))
                     (:use-uninterpreted (set-use-uninterpreted second hint))
                     (:under-induct (set-under-induct second hint))
                     (:global-hint (set-global-hint second hint))
                     (:custom-p (set-smt-cnf second hint))
                     (:wrld-fn-len (set-wrld-len second hint)))))
      (combine-hints rest new-hint)))

(define find-global-hint-helper ((user-hint smtlink-hint-syntax-p))
  :returns (name symbolp)
  :hints (("Goal" :in-theory (enable smtlink-hint-syntax-fix)))
  :measure (len user-hint)
  (b* ((user-hint (smtlink-hint-syntax-fix user-hint))
       ((unless (consp user-hint)) nil)
       ((list* option second rest) user-hint))
    (case option
      (:global-hint second)
      (t (find-global-hint-helper rest)))))

(define find-hint ((name symbolp) state)
  :returns (hint smtlink-hint-p)
  (b* ((smt-hint-tb (get-smt-hint-table (w state)))
       ((unless (smtlink-hint-alist-p smt-hint-tb))
        (prog2$ (er hard? 'Smtlink=>find-hint "Wrong type of hint:~q0"
                    smt-hint-tb)
                (make-smtlink-hint)))
       (the-hint-cons (assoc-equal name smt-hint-tb))
       ((unless (consp the-hint-cons))
        (prog2$ (cw "Using (make-smtlink-hint) because we failed to find the
  smtlink-hint ~p0 from state table ~p1~%" name smt-hint-tb)
                (make-smtlink-hint))))
    (cdr the-hint-cons)))

(define find-global-hint ((user-hint smtlink-hint-syntax-p)
                          state)
    :returns (name smtlink-hint-p)
    (b* ((user-hint (smtlink-hint-syntax-fix user-hint))
         (the-hint (find-global-hint-helper user-hint))
         ((if (null the-hint))
          (prog2$ (cw "Using :default smtlink-hint from state table ~p0~%"
                      'smt-hint-table)
                  (find-hint :default state))))
      (prog2$ (cw "Using ~p0 smtlink-hint as requested by the user.~%"
                  the-hint)
              (find-hint the-hint state))))

  (define process-hint ((cl pseudo-term-listp) (user-hint t) state)
    :returns (subgoal-lst pseudo-term-list-listp)
    :guard-debug t
    (b* ((cl (pseudo-term-list-fix cl))
         ((unless (smtlink-hint-syntax-p user-hint))
          (prog2$ (cw "User provided Smtlink hint can't be applied because of ~
    syntax error in the hints: ~q0Therefore proceed without Smtlink...~%" user-hint)
                  (list cl)))
         ;; Need to find global-hint first so that we know which hint to
         ;; combine onto.
         (the-hint (find-global-hint user-hint state))
         ((unless (smtlink-hint-p the-hint))
          (prog2$ (cw "The hint ~p0 from state is not smtlink-hint-p:
    ~p1~%Therefore proceed without Smtlink...~%" the-hint user-hint)
                  (list cl)))
         (combined-hint-w/o-info (combine-hints user-hint the-hint))
         (combined-hint (add-fixtype-info combined-hint-w/o-info))
         ;; (- (cw "combined-hint: ~q0" combined-hint))
         (next-cp (cdr (assoc-equal 'process-hint *SMT-architecture*)))
         ((if (null next-cp)) (list cl))
         (cp-hint `(:clause-processor (,next-cp clause ',combined-hint)))
         (subgoal-lst (cons `(hint-please ',cp-hint) cl)))
      (list subgoal-lst)))

  (define process-hint-cp ((cl pseudo-term-listp)
                           (hints t)
                           state)
    (b* ((expanded-clause (process-hint cl hints state)))
      (value expanded-clause)))
;;  )

;; ------------------------------------------------------------------------
;;     Run translate-cmp on terms to generate translated terms
(defsection translate-cmp-smtlink
  :parents (Smtlink-process-user-hint)

  (define wrld-fn-len ((cl t) (state))
    :mode :program
    (b* ((world (w state)))
      (+ (acl2-count cl)
         (len (remove-duplicates-eq
               (strip-cadrs (universal-theory :here)))))))

  (define trans-hypothesis ((val t) (state))
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

  (define trans-hypothesis-list ((val t) (state))
    :mode :program
    (b* (((unless (true-listp val)) val)
         ((unless (consp val)) val)
         ((cons first rest) val)
         (new-first (trans-hypothesis first state)))
      (cons new-first (trans-hypothesis-list rest state))))

  (define trans-argument ((val t))
    :mode :program
    (b* (((unless (and (true-listp val)
                       (car val) (cadr val)))
          val)
         ((list* name type rest) val))
      `(,name ,type ,@rest)))

  (define trans-argument-list ((val t) (state))
    :mode :program
    (b* (((unless (true-listp val)) val)
         ((unless (consp val)) val)
         ((cons first rest) val)
         (new-first (trans-argument first)))
      (cons new-first (trans-argument-list rest state))))

  (define trans-func-option ((opt t) (val t) (state))
    :mode :program
    (cond ((equal opt ':formals) (trans-argument-list val state))
          ((equal opt ':returns) (trans-argument-list val state))
          ((equal opt ':guard) (trans-hypothesis val state))
          ((equal opt ':more-returns) (trans-hypothesis-list val state))
          (t val)))

  (define trans-function ((val t) (state))
    :mode :program
    (b* (((unless (and (true-listp val) (consp val)))
          val)
         ((list* first second rest) val)
         (new-second (trans-func-option first second state))
         (new-functions `(,first ,new-second ,@(trans-function rest state))))
      new-functions))

  (define trans-functions ((val t) (state))
    :mode :program
    (b* (((unless (true-listp val)) val)
         ((unless (consp val)) val)
         ((cons first rest) val)
         ((cons fname options) first)
         (new-first `(,fname ,@(trans-function options state))))
      (cons new-first (trans-functions rest state))))

  (define trans-kind-option ((opt t) (val t) (state))
    :mode :program
    (cond ((equal opt ':theorems) (trans-hypothesis-list val state))
          (t val)))

  (define trans-type-kind ((val t) (state))
    :mode :program
    (b* (((unless (and (true-listp val) (consp val)))
          val)
         ((list* first second rest) val)
         (new-second (trans-kind-option first second state))
         (new-kinds `(,first ,new-second ,@(trans-type-kind rest state))))
      new-kinds))

  (define trans-type-option ((opt t) (val t) (state))
    :mode :program
    (cond ((equal opt ':type) (trans-type-kind val state))
          (t val)))

  (define trans-type ((val t) state)
    :mode :program
    (b* (((unless (and (true-listp val) (consp val)))
          val)
         ((list* first second rest) val)
         (new-second (trans-type-option first second state))
         (new-types `(,first ,new-second ,@(trans-type rest state))))
      new-types))

  (define trans-types ((val t) (state))
    :mode :program
    (b* (((unless (true-listp val)) val)
         ((unless (consp val)) val)
         ((cons first rest) val)
         ((cons typename options) first)
         (new-first `(,typename ,@(trans-type options state))))
      (cons new-first (trans-types rest state))))

  (define trans-hint-option ((opt t) (val t) (state))
    :mode :program
    (cond ((equal opt ':functions) (trans-functions val state))
          ((equal opt ':types) (trans-types val state))
          ((equal opt ':hypotheses) (trans-hypothesis-list val state))
          ((equal opt ':wrld-fn-len)
           (er hard?
               'Smtlink-process-user-hint->trans-hint-option
               "User trying to access internal parameter ~
                wrld-fn-len!"))
          (t val)))

  (define trans-hint ((cl t) (hint t) (state))
    :mode :program
    (b* (((unless (true-listp hint)) hint)
         (wrld-len (wrld-fn-len cl state))
         ((if (atom hint)) `(:wrld-fn-len ,wrld-len))
         ((unless (cdr hint)) hint)
         ((list* first second rest) hint)
         (new-second (trans-hint-option first second state))
         (new-hint `(,first ,new-second ,@(trans-hint cl rest state))))
      new-hint))
  )

;; ------------------------------------------------------------
;;         Prove correctness of clause processor
;;

;; -----------------------------------------------------------------
;;       Define evaluators
(defsection process-hint-clause-processor
  :parents (Smtlink-process-user-hint)

  (encapsulate ()
    (local (in-theory (enable process-hint-cp process-hint)))

    (defthm correctness-of-process-hint
      (implies (and (pseudo-term-listp cl)
                    (alistp b)
                    (ev-smtcp
                     (conjoin-clauses
                      (acl2::clauses-result
                       (process-hint-cp cl hint state)))
                     b))
               (ev-smtcp (disjoin cl) b))
      :rule-classes :clause-processor))
  ;; Smtlink is a macro that generates a clause processor hint. This clause
  ;;   processor hint generates a clause, with which a new smt-hint is attached.
  ;;   This new smt-hint combines user given hints with hints from the state.
  ;; A computed hint will be waiting to take the clause and hint for clause
  ;;   expansion and transformation.
  (defmacro smtlink (clause hint)
    `(process-hint-cp ,clause (trans-hint ,clause ',hint state) state))

  (defmacro smtlink-custom (clause hint)
    `(process-hint-cp ,clause
                      (trans-hint ,clause ',(append hint '(:custom-p t)) state)
                      state))

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
                              `(:clause-processor
                                (smtlink-custom clause ,acl2::val))
                              acl2::keyword-alist))))
  )

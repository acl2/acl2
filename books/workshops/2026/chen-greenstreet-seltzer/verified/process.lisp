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
(include-book "unique-sumtype-functions")

;; (defsection Smtlink-process-user-hint
;;   :parents (verified)
;;   :short "Functionalities for processing user hints given to Smtlink. User
;;   hints will be merged with (smt-hint)."

;; --------------------------------------------------------

(local (in-theory (disable pseudo-termp pseudo-term-listp)))

(defsection hypothesis-list-syntax
  :parents (Smtlink-process-user-hint)

  (define subst-syntax-p ((subst t))
    :returns (syntax-good? booleanp)
    (b* (((unless (consp subst)) (null subst))
         ((cons subst-hd subst-tl) subst)
         (res-hd
          (case-match subst-hd
            ((var term) (and (symbolp var) (pseudo-termp term)))
            (& nil))))
      (and res-hd (subst-syntax-p subst-tl))))

  (easy-fix subst-syntax 'nil)

  (define hypothesis-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for hypothesis-syntax."
    (or (and (consp term)
             (consp (cdr term))
             (null (cddr term))
             (equal (car term) :instance)
             (symbolp (cadr term)))
        (and (consp term)
             (consp (cdr term))
             (consp (cddr term))
             (null (cdddr term))
             (equal (car term) :instance)
             (symbolp (cadr term))
             (subst-syntax-p (caddr term)))))

  (easy-fix hypothesis-syntax '(:instance nil))

  (deflist hypothesis-list-syntax
    :pred hypothesis-list-syntax-p
    :elt-type hypothesis-syntax-p
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

(defsection thm-spec-option-syntax
  :parents (thm-spec-syntax)

  (define thm-spec-option-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for thm-spec-option-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>thm-spec-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:thm (symbolp second))
            (:formals (symbol-listp second))
            (:hypotheses (pseudo-termp second))
            (:lhs (pseudo-termp second))
            (:rhs (pseudo-termp second))
            (:judgements (pseudo-term-listp second))
            (:hints (true-listp second))
            (t (er hard? 'process=>thm-spec-option-syntax-p-helper
                   "Smtlink-hint thm-spec hint option doesn't include: ~p0. ~
                       They are :thm, :formals, :hypotheses, :lhs, :rhs, ~
                       :judgements, and :hints~%" first)))))
      (and first-ok
           (thm-spec-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and (symbol-listp used) ok (consp term))
                  (and (not (member-equal (car term) used))
                       (consp (cdr term))
                       (implies (equal (car term) :thm)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :formals)
                                (symbol-listp (cadr term)))
                       (implies (equal (car term) :hypotheses)
                                (pseudo-termp (cadr term)))
                       (implies (equal (car term) :lhs)
                                (pseudo-termp (cadr term)))
                       (implies (equal (car term) :rhs)
                                (pseudo-termp (cadr term)))
                       (implies (equal (car term) :judgements)
                                (pseudo-term-listp (cadr term)))
                       (implies (equal (car term) :hints)
                                (true-listp (cadr term)))))
         :name definition-of-thm-spec-option-syntax-p-helper
         :hints (("Goal"
                  :in-theory (disable consp-of-pseudo-lambdap))))
     (ok (implies (and (symbol-listp used) ok (consp term)
                       (not (equal (car term) :thm))
                       (not (equal (car term) :formals))
                       (not (equal (car term) :hypotheses))
                       (not (equal (car term) :lhs))
                       (not (equal (car term) :rhs))
                       (not (equal (car term) :judgements)))
                  (equal (car term) :hints))
         :name option-of-thm-spec-option-syntax-p-helper
         :hints (("Goal"
                  :in-theory (disable consp-of-pseudo-lambdap)))))
    (defthm monotonicity-of-thm-spec-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (thm-spec-option-syntax-p-helper term used))
               (thm-spec-option-syntax-p-helper term used-1))))

  (defthm monotonicity-of-thm-spec-option-syntax-p-helper-corollary
    (implies (thm-spec-option-syntax-p-helper term used)
             (thm-spec-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-thm-spec-option-syntax-p-helper)
             :use ((:instance monotonicity-of-thm-spec-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define thm-spec-option-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for thm-spec-option-syntax."
    (thm-spec-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :thm)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :formals)
                                (symbol-listp (cadr term)))
                       (implies (equal (car term) :hypotheses)
                                (pseudo-termp (cadr term)))
                       (implies (equal (car term) :lhs)
                                (pseudo-termp (cadr term)))
                       (implies (equal (car term) :rhs)
                                (pseudo-termp (cadr term)))
                       (implies (equal (car term) :judgements)
                                (pseudo-term-listp (cadr term)))
                       (implies (equal (car term) :hints)
                                (true-listp (cadr term)))))
         :name definition-of-thm-spec-option-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-thm-spec-option-syntax-p-helper)
                  :use ((:instance definition-of-thm-spec-option-syntax-p-helper
                                   (used nil))))))
     (ok (implies (and ok (consp term)
                       (not (equal (car term) :thm))
                       (not (equal (car term) :formals))
                       (not (equal (car term) :hypotheses))
                       (not (equal (car term) :lhs))
                       (not (equal (car term) :rhs))
                       (not (equal (car term) :judgements)))
                  (equal (car term) :hints))
         :name option-of-thm-spec-option-syntax-p
         :hints (("Goal"
                  :in-theory (disable option-of-thm-spec-option-syntax-p-helper)
                  :use ((:instance option-of-thm-spec-option-syntax-p-helper
                                   (used nil))))))
     (ok (implies (and ok (consp term))
                  (thm-spec-option-syntax-p (cddr term)))
         :hints (("Goal" :expand (thm-spec-option-syntax-p-helper term nil)))
         :name monotonicity-of-thm-spec-option-syntax-p)))

  (easy-fix thm-spec-option-syntax nil)
  )

(defsection thm-spec-syntax
  :parents (Smtlink-process-user-hint)

  (define thm-spec-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for thm-spec-syntax."
    (thm-spec-option-syntax-p term))

  (easy-fix thm-spec-syntax nil)

  (deflist thm-spec-list-syntax
    :elt-type thm-spec-syntax-p
    :pred thm-spec-list-syntax-p
    :true-listp t)
  )

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
            (:fn-to-const (booleanp second))
            (:translation (stringp second))
            (:kind (symbolp second))
            (:return (thm-spec-list-syntax-p second))
            (:return-type (symbolp second))
            (:uninterpreted-hints (true-listp second))
            (:depth (natp second))
            (t (er hard? 'process=>function-option-syntax-p-helper
                   "Smtlink-hint function hint option doesn't include: ~p0. ~
                       They are :fn-to-const, :translation, ~
                       :kind, :return, :return-type, :uninterpreted-hints, ~
                       and :depth.~%" first)))))
      (and first-ok
           (function-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and (symbol-listp used) ok (consp term))
                  (and (not (member-equal (car term) used))
                       (consp (cdr term))
                       (implies (equal (car term) :fn-to-const)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :translation)
                                (stringp (cadr term)))
                       (implies (equal (car term) :kind)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :return)
                                (thm-spec-list-syntax-p (cadr term)))
                       (implies (equal (car term) :return-type)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :uninterpreted-hints)
                                (true-listp (cadr term)))
                       (implies (equal (car term) :depth)
                                (natp (cadr term)))))
         :name definition-of-function-option-syntax-p-helper)
     (ok (implies (and (symbol-listp used) ok (consp term))
                  (or (equal (car term) :fn-to-const)
                      (equal (car term) :translation)
                      (equal (car term) :kind)
                      (equal (car term) :return)
                      (equal (car term) :return-type)
                      (equal (car term) :uninterpreted-hints)
                      (equal (car term) :depth)))
         :name option-of-function-option-syntax-p-helper))
    (defthm monotonicity-of-function-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (function-option-syntax-p-helper term used))
               (function-option-syntax-p-helper term used-1))))

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
    :short "Recognizer for function-option-syntax."
    (function-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :fn-to-const)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :translation)
                                (stringp (cadr term)))
                       (implies (equal (car term) :kind)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :return)
                                (thm-spec-list-syntax-p (cadr term)))
                       (implies (equal (car term) :return-type)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :uninterpreted-hints)
                                (true-listp (cadr term)))
                       (implies (equal (car term) :depth)
                                (natp (cadr term)))))
         :name definition-of-function-option-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-function-option-syntax-p-helper)
                  :use ((:instance definition-of-function-option-syntax-p-helper
                                   (used nil))))))
     (ok (implies (and ok (consp term)
                       (not (equal (car term) :fn-to-const))
                       (not (equal (car term) :translation))
                       (not (equal (car term) :kind))
                       (not (equal (car term) :return))
                       (not (equal (car term) :return-type))
                       (not (equal (car term) :uninterpreted-hints)))
                  (equal (car term) :depth))
         :name option-of-function-option-syntax-p
         :hints (("Goal"
                  :in-theory (disable option-of-function-option-syntax-p-helper)
                  :use ((:instance option-of-function-option-syntax-p-helper
                                   (used nil))))))
     (ok (implies (and ok (consp term))
                  (function-option-syntax-p (cddr term)))
         :hints (("Goal" :expand (function-option-syntax-p-helper term nil)))
         :name monotonicity-of-function-option-syntax-p)))

  (easy-fix function-option-syntax nil)
  )

(defsection function-syntax
  :parents (Smtlink-process-user-hint)

  (define function-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for function-syntax."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) nil)
         ((cons fname function-options) term))
      (and (symbolp fname)
           (function-option-syntax-p function-options))))

  (easy-fix function-syntax '(not))

  (deflist function-list-syntax
    :elt-type function-syntax-p
    :pred function-list-syntax-p
    :true-listp t)

  (defoption maybe-function-syntax function-syntax-p)
  )

(defsection sub/supertype-option-syntax
  :parents (Smtlink-process-user-hint)

  (define sub/supertype-option-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>sub/supertype-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:thm (thm-spec-syntax-p second))
            (t (er hard? 'process=>sub/supertype-option-syntax-p-helper
                   "Smtlink-hint sub/supertype options doesn't include: ~p0.
                       It is :thm.~%" first)))))
      (and first-ok
           (sub/supertype-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :thm)
                                (thm-spec-syntax-p (cadr term)))))
         :hints (("Goal"
                  :expand (sub/supertype-option-syntax-p-helper term used)))
         :name definition-of-sub/supertype-option-syntax-p-helper)
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (equal (car term) :thm))
         :hints (("Goal"
                  :expand (sub/supertype-option-syntax-p-helper term used)))
         :name option-of-sub/supertype-option-syntax-p-helper))
    (defthm monotonicity-of-sub/supertype-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (sub/supertype-option-syntax-p-helper term used))
               (sub/supertype-option-syntax-p-helper term used-1))))

  (defthm monotonicity-of-sub/supertype-option-syntax-p-helper-corollary
    (implies (sub/supertype-option-syntax-p-helper term used)
             (sub/supertype-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-sub/supertype-option-syntax-p-helper)
             :use ((:instance monotonicity-of-sub/supertype-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define sub/supertype-option-syntax-p ((term t))
    :returns (ok booleanp)
    (sub/supertype-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :thm)
                                (thm-spec-syntax-p (cadr term)))))
         :name definition-of-sub/supertype-option-syntax-p)
     (ok (implies (and (and ok (consp term)))
                  (equal (car term) :thm))
         :name option-of-sub/supertype-option-syntax-p)
     (ok (implies (and ok (consp term))
                  (sub/supertype-option-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (sub/supertype-option-syntax-p-helper term nil)))
         :name monotonicity-of-sub/supertype-option-syntax-p)))

  (easy-fix sub/supertype-option-syntax nil)
  )

(defsection sub/supertype-syntax
  :parents (Smtlink-process-user-hint)

  (define sub/supertype-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) t)
         ((cons tname type-options) term))
      (and (symbolp tname)
           (sub/supertype-option-syntax-p type-options))))

  (easy-fix sub/supertype-syntax nil)

  (deflist sub/supertype-list-syntax
    :elt-type sub/supertype-syntax-p
    :pred sub/supertype-list-syntax-p
    :true-listp t)
  )

(defsection type-sum-syntax
  :parents (Smtlink-process-user-hint)

  (define type-sum-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>type-sum-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:tag (symbolp second))
            (:constructor (function-syntax-p second))
            (:destructors (function-list-syntax-p second))
            (t (er hard? 'process=>type-sum-syntax-p-helper
                   "Smtlink-hint type-sum options doesn't include: ~p0.
                       They are :tag, :constructor, and :destructors.~%"
                   first)))))
      (and first-ok
           (type-sum-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :tag)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :constructor)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :destructors)
                                (function-list-syntax-p (cadr term)))))
         :hints (("Goal"
                  :expand (type-sum-syntax-p-helper term used)))
         :name definition-of-type-sum-syntax-p-helper)
     (ok (implies (and (and ok (consp term) (symbol-listp used))
                       (not (equal (car term) :tag))
                       (not (equal (car term) :constructor)))
                  (equal (car term) :destructors))
         :hints (("Goal"
                  :expand (type-sum-syntax-p-helper term used)))
         :name option-of-type-sum-syntax-p-helper))
    (defthm monotonicity-of-type-sum-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (type-sum-syntax-p-helper term used))
               (type-sum-syntax-p-helper term used-1))))

  (defthm monotonicity-of-type-sum-syntax-p-helper-corollary
    (implies (type-sum-syntax-p-helper term used)
             (type-sum-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-type-sum-syntax-p-helper)
             :use ((:instance monotonicity-of-type-sum-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define type-sum-syntax-p ((term t))
    :returns (ok booleanp)
    (type-sum-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :tag)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :constructor)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :destructors)
                                (function-list-syntax-p (cadr term)))))
         :name definition-of-type-sum-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :tag))
                       (not (equal (car term) :constructor)))
                  (equal (car term) :destructors))
         :name option-of-type-sum-syntax-p)
     (ok (implies (and ok (consp term))
                  (type-sum-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (type-sum-syntax-p-helper term nil)))
         :name monotonicity-of-type-sum-syntax-p)))

  (easy-fix type-sum-syntax nil)

  (deflist type-sum-list-syntax
    :elt-type type-sum-syntax-p
    :true-listp t)
  )

(defsection property-hints-syntax
  :parents (datatype-syntax)

  (define property-hints-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for property-hints."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) nil)
         ((cons name hints) term))
      (and (symbolp name)
           (true-listp hints))))

  (easy-fix property-hints-syntax '(nil :hints nil))

  (deflist property-hints-list-syntax
    :elt-type property-hints-syntax-p
    :pred property-hints-list-syntax-p
    :true-listp t)
  )

(defsection sumtype-option-syntax
  :parents (sumtype-syntax)

  (define sumtype-option-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for sumtype-option-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>sumtype-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:kind (maybe-function-syntax-p second))
            (:recognizer (function-syntax-p second))
            (:equal (function-syntax-p second))
            (:sums (type-sum-list-syntax-p second))
            (:property-hints (property-hints-list-syntax-p second))
            (t (er hard? 'process=>sumtype-option-syntax-p-helper
                   "Smtlink-hint sumtype option doesn't include: ~p0. ~
                       They are :kind, :recognizer, :sums and ~
                       :property-hints.~%"
                   first)))))
      (and first-ok
           (sumtype-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :kind)
                                (maybe-function-syntax-p (cadr term)))
                       (implies (equal (car term) :recognizer)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :equal)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :sums)
                                (type-sum-list-syntax-p (cadr term)))
                       (implies (equal (car term) :property-hints)
                                (property-hints-list-syntax-p (cadr term)))))
         :hints (("Goal"
                  :expand (sumtype-option-syntax-p-helper term used)))
         :name definition-of-sumtype-option-syntax-p-helper)
     (ok (implies (and (and ok (consp term) (symbol-listp used))
                       (not (equal (car term) :kind))
                       (not (equal (car term) :recognizer))
                       (not (equal (car term) :equal))
                       (not (equal (car term) :sums)))
                  (equal (car term) :property-hints))
         :hints (("Goal"
                  :expand (sumtype-option-syntax-p-helper term used)))
         :name option-of-sumtype-option-syntax-p-helper))
    (defthm monotonicity-of-sumtype-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (sumtype-option-syntax-p-helper term used))
               (sumtype-option-syntax-p-helper term used-1))))

  (defthm monotonicity-of-sumtype-option-syntax-p-helper-corollary
    (implies (sumtype-option-syntax-p-helper term used)
             (sumtype-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-sumtype-option-syntax-p-helper)
             :use ((:instance monotonicity-of-sumtype-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define sumtype-option-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for sumtype-option-syntax."
    (sumtype-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :kind)
                                (maybe-function-syntax-p (cadr term)))
                       (implies (equal (car term) :recognizer)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :equal)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :sums)
                                (type-sum-list-syntax-p (cadr term)))
                       (implies (equal (car term) :property-hints)
                                (property-hints-list-syntax-p (cadr term)))))
         :name definition-of-sumtype-option-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :kind))
                       (not (equal (car term) :recognizer))
                       (not (equal (car term) :equal))
                       (not (equal (car term) :sums)))
                  (equal (car term) :property-hints))
         :name option-of-sumtype-option-syntax-p)
     (ok (implies (and ok (consp term))
                  (sumtype-option-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (sumtype-option-syntax-p-helper term nil)))
         :name monotonicity-of-sumtype-option-syntax-p)))

  (easy-fix sumtype-option-syntax nil)
  )

(defsection sumtype-syntax
  :parents (datatype-syntax)

  (define sumtype-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for sumtype-syntax."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) nil)
         ((cons tname type-options) term))
      (and (symbolp tname)
           (sumtype-option-syntax-p type-options))))

  (easy-fix sumtype-syntax '(integerp))

  (deflist sumtype-list-syntax
    :elt-type sumtype-syntax-p
    :pred sumtype-list-syntax-p
    :true-listp t)
  )

(defsection init-syntax
  :parents (array-syntax)

  (define init-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for init-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>init-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:fn (function-syntax-p second))
            (:val (symbolp second))
            (t (er hard? 'process=>sumtype-option-syntax-p-helper
                   "Smtlink-hint init syntax options doesn't include: ~p0.
                       They are :fn, and :val.~%"
                   first)))))
      (and first-ok
           (init-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :fn)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :val)
                                (symbolp (cadr term)))))
         :hints (("Goal"
                  :expand (init-syntax-p-helper term used)))
         :name definition-of-init-syntax-p-helper)
     (ok (implies (and (and ok (consp term) (symbol-listp used))
                       (not (equal (car term) :fn)))
                  (equal (car term) :val))
         :hints (("Goal"
                  :expand (init-syntax-p-helper term used)))
         :name option-of-init-syntax-p-helper))
    (defthm monotonicity-of-init-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (init-syntax-p-helper term used))
               (init-syntax-p-helper term used-1))))

  (defthm monotonicity-of-init-syntax-p-helper-corollary
    (implies (init-syntax-p-helper term used)
             (init-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-init-syntax-p-helper)
             :use ((:instance monotonicity-of-init-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define init-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for init-syntax."
    (init-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :fn)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :val)
                                (symbolp (cadr term)))))
         :name definition-of-init-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :fn)))
                  (equal (car term) :val))
         :name option-of-init-syntax-p)
     (ok (implies (and ok (consp term))
                  (init-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (init-syntax-p-helper term nil)))
         :name monotonicity-of-init-syntax-p)))

  (easy-fix init-syntax nil)
  )

(defsection array-option-syntax
  :parents (array-syntax)

  (define array-option-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for array-option-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>array-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:recognizer (function-syntax-p second))
            (:key-type (symbolp second))
            (:val-type (symbolp second))
            (:init (init-syntax-p second))
            (:select (function-syntax-p second))
            (:store (function-syntax-p second))
            (:equal (function-syntax-p second))
            (:equal-witness (function-syntax-p second))
            (:property-hints (property-hints-list-syntax-p second))
            (t (er hard? 'process=>-option-syntax-p-helper
                   "Smtlink-hint array option doesn't include: ~p0.
                       They are :recognizer, :key-type, :val-type, :init, ~
                       :select, :store, :equal, :equal-witness and ~
                       :property-hints.~%"
                   first)))))
      (and first-ok
           (array-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :recognizer)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :key-type)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :val-type)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :init)
                                (init-syntax-p (cadr term)))
                       (implies (equal (car term) :select)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :store)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :equal)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :equal-witness)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :property-hints)
                                (property-hints-list-syntax-p (cadr term)))))
         :hints (("Goal"
                  :expand (array-option-syntax-p-helper term used)))
         :name definition-of-array-option-syntax-p-helper)
     (ok (implies (and (and ok (consp term) (symbol-listp used))
                       (not (equal (car term) :recognizer))
                       (not (equal (car term) :key-type))
                       (not (equal (car term) :val-type))
                       (not (equal (car term) :init))
                       (not (equal (car term) :select))
                       (not (equal (car term) :store))
                       (not (equal (car term) :equal))
                       (not (equal (car term) :equal-witness)))
                  (equal (car term) :property-hints))
         :hints (("Goal"
                  :expand (array-option-syntax-p-helper term used)))
         :name option-of-array-option-syntax-p-helper))
    (defthm monotonicity-of-array-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (array-option-syntax-p-helper term used))
               (array-option-syntax-p-helper term used-1))))

  (defthm monotonicity-of-array-option-syntax-p-helper-corollary
    (implies (array-option-syntax-p-helper term used)
             (array-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-array-option-syntax-p-helper)
             :use ((:instance monotonicity-of-array-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define array-option-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for array-option-syntax."
    (array-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :recognizer)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :key-type)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :val-type)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :init)
                                (init-syntax-p (cadr term)))
                       (implies (equal (car term) :select)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :store)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :equal)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :equal-witness)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :property-hints)
                                (property-hints-list-syntax-p (cadr term)))))
         :name definition-of-array-option-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :recognizer))
                       (not (equal (car term) :key-type))
                       (not (equal (car term) :val-type))
                       (not (equal (car term) :init))
                       (not (equal (car term) :select))
                       (not (equal (car term) :store))
                       (not (equal (car term) :equal))
                       (not (equal (car term) :equal-witness)))
                  (equal (car term) :property-hints))
         :name option-of-array-option-syntax-p)
     (ok (implies (and ok (consp term))
                  (array-option-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (array-option-syntax-p-helper term nil)))
         :name monotonicity-of-array-option-syntax-p)))

  (easy-fix array-option-syntax nil)
  )

(defsection array-syntax
  :parents (datatype-syntax)

  (define array-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for array-syntax."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) nil)
         ((cons tname type-options) term))
      (and (symbolp tname)
           (array-option-syntax-p type-options))))

  (easy-fix array-syntax '(array))

  (deflist array-list-syntax
    :elt-type array-syntax-p
    :pred array-list-syntax-p
    :true-listp t)
  )

(defsection abstract-option-syntax
  :parents (abstract-syntax)

  (define abstract-option-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper function for abstract-option-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>abstract-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:recognizer (function-syntax-p second))
            (:equal (function-syntax-p second))
            (:property-hints (property-hints-list-syntax-p second))
            (t (er hard? 'process=>abstract-option-syntax-p-helper
                   "Smtlink-hint abstract datatype option doesn't include: ~p0.
                       They are :recognizer, :equal and :property-hints.~%"
                   first)))))
      (and first-ok
           (abstract-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :recognizer)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :equal)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :property-hints)
                                (property-hints-list-syntax-p (cadr term)))))
         :hints (("Goal"
                  :expand (abstract-option-syntax-p-helper term used)))
         :name definition-of-abstract-option-syntax-p-helper)
     (ok (implies (and (and ok (consp term) (symbol-listp used)
                            (not (equal (car term) :recognizer))
                            (not (equal (car term) :equal))))
                  (equal (car term) :property-hints))
         :hints (("Goal"
                  :expand (abstract-option-syntax-p-helper term used)))
         :name option-of-abstract-option-syntax-p-helper))
    (defthm monotonicity-of-abstract-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (abstract-option-syntax-p-helper term used))
               (abstract-option-syntax-p-helper term used-1))))

  (defthm monotonicity-of-abstract-option-syntax-p-helper-corollary
    (implies (abstract-option-syntax-p-helper term used)
             (abstract-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-abstract-option-syntax-p-helper)
             :use ((:instance monotonicity-of-abstract-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define abstract-option-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recoginizer for abstract-option-syntax."
    (abstract-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :recognizer)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :equal)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :property-hints)
                                (property-hints-list-syntax-p (cadr term)))))
         :name definition-of-abstract-option-syntax-p)
     (ok (implies (and (and ok (consp term)
                            (not (equal (car term) :recognizer))
                            (not (equal (car term) :equal))))
                  (equal (car term) :property-hints))
         :name option-of-abstract-option-syntax-p)
     (ok (implies (and ok (consp term))
                  (abstract-option-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (abstract-option-syntax-p-helper term nil)))
         :name monotonicity-of-abstract-option-syntax-p)))

  (easy-fix abstract-option-syntax nil)
  )

(defsection abstract-syntax
  :parents (datatype-syntax)

  (define abstract-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for abstract-syntax."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) nil)
         ((cons tname type-options) term))
      (and (symbolp tname)
           (abstract-option-syntax-p type-options))))

  (easy-fix abstract-syntax '(array))

  (deflist abstract-list-syntax
    :elt-type abstract-syntax-p
    :pred abstract-list-syntax-p
    :true-listp t)
  )

(defsection datatype-suntax
  :parents (Smtlink-process-user-hint)

  (define datatype-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper for datatype-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>datatype-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:sumtypes (sumtype-list-syntax-p second))
            (:arrays (array-list-syntax-p second))
            (:abstracts (abstract-list-syntax-p second))
            (t (er hard? 'process=>datatype-syntax-p-helper
                   "Datatype option doesn't include: ~p0. ~
                       They are :sumtypes, :arrays and :abstracts.~%"
                   first)))))
      (and first-ok
           (datatype-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :sumtypes)
                                (sumtype-list-syntax-p (cadr term)))
                       (implies (equal (car term) :arrays)
                                (array-list-syntax-p (cadr term)))
                       (implies (equal (car term) :abstracts)
                                (abstract-list-syntax-p (cadr term)))))
         :hints (("Goal"
                  :expand (datatype-syntax-p-helper term used)))
         :name definition-of-datatype-syntax-p-helper)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :sumtypes))
                       (not (equal (car term) :arrays)))
                  (equal (car term) :abstracts))
         :hints (("Goal"
                  :expand (datatype-syntax-p-helper term used)))
         :name option-of-datatype-syntax-p-helper))
    (defthm monotonicity-of-datatype-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (datatype-syntax-p-helper term used))
               (datatype-syntax-p-helper term used-1))))

  (defthm monotonicity-of-datatype-syntax-p-helper-corollary
    (implies (datatype-syntax-p-helper term used)
             (datatype-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-datatype-syntax-p-helper)
             :use ((:instance monotonicity-of-datatype-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define datatype-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for datatype-syntax."
    (datatype-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :sumtypes)
                                (sumtype-list-syntax-p (cadr term)))
                       (implies (equal (car term) :arrays)
                                (array-list-syntax-p (cadr term)))
                       (implies (equal (car term) :abstracts)
                                (abstract-list-syntax-p (cadr term)))))
         :name definition-of-datatype-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :sumtypes))
                       (not (equal (car term) :arrays)))
                  (equal (car term) :abstracts))
         :name option-of-datatype-syntax-p)
     (ok (implies (and ok (consp term))
                  (datatype-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (datatype-syntax-p-helper term nil)))
         :name monotonicity-of-datatype-syntax-p)))

  (easy-fix datatype-syntax nil)
  )

(defsection acl2type-option-syntax
  :parents (acl2type-syntax)

  (define acl2type-option-syntax-p-helper ((term t) (used symbol-listp))
    :returns (ok booleanp)
    :short "Helper for acl2type-option-syntax."
    (b* ((used (symbol-list-fix used))
         ((unless (consp term)) t)
         ((unless (and (consp term) (consp (cdr term)))) nil)
         ((list* first second rest) term)
         ((if (member-equal first used))
          (er hard? 'process=>acl2type-option-syntax-p-helper
              "~p0 option is already defined in the hint.~%" first))
         (first-ok
          (case first
            (:subtypes (sub/supertype-list-syntax-p second))
            (:supertypes (sub/supertype-list-syntax-p second))
            (t (er hard? 'process=>acl2type-syntax-p-helper
                   "Acl2type option doesn't include: ~p0. ~
                       They are :subtypes and :supertypes.~%"
                   first)))))
      (and first-ok
           (acl2type-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :subtypes)
                                (sub/supertype-list-syntax-p (cadr term)))
                       (implies (equal (car term) :supertypes)
                                (sub/supertype-list-syntax-p (cadr term)))))
         :hints (("Goal"
                  :expand (acl2type-option-syntax-p-helper term used)))
         :name definition-of-acl2type-option-syntax-p-helper)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :subtypes)))
                  (equal (car term) :supertypes))
         :hints (("Goal"
                  :expand (acl2type-option-syntax-p-helper term used)))
         :name option-of-acl2type-option-syntax-p-helper))
    (defthm monotonicity-of-acl2type-option-syntax-p-helper
      (implies (and (subsetp used-1 used :test 'equal)
                    (acl2type-option-syntax-p-helper term used))
               (acl2type-option-syntax-p-helper term used-1))))

  (defthm monotonicity-of-acl2type-option-syntax-p-helper-corollary
    (implies (acl2type-option-syntax-p-helper term used)
             (acl2type-option-syntax-p-helper term nil))
    :hints (("Goal"
             :in-theory (disable monotonicity-of-acl2type-option-syntax-p-helper)
             :use ((:instance monotonicity-of-acl2type-option-syntax-p-helper
                              (used used)
                              (used-1 nil))))))

  (define acl2type-option-syntax-p ((term t))
    :returns (ok booleanp)
    :short "Recognizer for acl2type-option-syntax."
    (acl2type-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :subtypes)
                                (sub/supertype-list-syntax-p (cadr term)))
                       (implies (equal (car term) :supertypes)
                                (sub/supertype-list-syntax-p (cadr term)))))
         :name definition-of-acl2type-option-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :subtypes)))
                  (equal (car term) :supertypes))
         :name option-of-acl2type-option-syntax-p)
     (ok (implies (and ok (consp term))
                  (acl2type-option-syntax-p (cddr term)))
         :hints (("Goal"
                  :expand (acl2type-option-syntax-p-helper term nil)))
         :name monotonicity-of-acl2type-option-syntax-p)))

  (easy-fix acl2type-option-syntax nil)
  )

(defsection acl2type-syntax
  :parents (Smtlink-process-user-hint)

  (define acl2type-syntax-p ((term t))
    :returns (syntax-good? booleanp)
    :short "Recognizer for acl2type-syntax."
    (b* (((unless (true-listp term)) nil)
         ((unless (consp term)) nil)
         ((cons tname type-options) term))
      (and (symbolp tname)
           (acl2type-option-syntax-p type-options))))

  (easy-fix acl2type-syntax '(array))

  (deflist acl2type-list-syntax
    :elt-type acl2type-syntax-p
    :pred acl2type-list-syntax-p
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
            (:functions (function-list-syntax-p second))
            (:hypotheses (hypothesis-list-syntax-p second))
            (:acl2types (acl2type-list-syntax-p second))
            (:datatypes (datatype-syntax-p second))
            (:replaces (thm-spec-list-syntax-p second))
            (:int-to-ratp (int-to-rat-syntax-p second))
            (:under-inductionp (booleanp second))
            (:smt-dir (stringp second))
            (:smt-fname (stringp second))
            (:rm-file (booleanp second))
            (:global-hint (symbolp second))
            (:wrld-fn-len (natp second))
            (:translation-theory (pseudo-termp second))
            (:customp (booleanp second))
            (t (er hard? 'process=>smtlink-hint-syntax-p-helper
                   "Smtlink-hint option doesn't include: ~p0. ~
                       They are :functions, :hypotheses, :acl2types, ~
                       :datatypes, :arrays, :replaces :int-to-ratp, ~
                       :under-inductionp, :smt-dir, :smt-fname, :rm-file, ~
                       :global-hint, :wrld-fn-len, :translation-theory, ~
                       and :customp.~%"
                   first)))))
      (and first-ok
           (smtlink-hint-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :functions)
                                (function-list-syntax-p (cadr term)))
                       (implies (equal (car term) :hypotheses)
                                (hypothesis-list-syntax-p (cadr term)))
                       (implies (equal (car term) :acl2types)
                                (acl2type-list-syntax-p (cadr term)))
                       (implies (equal (car term) :datatypes)
                                (datatype-syntax-p (cadr term)))
                       (implies (equal (car term) :replaces)
                                (thm-spec-list-syntax-p (cadr term)))
                       (implies (equal (car term) :int-to-ratp)
                                (int-to-rat-syntax-p (cadr term)))
                       (implies (equal (car term) :under-inductionp)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :smt-dir)
                                (stringp (cadr term)))
                       (implies (equal (car term) :smt-fname)
                                (stringp (cadr term)))
                       (implies (equal (car term) :rm-file)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :global-hint)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :wrld-fn-len)
                                (natp (cadr term)))
                       (implies (equal (car term) :translation-theory)
                                (pseudo-termp (cadr term)))
                       (implies (equal (car term) :customp)
                                (booleanp (cadr term)))))
         :hints (("Goal"
                  :expand (smtlink-hint-syntax-p-helper term used)))
         :name definition-of-smtlink-hint-syntax-p-helper)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :functions))
                       (not (equal (car term) :hypotheses))
                       (not (equal (car term) :acl2types))
                       (not (equal (car term) :datatypes))
                       (not (equal (car term) :replaces))
                       (not (equal (car term) :int-to-ratp))
                       (not (equal (car term) :under-inductionp))
                       (not (equal (car term) :smt-dir))
                       (not (equal (car term) :smt-fname))
                       (not (equal (car term) :rm-file))
                       (not (equal (car term) :global-hint))
                       (not (equal (car term) :wrld-fn-len))
                       (not (equal (car term) :translation-theory)))
                  (equal (car term) :customp))
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
                                (function-list-syntax-p (cadr term)))
                       (implies (equal (car term) :hypotheses)
                                (hypothesis-list-syntax-p (cadr term)))
                       (implies (equal (car term) :acl2types)
                                (acl2type-list-syntax-p (cadr term)))
                       (implies (equal (car term) :datatypes)
                                (datatype-syntax-p (cadr term)))
                       (implies (equal (car term) :replaces)
                                (thm-spec-list-syntax-p (cadr term)))
                       (implies (equal (car term) :int-to-ratp)
                                (int-to-rat-syntax-p (cadr term)))
                       (implies (equal (car term) :under-inductionp)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :smt-dir)
                                (stringp (cadr term)))
                       (implies (equal (car term) :smt-fname)
                                (stringp (cadr term)))
                       (implies (equal (car term) :rm-file)
                                (booleanp (cadr term)))
                       (implies (equal (car term) :global-hint)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :wrld-fn-len)
                                (natp (cadr term)))
                       (implies (equal (car term) :translation-theory)
                                (pseudo-termp (cadr term)))
                       (implies (equal (car term) :customp)
                                (booleanp (cadr term)))))
         :name definition-of-smtlink-hint-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :functions))
                       (not (equal (car term) :hypotheses))
                       (not (equal (car term) :acl2types))
                       (not (equal (car term) :datatypes))
                       (not (equal (car term) :replaces))
                       (not (equal (car term) :int-to-ratp))
                       (not (equal (car term) :under-inductionp))
                       (not (equal (car term) :smt-dir))
                       (not (equal (car term) :smt-fname))
                       (not (equal (car term) :rm-file))
                       (not (equal (car term) :global-hint))
                       (not (equal (car term) :wrld-fn-len))
                       (not (equal (car term) :translation-theory)))
                  (equal (car term) :customp))
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
                           true-list-listp
                           pseudo-term-listp-of-symbol-listp
                           pseudo-term-listp-of-cdr-of-pseudo-termp
                           acl2::pseudo-lambdap-of-car-when-pseudo-termp
                           acl2::symbol-listp-of-cdr-when-symbol-listp
                           symbolp-of-fn-call-of-pseudo-termp
                           acl2::true-listp-of-car-when-true-list-listp
                           acl2::pseudo-term-listp-cdr)))

(define construct-thm-spec-option-lst
  ((ts-opt-lst thm-spec-option-syntax-p)
   (thm-spec thm-spec-p))
  :returns (new-thm-spec thm-spec-p)
  :measure (len ts-opt-lst)
  :hints (("Goal" :in-theory (enable thm-spec-option-syntax-fix)))
  (b* ((ts-opt-lst (thm-spec-option-syntax-fix ts-opt-lst))
       (thm-spec (thm-spec-fix thm-spec))
       ((unless (consp ts-opt-lst)) thm-spec)
       ((list* option content rest) ts-opt-lst)
       (new-thm-spec
        (case option
          (:thm (change-thm-spec thm-spec :thm content))
          (:formals (change-thm-spec thm-spec :formals content))
          (:hypotheses (change-thm-spec thm-spec :hypotheses content))
          (:lhs (change-thm-spec thm-spec :lhs content))
          (:rhs (change-thm-spec thm-spec :rhs content))
          (:judgements (change-thm-spec thm-spec :judgements content))
          (:hints (change-thm-spec thm-spec :hints content)))))
    (construct-thm-spec-option-lst rest new-thm-spec)))

(define construct-thm-spec ((thm-spec thm-spec-syntax-p))
  :returns (new-thm-spec thm-spec-p)
  :guard-hints (("Goal" :in-theory (enable thm-spec-syntax-p)))
  (construct-thm-spec-option-lst thm-spec (make-thm-spec))
  ///
  (more-returns
   (new-thm-spec (implies (thm-spec-syntax-p thm-spec)
                          (thm-spec-p new-thm-spec))
                 :name construct-thm-spec-not-null)))

(define construct-thm-spec-list ((thm-spec-lst thm-spec-list-syntax-p))
  :returns (new-thm-spec-lst thm-spec-list-p)
  :measure (len thm-spec-lst)
  (b* ((thm-spec-lst (thm-spec-list-syntax-fix thm-spec-lst))
       ((unless (consp thm-spec-lst)) nil)
       ((cons thm-spec-hd thm-spec-tl) thm-spec-lst))
    (cons (construct-thm-spec thm-spec-hd)
          (construct-thm-spec-list thm-spec-tl))))

(define merge-replaces ((content thm-spec-list-syntax-p)
                        (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :measure (len content)
  :short "Merging replace hints into smt-hint."
  (b* ((hint (smtlink-hint-fix hint))
       (content (thm-spec-list-syntax-fix content))
       ((unless (consp content)) hint)
       ((cons first rest) content)
       ((smtlink-hint h) hint)
       (new-replace-lst (cons (construct-thm-spec first) h.replaces))
       (new-hint (change-smtlink-hint h :replaces new-replace-lst)))
    (merge-replaces rest new-hint)))

(define construct-function-option-lst ((fun-opt-lst function-option-syntax-p)
                                       (smt-func smt-function-p))
  :returns (func smt-function-p)
  :short "Add option information into func."
  :measure (len fun-opt-lst)
  :hints (("Goal" :in-theory (enable function-option-syntax-fix)))
  (b* ((fun-opt-lst (function-option-syntax-fix fun-opt-lst))
       (smt-func (smt-function-fix smt-func))
       ((unless (consp fun-opt-lst)) smt-func)
       ((smt-function f) smt-func)
       ((list* option content rest) fun-opt-lst)
       (new-smt-func
        (case option
          (:fn-to-const
           (change-smt-function
            smt-func
            :translation-hint
            (change-trans-hint f.translation-hint :fn-to-const content)))
          (:translation
           (change-smt-function
            smt-func
            :translation-hint
            (change-trans-hint f.translation-hint :translation content)))
          (:kind (change-smt-function smt-func :kind content))
          (:return (change-smt-function
                    smt-func
                    :returns (construct-thm-spec-list content)))
          (:return-type
           (change-smt-function smt-func
                                :translation-hint
                                (change-trans-hint f.translation-hint
                                                   :return-type
                                                   content)))
          (:uninterpreted-hints (change-smt-function
                                 smt-func
                                 :uninterpreted-hints content))
          (:depth (change-smt-function smt-func :depth content)))))
    (construct-function-option-lst rest new-smt-func)))

(define construct-function ((func maybe-function-syntax-p))
  :returns (new-func maybe-smt-function-p)
  :short "Function for generating func-p of a single function hint."
  :guard-hints (("Goal" :in-theory (enable maybe-function-syntax-fix
                                           maybe-function-syntax-p
                                           function-syntax-fix
                                           function-syntax-p)))
  (b* ((func (maybe-function-syntax-fix func))
       ((unless func) nil)
       ((cons name fun-opt-lst) func))
    (construct-function-option-lst fun-opt-lst
                                   (make-smt-function :name name)))
  ///
  (more-returns
   (new-func (implies (function-syntax-p func)
                      (smt-function-p new-func))
             :name construct-function-not-null)))

(define merge-functions ((content function-list-syntax-p)
                         (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Merging function hints into smt-hint."
  :measure (len content)
  :hints (("Goal" :in-theory (enable function-list-syntax-fix)))
  :guard-hints (("Goal" :in-theory (enable function-list-syntax-fix
                                           function-list-syntax-p
                                           function-syntax-p
                                           function-syntax-fix)))
  (b* ((hint (smtlink-hint-fix hint))
       (content (function-list-syntax-fix content))
       ((unless (consp content)) hint)
       ((cons first rest) content)
       ((smtlink-hint h) hint)
       (new-func-lst (cons (construct-function first) h.functions))
       (new-hint (change-smtlink-hint h :functions new-func-lst)))
    (merge-functions rest new-hint)))

(define construct-function-list ((func-lst function-list-syntax-p))
  :returns (new-func-lst smt-function-list-p)
  :measure (len func-lst)
  (b* ((func-lst (function-list-syntax-fix func-lst))
       ((unless (consp func-lst)) nil)
       ((cons func-hd func-tl) func-lst))
    (cons (construct-function func-hd) (construct-function-list func-tl))))

(define construct-type-sum ((sum-opt-lst type-sum-syntax-p)
                            (smt-sum smt-sum-p))
  :returns (new-sum smt-sum-p)
  :hints (("Goal" :in-theory (enable type-sum-syntax-fix)))
  (b* ((sum-opt-lst (type-sum-syntax-fix sum-opt-lst))
       (smt-sum (smt-sum-fix smt-sum))
       ((unless (consp sum-opt-lst)) smt-sum)
       ((list* option content rest) sum-opt-lst)
       (new-smt-sum
        (case option
          (:tag
           (change-smt-sum smt-sum :tag content))
          (:constructor
           (change-smt-sum smt-sum
                           :constructor (construct-function content)))
          (:destructors
           (change-smt-sum smt-sum
                           :destructors (construct-function-list content))))))
    (construct-type-sum rest new-smt-sum)))

(define construct-type-sum-list ((sum-lst type-sum-list-syntax-p))
  :returns (new-sum-lst smt-sum-list-p)
  :measure (len sum-lst)
  (b* ((sum-lst (type-sum-list-syntax-fix sum-lst))
       ((unless (consp sum-lst)) nil)
       ((cons sum-hd sum-tl) sum-lst))
    (cons (construct-type-sum sum-hd (make-smt-sum))
          (construct-type-sum-list sum-tl))))

(define construct-sub/supertype-option-lst
  ((sub-opt-lst sub/supertype-option-syntax-p)
   (smt-sub smt-sub/supertype-p))
  :returns (new-sub smt-sub/supertype-p)
  :hints (("Goal" :in-theory (enable sub/supertype-option-syntax-fix)))
  :measure (len sub-opt-lst)
  (b* ((sub-opt-lst (sub/supertype-option-syntax-fix sub-opt-lst))
       (smt-sub (smt-sub/supertype-fix smt-sub))
       ((unless (consp sub-opt-lst)) smt-sub)
       ((list* option content rest) sub-opt-lst)
       (new-smt-sub
        (case option
          (:thm (change-smt-sub/supertype
                 smt-sub :thm (construct-thm-spec content))))))
    (construct-sub/supertype-option-lst rest new-smt-sub)))

(define construct-sub/supertype ((sub sub/supertype-syntax-p))
  :returns (new-sub smt-sub/supertype-p)
  :guard-hints (("Goal" :in-theory (e/d (sub/supertype-syntax-fix
                                         sub/supertype-syntax-p))))
  (b* ((sub (sub/supertype-syntax-fix sub))
       ((cons name sub-opt-lst) sub))
    (construct-sub/supertype-option-lst sub-opt-lst
                                        (make-smt-sub/supertype :type name))))

(define construct-sub/supertype-list ((sub-lst sub/supertype-list-syntax-p))
  :returns (new-sub-lst smt-sub/supertype-list-p)
  :measure (len sub-lst)
  (b* ((sub-lst (sub/supertype-list-syntax-fix sub-lst))
       ((unless (consp sub-lst)) nil)
       ((cons sub-hd sub-tl) sub-lst))
    (cons (construct-sub/supertype sub-hd)
          (construct-sub/supertype-list sub-tl))))

(define construct-property-hints-list
  ((prop-hints-lst property-hints-list-syntax-p))
  :returns (new-prop-alst
            symbol-hints-alist-p
            :hints (("Goal"
                     :in-theory
                     (enable property-hints-list-syntax-fix
                             property-hints-syntax-fix property-hints-syntax-p)
                     :expand (property-hints-list-syntax-fix prop-hints-lst))))
  :measure (len (property-hints-list-syntax-fix prop-hints-lst))
  :verify-guards nil
  (b* ((prop-hints-lst (property-hints-list-syntax-fix prop-hints-lst))
       ((unless (consp prop-hints-lst)) nil)
       ((cons hints-hd hints-tl) prop-hints-lst)
       ((cons name hints) hints-hd))
    (acons name hints (construct-property-hints-list hints-tl))))

(verify-guards construct-property-hints-list
  :hints (("Goal" :in-theory (enable property-hints-syntax-p))))

(define construct-sumtype-option-lst ((type-opt-lst sumtype-option-syntax-p)
                                      (smt-type smt-datatype-p))
  :guard (equal (smt-datatype-kind smt-type) :sumtype)
  :returns (smt-type smt-datatype-p)
  :measure (len type-opt-lst)
  :hints (("Goal" :in-theory (enable sumtype-option-syntax-fix)))
  (b* ((type-opt-lst (sumtype-option-syntax-fix type-opt-lst))
       (smt-type (smt-datatype-fix smt-type))
       ((unless (consp type-opt-lst)) smt-type)
       ((list* option content rest) type-opt-lst)
       (new-smt-type
        (case option
          (:kind
           (change-smt-datatype-sumtype
            smt-type :kind (construct-function content)))
          (:recognizer
           (change-smt-datatype-sumtype
            smt-type :recognizer (construct-function content)))
          (:equal
           (change-smt-datatype-sumtype
            smt-type :equal (construct-function content)))
          (:sums
           (change-smt-datatype-sumtype
            smt-type :sums (construct-type-sum-list content)))
          (:property-hints
           (change-smt-datatype-sumtype
            smt-type
            :property-hints (construct-property-hints-list content))))))
    (construct-sumtype-option-lst rest new-smt-type)))

(define construct-sumtype ((type sumtype-syntax-p))
  :returns (new-type smt-datatype-p)
  :guard-hints (("Goal" :in-theory (enable sumtype-syntax-fix
                                           sumtype-syntax-p)))
  (b* ((type (sumtype-syntax-fix type))
       ((cons & type-opt-lst) type))
    (construct-sumtype-option-lst type-opt-lst (make-smt-datatype-sumtype))))

(define merge-sumtypes ((content sumtype-list-syntax-p)
                        (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :measure (len content)
  :short "Merging sumtype hints into smt-hint."
  (b* ((hint (smtlink-hint-fix hint))
       (content (sumtype-list-syntax-fix content))
       ((unless (consp content)) hint)
       ((cons first rest) content)
       ((smtlink-hint h) hint)
       (new-type-lst (cons (construct-sumtype first) h.datatypes))
       (new-hint (change-smtlink-hint h :datatypes new-type-lst)))
    (merge-sumtypes rest new-hint)))

(define construct-init-option-lst ((init-opt-lst init-syntax-p)
                                   (smt-init init-p))
  :returns (new-init init-p)
  :measure (len init-opt-lst)
  :hints (("Goal" :in-theory (enable init-syntax-fix)))
  (b* ((init-opt-lst (init-syntax-fix init-opt-lst))
       (smt-init (init-fix smt-init))
       ((unless (consp init-opt-lst)) smt-init)
       ((list* option content rest) init-opt-lst)
       (new-smt-init
        (case option
          (:fn (change-init smt-init :fn (construct-function content)))
          (:val (change-init smt-init :val content)))))
    (construct-init-option-lst rest new-smt-init)))

(define construct-init ((init init-syntax-p))
  :returns (new-init init-p)
  :guard-hints (("Goal" :in-theory (enable init-syntax-fix init-syntax-p)))
  (construct-init-option-lst init (make-init)))

(define construct-array-option-lst ((type-opt-lst array-option-syntax-p)
                                    (smt-type smt-datatype-p))
  :guard (equal (smt-datatype-kind smt-type) :array)
  :returns (smt-type smt-datatype-p)
  :measure (len type-opt-lst)
  :hints (("Goal" :in-theory (enable array-option-syntax-fix)))
  (b* ((type-opt-lst (array-option-syntax-fix type-opt-lst))
       (smt-type (smt-datatype-fix smt-type))
       ((unless (consp type-opt-lst)) smt-type)
       ((list* option content rest) type-opt-lst)
       (new-smt-type
        (case option
          (:recognizer
           (change-smt-datatype-array
            smt-type :recognizer (construct-function content)))
          (:key-type
           (change-smt-datatype-array smt-type :key-type content))
          (:val-type
           (change-smt-datatype-array smt-type :val-type content))
          (:init
           (change-smt-datatype-array
            smt-type :init (construct-init content)))
          (:select
           (change-smt-datatype-array
            smt-type :select (construct-function content)))
          (:store
           (change-smt-datatype-array
            smt-type :store (construct-function content)))
          (:equal
           (change-smt-datatype-array
            smt-type :equal (construct-function content)))
          (:equal-witness
           (change-smt-datatype-array
            smt-type :equal-witness (construct-function content)))
          (:property-hints
           (change-smt-datatype-array
            smt-type
            :property-hints (construct-property-hints-list content))))))
    (construct-array-option-lst rest new-smt-type)))

(define construct-array ((type array-syntax-p))
  :returns (new-type smt-datatype-p)
  :guard-hints (("Goal" :in-theory (enable array-syntax-fix array-syntax-p)))
  (b* ((type (array-syntax-fix type))
       ((cons & type-opt-lst) type))
    (construct-array-option-lst type-opt-lst (make-smt-datatype-array))))

(define merge-arrays ((content array-list-syntax-p)
                      (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :measure (len content)
  :short "Merging array hints into smt-hint."
  (b* ((hint (smtlink-hint-fix hint))
       (content (array-list-syntax-fix content))
       ((unless (consp content)) hint)
       ((cons first rest) content)
       ((smtlink-hint h) hint)
       (new-type-lst (cons (construct-array first) h.datatypes))
       (new-hint (change-smtlink-hint h :datatypes new-type-lst)))
    (merge-arrays rest new-hint)))

(define construct-abstract-option-lst ((type-opt-lst abstract-option-syntax-p)
                                       (smt-type smt-datatype-p))
  :guard (equal (smt-datatype-kind smt-type) :abstract)
  :returns (smt-type smt-datatype-p)
  :measure (len type-opt-lst)
  :hints (("Goal" :in-theory (enable abstract-option-syntax-fix)))
  (b* ((type-opt-lst (abstract-option-syntax-fix type-opt-lst))
       (smt-type (smt-datatype-fix smt-type))
       ((unless (consp type-opt-lst)) smt-type)
       ((list* option content rest) type-opt-lst)
       (new-smt-type
        (case option
          (:recognizer
           (change-smt-datatype-abstract
            smt-type :recognizer (construct-function content)))
          (:equal
           (change-smt-datatype-abstract
            smt-type :equal (construct-function content)))
          (:property-hints
           (change-smt-datatype-abstract
            smt-type
            :property-hints (construct-property-hints-list content))))))
    (construct-abstract-option-lst rest new-smt-type)))

(define construct-abstract ((type abstract-syntax-p))
  :returns (new-type smt-datatype-p)
  :guard-hints (("Goal" :in-theory (enable abstract-syntax-fix
                                           abstract-syntax-p)))
  (b* ((type (abstract-syntax-fix type))
       ((cons & type-opt-lst) type))
    (construct-abstract-option-lst type-opt-lst (make-smt-datatype-abstract))))

(define merge-abstracts ((content abstract-list-syntax-p)
                         (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :measure (len content)
  :short "Merging abstract hints into smt-hint."
  (b* ((hint (smtlink-hint-fix hint))
       (content (abstract-list-syntax-fix content))
       ((unless (consp content)) hint)
       ((cons first rest) content)
       ((smtlink-hint h) hint)
       (new-type-lst (cons (construct-abstract first) h.datatypes))
       (new-hint (change-smtlink-hint h :datatypes new-type-lst)))
    (merge-abstracts rest new-hint)))

(define merge-datatypes ((type-opt-lst datatype-syntax-p)
                         (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :hints (("Goal" :in-theory (enable datatype-syntax-p datatype-syntax-fix)))
  (b* ((hint (smtlink-hint-fix hint))
       (type-opt-lst (datatype-syntax-fix type-opt-lst))
       ((unless (consp type-opt-lst)) hint)
       ((list* option content rest) type-opt-lst)
       (new-hint
        (case option
          (:sumtypes (merge-sumtypes content hint))
          (:arrays (merge-arrays content hint))
          (:abstracts (merge-abstracts content hint)))))
    (merge-datatypes rest new-hint)))

(define construct-acl2type-option-lst ((type-opt-lst acl2type-option-syntax-p)
                                       (smt-type smt-acl2type-p))
  :returns (new-type smt-acl2type-p)
  :measure (len (acl2type-option-syntax-fix type-opt-lst))
  (b* ((type-opt-lst (acl2type-option-syntax-fix type-opt-lst))
       (smt-type (smt-acl2type-fix smt-type))
       ((unless (consp type-opt-lst)) smt-type)
       ((list* option content rest) type-opt-lst)
       (new-smt-type
        (case option
          (:subtypes
           (change-smt-acl2type
            smt-type
            :subtypes (construct-sub/supertype-list content)))
          (:supertypes
           (change-smt-acl2type
            smt-type
            :supertypes (construct-sub/supertype-list content))))))
    (construct-acl2type-option-lst rest new-smt-type)))

(define construct-acl2type ((type acl2type-syntax-p))
  :returns (new-type smt-acl2type-p)
  :guard-hints (("Goal" :in-theory (enable acl2type-syntax-p)))
  (b* ((type (acl2type-syntax-fix type))
       ((unless type) nil)
       ((cons name type-opt-lst) type))
    (construct-acl2type-option-lst
     type-opt-lst (make-smt-acl2type :recognizer name))))

(define merge-acl2types ((content acl2type-list-syntax-p)
                         (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :measure (len (acl2type-list-syntax-fix content))
  (b* ((hint (smtlink-hint-fix hint))
       (content (acl2type-list-syntax-fix content))
       ((unless (consp content)) hint)
       ((cons first rest) content)
       ((smtlink-hint h) hint)
       (new-acl2types (cons (construct-acl2type first) h.acl2types))
       (new-hint (change-smtlink-hint h :acl2types new-acl2types)))
    (merge-acl2types rest new-hint)))

(define construct-hypothesis ((hypo hypothesis-syntax-p))
  :returns (smt-hypo smt-hypo-p)
  :guard-hints (("Goal" :in-theory (enable hypothesis-syntax-p
                                           subst-syntax-p)))
  (b* ((hypo (hypothesis-syntax-fix hypo)))
    (case-match hypo
      ((':instance thm subst)
       (make-smt-hypo :thm thm :subst (pairlis$ (strip-cars subst)
                                                (strip-cadrs subst))))
      (& (make-smt-hypo :thm (cadr hypo))))))

(define merge-hypotheses ((content hypothesis-list-syntax-p)
                          (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Merging type hints into smt-hint."
  :measure (len content)
  (b* ((content (hypothesis-list-syntax-fix content))
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
  :short "Set :int-to-ratp based on user hint."
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
       (new-hint (change-smtlink-hint hint :int-to-ratp new-int-to-rat)))
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

(define set-under-induct ((content booleanp)
                          (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Set :under-induct"
  (b* ((hint (smtlink-hint-fix hint))
       (new-hint (change-smtlink-hint hint :under-inductionp content)))
    new-hint))

(define set-global-hint ((content symbolp)
                         (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Set :global-hint"
  (b* ((hint (smtlink-hint-fix hint))
       (new-hint (change-smtlink-hint hint :global-hint content)))
    new-hint))

(define set-wrld-fn-len ((content natp)
                         (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Set :wrld-fn-len"
  (b* ((hint (smtlink-hint-fix hint))
       (new-hint (change-smtlink-hint hint :wrld-fn-len content)))
    new-hint))

(define set-translation-theory ((content pseudo-termp)
                                (hint smtlink-hint-p))
  :returns (new-hint smtlink-hint-p)
  :short "Set :translation-theory"
  (b* ((hint (smtlink-hint-fix hint))
       (content (pseudo-term-fix content))
       (new-hint (change-smtlink-hint hint :translation-theory content)))
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
                   (:hypotheses (merge-hypotheses second hint))
                   (:acl2types (merge-acl2types second hint))
                   (:datatypes
                    (b* ((datatype-hint (merge-datatypes second hint))
                         ((smtlink-hint h) datatype-hint)
                         (type (unique-sumtype-function-list h.datatypes))
                         ((if type)
                          (prog2$ (er hard? 'process=>combine-hints
                                      "Found destructors of the same name ~q0"
                                      type)
                                  hint)))
                      h))
                   (:replaces (merge-replaces second hint))
                   (:int-to-ratp (set-int-to-rat second hint))
                   (:under-inductionp (set-under-induct second hint))
                   (:smt-fname (set-fname second hint))
                   (:rm-file (set-rm-file second hint))
                   (:smt-dir (set-smt-dir second hint))
                   (:global-hint (set-global-hint second hint))
                   (:wrld-fn-len (set-wrld-fn-len second hint))
                   (:translation-theory (set-translation-theory second hint))
                   (:customp (set-smt-cnf second hint)))))
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
  :returns (subgoal-lst pseudo-term-list-listp
                        :hints (("Goal" :in-theory (enable pseudo-termp))))
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
       (combined-hint (combine-hints user-hint the-hint))
       (next-cp (cdr (assoc-equal 'process-hint *SMT-architecture*)))
       ((if (null next-cp)) (list cl))
       (cp-hint `(:clause-processor (,next-cp clause ',combined-hint state)))
       (subgoal-lst (cons `(hint-please ',cp-hint) cl)))
    (list subgoal-lst)))

(define process-hint-cp ((cl pseudo-term-listp)
                         (hints t)
                         state)
  (b* ((expanded-clause (process-hint cl hints state)))
    (value expanded-clause)))
;;  )

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
                    (alistp a)
                    (ev-smtcp
                     (conjoin-clauses
                      (acl2::clauses-result
                       (process-hint-cp cl hint state)))
                     a))
               (ev-smtcp (disjoin cl) a))
      :rule-classes :clause-processor))

  (define wrld-fn-len ((cl t) (state))
    :mode :program
    (b* ((world (w state)))
      (+ (acl2-count cl)
         (len (remove-duplicates-eq
               (strip-cadrs (universal-theory :here)))))))

  ;; Smtlink is a macro that generates a clause processor hint. This clause
  ;;   processor hint generates a clause, with which a new smt-hint is attached.
  ;;   This new smt-hint combines user given hints with hints from the state.
  ;; A computed hint will be waiting to take the clause and hint for clause
  ;;   expansion and transformation.
  (defmacro smtlink (clause hint)
    `(process-hint-cp ,clause
                      (append ',hint `(:wrld-fn-len ,(wrld-fn-len clause state)))
                      state))

  (defmacro smtlink-custom (clause hint)
    `(process-hint-cp ,clause
                      (append ',hint `(:wrld-fn-len ,(wrld-fn-len clause state)
                                                    :customp t))
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

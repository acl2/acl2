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

;; (defsection Smtlink-process-user-hint
;;   :parents (verified)
;;   :short "Functionalities for processing user hints given to Smtlink. User
;;   hints will be merged with (smt-hint)."

  ;; --------------------------------------------------------

;; Example:
;; :hints (("Goal"
;;            :clause-processor
;;            (SMT::smtlink clause
;;                          '(:functions ((f0 :formals (x y)
;;                                            :return (returns-thm
;;                                                     another-returns-thm)
;;                                            :uninterpreted-hints ((:use lemma))
;;                                            :replace replace-thm
;;                                            :depth 1))
;;                            :hypotheses ((:instance thm1 ((x (1+ (foo a))) (y n)))
;;                                         (:instance thm2 ...))
;;                            :types ((maybe-integer-listp
;;                                     :functions
;;                                     ((rational-list-fix
;;                                       :formals (lst)
;;                                       :returns (returns-thm)
;;                                       :replace replace-thm)
;;                                      (rational-list-car
;;                                       :formals (lst)
;;                                       :returns (returns-thm)
;;                                       :replace replace-thm)
;;                                      (rational-list-cdr
;;                                       :formals (lst)
;;                                       :returns (returns-thm)
;;                                       :replace replace-thm)
;;                                      (rational-list-cons
;;                                       :formals (x lst)
;;                                       :returns (returns-thm)
;;                                       :replace replace-thm))
;;                                     :subtypes
;;                                     ((integer-listp
;;                                       :formals (x)
;;                                       :thm maybe-integer-list-canbe-integer-list))
;;                                     :supertypes
;;                                     ((maybe-rational-listp
;;                                       :formals (x)
;;                                       :thm maybe-integer-list-is-maybe-rational-list))))
;;                            :int-to-ratp (x b)
;;                            :under-inductionp t
;;                            :smt-fname ""
;;                            :rm-file t
;;                            :global-hint current-hint
;;                            :customp nil))))
;; )

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
            (:formals (symbol-listp second))
            (:return (symbol-listp second))
            (:uninterpreted-hints (true-listp second))
            (:replace (symbolp second))
            (:depth (natp second))
            (t (er hard? 'process=>function-option-syntax-p-helper
                   "Smtlink-hint function hint option doesn't include: ~p0.
                       They are :formals, :return, :return-hints, :replace, and
                       :depth.~%" first)))))
      (and first-ok
           (function-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and (symbol-listp used) ok (consp term))
                  (and (not (member-equal (car term) used))
                       (consp (cdr term))
                       (implies (equal (car term) :formals)
                                (symbol-listp (cadr term)))
                       (implies (equal (car term) :return)
                                (symbol-listp (cadr term)))
                       (implies (equal (car term) :uninterpreted-hints)
                                (true-listp (cadr term)))
                       (implies (equal (car term) :replace)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :depth)
                                (natp (cadr term)))))
         :name definition-of-function-option-syntax-p-helper)
     (ok (implies (and (symbol-listp used) ok (consp term))
                  (or (equal (car term) :formals)
                      (equal (car term) :return)
                      (equal (car term) :uninterpreted-hints)
                      (equal (car term) :replace)
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
    :short "Recoginizer for function-option-syntax."
    (function-option-syntax-p-helper term nil)
    ///
    (more-returns
     (ok (implies (and ok (consp term))
                  (and (consp (cdr term))
                       (implies (equal (car term) :formals)
                                (symbol-listp (cadr term)))
                       (implies (equal (car term) :return)
                                (symbol-listp (cadr term)))
                       (implies (equal (car term) :uninterpreted-hints)
                                (true-listp (cadr term)))
                       (implies (equal (car term) :replace)
                                (symbolp (cadr term)))
                       (implies (equal (car term) :depth)
                                (natp (cadr term)))))
         :name definition-of-function-option-syntax-p
         :hints (("Goal"
                  :in-theory (disable definition-of-function-option-syntax-p-helper)
                  :use ((:instance definition-of-function-option-syntax-p-helper
                                   (used nil))))))
     (ok (implies (and ok (consp term)
                       (not (equal (car term) :formals))
                       (not (equal (car term) :return))
                       (not (equal (car term) :uninterpreted-hints))
                       (not(equal (car term) :replace)))
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
         ((unless (consp term)) t)
         ((cons fname function-options) term))
      (and (symbolp fname)
           (function-option-syntax-p function-options))))

  (easy-fix function-syntax nil)

  (deflist function-list-syntax
    :elt-type function-syntax-p
    :pred function-list-syntax-p
    :true-listp t)
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
            (:formals (symbol-listp second))
            (:thm (symbolp second))
            (t (er hard? 'process=>sub/supertype-option-syntax-p-helper
                   "Smtlink-hint sub/supertype options doesn't include: ~p0.
                       They are :formals, and :thm.~%" first)))))
      (and first-ok
           (sub/supertype-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :formals)
                                (symbol-listp (cadr term)))
                       (implies (equal (car term) :thm)
                                (symbolp (cadr term)))))
         :hints (("Goal"
                  :expand (sub/supertype-option-syntax-p-helper term used)))
         :name definition-of-sub/supertype-option-syntax-p-helper)
     (ok (implies (and (and ok (consp term) (symbol-listp used))
                       (not (equal (car term) :formals)))
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
                       (implies (equal (car term) :formals)
                                (symbol-listp (cadr term)))
                       (implies (equal (car term) :thm)
                                (symbolp (cadr term)))))
         :name definition-of-sub/supertype-option-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :formals)))
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
            (:functions (function-list-syntax-p second))
            (:fixer (function-syntax-p second))
            (:subtypes (sub/supertype-list-syntax-p second))
            (:supertypes (sub/supertype-list-syntax-p second))
            (t (er hard? 'process=>type-option-syntax-p-helper
                   "Smtlink-hint type option doesn't include: ~p0.
                       They are :functions, :subtypes and :supertypes.~%"
                   first)))))
      (and first-ok
           (type-option-syntax-p-helper rest (cons first used))))
    ///
    (more-returns
     (ok (implies (and ok (consp term) (symbol-listp used))
                  (and (consp (cdr term))
                       (implies (equal (car term) :functions)
                                (function-list-syntax-p (cadr term)))
                       (implies (equal (car term) :fixer)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :subtypes)
                                (sub/supertype-list-syntax-p (cadr term)))
                       (implies (equal (car term) :supertypes)
                                (sub/supertype-list-syntax-p (cadr term)))))
         :hints (("Goal"
                  :expand (type-option-syntax-p-helper term used)))
         :name definition-of-type-option-syntax-p-helper)
     (ok (implies (and (and ok (consp term) (symbol-listp used))
                       (not (equal (car term) :functions))
                       (not (equal (car term) :fixer))
                       (not (equal (car term) :subtypes)))
                  (equal (car term) :supertypes))
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
                       (implies (equal (car term) :functions)
                                (function-list-syntax-p (cadr term)))
                       (implies (equal (car term) :fixer)
                                (function-syntax-p (cadr term)))
                       (implies (equal (car term) :subtypes)
                                (sub/supertype-list-syntax-p (cadr term)))
                       (implies (equal (car term) :supertypes)
                                (sub/supertype-list-syntax-p (cadr term)))))
         :name definition-of-type-option-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :functions))
                       (not (equal (car term) :fixer))
                       (not (equal (car term) :subtypes)))
                  (equal (car term) :supertypes))
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

  (deflist type-list-syntax
    :elt-type type-syntax-p
    :pred type-list-syntax-p
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
            (:types (type-list-syntax-p second))
            (:int-to-ratp (int-to-rat-syntax-p second))
            (:under-inductionp (booleanp second))
            (:smt-dir (stringp second))
            (:smt-fname (stringp second))
            (:rm-file (booleanp second))
            (:global-hint (symbolp second))
            (:wrld-fn-len (natp second))
            (:customp (booleanp second))
            (t (er hard? 'process=>smtlink-hint-syntax-p-helper
                   "Smtlink-hint option doesn't include: ~p0. ~
                       They are :functions, :hypotheses, :types, :int-to-ratp, ~
                       :under-inductionp, :smt-dir, :smt-fname, :rm-file, ~
                       :global-hint, :wrld-fn-len :customp.~%" first)))))
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
                       (implies (equal (car term) :types)
                                (type-list-syntax-p (cadr term)))
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
                       (implies (equal (car term) :customp)
                                (booleanp (cadr term)))))
         :hints (("Goal"
                  :expand (smtlink-hint-syntax-p-helper term used)))
         :name definition-of-smtlink-hint-syntax-p-helper)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :functions))
                       (not (equal (car term) :hypotheses))
                       (not (equal (car term) :types))
                       (not (equal (car term) :int-to-ratp))
                       (not (equal (car term) :under-inductionp))
                       (not (equal (car term) :smt-dir))
                       (not (equal (car term) :smt-fname))
                       (not (equal (car term) :rm-file))
                       (not (equal (car term) :global-hint))
                       (not (equal (car term) :wrld-fn-len)))
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
                       (implies (equal (car term) :types)
                                (type-list-syntax-p (cadr term)))
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
                       (implies (equal (car term) :customp)
                                (booleanp (cadr term)))))
         :name definition-of-smtlink-hint-syntax-p)
     (ok (implies (and (and ok (consp term))
                       (not (equal (car term) :functions))
                       (not (equal (car term) :hypotheses))
                       (not (equal (car term) :types))
                       (not (equal (car term) :int-to-ratp))
                       (not (equal (car term) :under-inductionp))
                       (not (equal (car term) :smt-dir))
                       (not (equal (car term) :smt-fname))
                       (not (equal (car term) :rm-file))
                       (not (equal (car term) :global-hint))
                       (not (equal (car term) :wrld-fn-len)))
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
            (:formals (change-smt-function smt-func :formals content))
            (:return (change-smt-function smt-func :returns content))
            (:uninterpreted-hints (change-smt-function smt-func
                                                       :uninterpreted-hints content))
            (:replace (change-smt-function smt-func :replace-thm content))
            (:depth (change-smt-function smt-func :depth content)))))
      (construct-function-option-lst rest new-smt-func)))

  (define construct-function ((func function-syntax-p))
    :returns (new-func smt-function-p)
    :short "Function for generating func-p of a single function hint."
    :guard-hints (("Goal" :in-theory (enable function-syntax-fix function-syntax-p)))
    (b* ((func (function-syntax-fix func))
         ((cons name fun-opt-lst) func))
      (construct-function-option-lst fun-opt-lst
                                     (make-smt-function :name name))))

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

;; construct types
(define construct-type-functions ((func-lst function-list-syntax-p))
  :returns (new-func-lst smt-function-list-p)
  :measure (len func-lst)
  (b* ((func-lst (function-list-syntax-fix func-lst))
       ((unless (consp func-lst)) nil)
       ((cons func-hd func-tl) func-lst))
    (cons (construct-function func-hd) (construct-type-functions func-tl))))

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
          (:formals (change-smt-sub/supertype smt-sub :formals content))
          (:thm (change-smt-sub/supertype smt-sub :thm content)))))
    (construct-sub/supertype-option-lst rest new-smt-sub)))

(define construct-sub/supertype ((sub sub/supertype-syntax-p))
  :returns (new-sub smt-sub/supertype-p)
  :guard-hints (("Goal" :in-theory (enable sub/supertype-syntax-fix
                                           sub/supertype-syntax-p)))
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

(define construct-type-option-lst ((type-opt-lst type-option-syntax-p)
                                   (smt-type smt-type-p))
    :returns (smt-type smt-type-p)
    :measure (len type-opt-lst)
    :hints (("Goal" :in-theory (enable type-option-syntax-fix)))
    (b* ((type-opt-lst (type-option-syntax-fix type-opt-lst))
         (smt-type (smt-type-fix smt-type))
         ((unless (consp type-opt-lst)) smt-type)
         ((list* option content rest) type-opt-lst)
         (new-smt-type
          (case option
            (:functions
             (change-smt-type smt-type
                              :functions (construct-type-functions content)))
            (:fixer
             (change-smt-type smt-type
                              :fixer (construct-function content)))
            (:subtypes
             (change-smt-type smt-type
                              :subtypes (construct-sub/supertype-list content)))
            (:supertypes
             (change-smt-type smt-type
                              :supertypes (construct-sub/supertype-list content))))))
      (construct-type-option-lst rest new-smt-type)))

  (define construct-type ((type type-syntax-p))
    :returns (new-type smt-type-p)
    :guard-hints (("Goal" :in-theory (enable type-syntax-fix type-syntax-p)))
    (b* ((type (type-syntax-fix type))
         ((cons name type-opt-lst) type))
      (construct-type-option-lst type-opt-lst (make-smt-type :recognizer name))))

  (define merge-types ((content type-list-syntax-p)
                       (hint smtlink-hint-p))
    :returns (new-hint smtlink-hint-p)
    :measure (len content)
    :short "Merging type hints into smt-hint."
    (b* ((hint (smtlink-hint-fix hint))
         (content (type-list-syntax-fix content))
         ((unless (consp content)) hint)
         ((cons first rest) content)
         ((smtlink-hint h) hint)
         (new-type-lst (cons (construct-type first) h.types))
         (new-hint (change-smtlink-hint h :types new-type-lst)))
      (merge-types rest new-hint)))

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
                     (:types (merge-types second hint))
                     (:int-to-ratp (set-int-to-rat second hint))
                     (:under-inductionp (set-under-induct second hint))
                     (:smt-fname (set-fname second hint))
                     (:rm-file (set-rm-file second hint))
                     (:smt-dir (set-smt-dir second hint))
                     (:global-hint (set-global-hint second hint))
                     (:wrld-fn-len (set-wrld-fn-len second hint))
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
         (- (cw "user-hint: ~q0" user-hint))
         (- (cw "the-hint: ~q0" the-hint))
         (- (cw "combined-hint: ~q0" combined-hint))
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

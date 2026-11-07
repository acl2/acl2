;; Copyright (C) 2026, University of British Columbia
;; Written by Chris Chen
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

;;
;; This book defines a clause processor that extracts typing
;; information from unconditional, monomorphically-typed typed terms.

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "oslib/tempfile" :dir :system)
(include-book "kestrel/file-io-light/write-objects-to-file-bang" :dir :system)
(include-book "centaur/misc/tshell" :dir :system)
(include-book "std/alists/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "xdoc/top" :dir :system)

(include-book "../config")
(include-book "../verified/basics")
(include-book "../verified/hint-interface")
(include-book "../verified/smt-judgement")
(include-book "../verified/tterm")
(include-book "../verified/term-rewrite")

(set-state-ok t)
(set-induction-depth-limit 3)
(make-event
 (pprogn (set-warnings-as-errors t '("Use") state)
         (value '(value-triple nil))))

(defconst *SMT-Constants*
  (list (cons 'nil 'acl2::|false|)
        (cons 't 'acl2::|true|)))

(defconst *SMT-Sorts*
  (list (cons 'booleanp 'acl2::|Bool|)
        (cons 'integerp 'acl2::|Int|)
        (cons 'rationalp 'acl2::|Real|)
        (cons 'int-sym-array-p '(acl2::|Array| acl2::|Int| acl2::int-sym-consp))
        (cons 'nat-sym-array-p '(acl2::|Array| acl2::natp acl2::nat-sym-consp))))

;; First pass: only functions that occur in translated terms
(defconst *SMT-Core*
  (list (cons 'not 'acl2::|not|)
        (cons 'implies 'acl2::|=>|)
        (cons 'xor 'acl2::|xor|)
        (cons '= 'acl2::|=|)
        (cons 'equal 'acl2::|=|)
        (cons 'if 'acl2::|ite|)))

;; Only functions that occur in translated terms, so no division, etc.
(defconst *SMT-Reals*
  (list (cons 'rational-- 'acl2::|-|)
        (cons 'rational-+ 'acl2::|+|)
        (cons 'rational-* 'acl2::|*|)
        (cons 'rational-< 'acl2::|<|)
        (cons 'rational-/ 'acl2::|/|)
        (cons 'int-to-rat 'acl2::|to_real|)))

;; Partial support, no exponents, division, or modulus
(defconst *SMT-Ints*
  (list (cons 'integer-- 'acl2::|-|)
        (cons 'integer-+ 'acl2::|+|)
        (cons 'integer-* 'acl2::|*|)
        (cons 'integer-< 'acl2::|<|)))

;; Arrays
(defconst *SMT-ArraysEx*
  (list (cons 'int-sym-array-select 'acl2::|select|)
        (cons 'int-sym-array-store 'acl2::|store|)
        (cons 'nat-sym-array-select 'acl2::|select|)
        (cons 'nat-sym-array-store 'acl2::|store|)))

(defconst *SMT-QF_UFNRA*
  (append *SMT-Core*
          *SMT-Reals*))

(defconst *SMT-AUFNIRA*
  (append *SMT-Core*
          *SMT-Ints*
          *SMT-Reals*
          *SMT-ArraysEx*))

(define smt-sym-declp (x)
  :enabled t
  :returns (rv booleanp)
  (or (symbolp x)
      (symbol-listp x)))

(defsection smt-mapping

  (define normalize-symbol (sym)
    :returns (rv symbolp)
    (b* ((sym (symbol-fix sym))
         ((if (equal (acl2::symbol-package-name sym) "ACL2")) sym))
      (intern$ (symbol-name sym) "ACL2")))

  (std::defprojection normalize-symbol-list ((x symbol-listp))
    :returns (rv symbol-listp)
    (normalize-symbol x))

  (define acl2->smt-sym ((acl2-sym symbolp)
                         (sym-map alistp)
                         (err-sym symbolp))
    :returns (rv smt-sym-declp)
    (b* ((acl2-sym (symbol-fix acl2-sym))
         (sym-map (acl2::alist-fix sym-map))
         (err-sym (symbol-fix err-sym))
         (mapping (assoc acl2-sym sym-map))
         (smt-sym (if (null mapping)
                      acl2-sym
                    (cdr mapping)))
         ((unless (smt-sym-declp smt-sym)) err-sym))
      ;; I don't like this. Because we use the object writer, package
      ;; names get are emitted into the smt-lib script which chokes
      ;; the solver's parser (in Z3 at least). This assumes that the
      ;; user is calling smtlink from the "ACL2" package, which is
      ;; kinda gross.
      (if (symbolp smt-sym)
          (normalize-symbol smt-sym)
        (normalize-symbol-list smt-sym)))
    ///
    (fty::deffixequiv acl2->smt-sym))

  (define acl2->smt-constant ((acl2-const symbolp))
    :returns (rv smt-sym-declp)
    (acl2->smt-sym acl2-const
                   *SMT-Constants*
                   '|bad-constant|))

  (define acl2->smt-fn ((acl2-fn symbolp))
    :returns (rv smt-sym-declp)
    (acl2->smt-sym acl2-fn
                   *SMT-AUFNIRA*
                   '|bad-function|))

  (define acl2->smt-sort ((acl2-sort symbolp))
    :returns (rv smt-sym-declp)
    (acl2->smt-sym acl2-sort
                   *SMT-Sorts*
                   '|bad-sort|))

  (std::defprojection acl2->smt-sort-list ((x symbol-listp))
    (acl2->smt-sort x))
  )

(defsection smt-preamble
  (std::defprojection var-judgements->sorts ((x var-judgement-list-p))
    :returns (rv symbol-listp)
    (var-judgement->judgement x))

  (define fn-judgement->sorts ((f fn-judgement-p))
    :returns (rv symbol-listp)
    (b* ((f (fn-judgement-fix f)))
      (cons (fn-judgement->range f)
            (fn-judgement->domain f)))
    ///
    (fty::deffixequiv fn-judgement->sorts))

  (define fn-judgements->sorts ((fs fn-judgement-list-p))
    :returns (rv symbol-listp)
    :measure (acl2-count (fn-judgement-list-fix fs))
    (b* ((fs (fn-judgement-list-fix fs)))
      (if (consp fs)
          (append (fn-judgement->sorts (car fs))
                  (fn-judgements->sorts (cdr fs)))
        nil))
    ///
    (fty::deffixequiv fn-judgements->sorts))

  (define declare-sort ((x symbolp))
    (b* ((x (symbol-fix x)))
      `(acl2::|declare-sort| ,(normalize-symbol x) 0))
    ///
    (fty::deffixequiv declare-sort))

  (std::defprojection declare-sort-list ((x symbol-listp))
    (declare-sort x))

  (define smt-judgement->declare-sort-list ((s smt-judgement-p))
    :returns (rv true-listp)
    (b* ((s (smt-judgement-fix s))
         (vs (smt-judgement->vars s))
         (fs (smt-judgement->fns s))
         (var-sorts (var-judgements->sorts vs))
         (fn-sorts (fn-judgements->sorts fs))
         (smt-sorts (std::alist-keys *SMT-Sorts*))
         ((unless (symbol-listp smt-sorts)) nil)
         (all-sorts (append var-sorts fn-sorts))
         ((unless (symbol-listp all-sorts)) nil)
         (ui-sorts (set-difference$ (remove-duplicates all-sorts)
                                    smt-sorts))
         ((unless (symbol-listp ui-sorts)) nil))
      (declare-sort-list ui-sorts))
    ///
    (fty::deffixequiv smt-judgement->declare-sort-list))

  (define fn-judgements->declare-fun-list ((fs fn-judgement-list-p))
    :returns (rv true-listp)
    :measure (acl2-count (fn-judgement-list-fix fs))
    (b* ((fs (fn-judgement-list-fix fs))
         (theory-fns (std::alist-keys *SMT-AUFNIRA*))
         ((unless (consp fs)) nil)
         (j (car fs))
         (name (fn-judgement->name j)))
      (if (member name theory-fns)
          (fn-judgements->declare-fun-list (cdr fs))
        (b* ((domain (fn-judgement->domain j))
             (range (fn-judgement->range j))
             (term `(acl2::|declare-fun| ,(normalize-symbol name)
                                   ,(acl2->smt-sort-list domain)
                                   ,(acl2->smt-sort range)))
             ((unless (pseudo-termp term)) nil))
          (cons term
                (fn-judgements->declare-fun-list (cdr fs))))))
    ///
    (fty::deffixequiv fn-judgements->declare-fun-list))

  (define smt-judgement->declare-fun-list ((s smt-judgement-p))
    :returns (rv true-listp)
    (b* ((s (smt-judgement-fix s))
         (fs (smt-judgement->fns s)))
      (fn-judgements->declare-fun-list fs))
    ///
    (fty::deffixequiv smt-judgement->declare-fun-list))

  (define var-judgement->declare-const ((v var-judgement-p))
    (b* ((v (var-judgement-fix v))
         (name (var-judgement->name v))
         (acl2-sort (var-judgement->judgement v))
         (smt-sort (acl2->smt-sort acl2-sort)))
      `(acl2::|declare-const| ,(normalize-symbol name) ,smt-sort))
    ///
    (fty::deffixequiv var-judgement->declare-const))

  (define var-judgements->declare-const-list ((vs var-judgement-list-p))
    :returns (rv true-listp)
    :measure (acl2-count (var-judgement-list-fix vs))
    (b* ((vs (var-judgement-list-fix vs)))
      (if (consp vs)
          (cons (var-judgement->declare-const (car vs))
                (var-judgements->declare-const-list (cdr vs)))
        nil))
    ///
    (fty::deffixequiv var-judgements->declare-const-list))

  (define smt-judgement->preamble ((s smt-judgement-p))
    :returns (rv true-listp)
    (b* ((s (smt-judgement-fix s))
         (vs (smt-judgement->vars s)))
      (cons `(acl2::|set-logic| acl2::aufnira)
            (append (smt-judgement->declare-sort-list s)
                    (smt-judgement->declare-fun-list s)
                    (var-judgements->declare-const-list vs))))
    ///
    (fty::deffixequiv smt-judgement->preamble))
  )

(defsection smt-expr

  (define emit-number ((x rationalp))
    (b* ((x (rfix x)))
      (if (integerp x)
          (if (< x 0)
              `(- ,(- x))
            x)
        `(/ ,(emit-number (numerator x))
            ,(emit-number (denominator x)))))
    ///
    (fty::deffixequiv emit-number))

  (define emit-constant (x)
    (cond
     ((rationalp x) (emit-number x))
     ((symbolp x) (acl2->smt-constant x))
     (t '|bad-constant|)))

  (defines smt-expr
    :verify-guards nil
    :well-founded-relation l<

    (define smt-expr-list ((es pseudo-term-listp))
      :measure (list (acl2-count es) 1 0)
      :flag list
      :returns (rv true-listp)
      (b* ((es (pseudo-term-list-fix es)))
        (if (consp es)
            (cons (smt-expr (car es))
                  (smt-expr-list (cdr es)))
          nil)))

    (define smt-expr ((e pseudo-termp))
      :measure (list (acl2-count e) 2 0)
      :flag expr
      (b* ((e (pseudo-term-fix e)))
        (case-match e
          (('quote const) (emit-constant const))
          ((fn . args) (b* ((fn (symbol-fix fn))
                            (args (pseudo-term-list-fix args))
                            (smt-fn (acl2->smt-fn fn))
                            (smt-args (smt-expr-list args))
                            ((if (equal smt-fn 'quote))
                             '|bad-quote|)
                            ((if (member 'quote smt-args))
                             '|bad-quote|))
                         `(,smt-fn ,@smt-args)))
          (& (if (and (symbolp e)
                      (not (equal e 'quote)))
                 e
               '|bad-expr|))))
      ///
      (verify-guards smt-expr)
      (fty::deffixequiv-mutual smt-expr))
    )

  (define smt-assert-negation ((expr pseudo-termp))
    `((acl2::|assert| (acl2::|not| ,(smt-expr expr)))
      (acl2::|check-sat|)))

  )

(defsection SMT-smtlib-trusted
  :parents (verified)

  (program)

  (define SMT-expr-simplify-hint (cl kwd-alist state)
    :guard-debug t
    :parents (SMT-computed-hints)
    :short "@('SMT::SMT-expr-simplify-hint') WRITE SOMETHING."
    (b* (((unless (and (pseudo-term-listp cl)
                       (consp kwd-alist)
                       (consp (cdr kwd-alist))
                       (consp (cadr kwd-alist))
                       (= (len (cadr kwd-alist))
                          4)
                       (state-p state)))
          (prog2$ (cw "SMT-expr-simplify-hint: preconditions not met")
                  (value nil)))
         ((list* cp-kwd (list next-cp & q-smt-hint &) kwd-alist-tail) kwd-alist)
         ((unless (equal cp-kwd :clause-processor))
          (prog2$ (cw "SMT-expr-simplify-hint: missing clause processor in kwd-alist: ~x0~%"
                      kwd-alist)
                  (value nil)))
         ((unless (and (quotep q-smt-hint)
                       (smtlink-hint-p (unquote q-smt-hint))))
          (prog2$ (cw "not quoted smtlink-hint-p: ~x0" q-smt-hint)
                  (value nil)))
         (smt-hint (unquote q-smt-hint))
         (goal (disjoin cl))
         ((mv fail smt-j) (smt-judgement-clause->judgement goal))
         ((if fail) (prog2$ (cw "not a smt-judgement-clause: ~x0~%" smt-j)
                            (value nil)))
         (j-expr (smt-judgement->expr smt-j))
         (expr (smt-judgement-clause->expr goal))
         ((mv fail new-expr state)
          (rewrite$-helper expr
                           (list j-expr)
                           '(theory 'minimal-theory)
                           state))
         ((if fail) (value nil)))
      (value `(:computed-hint-replacement ((SMT-computed-hint clause))
               :clause-processor (,next-cp clause ',(cons smt-hint new-expr) state)
               ,@kwd-alist-tail))))

  (logic)

  (define check-sat-error ((err stringp)
                           (msgs string-listp)
                           state)
    :returns (mv (err booleanp)
                 (rv symbolp)
                 state)
    (b* ((err (str-fix err))
         ((unless (mbt (string-listp msgs)))
          (mv t :error state)))
      (prog2$ (cw "SMTLINK Error [~@0]:~%~*1"
                  err
                  `("no additional info.~%"
                     "~@*~%~%"
                     "~@*~%"
                     "~@*~%"
                     ,msgs))
              (mv t :error state))))

  (defttag smtlink-smtlib)

  (define check-sat ((script true-listp)
                     (solver-cmd stringp)
                     state)
    :returns (mv (err booleanp)
                 (rv symbolp)
                 state)
    :guard-debug t
    (b* (((mv file-name state) (oslib::tempfile "smtlink" state))
         ((if (null file-name))
          (check-sat-error "tempfile-name-generation" nil state))
         ((unless (member (get-serialize-character state)
                          '(nil #\Y #\Z)))
          (check-sat-error "assert-serialize-character" nil state))
         (- (cw "writing ~x0 to ~x1~%" script file-name))
         ((mv erp state)
          (acl2::write-objects-to-file! script
                                        file-name
                                        'smtlink
                                        state))
         ((unless (null erp))
          (check-sat-error "tempfile-io" nil state))
         (solver-cmd (str-fix solver-cmd))
         (cmdstr (concatenate 'string solver-cmd " -smt2 " file-name))
         ((mv status lines state) (tshell-call cmdstr :print nil :save t))
         ((unless (= status 0))
          (check-sat-error "solver" lines state)))
      (if (equal lines (list "unsat"))
          (mv nil :unsat state)
        (mv nil :unknown state))))

  (define smtlib-trusted-cp ((cl pseudo-term-listp)
                             (hint t)
                             state)
    :guard-debug t
    (b* (((unless (pseudo-term-listp cl)) (mv t nil state))
         ((unless (consp hint)) (mv t nil state))
         ((cons smt-hint simp-expr) hint)
         ((unless (smtlink-hint-p smt-hint)) (mv t nil state))
         (smt-config (smt-config-fix
                       (smtlink-hint->configurations smt-hint)))
         (smtlink-config (smtlink-config-fix
                           (smt-config->smt-cnf smt-config)))
         (solver-cmd (smtlink-config->smt-cmd smtlink-config))
         ((unless (pseudo-termp simp-expr)) (mv t nil state))
         (goal (disjoin cl))
         ((mv fail smt-j) (smt-judgement-clause->judgement goal))
         ((if fail) (mv t nil state))
         ;; the original (unsimplified) goal expr
         (expr (smt-judgement-clause->expr goal))
         ;; SMT-LIB script
         (smt-script (append (smt-judgement->preamble smt-j)
                             (smt-assert-negation simp-expr)))
         ((mv fail solver-result state)
          (check-sat smt-script solver-cmd state))
         ((if fail) (mv t nil state))
         ((unless (equal solver-result :unsat))
          (value (list nil)))
         ;; Side condition
         (side-condition (implies-expr (smt-judgement->expr smt-j)
                                       (equal-expr
                                         expr
                                         simp-expr)))
         (side-hint `(acl2::hint-wrapper
                       '(:in-theory (theory 'minimal-theory))))
         (hinted-goal2 `((not ,side-hint)
                         ,side-condition)))
      (value (list hinted-goal2))))

  (define-trusted-clause-processor
    smtlib-trusted-cp
    nil
    :ttag :smtlink-smtlib)

  )

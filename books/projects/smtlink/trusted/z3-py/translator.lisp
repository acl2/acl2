;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (13th March, 2014)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)
;; for lambda expression
(include-book "kestrel/utilities/terms" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)

(include-book "./translate-fty")

;; (defsection SMT-translator
;;   :parents (z3-py)
;;   :short "SMT-translator does the LISP to Python translation."

  (define SMT-numberp ((sym))
    (declare (xargs :guard t))
    :returns (is? booleanp)
    (if (or (rationalp sym) (integerp sym) (real/rationalp sym))
        t nil))

  (define SMT-number-fix ((num SMT-numberp))
    :returns (fixed SMT-numberp)
    (mbe :logic (if (SMT-numberp num) num 0)
         :exec num))

  (local (in-theory (enable SMT-number-fix)))
  (deffixtype SMT-number
    :fix SMT-number-fix
    :pred SMT-numberp
    :equiv SMT-number-equiv
    :define t)

  (define translate-function ((opr symbolp))
    :returns (mv (translated stringp)
                 (nargs natp))
    (b* ((fn-sig (cdr (assoc-equal opr *SMT-functions*)))
         ((if (equal fn-sig nil))
          (prog2$ (er hard? 'SMT-translator=>translate-function "Not a basic SMT function: ~q0" opr) (mv "" 0)))
         ((cons translated-fn nargs) fn-sig))
      (mv translated-fn nargs)))

  (defthm wordp-of-translate-function
    (b* (((mv fn &) (translate-function x)))
      (wordp fn))
    :hints (("Goal" :in-theory (enable wordp))))

  (local (in-theory (enable SMT-numberp characterp)))
  (define translate-number ((num SMT-numberp))
    :returns (translated paragraphp :hints (("Goal" :in-theory (enable wordp paragraphp))))
    :guard-debug t
    (b* ((num (SMT-number-fix num))
         ((if (and (rationalp num) (not (integerp num))))
          `("_SMT_.Qx(" ,(numerator num) "," ,(denominator num) ")")))
      (list num)))

  (defprod te-args
    ((expr-lst pseudo-term-listp :default nil)
     (fn-lst func-alistp :default nil)
     (uninterpreted-lst symbol-listp :default nil)
     (fty-info fty-info-alist-p)
     (symbol-index natp) ;; how many random symbols there are
     (symbol-list string-listp) ;; translated symbols in the symbol enumeration
     ))

  (define map-translated-actuals ((actuals paragraphp))
    :returns (mapped paragraphp
                     :hints (("Goal" :in-theory (enable paragraphp paragraph-fix))))
    (b* ((actuals (paragraph-fix actuals))
         ((unless (consp actuals)) actuals)
         ((unless (consp (cdr actuals))) actuals)
         ((cons first rest) actuals)
         (mapped-rest (map-translated-actuals rest)))
      (cons first (cons #\, mapped-rest))))

  (define translate-fty-special ((fn-call symbolp)
                                 (fn-actuals pseudo-term-listp)
                                 (fty-info fty-info-alist-p))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (enable wordp))))
    :guard-hints (("Goal" :in-theory (e/d (string-or-symbol-p) ())))
    (b* ((fn-call (symbol-fix fn-call))
         (fn-actuals (pseudo-term-list-fix fn-actuals))
         (fty-info (fty-info-alist-fix fty-info))
         ;; dealing with magic-fix
         ((if (and (or (equal fn-call 'CDR)
                       (equal fn-call 'CONSP))
                   (and (car fn-actuals) (null (cdr fn-actuals)))
                   (consp (car fn-actuals))
                   (equal (caar fn-actuals) 'SMT::MAGIC-FIX)
                   (consp (cadar fn-actuals))
                   (equal (car (cadar fn-actuals)) 'QUOTE)
                   (stringp (cadr (cadar fn-actuals)))))
          (list (concatenate 'string (cadr (cadar fn-actuals)) "_"
                             (str::downcase-string (translate-symbol fn-call)))))
         (fixed
          (cond ((or (equal fn-call 'CAR)
                     (equal fn-call 'CDR)
                     (equal fn-call 'CONSP))
                 (b* (((unless (and (car fn-actuals) (null (cdr fn-actuals))))
                       (er hard? 'SMT-translator=>translate-fty-special "Wrong ~
         number of arguments for ~p0: ~p1~%" fn-call fn-actuals)))
                   (car fn-actuals)))
                ((or (equal fn-call 'CONS)
                     (equal fn-call 'ASSOC-EQUAL))
                 (b* (((unless (and (cadr fn-actuals)
                                    (null (cddr fn-actuals))))
                       (er hard? 'SMT-translator=>translate-fty-special "Wrong ~
         number of arguments for ~p0: ~p1~%" fn-call fn-actuals)))
                   (cadr fn-actuals)))
                ((equal fn-call 'ACONS)
                 (b* (((unless (and (caddr fn-actuals)
                                    (null (cddr fn-actuals))))
                       (er hard? 'SMT-translator=>translate-fty-special "Wrong ~
         number of arguments for ~p0: ~p1~%" fn-call fn-actuals)))
                   (caddr fn-actuals)))
                (t
                 (er hard? 'SMT-translator=>translate-fty-special "Impossible path:
                                 ~q0" fn-call))))
         ((unless (and (consp fixed) (car fixed) (symbolp (car fixed))))
          (er hard? 'SMT-translator=>translate-fty-special "Not fixed:
                                 ~q0" fixed))
         (fixing? (fixing-of-flextype (car fixed) fty-info))
         ((unless fixing?)
          (er hard? 'SMT-translator=>translate-fty-special "Not fixed:
                                 ~q0" (car fixed))))
      ;; acons and assoc are treated differently because they are not class
      ;; methods in Z3 either
      (if (or (equal fn-call 'ACONS)
              (equal fn-call 'ASSOC-EQUAL)
              (equal fn-call 'CONSP))
          (list (concatenate 'string (translate-symbol fixing?) "_"
                             (str::downcase-string (translate-symbol fn-call))))
        (list (concatenate 'string (translate-symbol fixing?)  "."
                           (str::downcase-string (translate-symbol fn-call)))))))

  (define translate-field-accessor ((fty-name symbolp)
                                    (fn-call symbolp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (enable paragraphp wordp))))
    :guard-hints (("Goal" :in-theory (e/d (string-or-symbol-p)
                                          ())))
    (b* ((fty-name (symbol-fix fty-name))
         (fn-call (symbol-fix fn-call))
         (fty-name-str (symbol-name fty-name))
         (fn-call-str (symbol-name fn-call))
         ((unless (<= (+ 2 (length fty-name-str)) (length fn-call-str)))
          (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong1: ~p0 and ~p1" fty-name-str fn-call-str))
         (pos-prefix (search fty-name-str fn-call-str :test 'equal))
         ((unless (equal pos-prefix 0))
          (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong2: ~p0 and ~p1" fty-name-str fn-call-str))
         (pos1 (length fty-name-str))
         (pos-infix (search "->" fn-call-str :test 'equal))
         ((unless (equal pos1 pos-infix))
          (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong3: ~p0 and ~p1" fty-name-str fn-call-str))
         (pos-suffix (+ 2 pos1))
         (pos2 (search "$INLINE" fn-call-str :from-end t :test 'equal))
         ((unless (and (natp pos2)
                       (<= pos-suffix pos2)
                       (<= pos2 (length fn-call-str))))
          (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong4: ~p0 and ~p1" fty-name-str fn-call-str))
         (suffix (subseq fn-call-str pos-suffix pos2))
         ((unless (stringp suffix))
          (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong5: ~p0 and ~p1" fty-name-str fn-call-str)))
      (list (concatenate 'string (lisp-to-python-names fty-name-str)  "."
                         (lisp-to-python-names suffix)))))

  (define translate-fty ((fn-call symbolp)
                         (fn-actuals pseudo-term-listp)
                         (fty-info fty-info-alist-p))
    :returns (translated paragraphp)
    :guard (or (fncall-of-flextype-special fn-call)
               (assoc-equal fn-call fty-info))
    :guard-hints (("Goal" :in-theory (e/d (string-or-symbol-p) ())))
    (b* ((fn-call (symbol-fix fn-call))
         (special? (fncall-of-flextype-special fn-call))
         ((if special?)
          (translate-fty-special fn-call fn-actuals fty-info))
         (item (assoc-equal fn-call fty-info))
         (fty-name (fty-info->name (cdr item)))
         (fty-type (fty-info->type (cdr item)))
         ((unless (or (equal fty-type :field)
                      (equal fty-type :constructor)))
          (er hard? 'SMT-translator=>translate-fty "Unexpected fty function ~
                         found: ~p0 of ~p1~%" fn-call fty-type))
         ((if (equal fty-type :constructor))
          (list (concatenate 'string (translate-symbol fn-call)))))
      (translate-field-accessor fty-name fn-call)))

  (define generate-symbol-enumeration ((symbol-index natp))
    :returns (new-sym stringp)
    (b* ((symbol-index (nfix symbol-index))
         (new-sym (concatenate 'string "gensym_" (natstr symbol-index))))
      new-sym))

  (define translate-quote ((expr t))
    :returns (translated-quote paragraphp
                               :hints (("Goal" :in-theory (e/d (paragraphp wordp)
                                                               ()))))
    (b* (((unless (or (symbolp expr)
                      (SMT-numberp expr)
                      (booleanp expr)))
          (er hard? 'SMT-translator=>translate-expression "Atom not ~
                       supported: ~q0" expr)))
      (cond ((booleanp expr)
             (translate-bool expr nil))
            ((SMT-numberp expr)
             (translate-number expr))
            (t (concatenate 'string "Symbol." (translate-symbol expr))))))

  (define translate-expression ((args te-args-p))
    :returns (mv (translated paragraphp
                             :hints (("Goal" :in-theory (enable paragraphp
                                                                wordp))))
                 (uninterpreted symbol-listp)
                 (symbols string-listp)
                 (symbol-index natp))
    :measure (acl2-count (te-args->expr-lst args))
    :hints (("Goal" :in-theory (enable pseudo-lambdap)))
    :verify-guards nil
    (b* ((args (te-args-fix args))
         ((te-args a) args)
         ((unless (consp a.expr-lst))
          (mv nil a.uninterpreted-lst a.symbol-list a.symbol-index))
         ((cons expr rest) a.expr-lst)
         ((mv translated-rest uninterpreted-rest symbols-rest symbol-index-rest)
          (translate-expression (change-te-args a :expr-lst rest)))
         ;; If first term is an symbolp, should be a variable name
         ;; translate the variable then recurse on the rest of the list
         ((if (symbolp expr))
          (mv (cons (translate-symbol expr) translated-rest)
              uninterpreted-rest
              symbols-rest
              symbol-index-rest))
         ;; If car of term is 'quote, some constants
         ((if (equal (car expr) 'quote))
          (b* ((translated-quote (translate-quote (cadr expr))))
            (mv (cons translated-quote translated-rest)
                uninterpreted-rest
                (if (symbolp (cadr expr))
                    (cons translated-quote symbols-rest)
                  symbols-rest)
                symbol-index-rest)))
         ;; The first term is now a function call:
         ;; Either a lambda or a symbol
         ((cons fn-call fn-actuals) expr)

         ;; If fn-call is a lambda
         ((if (pseudo-lambdap fn-call))
          (b* ((formals (lambda-formals fn-call))
               (body (lambda-body fn-call))
               (lambda-sym (car fn-call))
               ((mv translated-lambda &) (translate-function lambda-sym))
               (translated-formals (translate-symbol-lst formals))
               ((mv translated-body uninterpreted-1 symbol-list-1 symbol-index-1)
                (translate-expression
                 (change-te-args a :expr-lst (list body)
                                 :uninterpreted-lst uninterpreted-rest
                                 :symbol-list symbols-rest
                                 :symbol-index symbol-index-rest)))
               ((mv translated-actuals uninterpreted-2 symbol-list-2 symbol-index-2)
                (translate-expression
                 (change-te-args a :expr-lst fn-actuals
                                 :uninterpreted-lst uninterpreted-1
                                 :symbol-list symbol-list-1
                                 :symbol-index symbol-index-1)))
               (translated-lambda-whole
                `(#\( ,translated-lambda #\Space ,translated-formals #\:
                  ,translated-body #\)
                  #\( ,(map-translated-actuals translated-actuals) #\))))
            (mv (cons translated-lambda-whole translated-rest)
                uninterpreted-2
                symbol-list-2
                symbol-index-2)))

         ;; if the fixing function is symbol-fix, invent a new symbol
         ;; enumeration and increase the symbol-index by 1
         ((if (equal fn-call 'SYMBOL-FIX))
          (b* (((mv translated-actuals uninterpreted-1 symbol-list-1 symbol-index-1)
                (translate-expression
                 (change-te-args a :expr-lst fn-actuals
                                 :uninterpreted-lst uninterpreted-rest
                                 :symbol-list symbols-rest
                                 :symbol-index symbol-index-rest))))
            (mv (cons translated-actuals translated-rest)
                uninterpreted-1
                (cons (generate-symbol-enumeration symbol-index-1)
                      symbol-list-1)
                (1+ symbol-index-1))))

         ;; If fn-call is smt::magic-fix, this function is used by the user.
         ;; Therefore probably in a different package?
         ((if (equal fn-call 'SMT::MAGIC-FIX))
          (b* (((unless (and (consp fn-actuals)
                             (consp (cdr fn-actuals))
                             (null (cddr fn-actuals))))
                (mv (er hard? 'SMT-translator=>translate-expression "Wrong ~
         number of arguments for magic-fix function: ~q0" expr)
                    nil nil 0))
               ((mv translated-actuals uninterpreted-1 symbol-list-1 symbol-index-1)
                (translate-expression
                 (change-te-args a
                                 :expr-lst (cdr fn-actuals)
                                 :uninterpreted-lst uninterpreted-rest
                                 :symbol-list symbols-rest
                                 :symbol-index symbol-index-rest))))
            (mv (cons translated-actuals translated-rest)
                uninterpreted-1
                symbol-list-1
                symbol-index-1)))

         ;; If fn-call is a fty fixing call
         (fixing? (fixing-of-flextype fn-call a.fty-info))
         ((if fixing?)
          (b* (((unless (and (consp fn-actuals) (null (cdr fn-actuals))))
                (mv (er hard? 'SMT-translator=>translate-expression "Wrong ~
         number of arguments for a fixing function: ~q0" expr)
                    nil nil 0))
               (fixed (car fn-actuals))
               ;; special case when it's a fixing on nil
               ((if (and (consp fixed)
                         (equal (car fixed) 'quote)
                         (symbolp (cadr expr))))
                (mv (cons (translate-bool (cadr fixed) fixing?)
                          translated-rest)
                    uninterpreted-rest
                    symbols-rest
                    symbol-index-rest))
               ((mv translated-actuals uninterpreted-1 symbol-list-1 symbol-index-1)
                (translate-expression
                 (change-te-args a
                                 :expr-lst fn-actuals
                                 :uninterpreted-lst uninterpreted-rest
                                 :symbol-list symbols-rest
                                 :symbol-index symbol-index-rest)))
               ;; if it's an option type fixing function, and it's not nil
               ((if (fixing-of-flextype-option fn-call a.fty-info))
                (mv (cons `(,fixing? ".val(" ,translated-actuals ")")
                          translated-rest)
                    uninterpreted-1
                    symbol-list-1
                    symbol-index-1)))
            (mv (cons translated-actuals translated-rest)
                uninterpreted-1
                symbol-list-1
                symbol-index-1)))

         ;; If fn-call is a fty call, but not a fixing function
         (fty? (fncall-of-flextype fn-call a.fty-info))
         ((if fty?)
          (b* ((translated-fn-call
                (translate-fty fn-call fn-actuals a.fty-info))
               ((mv translated-actuals uninterpreted-1 symbol-list-1 symbol-index-1)
                (translate-expression
                 (change-te-args a
                                 :expr-lst fn-actuals
                                 :uninterpreted-lst uninterpreted-rest
                                 :symbol-list symbols-rest
                                 :symbol-index symbol-index-rest)))
               (translated-expr
                `(,@translated-fn-call
                  #\( ,(map-translated-actuals translated-actuals) #\) )))
            (mv (cons translated-expr translated-rest)
                uninterpreted-1
                symbol-list-1
                symbol-index-1)))

         ;; If fn-call is neither a lambda expression nor a function call
         ((unless (mbt (symbolp fn-call))) (mv nil nil nil 0))
         ;; Now, fn-call should be treated as an uninterpreted function
         (fn (hons-get fn-call a.fn-lst))
         ((if fn)
          (b* (;; ((func f) (cdr fn))
               ;; ((if (not f.uninterpreted))
               ;;  (mv (er hard? 'SMT-translator=>translate-expression "Not a basic SMT function: ~q0" fn-call) nil))
               ((mv translated-actuals uninterpreted-1 symbol-list-1 symbol-index-1)
                (translate-expression
                 (change-te-args a :expr-lst fn-actuals
                                 :uninterpreted-lst uninterpreted-rest
                                 :symbol-list symbols-rest
                                 :symbol-index symbol-index-rest)))
               (translated-fn-call
                `(,(translate-symbol fn-call)
                  #\( ,(map-translated-actuals translated-actuals) #\) )))
            (mv (cons translated-fn-call translated-rest)
                (cons fn-call uninterpreted-1)
                symbol-list-1
                symbol-index-1)))
         ;; If fn-call is not an uninterpreted function, then it has to be a
         ;; basic function
         ((mv fn nargs) (translate-function fn-call))
         ((if (zp nargs))
          (mv (cons `( ,fn #\( #\) ) translated-rest)
              uninterpreted-rest
              symbols-rest
              symbol-index-rest))
         ((mv translated-actuals uninterpreted-1 symbol-list-1 symbol-index-1)
          (translate-expression
           (change-te-args a :expr-lst fn-actuals
                           :uninterpreted-lst uninterpreted-rest
                           :symbol-list symbols-rest
                           :symbol-index symbol-index-rest))))
      (mv (cons `( ,fn #\( ,(map-translated-actuals translated-actuals) #\) )
                translated-rest)
          uninterpreted-1
          symbol-list-1
          symbol-index-1)))

  (encapsulate ()
    (local (defthm lemma-1
             (implies (te-args-p x)
                      (pseudo-term-listp (te-args->expr-lst x)))))
    (local (defthm lemma-2
             (implies (and (pseudo-term-listp x) (consp x))
                      (pseudo-term-listp (cdr x)))))
    (defthm pseudo-term-listp-of-cdr-of-te-args->expr-lst
      (implies (and (te-args-p x)
                    (consp (te-args->expr-lst x)))
               (pseudo-term-listp (cdr (te-args->expr-lst x))))
      :hints (("Goal" :in-theory (enable pseudo-term-listp))))

    (local (defthm lemma-3
             (implies (and (pseudo-term-listp x) (consp x))
                      (pseudo-termp (car x)))))

    (local (defthm lemma-4
             (implies (and (pseudo-termp x) (not (symbolp x)))
                      (consp x))))

    (defthm consp-of-car-of-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args)))))
               (consp (car (te-args->expr-lst args)))))

    (local (defthm lemma-5
             (implies (and (pseudo-term-listp x) (consp x)
                           (not (symbolp (car x))) (equal (caar x) 'quote))
                      (consp (cdar x)))))

    (defthm not-cdr-of-car-of-quote-ex-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (equal (car (car (te-args->expr-lst args)))
                           'quote)
                    (not (consp (cdr (car (te-args->expr-lst args))))))
               (not (cdr (car (te-args->expr-lst args))))))

    (local (defthm lemma-6
             (implies (and (pseudo-term-listp x) (consp x)
                           (pseudo-lambdap (caar x)))
                      (symbolp (caaar x)))))

    (defthm symbolp-of-caaar-of-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (equal (car (car (te-args->expr-lst args)))
                                'quote))
                    (pseudo-lambdap (car (car (te-args->expr-lst args)))))
               (symbolp (car (car (car (te-args->expr-lst args)))))))

    (local (defthm lemma-7
             (implies (and (pseudo-term-listp x) (consp x)
                           (not (symbolp (car x))) (not (pseudo-lambdap (caar x))))
                      (symbolp (caar x)))
             :hints (("Goal" :in-theory (enable pseudo-termp pseudo-lambdap
                                                pseudo-term-listp)))))

    (defthm symbolp-of-caar-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (pseudo-lambdap (car (car (te-args->expr-lst args))))))
               (symbolp (car (car (te-args->expr-lst args))))))

    (local (defthm lemma-8
             (implies (and (pseudo-term-listp x) (consp x) (pseudo-lambdap (caar x)))
                      (symbol-listp (cadaar x)))
             :hints (("Goal" :in-theory (enable pseudo-termp pseudo-lambdap pseudo-term-listp)))))

    (defthm symbol-listp-of-cadaar-of-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (equal (car (car (te-args->expr-lst args)))
                                'quote))
                    (pseudo-lambdap (car (car (te-args->expr-lst args)))))
               (symbol-listp (cadr (car (car (te-args->expr-lst args)))))))

    (local (defthm lemma-9
             (implies (and (pseudo-term-listp x) (consp x)
                           (pseudo-lambdap (caar x)))
                      (pseudo-termp (caddr (caar x))))
             :hints (("Goal" :in-theory (enable pseudo-lambdap
                                                pseudo-term-listp
                                                pseudo-termp)))))

    (defthm pseudo-termp-of-caddaar-of-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (equal (car (car (te-args->expr-lst args)))
                                'quote))
                    (pseudo-lambdap (car (car (te-args->expr-lst args)))))
               (pseudo-termp (caddr (car (car (te-args->expr-lst args)))))))

    (local (defthm lemma-10
             (implies (and (pseudo-term-listp x) (consp x)
                           (pseudo-lambdap (caar x)))
                      (pseudo-term-listp (cdar x)))))

    (defthm pseudo-term-listp-of-cdar-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (equal (car (car (te-args->expr-lst args)))
                                'quote))
                    (pseudo-lambdap (car (car (te-args->expr-lst args)))))
               (pseudo-term-listp (cdr (car (te-args->expr-lst args))))))

    (local (defthm lemma-11
             (implies (and (pseudo-term-listp x) (consp x)
                           (not (symbolp (car x))) (not (pseudo-lambdap (caar x)))
                           (not (equal (caar x) 'quote)))
                      (pseudo-term-listp (cdar x)))))

    (defthm pseudo-term-listp-of-cdar-of-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (equal (car (car (te-args->expr-lst args)))
                                'quote))
                    (not (pseudo-lambdap (car (car (te-args->expr-lst args))))))
               (pseudo-term-listp (cdr (car (te-args->expr-lst args))))))

    (defthm crock-pseudo-term-listp
      (implies (pseudo-term-listp (cdr (car (te-args->expr-lst args))))
               (pseudo-term-listp (cddr (car (te-args->expr-lst args))))))

    (defthm pseudo-term-listp-of-cddar-of-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (equal (car (car (te-args->expr-lst args)))
                                'quote))
                    (not (pseudo-lambdap (car (car (te-args->expr-lst args))))))
               (pseudo-term-listp (cddr (car (te-args->expr-lst args)))))
      :hints (("Goal"
               :in-theory (e/d ()
                               (pseudo-term-listp-of-cdar-of-te-args->expr-lst))
               :use ((:instance pseudo-term-listp-of-cdar-of-te-args->expr-lst
                                (args args))))))

    (local (defthm lemma-12
             (implies (and (pseudo-term-listp x) (consp x)
                           (pseudo-lambdap (caar x)))
                      (consp (cdaar x)))
             :hints (("Goal" :in-theory (enable pseudo-lambdap
                                                pseudo-term-listp
                                                pseudo-termp)))))

    (defthm not-cdaar-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (equal (car (car (te-args->expr-lst args)))
                                'quote))
                    (pseudo-lambdap (car (car (te-args->expr-lst args))))
                    (not (consp (cdr (car (car (te-args->expr-lst args)))))))
               (not (cdr (car (car (te-args->expr-lst args)))))))

    (local (defthm lemma-13
             (implies (and (pseudo-term-listp x) (consp x)
                           (pseudo-lambdap (caar x)))
                      (consp (cddaar x)))
             :hints (("Goal" :in-theory (enable pseudo-lambdap
                                                pseudo-term-listp
                                                pseudo-termp)))))

    (defthm not-cddaar-of-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (equal (car (car (te-args->expr-lst args)))
                                'quote))
                    (pseudo-lambdap (car (car (te-args->expr-lst args))))
                    (not (consp (cddr (car (car (te-args->expr-lst args)))))))
               (not (cddr (car (car (te-args->expr-lst args)))))))

    (local (defthm lemma-14
             (implies (and (pseudo-term-listp x) (consp x)
                           (pseudo-lambdap (caar x)))
                      (consp (caar x)))
             :hints (("Goal" :in-theory (enable pseudo-lambdap
                                                pseudo-term-listp
                                                pseudo-termp)))))

    (defthm not-caar-of-te-args->expr-lst
      (implies (and (te-args-p args)
                    (consp (te-args->expr-lst args))
                    (not (symbolp (car (te-args->expr-lst args))))
                    (not (equal (car (car (te-args->expr-lst args)))
                                'quote))
                    (pseudo-lambdap (car (car (te-args->expr-lst args))))
                    (not (consp (car (car (te-args->expr-lst args))))))
               (not (car (car (te-args->expr-lst args))))))

    (defthm consp-of-pseudo-lambdap
      (implies (pseudo-lambdap x)
               (consp x))
      :hints (("Goal"
               :in-theory (enable pseudo-lambdap))))
    )

  (verify-guards translate-expression
    :guard-debug t
    :hints (("Goal"
             :in-theory (e/d ()
                             (fncall-of-flextype-conclusion))
             :use ((:instance fncall-of-flextype-conclusion
                              (fn-name (car (car (te-args->expr-lst args))))
                              (fty-info (te-args->fty-info args)))))))

  (define translate-declaration ((name symbolp) (type symbolp)
                                 (fty-info fty-info-alist-p)
                                 (int-to-rat booleanp))
    :returns (translated
              paragraphp
              :hints (("Goal"
                       :in-theory (enable translate-symbol translate-type
                                          paragraphp wordp))))
    (b* ((name (symbol-fix name))
         (type (symbol-fix type))
         (translated-name (translate-symbol name))
         (fty-item (assoc-equal type fty-info))
         (type (if fty-item (fty-info->name (cdr fty-item)) type))
         (translated-type
          (translate-type type int-to-rat 'common-type)))
      `(,translated-name = "z3.Const" #\( #\' ,translated-name #\' #\, #\Space
                         ,translated-type #\) #\Newline)))

  (encapsulate ()
    (local (in-theory (enable paragraph-fix paragraphp)))
    (define translate-type-decl-list ((type-decl-lst decl-listp)
                                      (fty-info fty-info-alist-p)
                                      (acc paragraphp)
                                      (int-to-rat booleanp))
      :returns (translated
                paragraphp
                :hints (("Goal" :in-theory (enable translate-declaration))))
      :measure (len type-decl-lst)
      (b* ((type-decl-lst (decl-list-fix type-decl-lst))
           (acc (paragraph-fix acc))
           ((unless (consp type-decl-lst)) acc)
           ((cons first rest) type-decl-lst)
           ((decl d) first)
           ((hint-pair h) d.type)
           (translated-type-decl
            (translate-declaration d.name h.thm fty-info int-to-rat)))
        (translate-type-decl-list rest fty-info
                                  (cons translated-type-decl acc)
                                  int-to-rat))))

  (encapsulate ()
    (local (defthm remove-duplicates-maintain-symbol-listp
             (implies (symbol-listp x)
                      (symbol-listp (remove-duplicates-equal x)))
             :hints (("Goal"
                      :in-theory (enable remove-duplicates-equal)))))

    (define translate-theorem ((theorem pseudo-termp) (fn-lst func-alistp)
                               (fty-info fty-info-alist-p))
      :returns (mv (translated
                    paragraphp
                    :hints (("Goal"
                             :in-theory (enable translate-expression))))
                   (uninterpreted symbol-listp
                                  :hints
                                  (("Goal"
                                    :in-theory (disable symbol-listp)
                                    :use ((:instance
                                           symbol-listp-of-translate-expression.uninterpreted)))))
                   (symbols string-listp))
      (b* ((theorem (pseudo-term-fix theorem))
           (uninterpreted-lst nil)
           ((mv translated-theorem-body uninterpreted symbols &)
            (with-fast-alists (fn-lst uninterpreted-lst)
              (translate-expression
               (make-te-args :expr-lst (list theorem)
                             :fn-lst fn-lst
                             :uninterpreted-lst uninterpreted-lst
                             :fty-info fty-info
                             :symbol-index 0
                             :symbol-list nil))))
           (short-uninterpreted (remove-duplicates-equal uninterpreted))
           (theorem-assign `("theorem" = ,translated-theorem-body #\Newline))
           (prove-theorem `("_SMT_.prove(theorem)" #\Newline)))
        (mv `(,theorem-assign ,prove-theorem) short-uninterpreted symbols))))

  (local (in-theory (enable paragraphp translate-type)))
  (define translate-uninterpreted-arguments ((type symbolp)
                                             (args decl-listp)
                                             (fty-info fty-info-alist-p)
                                             (int-to-rat booleanp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (disable true-listp))))
    :measure (len args)
    (b* ((type (symbol-fix type))
         (args (decl-list-fix args))
         ((unless (consp args)) nil)
         ((cons first rest) args)
         ((decl d) first)
         ((hint-pair h) d.type)
         (fty-item (assoc-equal h.thm fty-info))
         (type-name (if fty-item (fty-info->name (cdr fty-item)) h.thm))
         (translated-type
          (translate-type type-name int-to-rat 'uninterpreted)))
      (cons `(#\, #\Space ,translated-type)
            (translate-uninterpreted-arguments type rest
                                               fty-info int-to-rat))))

  (local (in-theory (enable wordp)))
  (define translate-uninterpreted-decl ((fn func-p)
                                        (fty-info fty-info-alist-p)
                                        (int-to-rat booleanp))
    :returns (translated paragraphp)
    (b* ((fn (func-fix fn))
         ;; Bind everything needed from fn
         ((func f) fn)
         (name f.name)
         (translated-formals
          (translate-uninterpreted-arguments 'formals f.formals
                                             fty-info int-to-rat))
         ((if (> (len f.returns) 1))
          (er hard? 'SMT-translator=>translate-uninterpreted-decl "Currently, ~
            mv returns are not supported."))
         (translated-returns
          (translate-uninterpreted-arguments 'returns f.returns
                                             fty-info int-to-rat)))
      `(,(translate-symbol name) "= z3.Function("
        #\' ,name #\' ,translated-formals ,translated-returns
        ")" #\Newline)))

  ;; func1 = Function('func1', I1-type, I2-type, R-type)
  ;; example:
  ;;   expr = Function('expr', RealSort(), IntSort(), RealSort())
  (encapsulate ()
    (local (in-theory (enable paragraph-fix paragraphp)))
    (define translate-uninterpreted-decl-lst ((uninterpreted symbol-listp)
                                              (fn-lst func-alistp)
                                              (fty-info fty-info-alist-p)
                                              (acc paragraphp)
                                              (int-to-rat booleanp))
      :measure (len uninterpreted)
      :returns (translated paragraphp)
      :guard-debug t
      (b* ((uninterpreted (symbol-list-fix uninterpreted))
           (fn-lst (func-alist-fix fn-lst))
           (acc (paragraph-fix acc))
           ((unless (consp uninterpreted)) acc)
           ((cons first rest) uninterpreted)
           (fn (hons-get first fn-lst))
           ;; ((unless (mbt fn)) acc)
           ((unless fn) acc)
           (first-decl
            (translate-uninterpreted-decl (cdr fn) fty-info int-to-rat)))
        (translate-uninterpreted-decl-lst rest fn-lst fty-info
                                          (cons first-decl acc) int-to-rat)))
    )

  (local
   (defthm crock-translate-symbol-declare
     (paragraphp (car (str::string-list-fix symbols)))
     :hints (("Goal" :in-theory (e/d (paragraphp
                                      str::string-list-fix)
                                     ()))))
   )

  (define translate-symbol-declare ((symbol-name stringp)
                                    (symbols string-listp))
    :returns (translated paragraphp)
    :measure (len symbols)
    (b* ((symbol-name (str-fix symbol-name))
         (symbols (str::string-list-fix symbols))
         ((unless (consp symbols)) nil)
         ((cons first rest) symbols))
      (cons `(,symbol-name ".declare('" ,first "')" #\Newline)
            (translate-symbol-declare symbol-name rest))))

  (define translate-symbol-enumeration ((symbols string-listp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (e/d (paragraphp)
                                                         ()))))
    (b* ((symbols
          (if (endp symbols) (list (generate-symbol-enumeration 0)) symbols))
         (symbol-name (cdr (assoc-equal 'symbolp *SMT-types*)))
         (datatype-line `(,symbol-name " = z3.Datatype('" ,symbol-name "')"
                                       #\Newline))
         (enumerations (translate-symbol-declare symbol-name symbols))
         (create-line `(,symbol-name " = " ,symbol-name ".create()" #\Newline)))
      `(,datatype-line
        ,@enumerations
        ,create-line)))

  (define SMT-translation ((term pseudo-termp) (smtlink-hint smtlink-hint-p))
    :returns (py-term paragraphp)
    (b* ((term (pseudo-term-fix term))
         (smtlink-hint (smtlink-hint-fix smtlink-hint))
         ((smtlink-hint h) smtlink-hint)
         ;; Make an alist version of fn-lst
         (fn-lst (make-alist-fn-lst h.functions))
         ((mv translated-theorem uninterpreted symbols)
          (translate-theorem term fn-lst h.fty-info))
         (- (cw "symbols: ~q0" symbols))
         (translated-uninterpreted-decls
          (with-fast-alist fn-lst
            (translate-uninterpreted-decl-lst uninterpreted fn-lst h.fty-info
                                              translated-theorem h.int-to-rat)))
         (translated-theorem-with-type-decls
          (translate-type-decl-list h.type-decl-list
                                    h.fty-info
                                    translated-uninterpreted-decls
                                    h.int-to-rat))
         (translated-fty-types (translate-fty-types h.fty-types h.int-to-rat))
         (translated-theorem-with-fty-type-decls
          `(,@translated-fty-types
            ,@translated-theorem-with-type-decls))
         (translated-symbol (translate-symbol-enumeration symbols))
         )
      `(,translated-symbol ,@translated-theorem-with-fty-type-decls)))
;;  )

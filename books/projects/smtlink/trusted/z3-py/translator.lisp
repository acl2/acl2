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
(include-book "kestrel/utilities/system/terms" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)

(include-book "../../verified/extractor")
(include-book "translate-type")
(include-book "recover-type-hyp")
(include-book "pretty-printer")

(defsection SMT-translator
  :parents (z3-py)
  :short "SMT-translator does the LISP to Python translation."

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

  (defalist symbol-string-alist
    :key-type symbolp
    :val-type stringp
    :pred symbol-string-alistp
    :true-listp t)

  (defprod te-args
    ((expr-lst pseudo-term-listp :default nil)
     (fn-lst func-alistp :default nil)
     (fty-info fty-info-alist-p)
     (symbol-index natp) ;; how many random symbols there are
     (symbol-list string-listp) ;; translated symbols in the symbol enumeration
     (avoid-list symbol-listp)  ;; avoid-list for symbols
     (symbol-map symbol-string-alistp)
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

  (local
   (defthm translate-fty-special-crock
     (implies (pseudo-term-listp x)
              (pseudo-termp (car x)))))

  (define translate-fty-special ((fn-call symbolp)
                                 (fn-actuals pseudo-term-listp)
                                 (fty-info fty-info-alist-p))
    :returns (mv (translated paragraphp
                             :hints (("Goal" :in-theory (enable wordp))))
                 (smt-precond pseudo-termp))
    :guard-hints (("Goal" :in-theory (e/d (string-or-symbol-p) ())))
    (b* ((fn-call (symbol-fix fn-call))
         (fn-actuals (pseudo-term-list-fix fn-actuals))
         (fty-info (fty-info-alist-fix fty-info))
         ;; dealing with magic-fix
         ((if (and (and (car fn-actuals) (null (cdr fn-actuals)))
                   (consp (car fn-actuals))
                   (equal (caar fn-actuals) 'SMT::MAGIC-FIX)
                   (consp (cadar fn-actuals))
                   (equal (car (cadar fn-actuals)) 'QUOTE)
                   (symbolp (cadr (cadar fn-actuals)))))
          (if (equal fn-call 'CONSP)
              (mv (list (str::downcase-string
                         (concatenate 'string
                                      (lisp-to-python-names (cadr (cadar fn-actuals))) "_"
                                      (translate-symbol fn-call))))
                  ''t)
            ;; the only case fall here is 'CDR for MAGIC-FIX'ed types
            (mv (list (str::downcase-string
                       (concatenate 'string
                                    (lisp-to-python-names (cadr (cadar fn-actuals))) "."
                                    (translate-symbol fn-call))))
                `,(car fn-actuals))))
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
                                    (null (cdddr fn-actuals))))
                       (er hard? 'SMT-translator=>translate-fty-special "Wrong ~
         number of arguments for ~p0: ~p1~%" fn-call fn-actuals)))
                   (caddr fn-actuals)))
                (t
                 (er hard? 'SMT-translator=>translate-fty-special "Impossible path:
                                 ~q0" fn-call))))
         ((unless (and (consp fixed) (car fixed) (cadr fixed)
                       (symbolp (car fixed))))
          (prog2$ (er hard? 'SMT-translator=>translate-fty-special "Not fixed1:
                                 ~q0" fixed)
                  (mv nil ''t)))
         ((mv fixing? &) (fixing-of-flextype (car fixed) fty-info))
         ((unless fixing?)
          (prog2$ (er hard? 'SMT-translator=>translate-fty-special "Not fixed2:
                                 ~q0" (car fixed))
                  (mv nil ''t)))
         ((unless (pseudo-termp (cadr fixed)))
          (prog2$ (er hard? 'SMT-translator=>translate-fty-special "not ~
                               pseudo-termp: ~q0" (cadr fixed))
                  (mv nil ''t)))
         (smt-precond (if (equal fn-call 'CAR)
                          `(consp ,(cadr fixed))
                        ''t)))
      ;; acons and assoc are treated differently because they are not class
      ;; methods in Z3 either
      (if (or (equal fn-call 'ACONS)
              (equal fn-call 'ASSOC-EQUAL)
              (equal fn-call 'CONSP))
          (mv (list (str::downcase-string
                     (concatenate 'string (translate-symbol fixing?) "_"
                                  (translate-symbol fn-call))))
              ''t)
        (mv (list (str::downcase-string
                   (concatenate 'string (translate-symbol fixing?)  "."
                                (translate-symbol fn-call))))
            smt-precond))))

  (define translate-field-accessor ((fty-name symbolp)
                                    (fn-call symbolp))
    :returns (mv (translated paragraphp
                             :hints (("Goal" :in-theory (enable paragraphp
                                                                wordp))))
                 (smt-precond pseudo-termp))
    :guard-hints (("Goal" :in-theory (e/d (string-or-symbol-p)
                                          ())))
    (b* ((fty-name (symbol-fix fty-name))
         (fn-call (symbol-fix fn-call))
         (fty-name-str (symbol-name fty-name))
         (fn-call-str (symbol-name fn-call))
         ((unless (<= (+ 2 (length fty-name-str)) (length fn-call-str)))
          (mv (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong1: ~p0 and ~p1" fty-name-str fn-call-str)
              ''t))
         (pos-prefix (search fty-name-str fn-call-str :test 'equal))
         ((unless (equal pos-prefix 0))
          (mv (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong2: ~p0 and ~p1" fty-name-str fn-call-str)
              ''t))
         (pos1 (length fty-name-str))
         (pos-infix (search "->" fn-call-str :test 'equal))
         ((unless (equal pos1 pos-infix))
          (mv (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong3: ~p0 and ~p1" fty-name-str fn-call-str)
              ''t))
         (pos-suffix (+ 2 pos1))
         (pos2 (search "$INLINE" fn-call-str :from-end t :test 'equal))
         ((unless (and (natp pos2)
                       (<= pos-suffix pos2)
                       (<= pos2 (length fn-call-str))))
          (mv (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong4: ~p0 and ~p1" fty-name-str fn-call-str)
              ''t))
         (suffix (subseq fn-call-str pos-suffix pos2))
         ((unless (stringp suffix))
          (mv (er hard? 'SMT-translator=>translate-field-accessor "Something is ~
             wrong5: ~p0 and ~p1" fty-name-str fn-call-str)
              ''t)))
      (mv (list (str::downcase-string
                 (concatenate 'string (lisp-to-python-names fty-name-str)  "."
                              (lisp-to-python-names suffix))))
          ''t)))

  (define translate-fty ((fn-call symbolp)
                         (fn-actuals pseudo-term-listp)
                         (fty-info fty-info-alist-p))
    :returns (mv (translated paragraphp
                             :hints (("Goal" :in-theory (e/d (paragraphp wordp)
                                                             ()))))
                 (smt-precond pseudo-termp))
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
         (option? (fncall-of-flextype-option fn-call fty-info))
         ((if (and option? (equal fty-type :constructor)))
          (mv (list (concatenate 'string (translate-symbol fty-name) ".some"))
              ''t))
         ((if (and option? (equal fty-type :field)))
          (mv (list (concatenate 'string (translate-symbol fty-name) ".val"))
              ''t))
         ((unless (or (equal fty-type :field)
                      (equal fty-type :constructor)))
          (mv (er hard? 'SMT-translator=>translate-fty "Unexpected fty function ~
                         found: ~p0 of ~p1~%" fn-call fty-type)
              ''t))
         ((if (equal fty-type :constructor))
          (mv (list (concatenate 'string (translate-symbol fty-name)
                                 "." (translate-symbol fn-call)))
              ''t)))
      (translate-field-accessor fty-name fn-call)))

  (define generate-symbol-enumeration ((symbol-index natp))
    :returns (new-sym stringp)
    (b* ((symbol-index (nfix symbol-index))
         (new-sym (concatenate 'string "gensym_" (nat-to-dec-string symbol-index))))
      new-sym))

  (define translate-quote ((expr t))
    :returns (translated-quote paragraphp
                               :hints (("Goal" :in-theory (e/d (paragraphp wordp)
                                                               ()))))
    (b* (((unless (or (symbolp expr)
                      (SMT-numberp expr)
                      (booleanp expr)))
          (er hard? 'SMT-translator=>translate-quote "Atom not ~
                       supported: ~q0" expr)))
      (cond ((booleanp expr)
             (translate-bool expr nil))
            ((SMT-numberp expr)
             (translate-number expr))
            (t (translate-symbol expr))))
    ///
    (more-returns
     (translated-quote
      (implies (and (symbolp expr) (not (booleanp expr)))
               (stringp translated-quote))
      :name stringp-of-translated-quote-when-symbolp)))

  (encapsulate ()
    (local
     (defthm crock0-translate-expression.translated
       (implies (and (symbol-string-alistp alist)
                     (cdr (assoc-equal key alist)))
                (stringp (cdr (assoc-equal key alist))))
       :hints (("Goal"
                :in-theory (enable paragraphp wordp))))
     )

    (local
     (defthm crock0-translate-expression.smt-precond
       (symbol-listp
        (mv-nth 1
                (fixing-of-flextype (car (car (te-args->expr-lst args)))
                                    (te-args->fty-info args))))))

    (local
     (defthm crock-lemma0
       (pseudo-termp (car (te-args->expr-lst args)))))

    (local
     (defthm crock-lemma1
       (implies (and (pseudo-termp x) (not (symbolp x))
                     (not (equal (car x) 'QUOTE)))
                (pseudo-term-listp (cdr x)))))

    (local
     (defthm crock-lemma2
       (implies (and (not (symbolp (car (te-args->expr-lst args))))
                     (not (equal (car (car (te-args->expr-lst args)))
                                 'quote)))
                (pseudo-term-listp (cdar (te-args->expr-lst args))))
       ))

    (local
     (defthm crock1-translate-expression.smt-precond
       (implies
        (and
         (consp (te-args->expr-lst args))
         (not (symbolp (car (te-args->expr-lst args))))
         (not (equal (car (car (te-args->expr-lst args)))
                     'quote)))
        (pseudo-termp (cadr (car (te-args->expr-lst args)))))
       )
     )

    (define translate-expression ((args te-args-p))
      :returns (mv (translated
                    paragraphp
                    :hints (("Goal"
                             :in-theory (e/d (paragraphp wordp)
                                             ()))))
                   (smt-precond pseudo-termp)
                   (symbols string-listp)
                   (symbol-index natp)
                   (symbol-map symbol-string-alistp))
      :measure (acl2-count (te-args->expr-lst args))
      :hints (("Goal" :in-theory (enable pseudo-lambdap)))
      :verify-guards nil
      (b* ((args (te-args-fix args))
           ((te-args a) args)
           ((unless (consp a.expr-lst))
            (mv nil ''t a.symbol-list a.symbol-index a.symbol-map))
           ((cons expr rest) a.expr-lst)
           ((mv translated-rest smt-precond-rest symbols-rest symbol-index-rest
                symbol-map-rest)
            (translate-expression (change-te-args a :expr-lst rest)))
           ;; If first term is an symbolp, should be a variable name
           ;; translate the variable then recurse on the rest of the list
           ((if (symbolp expr))
            (mv (cons (translate-symbol expr) translated-rest)
                smt-precond-rest
                symbols-rest
                symbol-index-rest
                symbol-map-rest))
           ;; If car of term is 'quote, some constants
           ((if (equal (car expr) 'quote))
            (b* ((the-sym (cadr expr))
                 ((unless (and (symbolp the-sym)
                               (not (booleanp the-sym))))
                  (mv (cons (translate-quote the-sym) translated-rest)
                      smt-precond-rest
                      symbols-rest
                      symbol-index-rest
                      symbol-map-rest))
                 ((unless (mbt (symbol-string-alistp symbol-map-rest)))
                  (mv (er hard? 'SMT-translator=>translate-expression "Can't reach ~
                      this branch~%")
                      nil nil 0 nil))
                 (exist-map? (cdr (assoc-equal the-sym symbol-map-rest)))
                 ((if exist-map?)
                  (mv (cons exist-map? translated-rest)
                      smt-precond-rest
                      (cons exist-map? symbols-rest)
                      symbol-index-rest
                      symbol-map-rest))
                 (exist-sym? (member-equal the-sym a.avoid-list))
                 (gen-sym (if exist-sym?
                              (generate-symbol-enumeration a.symbol-index)
                            (translate-symbol the-sym))))
              (mv (cons gen-sym translated-rest)
                  smt-precond-rest
                  (cons gen-sym symbols-rest)
                  (if exist-sym?
                      (1+ symbol-index-rest)
                    symbol-index-rest)
                  (if exist-map?
                      symbol-map-rest
                    (acons the-sym gen-sym symbol-map-rest)))))
           ;; The first term is now a function call:
           ;; Either a lambda or a symbol
           ((cons fn-call fn-actuals) expr)

           ;; If fn-call is a lambda
           ((if (pseudo-lambdap fn-call))
            (b* ((formals (lambda-formals fn-call))
                 ((unless (and (symbol-listp formals)
                               (equal (len formals)
                                      (len fn-actuals))
                               ;; shouldn't need this
                               (pseudo-term-listp fn-actuals)))
                  (mv (er hard? 'SMT-translator=>translate-expression
                          "bad lambda: ~q0" fn-call)
                      nil nil 0 nil))
                 (body (lambda-body fn-call))
                 (lambda-sym (car fn-call))
                 ((mv translated-lambda &) (translate-function lambda-sym))
                 (translated-formals (translate-symbol-lst formals))
                 ((mv translated-body smt-precond-1
                      symbol-list-1 symbol-index-1 symbol-map-1)
                  (translate-expression
                   (change-te-args a :expr-lst (list body)
                                   :symbol-list symbols-rest
                                   :symbol-index symbol-index-rest
                                   :symbol-map symbol-map-rest)))
                 ((mv translated-actuals smt-precond-2
                      symbol-list-2 symbol-index-2 symbol-map-2)
                  (translate-expression
                   (change-te-args a :expr-lst fn-actuals
                                   :symbol-list symbol-list-1
                                   :symbol-index symbol-index-1
                                   :symbol-map symbol-map-1)))
                 (translated-lambda-whole
                  `(#\( ,translated-lambda #\Space ,translated-formals #\:
                    ,translated-body #\)
                    #\( ,(map-translated-actuals translated-actuals) #\))))
              (mv (cons translated-lambda-whole translated-rest)
                  `(if (if ((lambda (,@formals) ,smt-precond-1) ,@fn-actuals)
                           ,smt-precond-2
                         'nil)
                       ,smt-precond-rest
                     'nil)
                  symbol-list-2
                  symbol-index-2
                  symbol-map-2)))

           ;; If fn-call is smt::magic-fix, this function is used by the user.
           ;; Therefore probably in a different package?
           ((if (equal fn-call 'SMT::MAGIC-FIX))
            (b* (((unless (and (consp fn-actuals)
                               (consp (cdr fn-actuals))
                               (null (cddr fn-actuals))))
                  (mv (er hard? 'SMT-translator=>translate-expression "Wrong ~
         number of arguments for magic-fix function: ~q0" expr)
                      nil nil 0 nil))
                 ;; special case when it's a fixing on nil
                 (the-type (car fn-actuals))
                 (the-nil (cadr fn-actuals))
                 ((if (and (consp the-nil)
                           (equal (car the-nil) 'quote)
                           (consp (cdr the-nil))
                           (equal (cadr the-nil) nil)
                           ;;
                           (consp the-type)
                           (equal (car the-type) 'quote)
                           (consp (cdr the-type))
                           (symbolp (cadr the-type))))
                  (mv (cons (translate-bool nil (cadr the-type))
                            translated-rest)
                      smt-precond-rest ;; if it's magic-fixing a nil, then no guards needed
                      symbols-rest
                      symbol-index-rest
                      symbol-map-rest))
                 ((mv translated-actuals smt-precond-1 symbol-list-1 symbol-index-1
                      symbol-map-1)
                  (translate-expression
                   (change-te-args a
                                   :expr-lst (cdr fn-actuals)
                                   :symbol-list symbols-rest
                                   :symbol-index symbol-index-rest
                                   :symbol-map symbol-map-rest))))
              (mv (cons translated-actuals translated-rest)
                  `(if ,smt-precond-1 ,smt-precond-rest 'nil)
                  symbol-list-1
                  symbol-index-1
                  symbol-map-1)))

           ;; If fn-call is a fty fixing call
           ((mv fixing? guards) (fixing-of-flextype fn-call a.fty-info))
           ((if fixing?)
            (b* (((unless (and (consp fn-actuals)
                               (car fn-actuals)
                               (null (cdr fn-actuals))))
                  (mv (er hard? 'SMT-translator=>translate-expression "Wrong ~
         number of arguments for a fixing function: ~q0" expr)
                      nil nil 0 nil))
                 (fixed (car fn-actuals))
                 ((unless (and (consp guards)
                               (car guards)
                               (null (cdr guards))
                               (not (equal (car guards) 'QUOTE))))
                  (mv (er hard? 'SMT-translator=>translate-expression "bad guards :
       ~q0" guards)
                      nil nil 0 nil))
                 ;; special case when it's a fixing on nil
                 ((if (and (consp fixed)
                           (equal (car fixed) 'quote)
                           (consp (cdr fixed))
                           (equal (cadr fixed) nil)))
                  (mv (cons (translate-bool nil fixing?)
                            translated-rest)
                      `(if (,(car guards) ,fixed) ,smt-precond-rest 'nil)
                      symbols-rest
                      symbol-index-rest
                      symbol-map-rest))
                 ((mv translated-actuals smt-precond-1 symbol-list-1 symbol-index-1
                      symbol-map-1)
                  (translate-expression
                   (change-te-args a
                                   :expr-lst fn-actuals
                                   :symbol-list symbols-rest
                                   :symbol-index symbol-index-rest
                                   :symbol-map symbol-map-rest))))
              (mv (cons translated-actuals translated-rest)
                  `(if (if (,(car guards) ,fixed)
                           ,smt-precond-1
                         'nil)
                       ,smt-precond-rest
                     'nil)
                  symbol-list-1
                  symbol-index-1
                  symbol-map-1)))

           ;; If fn-call is a fty call, but not a fixing function
           (fty? (fncall-of-flextype fn-call a.fty-info))
           ((if fty?)
            (b* (((mv translated-fn-call fty-smt-precond)
                  (translate-fty fn-call fn-actuals a.fty-info))
                 ((mv translated-actuals smt-precond-1 symbol-list-1 symbol-index-1
                      symbol-map-1)
                  (translate-expression
                   (change-te-args a
                                   :expr-lst fn-actuals
                                   :symbol-list symbols-rest
                                   :symbol-index symbol-index-rest
                                   :symbol-map symbol-map-rest)))
                 (translated-expr
                  `(,translated-fn-call
                    #\( ,(map-translated-actuals translated-actuals) #\) )))
              (mv (cons translated-expr translated-rest)
                  `(if (if ,fty-smt-precond ,smt-precond-1
                         'nil)
                       ,smt-precond-rest
                     'nil)
                  symbol-list-1
                  symbol-index-1
                  symbol-map-1)))

           ;; If fn-call is neither a lambda expression nor a function call
           ((unless (mbt (symbolp fn-call))) (mv nil ''t nil 0 nil))
           ;; Now, fn-call should be treated as an uninterpreted function
           (fn (hons-get fn-call a.fn-lst))
           ((if fn)
            (b* (;; ((func f) (cdr fn))
                 ;; ((if (not f.uninterpreted))
                 ;;  (mv (er hard? 'SMT-translator=>translate-expression "Not a basic SMT function: ~q0" fn-call) nil))
                 ((mv translated-actuals smt-precond-1 symbol-list-1 symbol-index-1
                      symbol-map-1)
                  (translate-expression
                   (change-te-args a :expr-lst fn-actuals
                                   :symbol-list symbols-rest
                                   :symbol-index symbol-index-rest
                                   :symbol-map symbol-map-rest)))
                 (translated-fn-call
                  `(,(translate-symbol fn-call)
                    #\( ,(map-translated-actuals translated-actuals) #\) )))
              (mv (cons translated-fn-call translated-rest)
                  `(if ,smt-precond-1 ,smt-precond-rest 'nil)
                  symbol-list-1
                  symbol-index-1
                  symbol-map-1)))
           ;; If fn-call is not an uninterpreted function, then it has to be a
           ;; basic function
           ((mv fn nargs) (translate-function fn-call))
           ((if (zp nargs))
            (mv (cons `( ,fn #\( #\) ) translated-rest)
                smt-precond-rest
                symbols-rest
                symbol-index-rest
                symbol-map-rest))
           ((if (equal fn-call 'IF))
            (b* (((unless (and (consp fn-actuals)
                               (car fn-actuals)
                               (consp (cdr fn-actuals))
                               (cadr fn-actuals)
                               (consp (cddr fn-actuals))
                               (caddr fn-actuals)
                               (null (cdddr fn-actuals))))
                  (mv (er hard? 'SMT-translator=>translate-expression "fn-actuals ~
       for if should be of length 3: ~q0" fn-actuals)
                      nil nil 0 nil))
                 ((mv translated-car-actual smt-precond-if symbol-list-1
                      symbol-index-1 symbol-map-1)
                  (translate-expression
                   (change-te-args a :expr-lst (list (car fn-actuals))
                                   :symbol-list symbols-rest
                                   :symbol-index symbol-index-rest
                                   :symbol-map symbol-map-rest)))
                 ((mv translated-cadr-actual smt-precond-then symbol-list-2
                      symbol-index-2 symbol-map-2)
                  (translate-expression
                   (change-te-args a :expr-lst (list (cadr fn-actuals))
                                   :symbol-list symbol-list-1
                                   :symbol-index symbol-index-1
                                   :symbol-map symbol-map-1)))
                 ((mv translated-caddr-actual smt-precond-else symbol-list-3
                      symbol-index-3 symbol-map-3)
                  (translate-expression
                   (change-te-args a :expr-lst (list (caddr fn-actuals))
                                   :symbol-list symbol-list-2
                                   :symbol-index symbol-index-2
                                   :symbol-map symbol-map-2)))
                 (translated-actuals `(,translated-car-actual
                                       ,translated-cadr-actual
                                       ,translated-caddr-actual))
                 ((unless (and (pseudo-termp (car fn-actuals))
                               (pseudo-termp (cadr fn-actuals))
                               (pseudo-termp (caddr fn-actuals))))
                  (mv (er hard? 'SMT-translator=>translate-expression "pseudo-termp
       ensured: ~q0" fn-actuals)
                      nil nil 0 nil))
                 (smt-precond `(if ,smt-precond-if
                                   (if ,(car fn-actuals)
                                       ,smt-precond-then
                                     ,smt-precond-else)
                                 'nil)))
              (mv (cons `( ,fn #\(
                               ,(map-translated-actuals translated-actuals) #\))
                        translated-rest)
                  `(if ,smt-precond ,smt-precond-rest 'nil)
                  symbol-list-3
                  symbol-index-3
                  symbol-map-3)))
           ((mv translated-actuals smt-precond-1 symbol-list-1 symbol-index-1
                symbol-map-1)
            (translate-expression
             (change-te-args a :expr-lst fn-actuals
                             :symbol-list symbols-rest
                             :symbol-index symbol-index-rest
                             :symbol-map symbol-map-rest))))
        (mv (cons `( ,fn #\( ,(map-translated-actuals translated-actuals) #\) )
                  translated-rest)
            `(if ,smt-precond-1 ,smt-precond-rest 'nil)
            symbol-list-1
            symbol-index-1
            symbol-map-1)))
    )

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

    (defthm symbol-string-alistp-is-true-listp
      (implies (and (symbol-string-alistp alist)
                    (not (consp (assoc-equal key alist))))
               (not (assoc-equal key alist)))
      )
    )

  (local
   (defthm crock0-translate-expression-guard
     (implies (pseudo-term-listp (cddr (car (te-args->expr-lst args))))
              (pseudo-term-listp (cdddr (car (te-args->expr-lst args)))))))

  (local
   (defthm crock1-translate-expression-guard
     (implies (and (te-args-p args)
                   (not (symbolp (car (te-args->expr-lst args))))
                   (consp (te-args->expr-lst args))
                   (equal (car (car (te-args->expr-lst args)))
                          'if))
              (pseudo-term-listp (cdddr (car (te-args->expr-lst args)))))
     :hints (("Goal" :in-theory (e/d ()
                                     (PSEUDO-TERM-LISTP-OF-CDDAR-OF-TE-ARGS->EXPR-LST
                                      ))
              :use ((:instance PSEUDO-TERM-LISTP-OF-CDDAR-OF-TE-ARGS->EXPR-LST
                               (args args)))))))

  (local
   (defthm crock2-translate-expression-guard
     (implies (and (te-args-p args)
                   (not (symbolp (car (te-args->expr-lst args))))
                   (consp (te-args->expr-lst args))
                   (equal (car (car (te-args->expr-lst args)))
                          'if))
              (pseudo-termp (cadddr (car (te-args->expr-lst args)))))
     ))

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
                               (fty-info fty-info-alist-p) (acc symbol-listp))
      :returns (mv (translated
                    paragraphp
                    :hints (("Goal"
                             :in-theory (enable translate-expression))))
                   (smt-precond pseudo-termp)
                   (symbols string-listp))
      (b* ((theorem (pseudo-term-fix theorem))
           ((mv translated-theorem-body smt-precond symbols & &)
            (with-fast-alists (fn-lst)
              (translate-expression
               (make-te-args :expr-lst (list theorem)
                             :fn-lst fn-lst
                             :fty-info fty-info
                             :symbol-index 0
                             :symbol-list nil
                             :avoid-list acc))))
           (theorem-assign `("theorem = " ,translated-theorem-body #\Newline))
           (prove-theorem `("_SMT_.prove(theorem)" #\Newline)))
        (mv `(,theorem-assign ,prove-theorem) smt-precond symbols))))

  (define translate-uninterpreted-arguments ((type symbolp)
                                             (args decl-listp)
                                             (fty-info fty-info-alist-p)
                                             (int-to-rat booleanp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (e/d (wordp
                                                          paragraphp translate-type)
                                                         (true-listp)))))
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

  (define translate-uninterpreted-decl ((fn func-p)
                                        (fty-info fty-info-alist-p)
                                        (int-to-rat booleanp))
    :returns (translated
              paragraphp
              :hints (("Goal" :in-theory (e/d (wordp
                                               paragraphp translate-type)
                                              (true-listp)))))
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
    (define translate-uninterpreted-decl-lst ((fn-lst func-alistp)
                                              (fty-info fty-info-alist-p)
                                              (acc paragraphp)
                                              (int-to-rat booleanp))
      :measure (len (func-alist-fix fn-lst))
      :returns (translated paragraphp)
      :guard-debug t
      (b* ((fn-lst (func-alist-fix fn-lst))
           (acc (paragraph-fix acc))
           ((unless (consp fn-lst)) acc)
           ((cons first rest) fn-lst)
           (first-decl
            (translate-uninterpreted-decl (cdr first) fty-info int-to-rat)))
        (translate-uninterpreted-decl-lst rest fty-info
                                          (cons first-decl acc) int-to-rat)))
    )

  (local
   (defthm crock-translate-symbol-declare
     (paragraphp (car (str::string-list-fix symbols)))
     :hints (("Goal" :in-theory (e/d (paragraphp wordp
                                                 str::string-list-fix)
                                     ()))))
   )

  (define translate-symbol-declare ((symbols string-listp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (e/d (wordp
                                                          paragraphp translate-type)))))
    :measure (len symbols)
    (b* ((symbols (str::string-list-fix symbols))
         ((unless (consp symbols)) nil)
         ((cons first rest) symbols))
      (cons `(,first " = Symbol_z3.intern('" ,first "')" #\Newline)
            (translate-symbol-declare rest))))

  (define translate-symbol-enumeration ((symbols string-listp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (e/d (paragraphp)
                                                         ()))))
    (b* ((datatype-line '("Symbol_z3 = _SMT_.Symbol()" #\Newline))
         (declarations (translate-symbol-declare symbols)))
      `(,datatype-line
        ,@declarations)))

  (local (defthm remove-duplicates-maintain-string-listp
           (implies (string-listp x)
                    (string-listp (remove-duplicates-equal x)))
           :hints (("Goal"
                    :in-theory (enable remove-duplicates-equal)))))

  (local (defthm string-listp-is-true-listp
           (implies (string-listp x) (true-listp x))))

  (define SMT-translation ((term pseudo-termp) (smtlink-hint smtlink-hint-p) state)
    ;; :returns (mv (py-term paragraphp)
    ;;              (smt-precond pseudo-termp))
    :mode :program
    (b* ((term (pseudo-term-fix term))
         (smtlink-hint (smtlink-hint-fix smtlink-hint))
         ((smtlink-hint h) smtlink-hint)
         ;; Make an alist version of fn-lst
         (fn-alst (make-alist-fn-lst h.functions))
         ((mv decl-list theorem) (smt-extract term h.fty-info h.abs))
         ((mv fn-decl-list type-decl-list)
          (recover-type-hyp decl-list fn-alst h.fty-info h.abs nil state))
         ((unless (and (func-alistp fn-decl-list)
                       (decl-listp type-decl-list)))
          (mv (er hard? 'translator=>SMT-translation "returned values from ~
    recover-type-hyp is not of the right type!~%")
              nil))
         (acc (acl2::all-vars1 term nil))
         ((unless (symbol-listp acc))
          (mv (er hard? 'translator=>SMT-translation "returned values from ~
    acl2::all-vars1 is not of type symbol-listp!~%")
              nil))
         ((mv translated-theorem smt-precond symbols)
          (translate-theorem theorem fn-decl-list h.fty-info acc))
         (pretty-translated-theorem (pretty-print-theorem translated-theorem 160))
         (symbols (remove-duplicates-equal symbols))
         (translated-uninterpreted-decls
          (with-fast-alist fn-decl-list
            (translate-uninterpreted-decl-lst fn-decl-list h.fty-info
                                              pretty-translated-theorem
                                              h.int-to-rat)))
         (translated-theorem-with-type-decls
          (translate-type-decl-list type-decl-list
                                    h.fty-info
                                    translated-uninterpreted-decls
                                    h.int-to-rat))
         (translated-abs-types (translate-abstract-types h.abs))
         (translated-fty-types (translate-fty-types h.fty-types h.int-to-rat))
         (translated-theorem-with-fty-type-decls
          `(,@translated-abs-types
            ,@translated-fty-types
            ,@translated-theorem-with-type-decls))
         (translated-symbol (translate-symbol-enumeration symbols))
         )
      (mv `(,translated-symbol ,@translated-theorem-with-fty-type-decls)
          smt-precond)))
  )

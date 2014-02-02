; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../lexer/tokens")
(include-book "../../util/warnings")
(include-book "misc/seqw" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "tools/rulesets" :dir :system)
(local (include-book "../../util/arithmetic"))

; Our Verilog parser makes extensive use of the defparser macro, which is now
; introduced.  The simplest form for this is:
;
; (defparser foo (x y tokens warnings)  ;; formals always end with "tokens" and "warnings"
;
;   {{{ OPTIONAL KEYWORDS:
;
;     :guard (blah x y)
;     :verify-guards { t, nil }
;     :count { weak, strong, strong-on-value }
;     :result (blah-blah val)
;     :resultp-of-nil { t, nil }
;     :true-listp { t, nil }
;     :fails { never, gracefully }
;     :result-hints (("Goal" ...))
;
;   }}}
;
;   (declare ...)              ;; extra declarations for foo-fn
;   (declare ...)
;   <body>                     ;; the body of foo-fn, which usually is
;                              ;; (seq tokens ...)
;
;   )
;
; Such an event always introduces:
;
;  * A macro, (foo x y), that just calls (foo-fn x y tokens warnings).
;
;  * A function, (foo-fn x y tokens warnings), that implicitly binds the variable
;    __function__ to 'foo and otherwise has the given bodies and declares, with
;    the :guard thrown in if that is provided.
;
;  * An add-macro-alias so foo can be used in place of foo-fn in enables and
;    disables.
;
;  * An untranslate-pattern so that (foo-fn x y tokens warnings) is displayed as
;    (foo x y) during theorems.
;
; In addition to these events, several theorems may be generated depending upon
; the optional keyword arguments given above.  In particular, if any of the
; following keywords are provided, then some theorems will be generated:
;
;    result, resultp-of-nil, true-listp, count, fails
;
; The RESULT theorem will forcibly assume (vl-tokenlist-p tokens), and you can
; also sort of assume that no error has occurred (the actual rule we produce is
; influenced by the RESULTP-OF-NIL setting).  All you have to say is the
; property you want to establish, targetting the variable VAL.
;
; The TRUE-LISTP flag may be set when foo unconditionally returns a true-listp,
; and is only used to generate a type-prescription rule for foo.
;
; The FAILS keyword can be used to introduce a theorem about the failure
; behavior of a parsing function.  Recall that we have standardized upon the
; (mv err val tokens) format for all of our parsing functions.  We say that our
; functions fail GRACEFULLY if, whenever they return a non-nil err, the val
; returned is nil.  Almost all of our functions fail gracefully, and we can
; sometimes exploit this fact along with resultp-of-nil to create stronger
; rewrite rules for the result theorem.   Another common paradigm is a parser
; that NEVER fails -- e.g., perhaps it is for an "optional" production or for
; "zero or more occurrences" of something.
;
; The COUNT theorem is used to create a theorem about acl2-count.  In practice,
; most parsers have a STRONG count-decreasing behavior, which is to say that
; they always decrease acl2-count on success.  But functions which never fail,
; such as "match zero or more" parsers, usually have a weaker property which we
; call STRONG-ON-VALUE, which means that whenever the value they return is
; non-nil, the count decreases.  We also allow for WEAK count theorems, which
; just say the count never increases, but these do not occur very frequently.

(defun wrap-list-in-forces (x)
  (if (consp x)
      (cons `(force ,(car x))
            (wrap-list-in-forces (cdr x)))
    nil))

(defun adjust-guard-for-theorems (x)
  (if (and (consp x)
           (eq (car x) 'and))
      `(and . ,(wrap-list-in-forces (cdr x)))
    `(force ,x)))

(defun expand-and-maybe-induct-hint-fn
  (fncall world id disables enables)
  (and (not (cdr (car id))) ;; not under a top-level induction
       (let* ((fn (car fncall))
              ;; JCD: sometimes I ran into trouble with the expand hint not
              ;; working right because of formals other than "tokens" being
              ;; simplified into constants.  I now let them be free.
              (frees (remove-eq 'tokens (cdr fncall)))
              (recursivep (acl2::getprop
                           fn
                           'acl2::recursivep nil
                           'acl2::current-acl2-world
                           world)))
         (if recursivep
             `(:expand ((:free ,frees ,fncall))
                       :in-theory (e/d ((:induction ,fn) . ,enables)
                                       ((:definition ,fn) . ,disables))
                       :induct ,fncall)
           `(:in-theory (e/d ,enables
                             ((:definition ,fn) . ,disables))
             :expand ((:free ,frees ,fncall)))))))

(defmacro expand-and-maybe-induct-hint
  (fncall &key disable enable)
  `(expand-and-maybe-induct-hint-fn ,fncall world id ,disable ,enable))

(ACL2::def-ruleset defparser-type-prescriptions
                   ;; This is a ruleset for type-prescription rules for
                   ;; each defparser we introduce.  Normally these rules
                   ;; are not helpful, but they are needed for the guard
                   ;; verification of mv-lets.
                   nil)

(defun defparser-fn (name formals args)
  (declare (xargs :guard (and (symbolp name)
                              (true-listp formals)
                              (equal (nthcdr (- (len formals) 2) formals)
                                     '(tokens warnings)))
                  :mode :program))
  (let* ((fn-name (intern-in-package-of-symbol (cat (symbol-name name) "-FN")
                                               name))
         (args-for-def   (throw-away-keyword-parts args))
         (decls          (butlast args-for-def 1))
         (body           (car (last args)))
         (count          (cdr (extract-keyword-from-args :count args)))
         (result         (cdr (extract-keyword-from-args :result args)))
         (result-hints   (cdr (extract-keyword-from-args :result-hints args)))
         (resultp-of-nil (extract-keyword-from-args :resultp-of-nil args))
         (true-listp     (cdr (extract-keyword-from-args :true-listp args)))
         (fails          (cdr (extract-keyword-from-args :fails args)))
         (guard          (extract-keyword-from-args :guard args))
         (hint-chicken-switch (cdr (extract-keyword-from-args
                                    :hint-chicken-switch args)))
         (verify-guards  (extract-keyword-from-args :verify-guards args))
         (thm-hyps       (if guard
                             `(and (force (vl-tokenlist-p tokens))
                                   ,(adjust-guard-for-theorems (cdr guard)))
                           `(force (vl-tokenlist-p tokens))))
         )
    `(progn
       (defmacro ,name (,@(butlast formals 2) &optional (tokens 'tokens) (warnings 'warnings))
         (list ',fn-name ,@formals))

       (defund ,fn-name ,formals
         (declare (xargs :guard ,(if guard
                                     `(and (vl-tokenlist-p tokens)
                                           (vl-warninglist-p warnings)
                                           ,(cdr guard))
                                   `(and (vl-tokenlist-p tokens)
                                         (vl-warninglist-p warnings)))
                         ,@(if verify-guards
                               `(:verify-guards ,(cdr verify-guards))
                             nil)))
         ,@decls
         (let ((__function__ ',name))
           (declare (ignorable __function__))
           ,body))

       (ACL2::add-to-ruleset defparser-type-prescriptions
                             '((:type-prescription ,fn-name)))

       (add-macro-alias ,name ,fn-name)
       (add-untranslate-pattern (,fn-name ,@formals) (,name ,@(butlast formals 2)))

       (encapsulate
        ()
        (local (in-theory (enable ,name)))

        ,@(if (not (or count result resultp-of-nil result-hints true-listp fails))
              nil
            `((defthm ,(intern-in-package-of-symbol
                        (cat "VL-TOKENLIST-P-OF-" (symbol-name name))
                        name)
                (implies (force (vl-tokenlist-p tokens))
                         (vl-tokenlist-p (mv-nth 2 (,name . ,formals))))
                :hints (,@(if hint-chicken-switch
                              nil
                            `((expand-and-maybe-induct-hint
                               '(,fn-name . ,formals)))))
                :rule-classes ((:rewrite :backchain-limit-lst 0)))

              (defthm ,(intern-in-package-of-symbol
                        (cat "VL-WARNINGLIST-P-OF-" (symbol-name name))
                        name)
                (implies (force (vl-warninglist-p warnings))
                         (vl-warninglist-p (mv-nth 3 (,name . ,formals))))
                :hints (,@(if hint-chicken-switch
                              nil
                            `((expand-and-maybe-induct-hint
                               '(,fn-name . ,formals)))))
                :rule-classes ((:rewrite :backchain-limit-lst 0)))))

        ,@(cond ((not fails)
                 nil)
                ((equal (symbol-name fails) "NEVER")
                 `((defthm ,(intern-in-package-of-symbol
                             (cat (symbol-name name) "-NEVER-FAILS")
                             name)
                     (not (mv-nth 0 (,name . ,formals)))
                     :hints(,@(if hint-chicken-switch
                                  '(("Goal" :in-theory (disable (force))))
                                `((expand-and-maybe-induct-hint
                                   '(,fn-name . ,formals) :disable '((force)))))))))
                ((equal (symbol-name fails) "GRACEFULLY")
                 `((defthm ,(intern-in-package-of-symbol
                             (cat (symbol-name name) "-FAILS-GRACEFULLY")
                             name)
                     (implies (mv-nth 0 (,name . ,formals))
                              (not (mv-nth 1 (,name . ,formals))))
                     :hints(,@(if hint-chicken-switch
                                  '(("Goal" :in-theory (disable (force))))
                                `((expand-and-maybe-induct-hint
                                   '(,fn-name . ,formals) :disable '((force)))))))))
                (t
                 (er hard? 'defparser "Bad :fails: ~s0." fails)))

        ,@(cond ((not result)
                 nil)
                (t
                 `((defthm ,(intern-in-package-of-symbol
                             (cat (symbol-name name) "-RESULT")
                             name)
                     ,(cond
                       ((and resultp-of-nil
                             (cdr resultp-of-nil)
                             (equal (symbol-name fails) "GRACEFULLY"))
                        ;; On failure val is nil, and resultp is true of
                        ;; nil, so resultp is always true of val.
                        `(implies ,thm-hyps
                                  ,(ACL2::subst `(mv-nth 1 (,name . ,formals))
                                                'val result)))

                       ((and resultp-of-nil
                             (not (cdr resultp-of-nil))
                             (equal (symbol-name fails) "GRACEFULLY"))
                        ;; Resultp is not true of nil, and fails
                        ;; gracefully, so result is true exactly when
                        ;; it does not fail.
                        `(implies ,thm-hyps
                                  (equal ,(ACL2::subst
                                           `(mv-nth 1 (,name . ,formals))
                                           'val result)
                                         (not (mv-nth 0 (,name . ,formals))))))

                       (t
                        ;; We don't know enough to make the theorem
                        ;; better, so just make it conditional.
                        `(implies (and (not (mv-nth 0 (,name . ,formals)))
                                       ,thm-hyps)
                                  ,(ACL2::subst
                                    `(mv-nth 1 (,name . ,formals))
                                    'val result))))
                     :hints (,@(if hint-chicken-switch
                                   nil
                                 `((expand-and-maybe-induct-hint
                                    '(,fn-name . ,formals))))
                             . ,result-hints)))))

        ,@(cond ((not true-listp)
                 nil)
                (t
                 `((defthm ,(intern-in-package-of-symbol
                             (cat (symbol-name name) "-TRUE-LISTP")
                             name)
                     (true-listp (mv-nth 1 (,name . ,formals)))
                     :rule-classes :type-prescription
                     :hints(,@(if hint-chicken-switch
                                  '(("Goal" :in-theory (disable (force))))
                                `((expand-and-maybe-induct-hint
                                   '(,fn-name . ,formals)
                                   :disable '((force))))))))))

        ,@(cond ((not count)
                 nil)
                ((equal (symbol-name count) "WEAK")
                 `((defthm ,(intern-in-package-of-symbol
                             (cat (symbol-name name) "-COUNT-WEAK")
                             name)
                     (<= (acl2-count (mv-nth 2 (,name . ,formals)))
                         (acl2-count tokens))
                     :rule-classes ((:rewrite) (:linear))
                     :hints(,@(if hint-chicken-switch
                                  '(("Goal" :in-theory (disable (force))))
                                `((expand-and-maybe-induct-hint
                                   '(,fn-name . ,formals)
                                   :disable '((force)))))))))

                ((equal (symbol-name count) "STRONG")
                 `((defthm ,(intern-in-package-of-symbol
                             (cat (symbol-name name) "-COUNT-STRONG")
                             name)
                     (and (<= (acl2-count (mv-nth 2 (,name . ,formals)))
                              (acl2-count tokens))
                          (implies (not (mv-nth 0 (,name . ,formals)))
                                   (< (acl2-count (mv-nth 2 (,name . ,formals)))
                                      (acl2-count tokens))))
                     :rule-classes ((:rewrite) (:linear))
                     :hints(,@(if hint-chicken-switch
                                  '(("Goal" :in-theory (disable (force))))
                                `((expand-and-maybe-induct-hint
                                   '(,fn-name . ,formals)
                                   :disable '((force)))))))))

                ((equal (symbol-name count) "STRONG-ON-VALUE")
                 `((defthm ,(intern-in-package-of-symbol
                             (cat (symbol-name name) "-COUNT-STRONG-ON-VALUE")
                             name)
                     (and (<= (acl2-count (mv-nth 2 (,name . ,formals)))
                              (acl2-count tokens))
                          (implies (mv-nth 1 (,name . ,formals))
                                   (< (acl2-count (mv-nth 2 (,name . ,formals)))
                                      (acl2-count tokens))))
                     :rule-classes ((:rewrite) (:linear))
                     :hints(,@(if hint-chicken-switch
                                  '(("Goal" :in-theory (disable (force))))
                                `((expand-and-maybe-induct-hint
                                   '(,fn-name . ,formals)
                                   :disable '((force)))))))))

                (t
                 (er hard? 'defparser "Bad :count: ~s0." count)))

        ))))

(defmacro defparser (name formals &rest args)
  (defparser-fn name formals args))



(defund vl-is-token?-fn (type tokens)
  (declare (xargs :guard (vl-tokenlist-p tokens)))
  (and (consp tokens)
       (eq (vl-token->type (car tokens)) type)))

(defmacro vl-is-token? (type &optional (tokens 'tokens))
  ;; We used to implement this inline, but now we call a function so we can
  ;; disable it and reduce the number of ifs in our proofs.
  `(vl-is-token?-fn ,type ,tokens))

(add-macro-alias vl-is-token? vl-is-token?-fn)
(add-untranslate-pattern (vl-is-token?-fn ?type tokens) (vl-is-token? ?type))

(defthm vl-is-token?-fn-when-not-consp-of-tokens
  (implies (not (consp tokens))
           (equal (vl-is-token?-fn type tokens)
                  nil))
  :hints(("Goal" :in-theory (enable vl-is-token?-fn))))



(defund vl-is-some-token?-fn (types tokens)
  (declare (xargs :guard (and (true-listp types)
                              (vl-tokenlist-p tokens))))
  (and (consp tokens)
       (member-eq (vl-token->type (car tokens)) types)
       t))

(defmacro vl-is-some-token? (types &optional (tokens 'tokens))
  ;; We used to implement this inline, but now we call a function so we can
  ;; disable it and reduce the number of ifs in our proofs.
  `(vl-is-some-token?-fn ,types ,tokens))

(add-macro-alias vl-is-some-token? vl-is-some-token?-fn)
(add-untranslate-pattern (vl-is-some-token?-fn ?types tokens) (vl-is-some-token? ?types))

(defthm vl-is-some-token?-fn-when-not-consp-of-tokens
  (implies (not (consp tokens))
           (equal (vl-is-some-token?-fn type tokens)
                  nil))
  :hints(("Goal" :in-theory (enable vl-is-some-token?-fn))))

(defthm vl-is-some-token?-fn-when-not-consp-of-types
  (implies (not (consp types))
           (equal (vl-is-some-token?-fn types tokens)
                  nil))
  :hints(("Goal" :in-theory (enable vl-is-some-token?-fn))))




(defund vl-parse-error-fn (function description tokens warnings)
  (declare (xargs :guard (and (symbolp function)
                              (stringp description)
                              (vl-tokenlist-p tokens)
                              (vl-warninglist-p warnings))))
  (mv (if (consp tokens)
          (list (cat "Parse error in ~s0 (at ~l1): " description)
                function (vl-token->loc (car tokens)))
        (list (cat "Parser error in ~s0 (at EOF): " description)
              function))
      nil tokens warnings))

(defmacro vl-parse-error (description &optional (tokens 'tokens) (warnings 'warnings))
  ;; We used to implement this inline, but now we call a function so we can
  ;; disable it and reduce the number of ifs in our proofs.
  `(vl-parse-error-fn __function__ ,description ,tokens ,warnings))

(add-macro-alias vl-parse-error vl-parse-error-fn)
(add-untranslate-pattern (vl-parse-error-fn ?function ?description tokens warnings)
                         (vl-parse-error ?function ?description))

(defthm err-of-vl-parse-error-fn-under-iff
  (iff (mv-nth 0 (vl-parse-error-fn function description tokens warnings))
       t)
  :hints(("Goal" :in-theory (enable vl-parse-error-fn))))

(defthm val-of-vl-parse-error-fn
  (equal (mv-nth 1 (vl-parse-error-fn function description tokens warnings))
         nil)
  :hints(("Goal" :in-theory (enable vl-parse-error-fn))))

(defthm tokens-of-vl-parse-error-fn
  (equal (mv-nth 2 (vl-parse-error-fn function description tokens warnings))
         tokens)
  :hints(("Goal" :in-theory (enable vl-parse-error-fn))))

(defthm warnings-of-vl-parse-error-fn
  (equal (mv-nth 3 (vl-parse-error-fn function description tokens warnings))
         warnings)
  :hints(("Goal" :in-theory (enable vl-parse-error-fn))))




(defund vl-parse-warning-fn (function type description tokens warnings)
  (declare (xargs :guard (and (symbolp function)
                              (symbolp type)
                              (stringp description)
                              (vl-tokenlist-p tokens)
                              (vl-warninglist-p warnings))))
  (let* ((msg (if (atom tokens)
                  (cat "Warning in ~s0 (at EOF): " description)
                (cat "Warning in ~s0 (at ~l1): " description)))
         (args (if (atom tokens)
                   (list function)
                 (list function (vl-token->loc (car tokens)))))
         (warning (make-vl-warning :type (mbe :logic (and (symbolp type) type)
                                              :exec type)
                                   :msg msg
                                   :args args
                                   :fn (mbe :logic (and (symbolp function) function)
                                            :exec function))))
     (mv nil nil tokens (cons warning warnings))))

(defmacro vl-parse-warning (type description &optional (tokens 'tokens) (warnings 'warnings))
  ;; We used to implement this inline, but now we call a function so we can
  ;; disable it and reduce the number of ifs in our proofs.
  `(vl-parse-warning-fn __function__ ,type ,description ,tokens ,warnings))

(add-macro-alias vl-parse-warning vl-parse-warning-fn)
(add-untranslate-pattern (vl-parse-warning-fn ?function ?description tokens warnings)
                         (vl-parse-warning ?function ?description))

(defthm err-of-vl-parse-warning-fn
  (equal (mv-nth 0 (vl-parse-warning-fn function type description tokens warnings))
         nil)
  :hints(("Goal" :in-theory (enable vl-parse-warning-fn))))

(defthm val-of-vl-parse-warning-fn
  (equal (mv-nth 1 (vl-parse-warning-fn function type description tokens warnings))
         nil)
  :hints(("Goal" :in-theory (enable vl-parse-warning-fn))))

(defthm tokens-of-vl-parse-warning-fn
  (equal (mv-nth 2 (vl-parse-warning-fn function type description tokens warnings))
         tokens)
  :hints(("Goal" :in-theory (enable vl-parse-warning-fn))))

(defthm vl-warninglist-p-of-vl-parse-warning-fn
  (implies (force (vl-warninglist-p warnings))
           (equal (vl-warninglist-p (mv-nth 3 (vl-parse-warning-fn function type description tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-parse-warning-fn))))




(defmacro vl-unimplemented ()
  `(vl-parse-error "Unimplemented Verilog production."))



(defund vl-match-token-fn (function type tokens warnings)
  "Returns (MV ERROR TOKEN REMAINDER WARNINGS) for SEQW compatibility."
  (declare (xargs :guard (and (symbolp function)
                              (vl-tokenlist-p tokens)
                              (vl-warninglist-p warnings))))

; If the first token has the given type, we remove it from the list of tokens
; and return it as our value.  Otherwise, we signal an error.

  (if (not (consp tokens))
      (vl-parse-error-fn function "Unexpected EOF." tokens warnings)
    (let ((token1 (car tokens)))
      (if (not (eq type (vl-token->type token1)))
          ;; We want a custom error message, so we don't use vl-parse-error-fn.
          (mv (list "Parse error in ~s0 (at ~l1): expected ~s2, but found ~s3."
                    function (vl-token->loc token1) type (vl-token->type token1))
              nil tokens warnings)
        (mv nil token1 (cdr tokens) warnings)))))

(defmacro vl-match-token (type &optional (tokens 'tokens) (warnings 'warnings))
  ;; We used to implement this inline, but now we call a function so we can
  ;; disable it and reduce the number of ifs in our proofs.
  `(vl-match-token-fn __function__ ,type ,tokens ,warnings))

(add-macro-alias vl-match-token vl-match-token-fn)
(add-untranslate-pattern (vl-match-token-fn ?function ?type tokens warnings)
                         (vl-match-token ?function ?type))

(defthm vl-match-token-fn-succeeds-when-vl-is-token?-fn
  (iff (mv-nth 0 (vl-match-token-fn function type tokens warnings))
       (not (vl-is-token?-fn type tokens)))
  :hints(("Goal" :in-theory (enable vl-is-token?-fn vl-match-token-fn))))

(defthm vl-match-token-fn-fails-gracefully
  (implies (not (vl-is-token?-fn type tokens))
           (not (mv-nth 1 (vl-match-token-fn function type tokens warnings))))
  :hints(("Goal" :in-theory (enable vl-match-token-fn
                                    vl-is-token?-fn))))

(defthm vl-token-p-of-vl-match-token-fn
  (implies (and (vl-is-token?-fn type tokens)
                (force (vl-tokenlist-p tokens)))
           (equal (vl-token-p (mv-nth 1 (vl-match-token-fn function type tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-match-token-fn
                                    vl-is-token?-fn))))

(defthm vl-token->type-of-vl-match-token-fn
  (implies (vl-is-token?-fn type tokens)
           (equal (vl-token->type (mv-nth 1 (vl-match-token-fn function type tokens warnings)))
                  type))
  :hints(("Goal" :in-theory (enable vl-match-token-fn
                                    vl-is-token?-fn))))

(defthm vl-tokenlist-p-of-vl-match-token-fn
  (implies (force (vl-tokenlist-p tokens))
           (equal (vl-tokenlist-p (mv-nth 2 (vl-match-token-fn function type tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-match-token-fn))))

(defthm vl-warninglist-p-vl-match-token-fn
  (implies (force (vl-warninglist-p warnings))
           (equal (vl-warninglist-p (mv-nth 3 (vl-match-token-fn function type tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-match-token-fn))))

(defthm vl-match-token-fn-count-strong-on-value
  (and (<= (acl2-count (mv-nth 2 (vl-match-token-fn function type tokens warnings)))
           (acl2-count tokens))
       (implies (mv-nth 1 (vl-match-token-fn function type tokens warnings))
                (< (acl2-count (mv-nth 2 (vl-match-token-fn function type tokens warnings)))
                   (acl2-count tokens))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-match-token-fn))))

(defthm equal-of-vl-match-token-fn-count
  (equal (equal (acl2-count (mv-nth 2 (vl-match-token-fn function type tokens warnings)))
                (acl2-count tokens))
         (if (mv-nth 0 (vl-match-token-fn function type tokens warnings))
             t
           nil))
  :hints(("Goal" :in-theory (enable vl-match-token-fn))))





(defund vl-match-some-token-fn (function types tokens warnings)
  "Returns (MV ERROR TOKEN REMAINDER WARNINGS) for SEQW compatibility."
  (declare (xargs :guard (and (symbolp function)
                              (true-listp types)
                              (vl-tokenlist-p tokens)
                              (vl-warninglist-p warnings))))
  (if (not (consp tokens))
      (vl-parse-error-fn function "Unexpected EOF." tokens warnings)
    (let ((token1 (car tokens)))
      (if (not (member-eq (vl-token->type token1) types))
          (mv (list "Parse error in ~s0 (at ~l1): expected one of ~x2, but found ~s3."
                    function (vl-token->loc token1) types (vl-token->type token1))
              nil tokens warnings)
        (mv nil token1 (cdr tokens) warnings)))))

(defmacro vl-match-some-token (types &optional (tokens 'tokens) (warnings 'warnings))
  ;; We used to implement this inline, but now we call a function so we can
  ;; disable it and reduce the number of ifs in our proofs.
  `(vl-match-some-token-fn __function__ ,types ,tokens ,warnings))

(add-macro-alias vl-match-some-token vl-match-some-token-fn)
(add-untranslate-pattern (vl-match-some-token-fn ?function ?types tokens warnings)
                         (vl-match-some-token ?function ?types))

(defthm vl-match-some-token-fn-succeeds-when-vl-is-some-token?-fn
  (iff (mv-nth 0 (vl-match-some-token-fn function types tokens warnings))
       (not (vl-is-some-token?-fn types tokens)))
  :hints(("Goal" :in-theory (enable vl-is-some-token?-fn
                                    vl-match-some-token-fn))))

(defthm vl-match-some-token-fn-fails-gracefully
  (implies (not (vl-is-some-token?-fn types tokens))
           (equal (mv-nth 1 (vl-match-some-token-fn function types tokens warnings))
                  nil))
  :hints(("Goal" :in-theory (enable vl-match-some-token-fn
                                    vl-is-some-token?-fn))))

(defthm vl-token-p-of-vl-match-some-token-fn
  (implies (and (vl-is-some-token?-fn types tokens)
                (force (vl-tokenlist-p tokens)))
           (equal (vl-token-p (mv-nth 1 (vl-match-some-token-fn function types tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-match-some-token-fn
                                    vl-is-some-token?-fn))))

(defthm vl-tokenlist-p-of-vl-match-some-token-fn
  (implies (force (vl-tokenlist-p tokens))
           (equal (vl-tokenlist-p (mv-nth 2 (vl-match-some-token-fn function types tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-match-some-token-fn
                                    vl-is-some-token?-fn))))

(defthm vl-warninglist-p-vl-match-some-token-fn
  (implies (force (vl-warninglist-p warnings))
           (equal (vl-warninglist-p (mv-nth 3 (vl-match-some-token-fn function types tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-match-some-token-fn))))

(defthm vl-match-some-token-fn-count-strong-on-value
  (and (<= (acl2-count (mv-nth 2 (vl-match-some-token-fn function types tokens warnings)))
           (acl2-count tokens))
       (implies (mv-nth 1 (vl-match-some-token-fn function types tokens warnings))
                (< (acl2-count (mv-nth 2 (vl-match-some-token-fn function types tokens warnings)))
                   (acl2-count tokens))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-match-some-token-fn))))

(defthm equal-of-vl-match-some-token-fn-count
  (equal (equal (acl2-count (mv-nth 2 (vl-match-some-token-fn function types tokens warnings)))
                (acl2-count tokens))
         (if (mv-nth 0 (vl-match-some-token-fn function types tokens warnings))
             t
           nil))
  :hints(("Goal" :in-theory (enable vl-match-some-token-fn))))




(defund vl-type-of-matched-token (types tokens)
  (declare (xargs :guard (and (true-listp types)
                              (vl-tokenlist-p tokens))))

; We added this when we disabled the functions vl-is-some-token? and
; vl-match-some-token to address the problem of reasoning about which kind of
; token was matched.  We could prove, for instance, that
;
;    (implies (vl-is-some-token? types tokens)
;             (member-eq (second (vl-match-some-token types tokens))
;                        types))
;
; But it was difficult to get ACL2 to actually make use of this rule, because
; the member-eq term never arose.
;
; Instead, we use this function so that we can rewrite
;
;    (equal (mv-nth 1 (vl-match-some-token types tokens))
;           (vl-type-of-token)).

  (if (and (consp tokens)
           (member-eq (vl-token->type (car tokens)) types))
      (vl-token->type (car tokens))
    nil))

(defthm vl-token->type-of-vl-match-some-token-fn
  (equal (vl-token->type (mv-nth 1 (vl-match-some-token-fn function types tokens warnings)))
         (vl-type-of-matched-token types tokens))
  :hints(("Goal" :in-theory (enable vl-match-some-token-fn
                                    vl-type-of-matched-token))))

(defthm vl-type-of-matched-token-when-not-consp-of-types
  (implies (not (consp types))
           (equal (vl-type-of-matched-token types tokens)
                  nil))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token))))

(defthm vl-type-of-matched-token-when-not-consp-of-tokens
  (implies (not (consp tokens))
           (equal (vl-type-of-matched-token types tokens)
                  nil))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token))))



;; Experimental rules to kick ass.

(defthm magically-reduce-possible-types-from-vl-is-some-token?
  (implies (and (not (equal (vl-type-of-matched-token types2 tokens) exclude))
                (syntaxp (quotep types))
                (syntaxp (quotep types2))
                (member-equal exclude types)
                (subsetp-equal types types2))
           (equal (vl-is-some-token? types tokens)
                  (vl-is-some-token? (remove-equal exclude types) tokens)))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token
                                    vl-is-some-token?))))

(defthm magically-reduce-possible-types-from-vl-type-of-matched-token
  (implies (and (not (equal (vl-type-of-matched-token types2 tokens) exclude))
                (syntaxp (quotep types))
                (syntaxp (quotep types2))
                (member-equal exclude types)
                (subsetp-equal types types2))
           (equal (vl-type-of-matched-token types tokens)
                  (vl-type-of-matched-token (remove-equal exclude types) tokens)))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token
                                    vl-is-some-token?))))

(defthm magically-resolve-vl-is-some-token?
  (implies (and (equal (vl-type-of-matched-token types2 tokens) value)
                (member-equal value types)
                value)
           (equal (vl-is-some-token? types tokens)
                  t))
  :hints(("Goal" :in-theory (enable vl-is-some-token?
                                    vl-type-of-matched-token))))

(defthm magically-resolve-type-of-matched-token
  (implies (and (equal (vl-type-of-matched-token types2 tokens) value)
                (member-equal value types)
                value)
           (equal (vl-type-of-matched-token types tokens)
                  value))
  :hints(("Goal" :in-theory (enable vl-is-some-token?
                                    vl-type-of-matched-token))))

(defthm vl-type-of-matched-token-under-iff
  (implies (not (member-equal nil types))
           (iff (vl-type-of-matched-token types tokens)
                (vl-is-some-token? types tokens)))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token
                                    vl-is-some-token?))))







(defund vl-current-loc-fn (tokens warnings)
  "Returns (MV ERROR LOC REMAINDER WARNINGS) for SEQW compatibility."
  (declare (xargs :guard (and (vl-tokenlist-p tokens)
                              (vl-warninglist-p warnings))))

; We return the location of the first token, if there is one.  Or, if the
; token stream is empty, we just return *vl-fakeloc*

  (mv nil
      (if (consp tokens)
          (vl-token->loc (car tokens))
        *vl-fakeloc*)
      tokens
      warnings))

(defmacro vl-current-loc (&optional (tokens 'tokens) (warnings 'warnings))
  ;; We used to implement this inline, but now we call a function so we can
  ;; disable it and reduce the number of ifs in our proofs.
  `(vl-current-loc-fn ,tokens ,warnings))

(add-macro-alias vl-current-loc vl-current-loc-fn)
(add-untranslate-pattern (vl-current-loc tokens warnings)
                         (vl-current-loc))

(defthm vl-current-loc-fn-never-fails
  (equal (mv-nth 0 (vl-current-loc-fn tokens warnings))
         nil)
  :hints(("Goal" :in-theory (enable vl-current-loc-fn))))

(defthm vl-location-p-of-vl-current-loc-fn
  (implies (force (vl-tokenlist-p tokens))
           (equal (vl-location-p (mv-nth 1 (vl-current-loc-fn tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-current-loc-fn))))

(defthm tokens-of-vl-current-loc-fn
  (equal (mv-nth 2 (vl-current-loc-fn tokens warnings))
         tokens)
  :hints(("Goal" :in-theory (enable vl-current-loc-fn))))

(defthm warnings-of-vl-current-loc-fn
  (equal (mv-nth 3 (vl-current-loc-fn tokens warnings))
         warnings)
  :hints(("Goal" :in-theory (enable vl-current-loc-fn))))





(defmacro vl-copy-tokens (&optional (tokens 'tokens) (warnings 'warnings))
  "Returns (MV ERROR TOKENS TOKENS WARNINGS) for SEQW compatibility."
  (declare (xargs :guard t))
  `(let ((tokens ,tokens)
         (warnings ,warnings))
     (mv nil tokens tokens warnings)))




(defund vl-match-any-fn (function tokens warnings)
  (declare (xargs :guard (and (symbolp function)
                              (vl-tokenlist-p tokens)
                              (vl-warninglist-p warnings))))
  (if (not (consp tokens))
      (vl-parse-error-fn function "Unexpected EOF." tokens warnings)
    (mv nil (car tokens) (cdr tokens) warnings)))

(defmacro vl-match-any (&optional (tokens 'tokens) (warnings 'warnings))
  `(vl-match-any-fn __function__ ,tokens ,warnings))

(add-macro-alias vl-match-any vl-match-any-fn)
(add-untranslate-pattern (vl-match-any-fn ?function tokens warnings)
                         (vl-match-any ?function))

(defthm vl-match-any-fn-fails-gracefully
  (implies (mv-nth 0 (vl-match-any-fn function tokens warnings))
           (equal (mv-nth 1 (vl-match-any-fn function tokens warnings))
                  nil))
  :hints(("Goal" :in-theory (enable vl-match-any-fn))))

(defthm vl-tokenlist-p-of-vl-match-any-fn
  (implies (force (vl-tokenlist-p tokens))
           (vl-tokenlist-p (mv-nth 2 (vl-match-any-fn functions tokens warnings))))
  :hints(("Goal" :in-theory (enable vl-match-any-fn))))

(defthm vl-warninglist-p-of-vl-match-any-fn
  (implies (force (vl-warninglist-p warnings))
           (vl-warninglist-p (mv-nth 3 (vl-match-any-fn functions tokens warnings))))
  :hints(("Goal" :in-theory (enable vl-match-any-fn))))

(defthm vl-token-p-of-vl-match-any-fn
  (implies (and (not (mv-nth 0 (vl-match-any-fn functions tokens warnings)))
                (force (vl-tokenlist-p tokens)))
           (vl-token-p (mv-nth 1 (vl-match-any-fn function tokens warnings))))
  :hints(("Goal" :in-theory (enable vl-match-any-fn))))

(defthm vl-match-any-fn-count-strong-on-value
  (and (<= (acl2-count (mv-nth 2 (vl-match-any-fn function tokens warnings)))
           (acl2-count tokens))
       (implies (mv-nth 1 (vl-match-any-fn function tokens warnings))
                (< (acl2-count (mv-nth 2 (vl-match-any-fn function tokens warnings)))
                   (acl2-count tokens))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-match-any-fn))))

(defthm equal-of-vl-match-any-fn-count
  (equal (equal (acl2-count (mv-nth 2 (vl-match-any-fn function tokens warnings)))
                (acl2-count tokens))
         (if (mv-nth 0 (vl-match-any-fn function tokens warnings))
             t
           nil))
  :hints(("Goal" :in-theory (enable vl-match-any-fn))))




(defund vl-match-any-except-fn (function types tokens warnings)
  "Returns (MV ERROR TOKEN REMAINDER WARNINGS) for SEQW compatibility."
  (declare (xargs :guard (and (symbolp function)
                              (true-listp types)
                              (vl-tokenlist-p tokens)
                              (vl-warninglist-p warnings))))
  (if (not (consp tokens))
      (vl-parse-error-fn function "Unexpected EOF." tokens warnings)
    (let ((token1 (car tokens)))
      (if (member-eq (vl-token->type token1) types)
          (mv (list "Parse error in ~s0 (at ~l1): unexpected ~s2."
                    function (vl-token->loc token1) (vl-token->type token1))
              nil tokens warnings)
        (mv nil token1 (cdr tokens) warnings)))))

(defmacro vl-match-any-except (types &optional (tokens 'tokens) (warnings 'warnings))
  `(vl-match-any-except-fn __function__ ,types ,tokens ,warnings))

(add-macro-alias vl-match-any-except vl-match-any-except-fn)
(add-untranslate-pattern (vl-match-any-except-fn ?function ?types tokens warnings)
                         (vl-match-any-except ?function ?types))

(defthm vl-match-any-except-fn-succeeds-when-vl-is-some-token?-fn
  (iff (mv-nth 0 (vl-match-any-except-fn function types tokens warnings))
       (or (atom tokens)
           (vl-is-some-token?-fn types tokens)))
  :hints(("Goal" :in-theory (enable vl-is-some-token?-fn
                                    vl-match-any-except-fn))))

(defthm vl-match-any-except-fn-fails-gracefully
  (implies (or (atom tokens)
               (vl-is-some-token?-fn types tokens))
           (equal (mv-nth 1 (vl-match-any-except-fn function types tokens warnings))
                  nil))
  :hints(("Goal" :in-theory (enable vl-match-any-except-fn
                                    vl-is-some-token?-fn))))

(defthm vl-token-p-of-vl-match-any-except-fn
  (implies (and (not (vl-is-some-token?-fn types tokens))
                (consp tokens)
                (force (vl-tokenlist-p tokens)))
           (equal (vl-token-p (mv-nth 1 (vl-match-any-except-fn function types tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-match-any-except-fn
                                    vl-is-some-token?-fn))))

(defthm vl-tokenlist-p-of-vl-match-any-except-fn
  (implies (force (vl-tokenlist-p tokens))
           (equal (vl-tokenlist-p (mv-nth 2 (vl-match-any-except-fn function types tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-match-any-except-fn))))

(defthm vl-warninglist-p-vl-match-any-except-fn
  (implies (force (vl-warninglist-p warnings))
           (equal (vl-warninglist-p (mv-nth 3 (vl-match-any-except-fn function types tokens warnings)))
                  t))
  :hints(("Goal" :in-theory (enable vl-match-any-except-fn))))

(defthm vl-match-any-except-fn-count-strong-on-value
  (and (<= (acl2-count (mv-nth 2 (vl-match-any-except-fn function types tokens warnings)))
           (acl2-count tokens))
       (implies (mv-nth 1 (vl-match-any-except-fn function types tokens warnings))
                (< (acl2-count (mv-nth 2 (vl-match-any-except-fn function types tokens warnings)))
                   (acl2-count tokens))))
  :rule-classes ((:rewrite) (:linear))
  :hints(("Goal" :in-theory (enable vl-match-any-except-fn))))

(defthm equal-of-vl-match-any-except-fn-count
  (equal (equal (acl2-count (mv-nth 2 (vl-match-any-except-fn function types tokens warnings)))
                (acl2-count tokens))
         (if (mv-nth 0 (vl-match-any-except-fn function types tokens warnings))
             t
           nil))
  :hints(("Goal" :in-theory (enable vl-match-any-except-fn))))






;                           VL-MUTUAL-RECURSION
;
; This is an extension of mutual-recursion which performs single-step
; macroexpansion on its arguments until they are resolved into defuns,
; defmacros, add-macro-alias, or add-untranslate-patterns.  We move the defuns
; to before the regular call of mutual-recursion, and the macro aliases and
; untranslate patterns to afterwards.  This isn't particularly general, but it
; works with defparser, at least.

(mutual-recursion

 (defun vl-macroexpand-until-recognized-type (form types state)
   (declare (xargs :stobjs state :mode :program))
   (cond ((and (consp form)
               (member-eq (car form) types))
          (mv nil (list form) state))
         ((and (consp form)
               (eq (car form) 'progn))
          (vl-macroexpand-all-until-recognized-type (cdr form) types state))
         (t
          (mv-let (erp val state)
                  (acl2::macroexpand1 form 'vl-macroexpand-until-recognized-type state)
                  (if erp
                      (mv erp val state)
                    (vl-macroexpand-until-recognized-type val types state))))))

 (defun vl-macroexpand-all-until-recognized-type (forms types state)
   (declare (xargs :stobjs state :mode :program))
   (if (atom forms)
       (mv nil nil state)
     (mv-let (erp first state)
             (vl-macroexpand-until-recognized-type (car forms) types state)
             (if erp
                 (mv erp first state)
               (mv-let (erp rest state)
                       (vl-macroexpand-all-until-recognized-type (cdr forms) types state)
                       (if erp
                           (mv erp rest state)
                         (mv erp (append first rest) state))))))))

(defun vl-gather-forms-of-type (forms types)
  (declare (xargs :guard (symbol-listp types)))
  (cond ((atom forms)
         nil)
        ((and (consp (car forms))
              (member-eq (caar forms) types))
         (cons (car forms)
               (vl-gather-forms-of-type (cdr forms) types)))
        (t
         (vl-gather-forms-of-type (cdr forms) types))))

(defun vl-mutual-recursion-fn (forms state)
  (declare (xargs :stobjs state :mode :program))
  (let* ((main-types '(defun defund))
         (pre-types  '(defmacro))
         (post-types '(add-untranslate-pattern add-macro-alias encapsulate acl2::add-to-ruleset
                                               in-theory))
         (all-types  (append main-types pre-types post-types)))
    (mv-let (erp val state)
            (vl-macroexpand-all-until-recognized-type forms all-types state)
            (if erp
                (mv erp val state)
              (let ((pre-forms  (vl-gather-forms-of-type val pre-types))
                    (main-forms (vl-gather-forms-of-type val main-types))
                    (post-forms (vl-gather-forms-of-type val post-types)))
                (mv nil `(encapsulate
                          ()
                          ,@pre-forms
                          (mutual-recursion ,@main-forms)
                          ,@post-forms)
                    state))))))

(defmacro vl-mutual-recursion (&rest forms)
  `(make-event (vl-mutual-recursion-fn ',forms state)))


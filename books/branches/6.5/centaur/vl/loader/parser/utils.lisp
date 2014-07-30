; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "../config")
(include-book "../lexer/tokens")
(include-book "../../util/warnings")
(include-book "misc/seqw" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "tools/rulesets" :dir :system)
(local (include-book "../../util/arithmetic"))

(defxdoc parse-utils
  :parents (parser)
  :short "Supporting functions for the parser.")

(local (xdoc::set-default-parents parse-utils))


(defval *vl-default-token*
  (make-vl-plaintoken :type :vl-ws
                      :etext (list (make-vl-echar
                                    :char #\Space
                                    :loc *vl-fakeloc*))))



(define vl-tokenlist-fix ((x vl-tokenlist-p))
  :verify-guards nil
  :inline t
  (mbe :logic
       (if (atom x)
           x
         (cons (if (vl-token-p (car x))
                   (car x)
                 *vl-default-token*)
               (vl-tokenlist-fix (cdr x))))
       :exec x)
  ///
  (defthm vl-tokenlist-p-of-vl-tokenlist-fix
    (vl-tokenlist-p (vl-tokenlist-fix x)))
  (defthm vl-tokenlist-fix-when-vl-tokenlist-p
    (implies (vl-tokenlist-p x)
             (equal (vl-tokenlist-fix x)
                    x)))
  (verify-guards+ vl-tokenlist-fix)
  (defthm len-of-vl-tokenlist-fix
    (equal (len (vl-tokenlist-fix x))
           (len x)))
  (defthm consp-of-vl-tokenlist-fix
    (equal (consp (vl-tokenlist-fix x))
           (consp x)))
  (defthm cdr-of-vl-tokenlist-fix
    (equal (cdr (vl-tokenlist-fix (cons a x)))
           (vl-tokenlist-fix x)))
  (defthm len-of-cdr-of-vl-tokenlist-fix
    (equal (len (cdr (vl-tokenlist-fix x)))
           (len (cdr x)))))



(defxdoc defparser
  :short "Core macro for writing recursive-descent parsers, used throughout
VL's parsing routines."
  :long "<h3>General Form</h3>

<h3>BOZO warning this documentation is very out of date</h3>

@({
     (defparser name (x y)

        [:guard (blah x y)]
        [:verify-guards { t, nil }]
        [:count { weak, strong, strong-on-value }]
        [:result (blah-blah val)]
        [:resultp-of-nil { t, nil }]
        [:true-listp { t, nil }]
        [:fails { never, gracefully }]
        [:result-hints ((\"Goal\" ...))]

        [(declare ...)]
        [(declare ...)]
        <body>             ;; usually (seqw tokens warnings ...)
        )

<p>Such an event always introduces:</p>

<ul>
<li>A macro, (foo x y), that just calls (foo-fn x y tokens warnings).</li>

<li>A function, (foo-fn x y tokens warnings), that implicitly binds the variable
    __function__ to 'foo and otherwise has the given bodies and declares, with
    the :guard thrown in if that is provided.</li>

<li>An add-macro-alias so foo can be used in place of foo-fn in enables and
    disables.</li>

<li>An untranslate-pattern so that (foo-fn x y tokens warnings) is displayed as
    (foo x y) during theorems.</li.

</ul>

<p>In addition to these events, several theorems may be generated depending
upon the optional keyword arguments given above.  In particular, if any of the
following keywords are provided, then some theorems will be generated:</p>

@({ result, resultp-of-nil, true-listp, count, fails })

<p>The RESULT theorem will forcibly assume (vl-tokenlist-p tokens), and you can
 also sort of assume that no error has occurred (the actual rule we produce is
 influenced by the RESULTP-OF-NIL setting).  All you have to say is the
 property you want to establish, targetting the variable VAL.</p>

<p>The TRUE-LISTP flag may be set when foo unconditionally returns a true-listp,
 and is only used to generate a type-prescription rule for foo.</p>

<p>The FAILS keyword can be used to introduce a theorem about the failure
behavior of a parsing function.  Recall that we have standardized upon the (mv
err val tokens) format for all of our parsing functions.  We say that our
functions fail GRACEFULLY if, whenever they return a non-nil err, the val
returned is nil.  Almost all of our functions fail gracefully, and we can
sometimes exploit this fact along with resultp-of-nil to create stronger
rewrite rules for the result theorem.  Another common paradigm is a parser that
NEVER fails -- e.g., perhaps it is for an \"optional\" production or for \"zero
or more occurrences\" of something.</p>

<p>The COUNT theorem is used to create a theorem about (len tokens).  In
practice, most parsers have a STRONG count-decreasing behavior, which is to say
that they always decrease the length on success.  But functions which never
fail, such as \"match zero or more\" parsers, usually have a weaker property
which we call STRONG-ON-VALUE, which means that whenever the value they return
is non-nil, the count decreases.  We also allow for WEAK count theorems, which
just say the count never increases, but these do not occur very
frequently.</p>")

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

              ;; After adding token fixing, I found that I could run into weird
              ;; loops due to (vl-warninglist-fix warnings) and
              ;; (vl-tokenlist-fix tokens) being around.  To try to avoid this,
              ;; I no longer let warnings be free, either.
              (frees (set-difference-eq (cdr fncall) '(tokens warnings)))
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

(def-ruleset! defparser-type-prescriptions
  ;; This is a ruleset for type-prescription rules for each defparser we
  ;; introduce.  Normally these rules are not helpful, but they are needed for
  ;; the guard verification of mv-lets.
  nil)

(defun defparser-fn (name formals args)
  (declare (xargs :guard (and (symbolp name)
                              (true-listp formals)
                              ;; Tokens, warnings, and config will be provided
                              ;; automatically
                              (not (member 'tokens formals))
                              (not (member 'warnings formals))
                              (not (member 'config formals)))
                  :mode :program))
  (b* ((fn-name
        ;; BOZO want to use defguts or something instead
        (intern-in-package-of-symbol (cat (symbol-name name) "-FN") name))
       (fn-formals
        (append formals '(tokens warnings config)))

       ((mv args rest-events) (std::split-/// name args))

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

       (parents        (extract-keyword-from-args :parents args))
       (short          (extract-keyword-from-args :short args))
       (long           (extract-keyword-from-args :long args))

       (measure        (or (cdr (extract-keyword-from-args :measure args))
                           '(len tokens)))
       (hint-chicken-switch (cdr (extract-keyword-from-args
                                  :hint-chicken-switch args)))
       (verify-guards  (extract-keyword-from-args :verify-guards args))
       (thm-hyps       (if guard
                           `(and ;(force (vl-tokenlist-p tokens))
                                 ,(adjust-guard-for-theorems (cdr guard)))
                         `(and ;(force (vl-tokenlist-p tokens))
                           t))))
    `(define ,name
       ,(append formals
                '(&key
                  ((tokens   vl-tokenlist-p)   'tokens)
                  ((warnings vl-warninglist-p) 'warnings)
                  ((config   vl-loadconfig-p)  'config)
                  ))
       :returns (mv (errmsg?)
                    (value)
                    (tokens)
                    (warnings))
       ,@(and parents       `(:parents ,(cdr parents)))
       ,@(and short         `(:short ,(cdr short)))
       ,@(and long          `(:long ,(cdr long)))
       ,@(and guard         `(:guard ,(cdr guard)))
       ,@(and verify-guards `(:verify-guards ,(cdr verify-guards)))
       :measure ,measure
       ,@decls
       (declare (ignorable config))
       (b* ((warnings (mbe :logic (vl-warninglist-fix warnings)
                           :exec warnings))
            (tokens   (mbe :logic (vl-tokenlist-fix tokens)
                           :exec tokens)))
         ,body)
       ///
       (ACL2::add-to-ruleset defparser-type-prescriptions '((:t ,name)))

       (defthm ,(intern-in-package-of-symbol
                 (cat (symbol-name name) "-OF-VL-TOKENLIST-FIX")
                 name)
         (equal (,fn-name . ,(subst '(vl-tokenlist-fix tokens) 'tokens fn-formals))
                (,fn-name . ,fn-formals))
         :hints(("Goal"
                 :expand ((,fn-name . ,(subst '(vl-tokenlist-fix tokens)
                                              'tokens fn-formals))
                          (,fn-name . ,fn-formals)))))

       (defthm ,(intern-in-package-of-symbol
                 (cat (symbol-name name) "-OF-VL-WARNINGLIST-FIX")
                 name)
         (equal (,fn-name . ,(subst '(vl-warninglist-fix warnings)
                                    'warnings fn-formals))
                (,fn-name . ,fn-formals))
         :hints(("Goal"
                 :expand ((,fn-name . ,(subst '(vl-warninglist-fix warnings)
                                              'warnings fn-formals))
                          (,fn-name . ,fn-formals)))))

       ,@(if (not (or count result resultp-of-nil result-hints true-listp fails))
             nil
           `((defthm ,(intern-in-package-of-symbol
                       (cat "VL-TOKENLIST-P-OF-" (symbol-name name))
                       name)
               (vl-tokenlist-p (mv-nth 2 (,name . ,formals)))
               :hints (,@(if hint-chicken-switch
                             nil
                           `((expand-and-maybe-induct-hint
                              '(,fn-name . ,fn-formals))))))

             (defthm ,(intern-in-package-of-symbol
                       (cat "VL-WARNINGLIST-P-OF-" (symbol-name name))
                       name)
               (vl-warninglist-p (mv-nth 3 (,name . ,formals)))
               :hints (,@(if hint-chicken-switch
                             nil
                           `((expand-and-maybe-induct-hint
                              '(,fn-name . ,fn-formals))))))))

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
                                  '(,fn-name . ,fn-formals) :disable '((force)))))))))
               ((equal (symbol-name fails) "GRACEFULLY")
                `((defthm ,(intern-in-package-of-symbol
                            (cat (symbol-name name) "-FAILS-GRACEFULLY")
                            name)
                    (implies (mv-nth 0 (,name . ,formals))
                             (not (mv-nth 1 (,name . ,formals))))
                    :hints(,@(if hint-chicken-switch
                                 '(("Goal" :in-theory (disable (force))))
                               `((expand-and-maybe-induct-hint
                                  '(,fn-name . ,fn-formals) :disable '((force)))))))))
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
                                   '(,fn-name . ,fn-formals))))
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
                                  '(,fn-name . ,fn-formals)
                                  :disable '((force))))))))))

       ,@(cond ((not count)
                nil)
               ((equal (symbol-name count) "WEAK")
                `((defthm ,(intern-in-package-of-symbol
                            (cat (symbol-name name) "-COUNT-WEAK")
                            name)
                    (<= (len (mv-nth 2 (,name . ,formals)))
                        (len tokens))
                    :rule-classes ((:rewrite) (:linear))
                    :hints(,@(if hint-chicken-switch
                                 '(("Goal" :in-theory (disable (force))))
                               `((expand-and-maybe-induct-hint
                                  '(,fn-name . ,fn-formals)
                                  :disable '((force)))))))))

               ((equal (symbol-name count) "STRONG")
                `((defthm ,(intern-in-package-of-symbol
                            (cat (symbol-name name) "-COUNT-STRONG")
                            name)
                    (and (<= (len (mv-nth 2 (,name . ,formals)))
                             (len tokens))
                         (implies (not (mv-nth 0 (,name . ,formals)))
                                  (< (len (mv-nth 2 (,name . ,formals)))
                                     (len tokens))))
                    :rule-classes ((:rewrite) (:linear))
                    :hints(,@(if hint-chicken-switch
                                 '(("Goal" :in-theory (disable (force))))
                               `((expand-and-maybe-induct-hint
                                  '(,fn-name . ,fn-formals)
                                  :disable '((force)))))))))

               ((equal (symbol-name count) "STRONG-ON-VALUE")
                `((defthm ,(intern-in-package-of-symbol
                            (cat (symbol-name name) "-COUNT-STRONG-ON-VALUE")
                            name)
                    (and (<= (len (mv-nth 2 (,name . ,formals)))
                             (len tokens))
                         (implies (mv-nth 1 (,name . ,formals))
                                  (< (len (mv-nth 2 (,name . ,formals)))
                                     (len tokens))))
                    :rule-classes ((:rewrite) (:linear))
                    :hints(,@(if hint-chicken-switch
                                 '(("Goal" :in-theory (disable (force))))
                               `((expand-and-maybe-induct-hint
                                  '(,fn-name . ,fn-formals)
                                  :disable '((force)))))))))

               (t
                (er hard? 'defparser "Bad :count: ~s0." count)))

       . ,rest-events)))

(defmacro defparser (name formals &rest args)
  (defparser-fn name formals args))

(define expand-defparsers (forms)
  ;; For mutually recursive parsers.  FORMS should be a list of defparser
  ;; invocations, e.g.,: ((DEFPARSER FOO ...) ... (DEFPARSER BAR ...))
  :mode :program
  (b* (((when (atom forms))
        nil)
       (form1 (car forms))
       ((when (eq form1 '///))
        ;; Pass any /// part transparently through to DEFINES
        forms)
       ((when (and (keywordp form1)
                   (consp (cdr forms))))
        ;; Pass any :key val pairs transparently through to DEFINES
        (list* form1
               (second forms)
               (expand-defparsers (rest-n 2 forms))))
       ((unless (and (< 3 (len form1))
                     (equal (first form1) 'defparser)))
        (raise "Expected defparser forms, but found ~x0." form1))
       (name1    (second form1))
       (formals1 (third form1))
       (args1    (rest-n 3 form1)))
    (cons (defparser-fn name1 formals1 args1)
          (expand-defparsers (cdr forms)))))

(defmacro defparsers (name &rest defparser-forms)
  ;; (defparsers expr (defparser parse-expr ...) (defparser parse-exprlist ...))
  `(defines ,name . ,(expand-defparsers defparser-forms)))


(define vl-is-token?
  :short "Check whether the current token has a particular type."
  ((type "Type of token to match.")
   &key ((tokens vl-tokenlist-p) 'tokens))
  :returns bool
  :inline t
  (mbe :logic
       (b* ((tokens (vl-tokenlist-fix tokens)))
         (and (consp tokens)
              (eq (vl-token->type (car tokens)) type)))
       :exec
       (and (consp tokens)
            (eq (vl-token->type (car tokens)) type)))
  ///
  (add-untranslate-pattern (vl-is-token?-fn ?type tokens) (vl-is-token? ?type))

  (defthm vl-is-token?-of-vl-tokenlist-fix
    (equal (vl-is-token? type :tokens (vl-tokenlist-fix tokens))
           (vl-is-token? type)))

  (defthm vl-is-token?-fn-when-atom-of-tokens
    (implies (atom tokens)
             (equal (vl-is-token? type)
                    nil))))


(define vl-is-some-token?
  :short "Check whether the current token is one of some particular types."
  ((types true-listp)
   &key
   ((tokens vl-tokenlist-p) 'tokens))
  :returns bool
  :inline t
  (b* ((tokens (vl-tokenlist-fix tokens)))
    (and (consp tokens)
         (member-eq (vl-token->type (car tokens)) types)
         t))
  ///
  (add-untranslate-pattern (vl-is-some-token?$inline ?types tokens)
                           (vl-is-some-token? ?types))

  (defthm vl-is-some-token?-when-atom-of-tokens
    (implies (atom tokens)
             (equal (vl-is-some-token? type :tokens tokens)
                    nil)))

  (defthm vl-is-some-token?-when-atom-of-types
    (implies (atom types)
             (equal (vl-is-some-token? types :tokens tokens)
                    nil)))

  (defthm vl-is-some-token?-of-vl-tokenlist-fix
    (equal (vl-is-some-token? types :tokens (vl-tokenlist-fix tokens))
           (vl-is-some-token? types))))



(define vl-parse-error
  :short "Compatible with @(see seqw).  Produce an error message (stopping
execution) that includes the current location."
  ((description stringp "Short description of what went wrong.")
   &key
   ((function symbolp)          '__function__)
   ((tokens   vl-tokenlist-p)   'tokens)
   ((warnings vl-warninglist-p) 'warnings))
  :returns
  (mv (errmsg   "An error message suitable for @(see vl-cw-obj)." (iff errmsg t))
      (value    "Always just @('nil')." (equal value nil))
      (remainder     (equal remainder (vl-tokenlist-fix tokens)))
      (new-warnings  (equal new-warnings (vl-warninglist-fix warnings))))
  (b* ((tokens   (vl-tokenlist-fix tokens))
       (warnings (vl-warninglist-fix warnings)))
    (mv (if (consp tokens)
            (list (cat "Parse error in ~s0 (at ~l1): " description)
                  function (vl-token->loc (car tokens)))
          (list (cat "Parser error in ~s0 (at EOF): " description)
                function))
        nil tokens warnings))
  ///
  (add-macro-alias vl-parse-error vl-parse-error-fn)
  (add-untranslate-pattern
   (vl-parse-error-fn ?function ?description tokens warnings)
   (vl-parse-error ?function ?description)))

(define vl-parse-warning
  :short "Compatible with @(see seqw).  Produce a warning (not an error,
doesn't stop execution) that includes the current location."
  ((type        symbolp "Type for this @(see warnings).")
   (description stringp "Short message about what happened.")
   &key
   ((function symbolp) '__function__)
   ((tokens   vl-tokenlist-p) 'tokens)
   ((warnings vl-warninglist-p) 'warnings))
  :returns
  (mv (errmsg (not errmsg) "Never produces an error.")
      (value  (not value) "Value is always @('nil').")
      (new-tokens (equal new-tokens (vl-tokenlist-fix tokens)))
      (warnings   vl-warninglist-p))
  (b* ((tokens   (vl-tokenlist-fix tokens))
       (warnings (vl-warninglist-fix warnings))
       (msg (if (atom tokens)
                (cat "Warning in ~s0 (at EOF): " description)
              (cat "Warning in ~s0 (at ~l1): " description)))
       (args (if (atom tokens)
                 (list function)
               (list function (vl-token->loc (car tokens)))))
       (warning
        (make-vl-warning :type (mbe :logic (and (symbolp type) type)
                                    :exec type)
                         :msg msg
                         :args args
                         :fn (mbe :logic (and (symbolp function) function)
                                  :exec function)))
       (warnings (cons warning warnings)))
    (mv nil nil tokens warnings))
  ///
  (add-macro-alias vl-parse-warning vl-parse-warning-fn)
  (add-untranslate-pattern
   (vl-parse-warning-fn ?function ?description tokens warnings)
   (vl-parse-warning ?function ?description)))


(defmacro vl-unimplemented ()
  `(vl-parse-error "Unimplemented Verilog production."))


(define vl-match-token
  :short "Compatible with @(see seqw).  Consume and return a token of exactly
some particular type, or cause an error if the desired kind of token is not at
the start of the input stream."
  ((type "Kind of token to match.") ;; BOZO why not a stronger guard?
   &key
   ((function symbolp) '__function__)
   ((tokens   vl-tokenlist-p) 'tokens)
   ((warnings vl-warninglist-p) 'warnings))

  :returns
  (mv (errmsg?   (iff errmsg? (not (vl-is-token? type))))
      (token     vl-token-p :hyp (vl-is-token? type))
      (remainder vl-tokenlist-p)
      (warnings  vl-warninglist-p))

  (b* ((warnings (vl-warninglist-fix warnings))
       (tokens   (vl-tokenlist-fix tokens))
       ((when (atom tokens))
        (vl-parse-error "Unexpected EOF." :function function))
       (token1 (car tokens))
       ((unless (eq type (vl-token->type token1)))
        ;; We want a custom error message, so we don't use vl-parse-error-fn.
        (mv (list "Parse error in ~s0 (at ~l1): expected ~s2, but found ~s3."
                  function (vl-token->loc token1) type (vl-token->type token1))
            nil tokens warnings)))
    (mv nil token1 (cdr tokens) warnings))

  :prepwork
  ((local (in-theory (enable vl-is-token?))))
  ///
  (add-untranslate-pattern (vl-match-token-fn ?type ?function tokens warnings)
                           (vl-match-token ?type))

  (defthm vl-match-token-of-vl-tokenlist-fix
    (equal (vl-match-token type :tokens (vl-tokenlist-fix tokens))
           (vl-match-token type)))

  (defthm vl-match-token-fails-gracefully
    (implies (not (vl-is-token? type))
             (not (mv-nth 1 (vl-match-token type)))))

  (defthm vl-token->type-of-vl-match-token
    (implies (vl-is-token? type)
             (equal (vl-token->type (mv-nth 1 (vl-match-token type)))
                    type)))

  (defthm vl-match-token-count-strong-on-value
    (and (<= (len (mv-nth 2 (vl-match-token type)))
             (len tokens))
         (implies (mv-nth 1 (vl-match-token type))
                  (< (len (mv-nth 2 (vl-match-token type)))
                     (len tokens))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-vl-match-token-count
    (equal (equal (len (mv-nth 2 (vl-match-token type)))
                  (len tokens))
           (if (mv-nth 0 (vl-match-token type))
               t
             nil))))


(define vl-match-some-token
  :short "Compatible with @(see seqw).  Consume and return a token if it has
one of several types.  Cause an error if the first token isn't one of the
acceptable types."
  ((types true-listp) ;; BOZO why not a stronger guard?
   &key
   ((function symbolp) '__function__)
   ((tokens   vl-tokenlist-p) 'tokens)
   ((warnings vl-warninglist-p) 'warnings))
  :returns
  (mv (errmsg?  (iff errmsg? (not (vl-is-some-token? types))))
      (token     vl-token-p :hyp (vl-is-some-token? types))
      (remainder vl-tokenlist-p)
      (warnings  vl-warninglist-p))

  (b* ((tokens (vl-tokenlist-fix tokens))
       (warnings (vl-warninglist-fix warnings))
       ((when (atom tokens))
        (vl-parse-error "Unexpected EOF." :function function))
       (token1 (car tokens))
       ((unless (member-eq (vl-token->type token1) types))
        (mv (list "Parse error in ~s0 (at ~l1): expected one of ~x2, but found ~s3."
                  function (vl-token->loc token1) types (vl-token->type token1))
            nil tokens warnings)))
    (mv nil token1 (cdr tokens) warnings))

  :prepwork
  ((local (in-theory (enable vl-is-some-token?))))

  ///
  (add-untranslate-pattern (vl-match-some-token-fn ?types ?function tokens warnings)
                           (vl-match-some-token ?types))

  (defthm vl-match-some-token-fails-gracefully
    (implies (not (vl-is-some-token? types))
             (equal (mv-nth 1 (vl-match-some-token types))
                    nil)))

  (defthm vl-match-some-token-count-strong-on-value
    (and (<= (len (mv-nth 2 (vl-match-some-token types)))
             (len tokens))
         (implies (mv-nth 1 (vl-match-some-token types))
                  (< (len (mv-nth 2 (vl-match-some-token types)))
                     (len tokens))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-vl-match-some-token-count
    (equal (equal (len (mv-nth 2 (vl-match-some-token types)))
                  (len tokens))
           (if (mv-nth 0 (vl-match-some-token types))
               t
             nil)))

  (defthm vl-match-some-token-of-vl-tokenlist-fix
    (equal (vl-match-some-token types :tokens (vl-tokenlist-fix tokens))
           (vl-match-some-token types))))



(define vl-type-of-matched-token
  :short "Reasoning trick.  Alias for the type of the token returned by @(see
vl-match-some-token)."
  ((types true-listp)
   (tokens vl-tokenlist-p))

  :long "<p>We added this when we disabled the functions @(see
vl-is-some-token?) and @(see vl-match-some-token) to address the problem of
reasoning about which kind of token was matched.  We could prove, for instance,
that</p>

@({
    (implies (vl-is-some-token? types tokens)
             (member (mv-nth 1 (vl-match-some-token types))
                     types))
})

<p>But it was difficult to get ACL2 to actually make use of this rule, because
the @('member') term never arose.</p>

<p>Instead, we use this new alias so that we can rewrite</p>

@({
     (equal (mv-nth 1 (vl-match-some-token types))
            (vl-type-of-matched-tokens types tokens))
})"

  (b* ((tokens (vl-tokenlist-fix tokens)))
    (if (and (consp tokens)
             (member-eq (vl-token->type (car tokens)) types))
        (vl-token->type (car tokens))
      nil))

  ///
  (local (in-theory (enable vl-match-some-token)))

  (defthm vl-token->type-of-vl-match-some-token
    (equal (vl-token->type (mv-nth 1 (vl-match-some-token types)))
           (vl-type-of-matched-token types tokens)))

  (defthm vl-type-of-matched-token-when-atom-of-types
    (implies (atom types)
             (equal (vl-type-of-matched-token types tokens)
                    nil)))

  (defthm vl-type-of-matched-token-when-atom-of-tokens
    (implies (atom tokens)
             (equal (vl-type-of-matched-token types tokens)
                    nil)))

  (defthm vl-type-of-matched-token-of-vl-tokenlist-fix
    (equal (vl-type-of-matched-token types (vl-tokenlist-fix tokens))
           (vl-type-of-matched-token types tokens))))



;; Experimental rules to kick ass.

(defthm magically-reduce-possible-types-from-vl-is-some-token?
  (implies (and (not (equal (vl-type-of-matched-token types2 tokens) exclude))
                (syntaxp (quotep types))
                (syntaxp (quotep types2))
                (member-equal exclude types)
                (subsetp-equal types types2))
           (equal (vl-is-some-token? types :tokens tokens)
                  (vl-is-some-token? (remove-equal exclude types)
                                     :tokens tokens)))
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
           (equal (vl-is-some-token? types :tokens tokens)
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
                (vl-is-some-token? types :tokens tokens)))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token
                                    vl-is-some-token?))))





(define vl-current-loc
  :short "Compatible with @(see seqw).  Get the current location."
  (&key ((tokens vl-tokenlist-p) 'tokens)
        ((warnings vl-warninglist-p) 'warnings))
  :returns (mv (errmsg    (not errmsg))
               (loc       vl-location-p
                          ;; BOZO bad hyp
                          :hyp (force (vl-tokenlist-p tokens)))
               (new-tokens    (equal new-tokens (vl-tokenlist-fix tokens)))
               (new-warnings  (equal new-warnings warnings)))
  :long "<p>We just return the location of the first token, if there is one.
Or, if the token stream is empty, we just return @(see *vl-fakeloc*)</p>"
  (b* ((tokens (vl-tokenlist-fix tokens)))
    (mv nil
        (if (consp tokens)
            (vl-token->loc (car tokens))
          *vl-fakeloc*)
        tokens
        warnings))
  ///
  (add-untranslate-pattern (vl-current-loc tokens warnings)
                           (vl-current-loc)))


(defmacro vl-copy-tokens (&key (tokens 'tokens) (warnings 'warnings))
  "Returns (MV ERROR TOKENS TOKENS WARNINGS) for SEQW compatibility."
  (declare (xargs :guard t))
  `(let ((tokens ,tokens)
         (warnings ,warnings))
     (mv nil tokens tokens warnings)))


(define vl-match (&key
                  ((tokens vl-tokenlist-p) 'tokens)
                  ((warnings vl-warninglist-p) 'warnings))
  :guard (consp tokens)
  :short "Compatible with @(see seqw).  Get the first token, no matter what
kind of token it is.  Only usable when you know there is a token there (via the
guard)."
  :inline t
  :returns (mv (errmsg?   (not errmsg?))
               (token     (equal (vl-token-p token)
                                 (consp (vl-tokenlist-fix tokens))))
               (remainder vl-tokenlist-p)
               (warnings  vl-warninglist-p))
  (mbe :logic
       (b* ((tokens (vl-tokenlist-fix tokens))
            (warnings (vl-warninglist-fix warnings)))
         (mv nil (car tokens) (cdr tokens) warnings))
       :exec
       (mv nil (car tokens) (cdr tokens) warnings))
  ///
  (defthm vl-match-of-vl-tokenlist-fix
    (equal (vl-match :tokens (vl-tokenlist-fix tokens))
           (vl-match)))

  (defthm vl-match-of-vl-warninglist-fix
    (equal (vl-match :warnings (vl-warninglist-fix warnings))
           (vl-match)))

  (defthm vl-match-count-strong-on-value
    (and (<= (len (mv-nth 2 (vl-match)))
             (len tokens))
         (implies (mv-nth 1 (vl-match))
                  (< (len (mv-nth 2 (vl-match)))
                     (len tokens))))
  :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-vl-match-count
    (equal (equal (len (mv-nth 2 (vl-match)))
                  (len tokens))
           (atom (vl-tokenlist-fix tokens))))

  (defthm vl-token->type-of-vl-match-when-vl-is-token?
    (implies (vl-is-token? type)
             (equal (vl-token->type (mv-nth 1 (vl-match)))
                    type))
    :hints(("Goal" :in-theory (enable vl-is-token?))))

  (defthm vl-token->type-of-vl-match-when-vl-is-some-token?
    (implies (vl-is-some-token? types)
             (equal (vl-token->type (mv-nth 1 (vl-match)))
                    (vl-type-of-matched-token types tokens)))
    :hints(("Goal" :in-theory (enable vl-type-of-matched-token
                                      vl-is-some-token?)))))



(define vl-match-any
  :short "Compatible with @(see seqw).  Get the first token, no matter what
kind of token it is.  Causes an error on EOF."
  (&key
   ((function symbolp)          '__function__)
   ((tokens  vl-tokenlist-p)    'tokens)
   ((warnings vl-warninglist-p) 'warnings))
  :inline t
  :returns
  (mv (errmsg?)
      (token)
      (new-tokens   vl-tokenlist-p)
      (new-warnings vl-warninglist-p))
  (b* ((tokens (vl-tokenlist-fix tokens))
       (warnings (vl-warninglist-fix warnings))
       ((when (atom tokens))
        (vl-parse-error "Unexpected EOF." :function function)))
    (mv nil (car tokens) (cdr tokens) warnings))
  ///
  (add-macro-alias vl-match-any vl-match-any$inline)
  (add-untranslate-pattern (vl-match-any$inline ?function tokens warnings)
                           (vl-match-any :function ?function))

  (defthm vl-match-any-of-vl-tokenlist-fix
    (equal (vl-match-any :tokens (vl-tokenlist-fix tokens))
           (vl-match-any)))

  (defthm vl-match-any-of-vl-warninglist-fix
    (equal (vl-match-any :warnings (vl-warninglist-fix warnings))
           (vl-match-any)))

  (defthm vl-match-any-fails-gracefully
    (implies (mv-nth 0 (vl-match-any))
             (equal (mv-nth 1 (vl-match-any))
                    nil)))

  (defthm vl-token-p-of-vl-match-any
    (implies (not (mv-nth 0 (vl-match-any)))
             (vl-token-p (mv-nth 1 (vl-match-any)))))

  (defthm vl-match-any-fn-count-strong-on-value
    (and (<= (len (mv-nth 2 (vl-match-any)))
             (len tokens))
         (implies (mv-nth 1 (vl-match-any))
                  (< (len (mv-nth 2 (vl-match-any)))
                     (len tokens))))
  :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-vl-match-any-fn-count
    (equal (equal (len (mv-nth 2 (vl-match-any)))
                  (len tokens))
           (if (mv-nth 0 (vl-match-any))
               t
             nil))))


(define vl-match-any-except
  :short "Compatible with @(see seqw).  Match any token that is not of the
listed types.  Causes an error on EOF."
  ((types true-listp) ;; BOZO stronger guard?
   &key
   ((function symbolp) '__function__)
   ((tokens   vl-tokenlist-p) 'tokens)
   ((warnings vl-warninglist-p) 'warnings))
  :returns
  (mv (errmsg?)
      (token)
      (new-tokens   vl-tokenlist-p)
      (new-warnings (equal new-warnings (vl-warninglist-fix warnings))))
  (b* ((tokens   (vl-tokenlist-fix tokens))
       (warnings (vl-warninglist-fix warnings))
       ((when (atom tokens))
        (vl-parse-error "Unexpected EOF." :function function))
       (token1 (car tokens))
       ((when (member-eq (vl-token->type token1) types))
        (mv (list "Parse error in ~s0 (at ~l1): unexpected ~s2."
                  function (vl-token->loc token1) (vl-token->type token1))
            nil tokens warnings)))
    (mv nil token1 (cdr tokens) warnings))
  ///
  (add-macro-alias vl-match-any-except vl-match-any-except-fn)
  (add-untranslate-pattern (vl-match-any-except-fn ?types ?function tokens warnings)
                           (vl-match-any-except ?types :function ?function))
  (local (in-theory (enable vl-is-some-token?)))

  (defthm vl-match-any-except-of-vl-tokenlist-fix
    (equal (vl-match-any-except types :tokens (vl-tokenlist-fix tokens))
           (vl-match-any-except types)))

  (defthm vl-match-any-except-of-vl-warninglist-fix
    (equal (vl-match-any-except types :warnings (vl-warninglist-fix warnings))
           (vl-match-any-except types)))

  (defthm vl-match-any-except-fails-when-vl-is-some-token?
    (iff (mv-nth 0 (vl-match-any-except types))
         (or (atom tokens)
             (vl-is-some-token? types))))

  (defthm vl-match-any-except-fails-gracefully
    (implies (or (atom tokens)
                 (vl-is-some-token? types))
             (equal (mv-nth 1 (vl-match-any-except types))
                    nil)))

  (defthm vl-match-any-except-when-atom-of-tokens
    (implies (atom tokens)
             (equal (mv-nth 2 (vl-match-any-except types))
                    tokens)))

  (defthm vl-token-p-of-vl-match-any-except
    (implies (and (not (vl-is-some-token? types))
                  (consp tokens))
             (vl-token-p (mv-nth 1 (vl-match-any-except types)))))

  (defthm vl-match-any-except-count-strong-on-value
    (and (<= (len (mv-nth 2 (vl-match-any-except types)))
             (len tokens))
         (implies (mv-nth 1 (vl-match-any-except types))
                  (< (len (mv-nth 2 (vl-match-any-except types)))
                     (len tokens))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-vl-match-any-except-fn-count
    (equal (equal (len (mv-nth 2 (vl-match-any-except types)))
                  (len tokens))
           (if (mv-nth 0 (vl-match-any-except types))
               t
             nil))))



(defaggregate vl-endinfo
  :short "Temporary structure created to parse named endings like
@('endmodule : foo')."

  :long "<p>SystemVerilog allows many syntactic constructs such as modules,
user-defined primitives, programs, packages, etc., to optionally be closed
using a verbose syntax that repeats the name.  For instance, one can write:</p>

@({
       module foo (...);
         ...
       endmodule : foo     // <-- named ending
})

<p>The ending name must match or it's an error, see \"Block Names\", Section
9.3.4 of the SystemVerilog-2012 spec.  Note that these named endings aren't
allowed in Verilog-2005.</p>

<p>An @('vl-endinfo-p') structure is just a temporary structure used by our
parser when we encounter such an ending.</p>"

  :legiblep nil

  ((name maybe-stringp :rule-classes :type-prescription
         "The name we matched after the colon, e.g., @('foo') above.")

   (loc  vl-location-p
         "The location of this name, for mismatch reporting.")))

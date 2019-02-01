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
(include-book "parsestate")
(include-book "../config")
(include-book "../lexer/tokens")
(include-book "../../util/warnings")
(include-book "seq")
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



(make-event
 `(defstobj tokstream
    (tokens :type (satisfies vl-tokenlist-p)
            :initially nil)
    (position :type (integer 0 *)
              :initially 0)
    (pstate :type (satisfies vl-parsestate-p)
            :initially ,(make-vl-parsestate))
    :inline t
    :non-memoizable t
    :renaming
    ((tokens          vl-tokstream->tokens-raw)
     (pstate          vl-tokstream->pstate-raw)
     (position        vl-tokstream->position-raw)
     (update-tokens   vl-tokstream-update-tokens-fn)
     (common-lisp::update-position vl-tokstream-update-position-fn)
     (update-pstate   vl-tokstream-update-pstate-fn)
     (common-lisp::positionp       vl-tokstream-positionp))))

(defthm vl-tokstream-positionp-rw
  (equal (vl-tokstream-positionp x)
         (natp x))
  :rule-classes (:rewrite :compound-recognizer))

(in-theory (disable vl-tokstream-positionp))

(define vl-tokstream->tokens (&key (tokstream 'tokstream))
  :returns (tokens vl-tokenlist-p)
  :inline t
  (mbe :logic (vl-tokenlist-fix (vl-tokstream->tokens-raw tokstream))
       :exec (vl-tokstream->tokens-raw tokstream)))

(define vl-tokstream->position (&key (tokstream 'tokstream))
  :returns (position natp :rule-classes :type-prescription)
  :inline t
  (lnfix (vl-tokstream->position-raw tokstream)))

(define vl-tokstream->pstate (&key (tokstream 'tokstream))
  :returns (pstate vl-parsestate-p)
  :inline t
  (mbe :logic (vl-parsestate-fix (vl-tokstream->pstate-raw tokstream))
       :exec (vl-tokstream->pstate-raw tokstream)))

(defmacro vl-tokstream-update-tokens (tokens &key (tokstream 'tokstream))
  `(vl-tokstream-update-tokens-fn ,tokens ,tokstream))

(defmacro vl-tokstream-update-pstate (pstate &key (tokstream 'tokstream))
  `(vl-tokstream-update-pstate-fn ,pstate ,tokstream))

(defmacro vl-tokstream-update-position (position &key (tokstream 'tokstream))
  `(vl-tokstream-update-position-fn ,position ,tokstream))

(add-macro-alias vl-tokstream-update-tokens vl-tokstream-update-tokens-fn)
(add-macro-alias vl-tokstream-update-pstate vl-tokstream-update-pstate-fn)
(add-macro-alias vl-tokstream-update-position vl-tokstream-update-position-fn)

(in-theory (disable vl-tokstream-update-tokens
                    vl-tokstream-update-pstate
                    vl-tokstream-update-position))

(define vl-tokstream-pop (&key (tokstream 'tokstream))
  :guard (consp (vl-tokstream->tokens))
  :inline t
  (b* ((tokstream (vl-tokstream-update-tokens (cdr (vl-tokstream->tokens)))))
    (vl-tokstream-update-position (+ 1 (vl-tokstream->position)))))

(encapsulate
  ()
  (local (in-theory (enable vl-tokstream->tokens
                            vl-tokstream->pstate
                            vl-tokstream->position
                            vl-tokstream-update-tokens
                            vl-tokstream-update-pstate
                            vl-tokstream-update-position)))

  (defthm vl-tokstream->tokens-of-vl-tokstream-update-tokens
    (equal (vl-tokstream->tokens :tokstream (vl-tokstream-update-tokens new-tokens))
           (vl-tokenlist-fix new-tokens)))

  (defthm vl-tokstream->pstate-of-vl-tokstream-update-tokens
    (equal (vl-tokstream->pstate :tokstream (vl-tokstream-update-tokens new-tokens))
           (vl-tokstream->pstate :tokstream tokstream)))

  (defthm vl-tokstream->tokens-of-vl-tokstream-update-pstate
    (equal (vl-tokstream->tokens :tokstream (vl-tokstream-update-pstate new-pstate))
           (vl-tokstream->tokens :tokstream tokstream)))

  (defthm vl-tokstream->tokens-of-vl-tokstream-update-position
    (equal (vl-tokstream->tokens :tokstream (vl-tokstream-update-position new-position))
           (vl-tokstream->tokens :tokstream tokstream)))

  (defthm vl-tokstream->pstate-of-vl-tokstream-update-pstate
    (equal (vl-tokstream->pstate :tokstream (vl-tokstream-update-pstate new-pstate))
           (vl-parsestate-fix new-pstate)))

  (defthm vl-tokstream->tokens-of-vl-tokstream-pop
    (equal (vl-tokstream->tokens :tokstream (vl-tokstream-pop))
           (cdr (vl-tokstream->tokens :tokstream tokstream)))
    :hints(("Goal" :in-theory (enable vl-tokstream-pop)))))



(defmacro vl-tokstream-measure (&key (tokstream 'tokstream))
  `(len (vl-tokstream->tokens :tokstream ,tokstream)))

(define vl-tokstream-fix (&key (tokstream 'tokstream))
  (mbe :logic (b* ((tokens (vl-tokstream->tokens))
                   (pstate (vl-tokstream->pstate))
                   (position (vl-tokstream->position)))
                (non-exec
                 (list tokens position pstate)))
       :exec tokstream)
  :prepwork
  ((local (in-theory (enable vl-tokstream->pstate
                             vl-tokstream->tokens
                             vl-tokstream->position))))
  ///
  (defthm vl-tokstream->pstate-of-vl-tokstream-fix
    (equal (vl-tokstream->pstate :tokstream (vl-tokstream-fix))
           (vl-tokstream->pstate)))

  (defthm vl-tokstream->tokens-of-vl-tokstream-fix
    (equal (vl-tokstream->tokens :tokstream (vl-tokstream-fix))
           (vl-tokstream->tokens)))

  (defthm vl-tokstream->position-of-vl-tokstream-fix
    (equal (vl-tokstream->position :tokstream (vl-tokstream-fix))
           (vl-tokstream->position)))

  (defthm vl-tokstream-measure-of-vl-tokstream-fix
    (equal (vl-tokstream-measure :tokstream (vl-tokstream-fix))
           (vl-tokstream-measure))))


(defaggregate vl-tokstream-backup
  :tag nil
  :layout :fulltree
  ((tokens vl-tokenlist-p)
   (position natp :rule-classes :type-prescription)
   (pstate vl-parsestate-p)))

(define vl-tokstream-save (&key (tokstream 'tokstream))
  :returns (backup vl-tokstream-backup-p)
  (make-vl-tokstream-backup :tokens (vl-tokstream->tokens)
                            :position (vl-tokstream->position)
                            :pstate (vl-tokstream->pstate))
  ///
  (defthm vl-tokstream-backup->tokens-of-vl-tokstream-save
    (equal (vl-tokstream-backup->tokens (vl-tokstream-save))
           (vl-tokstream->tokens))))

(define vl-tokstream-restore ((backup vl-tokstream-backup-p) &key (tokstream 'tokstream))
  (b* (((vl-tokstream-backup backup))
       (tokstream (vl-tokstream-update-pstate backup.pstate))
       (tokstream (vl-tokstream-update-position backup.position))
       (tokstream (vl-tokstream-update-tokens backup.tokens)))
    (vl-tokstream-fix))
  ///
  (local (in-theory (enable vl-tokstream->tokens
                            vl-tokstream->pstate
                            vl-tokstream->position
                            vl-tokstream-update-tokens
                            vl-tokstream-update-pstate
                            vl-tokstream-update-position
                            vl-tokstream-fix
                            vl-tokstream-save)))
  (defthm vl-tokstream-restore-of-vl-tokstream-save
    (equal (vl-tokstream-restore (vl-tokstream-save) :tokstream anything)
           (vl-tokstream-fix))))

(define vl-add-context-to-parser-warning ((warning vl-warning-p)
                                          &key (tokstream 'tokstream))
  :returns (new-warning vl-warning-p)
  (b* ((tokens  (vl-tokstream->tokens))
       (context (cat "  Near: \""
                     (vl-tokenlist->string-with-spaces
                      (take (min 4 (len tokens))
                            (list-fix tokens)))
                     (if (> (len tokens) 4) "..." "")
                     "\""))
       (new-msg (cat (vl-warning->msg warning)
                     (str::strsubst "~" "~~" context))))
    (change-vl-warning warning :msg new-msg)))

(define vl-tokstream-add-warning ((warning vl-warning-p)
                                  &key (tokstream 'tokstream))
  :returns (new-tokstream)
  (b* ((warning (vl-add-context-to-parser-warning warning))
       (pstate (vl-tokstream->pstate))
       (pstate (vl-parsestate-add-warning warning pstate))
       (tokstream (vl-tokstream-update-pstate pstate)))
    tokstream)
  ///
  (defthm vl-tokstream->tokens-of-vl-tokstream-add-warning
    (equal (vl-tokstream->tokens :tokstream (vl-tokstream-add-warning warning))
           (vl-tokstream->tokens))))


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
        <body>             ;; usually (seq tokens pstate ...)
        )

<p>Such an event always introduces:</p>

<ul>
<li>A macro, (foo x y), that just calls (foo-fn x y tokstream).</li>

<li>A function, (foo-fn x y tokstream), that implicitly binds the variable
    __function__ to 'foo and otherwise has the given bodies and declares, with
    the :guard thrown in if that is provided.</li>

<li>An add-macro-alias so foo can be used in place of foo-fn in enables and
    disables.</li>

<li>An untranslate-pattern so that (foo-fn x y tokstream) is displayed as
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
              (frees (set-difference-eq (cdr fncall) '(tokstream)))
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

(defun defparser-fn (name formals args single-p)
  (declare (xargs :guard (and (symbolp name)
                              (true-listp formals)
                              ;; Tokstream and config will be provided automatically
                              ;; We also prohibit tokens and pstate for historic reasons
                              (not (member 'tokens formals))
                              (not (member 'pstate formals))
                              (not (member 'config formals))
                              (not (member 'tokstream formals)))
                  :mode :program))
  (b* ((fn-name
        ;; BOZO want to use defguts or something instead
        (intern-in-package-of-symbol (cat (symbol-name name) "-FN") name))
       (fn-formals
        (append formals '(tokstream config)))

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
       (guard-debug    (extract-keyword-from-args :guard-debug args))
       (prepwork       (extract-keyword-from-args :prepwork args))

       (parents        (extract-keyword-from-args :parents args))
       (short          (extract-keyword-from-args :short args))
       (long           (extract-keyword-from-args :long args))

       (measure        (or (cdr (extract-keyword-from-args :measure args))
                           '(vl-tokstream-measure :tokstream tokstream)))
       (hint-chicken-switch (cdr (extract-keyword-from-args
                                  :hint-chicken-switch args)))
       (verify-guards  (extract-keyword-from-args :verify-guards args))
       (thm-hyps       (if guard
                           `(and ;(force (vl-tokenlist-p tokens))
                                 ,(adjust-guard-for-theorems (cdr guard)))
                         `(and ;(force (vl-tokenlist-p tokens))
                           t)))
       (define-form    `(define ,name
                          ,(append formals
                                   '(&key
                                     (tokstream 'tokstream)
                                     ((config vl-loadconfig-p) 'config)
                                     ))
                          :returns (mv (errmsg?)
                                       (value)
                                       (new-tokstream))
                          ,@(and parents       `(:parents ,(cdr parents)))
                          ,@(and short         `(:short ,(cdr short)))
                          ,@(and long          `(:long ,(cdr long)))
                          ,@(and guard         `(:guard ,(cdr guard)))
                          ,@(and guard-debug   `(:guard-debug ,(cdr guard-debug)))
                          ,@(and verify-guards `(:verify-guards ,(cdr verify-guards)))
                          ,@(and prepwork      `(:prepwork ,(cdr prepwork)))
                          :measure ,measure
                          ,@decls
                          (declare (ignorable config))
                          ;; (b* ((pstate (mbe :logic (vl-parsestate-fix pstate)
                          ;;                   :exec pstate))
                          ;;      (tokens   (mbe :logic (vl-tokenlist-fix tokens)
                          ;;                     :exec tokens)))
                          ;;   ,body)
                          ,body
                          ///

                          (ACL2::add-to-ruleset defparser-type-prescriptions '((:t ,name)))

                          ;; (defthm ,(intern-in-package-of-symbol
                          ;;           (cat (symbol-name name) "-OF-VL-TOKENLIST-FIX")
                          ;;           name)
                          ;;   (equal (,fn-name . ,(subst '(vl-tokenlist-fix tokens) 'tokens fn-formals))
                          ;;          (,fn-name . ,fn-formals))
                          ;;   :hints(("Goal"
                          ;;           :expand ((,fn-name . ,(subst '(vl-tokenlist-fix tokens)
                          ;;                                        'tokens fn-formals))
                          ;;                    (,fn-name . ,fn-formals)))))

                          ;; (defthm ,(intern-in-package-of-symbol
                          ;;           (cat (symbol-name name) "-OF-VL-PARSESTATE-FIX")
                          ;;           name)
                          ;;   (equal (,fn-name . ,(subst '(vl-parsestate-fix pstate)
                          ;;                              'pstate fn-formals))
                          ;;          (,fn-name . ,fn-formals))
                          ;;   :hints(("Goal"
                          ;;           :expand ((,fn-name . ,(subst '(vl-parsestate-fix pstate)
                          ;;                                        'pstate fn-formals))
                          ;;                    (,fn-name . ,fn-formals)))))

                          ;; ,@(if (not (or count result resultp-of-nil result-hints true-listp fails))
                          ;;       nil
                          ;;     `((defthm ,(intern-in-package-of-symbol
                          ;;                 (cat "VL-TOKENLIST-P-OF-" (symbol-name name))
                          ;;                 name)
                          ;;         (vl-tokenlist-p (mv-nth 2 (,name . ,formals)))
                          ;;         :hints (,@(if hint-chicken-switch
                          ;;                       nil
                          ;;                     `((expand-and-maybe-induct-hint
                          ;;                        '(,fn-name . ,fn-formals))))))

                          ;;       (defthm ,(intern-in-package-of-symbol
                          ;;                 (cat "VL-PARSESTATE-P-OF-" (symbol-name name))
                          ;;                 name)
                          ;;         (vl-parsestate-p (mv-nth 3 (,name . ,formals)))
                          ;;         :hints (,@(if hint-chicken-switch
                          ;;                       nil
                          ;;                     `((expand-and-maybe-induct-hint
                          ;;                        '(,fn-name . ,fn-formals))))))))

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
                                                     '(,fn-name . ,fn-formals) :disable '((force)))))))
                                     (defthm ,(intern-in-package-of-symbol
                                               (cat "VL-WARNING-P-OF-" (symbol-name name))
                                               name)
                                       (iff (vl-warning-p (mv-nth 0 (,name . ,formals)))
                                            (mv-nth 0 (,name . ,formals)))
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
                                       (<= (vl-tokstream-measure :tokstream (mv-nth 2 (,name . ,formals)))
                                           (vl-tokstream-measure))
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
                                       (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (,name . ,formals)))
                                                (vl-tokstream-measure))
                                            (implies (not (mv-nth 0 (,name . ,formals)))
                                                     (< (vl-tokstream-measure :tokstream (mv-nth 2 (,name . ,formals)))
                                                        (vl-tokstream-measure))))
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
                                       (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (,name . ,formals)))
                                                (vl-tokstream-measure))
                                            (implies (mv-nth 1 (,name . ,formals))
                                                     (< (vl-tokstream-measure :tokstream (mv-nth 2 (,name . ,formals)))
                                                        (vl-tokstream-measure))))
                                       :rule-classes ((:rewrite) (:linear))
                                       :hints(,@(if hint-chicken-switch
                                                    '(("Goal" :in-theory (disable (force))))
                                                  `((expand-and-maybe-induct-hint
                                                     '(,fn-name . ,fn-formals)
                                                     :disable '((force)))))))))

                                  (t
                                   (er hard? 'defparser "Bad :count: ~s0." count)))

                          . ,rest-events)))
    (if single-p
        `(encapsulate
           ()

; The generated parser can sensibly be recursive or non-recursive, and in the
; recursive case, by default we want to use a particular measure which isn't
; just acl2-count.  So, it seems convenient not to have to give an explicit
; measure when you introduce a recursive function (since we know what measure
; it should be), and it seems like it should not be an error to introduce a
; non-recursive parser.  Given all of that, we turn off the default check for
; recursion when providing a :measure.

           (set-bogus-measure-ok t)
           ,define-form)
      define-form)))

(defmacro defparser (name formals &rest args)
  (defparser-fn name formals args t))

(defun defparser-top-fn (name guard resulttype state)
  (declare (xargs :mode :program :stobjs state))
  (b* ((wrld (w state))
       (fnname (acl2::deref-macro-name name (acl2::macro-aliases wrld)))
       (formals (acl2::formals fnname wrld))
       (formals (set-difference-eq formals '(tokstream config))))
    `(define ,(intern-in-package-of-symbol (cat (symbol-name name) "-TOP") name)
       ,(append formals '(&key ((tokens vl-tokenlist-p) 'tokens)
                               ((pstate vl-parsestate-p) 'pstate)
                               ((config vl-loadconfig-p) 'config)))
       :guard ,guard
       :returns (mv erp
                    (result . ,(and resulttype `((implies (and (not erp) ,guard)
                                                          (,resulttype result)))))
                    (tokens vl-tokenlist-p)
                    (pstate vl-parsestate-p))
       (b* (((acl2::local-stobjs tokstream)
             (mv erp result tokens pstate tokstream))
            (tokstream (vl-tokstream-update-tokens tokens))
            (tokstream (vl-tokstream-update-pstate pstate))
            ((mv erp result tokstream) (,name . ,formals)))
         (mv erp result (vl-tokstream->tokens) (vl-tokstream->pstate) tokstream)))))

(defmacro defparser-top (name &key (guard 't) resulttype)
  `(make-event (defparser-top-fn ',name ',guard ',resulttype state)))

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
    (cons (defparser-fn name1 formals1 args1 nil)
          (expand-defparsers (cdr forms)))))

(defmacro defparsers (name &rest defparser-forms)
  ;; (defparsers expr (defparser parse-expr ...) (defparser parse-exprlist ...))
  `(encapsulate ; See the comment on the encapsulate in defparser-fn
     ()
     (set-bogus-measure-ok t)
     (defines ,name . ,(expand-defparsers defparser-forms))))


(define vl-is-token?
  :short "Check whether the current token has a particular type."
  ((type "Type of token to match.")
   &key (tokstream 'tokstream))
  :guard (symbolp type)
  :returns bool
  :inline t
  (b* ((tokens (vl-tokstream->tokens)))
    (and (consp tokens)
         (eq (vl-token->type (car tokens)) type)))
  ///
  ;; (defthm vl-is-token?-of-vl-tokenlist-fix
  ;;   (equal (vl-is-token? type :tokens (vl-tokenlist-fix tokens))
  ;;          (vl-is-token? type)))

  (defthm vl-is-token?-fn-when-atom-of-tokens
    (implies (atom (vl-tokstream->tokens))
             (equal (vl-is-token? type)
                    nil))
    ;; I found this rule to be expensive as a rewrite, so making it a
    ;; type-prescription instead
    :rule-classes :type-prescription))


(define vl-is-some-token?
  :short "Check whether the current token is one of some particular types."
  ((types true-listp)
   &key (tokstream 'tokstream))
  :returns bool
  :inline t
  (b* ((tokens (vl-tokstream->tokens)))
    (and (consp tokens)
         (member-eq (vl-token->type (car tokens)) types)
         t))
  ///
  (defthm vl-is-some-token?-when-atom-of-tokens
    (implies (atom (vl-tokstream->tokens))
             (equal (vl-is-some-token? type)
                    nil)))

  (defthm vl-is-some-token?-when-atom-of-types
    (implies (atom types)
             (equal (vl-is-some-token? types)
                    nil)))

  ;; (defthm vl-is-some-token?-of-vl-tokenlist-fix
  ;;   (equal (vl-is-some-token? types :tokens (vl-tokenlist-fix tokens))
  ;;          (vl-is-some-token? types)))
  )


(define vl-lookahead-is-token?
  :short "Check whether the current token has a particular type."
  ((type   "Type of token to match.")
   (tokens vl-tokenlist-p))
  :returns bool
  :inline t
  (and (consp tokens)
       (eq (vl-token->type (car tokens)) type))
  ///
  (defthm vl-lookahead-is-token?-fn-when-atom-of-tokens
    (implies (atom tokens)
             (equal (vl-lookahead-is-token? type tokens)
                    nil))
    ;; I found this rule to be expensive as a rewrite, so making it a
    ;; type-prescription instead
    :rule-classes :type-prescription))


(define vl-lookahead-is-some-token?
  :short "Check whether the current token is one of some particular types."
  ((types  true-listp)
   (tokens vl-tokenlist-p))
  :returns bool
  :inline t
  (and (consp tokens)
       (member-eq (vl-token->type (car tokens)) types)
       t)
  ///
  (defthm vl-lookahead-is-some-token?-when-atom-of-tokens
    (implies (atom tokens)
             (equal (vl-lookahead-is-some-token? type tokens)
                    nil)))

  (defthm vl-lookahead-is-some-token?-when-atom-of-types
    (implies (atom types)
             (equal (vl-lookahead-is-some-token? types tokens)
                    nil))))


(define vl-parse-error
  :short "Compatible with @(see seq).  Produce an error message (stopping
execution) that includes the current location."
  ((description stringp "Short description of what went wrong.")
   &key
   ((function symbolp) '__function__)
   (tokstream 'tokstream))
  :returns
  (mv (errmsg   vl-warning-p
                "Note that such a warning is not automatically extended with
                 ``nearby'' context, because for backtracking these are often
                 ephemeral.")
      (value    "Always just @('nil')." (equal value nil))
      (new-tokstream (equal new-tokstream tokstream)))
  (b* ((tokens  (vl-tokstream->tokens))
       (warning (make-vl-warning :type :vl-parse-error
                         :msg "Parse error at ~a0: ~s1"
                         :args (list (if (consp tokens)
                                         (vl-token->loc (car tokens))
                                       "EOF")
                                     description)
                         :fn function
                         :fatalp t)))
    (mv warning nil tokstream))
  ///
  (more-returns (errmsg (iff errmsg t)
                        :name vl-parse-error-0-under-iff)))

(define vl-parse-warning
  :short "Compatible with @(see seq).  Produce a non-fatal warning (not an
error, doesn't stop execution) that includes the current location."
  ((type        symbolp "Type for this warning.")
   (description stringp "Short message about what happened.")
   &key
   ((function symbolp) '__function__)
   (tokstream 'tokstream))
  :returns
  (mv (errmsg (not errmsg) "Never produces an error.")
      (value  (not value)  "Value is always @('nil').")
      (new-tokstream))
  (b* ((tokens  (vl-tokstream->tokens))
       (warning (make-vl-warning :type type
                                 :msg "At ~a0: ~s1"
                                 :args (list (if (consp tokens)
                                                 (vl-token->loc (car tokens))
                                               "EOF")
                                             description)
                                 :fn function
                                 :fatalp nil))
       (tokstream (vl-tokstream-add-warning warning)))
    (mv nil nil tokstream))
  ///
  (more-returns
   (new-tokstream (equal (vl-tokstream->tokens :tokstream new-tokstream)
                         (vl-tokstream->tokens))
                  :name vl-tokstream->tokens-of-vl-parse-warning)))


(defmacro vl-unimplemented ()
  `(vl-parse-error "Unimplemented Verilog production."))

(define vl-match-token
  :short "Compatible with @(see seq).  Consume and return a token of exactly
some particular type, or cause an error if the desired kind of token is not at
the start of the input stream."
  ((type "Kind of token to match.") ;; BOZO why not a stronger guard?
   &key
   ((function symbolp) '__function__)
   (tokstream 'tokstream))
  :returns
  (mv (errmsg?   (and (iff errmsg? (not (vl-is-token? type)))
                      (iff (vl-warning-p errmsg?) errmsg?)))
      (token     vl-token-p :hyp (vl-is-token? type))
      (new-tokstream))

  (b* ((tokens (vl-tokstream->tokens))
       ((when (atom tokens))
        (vl-parse-error "Unexpected EOF." :function function))
       (token1 (car tokens))
       ((unless (eq type (vl-token->type token1)))
        ;; We want a custom error message, so we don't use vl-parse-error-fn.
        (mv (make-vl-warning :type :vl-parse-error
                             :msg "Parse error at ~a0: expected ~s1 but found ~s2."
                             :args (list (vl-token->loc (car tokens))
                                         type
                                         (vl-token->type token1))
                             :fatalp t
                             :fn function)
            nil tokstream))
       (tokstream (vl-tokstream-pop)))
    (mv nil token1 tokstream))

  :prepwork
  ((local (in-theory (enable vl-is-token?))))
  ///
  ;; (defthm vl-match-token-of-vl-tokenlist-fix
  ;;   (equal (vl-match-token type :tokens (vl-tokenlist-fix tokens))
  ;;          (vl-match-token type)))

  (defthm vl-match-token-fails-gracefully
    (implies (not (vl-is-token? type))
             (equal (mv-nth 1 (vl-match-token type)) nil)))

  (local (defthmd car-of-vl-tokenlist-under-iff
           (implies (vl-tokenlist-p x)
                    (iff (car x) (consp x)))
           :hints(("Goal" :in-theory (enable vl-tokenlist-p)))))

  (defthm vl-match-token-under-iff
    (iff (mv-nth 1 (vl-match-token type))
         (vl-is-token? type))
    :hints(("Goal" :in-theory (enable car-of-vl-tokenlist-under-iff))))

  (defthm vl-token->type-of-vl-match-token
    (implies (vl-is-token? type)
             (equal (vl-token->type (mv-nth 1 (vl-match-token type)))
                    type)))

  (defthm vl-match-token-count-strong-on-value
    (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-token type)))
             (vl-tokstream-measure))
         (implies (mv-nth 1 (vl-match-token type))
                  (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-token type)))
                     (vl-tokstream-measure))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-vl-match-token-count
    (equal (equal (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-token type)))
                  (vl-tokstream-measure))
           (if (mv-nth 0 (vl-match-token type))
               t
             nil))))


(define vl-match-some-token
  :short "Compatible with @(see seq).  Consume and return a token if it has
one of several types.  Cause an error if the first token isn't one of the
acceptable types."
  ((types true-listp) ;; BOZO why not a stronger guard?
   &key
   ((function symbolp) '__function__)
   (tokstream 'tokstream))
  :returns
  (mv (errmsg?   (and (iff errmsg? (not (vl-is-some-token? types)))
                      (iff (vl-warning-p errmsg?) errmsg?)))
      (token     vl-token-p :hyp (vl-is-some-token? types))
      (new-tokstream))

  (b* ((tokens (vl-tokstream->tokens))
       ((when (atom tokens))
        (vl-parse-error "Unexpected EOF." :function function))
       (token1 (car tokens))
       ((unless (member-eq (vl-token->type token1) types))
        (mv (make-vl-warning :type :vl-parse-error
                             :msg  "Parse error at ~a0: expected one of ~x1, but found ~s2."
                             :args (list (vl-token->loc token1)
                                         types
                                         (vl-token->type token1))
                             :fatalp t
                             :fn function)
            nil tokstream))
       (tokstream (vl-tokstream-pop)))
    (mv nil token1 tokstream))

  :prepwork
  ((local (in-theory (enable vl-is-some-token?))))

  ///
  (defthm vl-match-some-token-fails-gracefully
    (implies (not (vl-is-some-token? types))
             (equal (mv-nth 1 (vl-match-some-token types))
                    nil)))

  (defthm vl-match-some-token-count-strong-on-value
    (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-some-token types)))
             (vl-tokstream-measure))
         (implies (mv-nth 1 (vl-match-some-token types))
                  (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-some-token types)))
                     (vl-tokstream-measure))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-vl-match-some-token-count
    (equal (equal (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-some-token types)))
                  (vl-tokstream-measure))
           (if (mv-nth 0 (vl-match-some-token types))
               t
             nil)))

  ;; (defthm vl-match-some-token-of-vl-tokenlist-fix
  ;;   (equal (vl-match-some-token types :tokens (vl-tokenlist-fix tokens))
  ;;          (vl-match-some-token types)))
  )

(define vl-maybe-match-token
  :short "Compatible with @(see seq).  Consume and return a token if it is of
the given type, but if not, don't consume anything and return nil."
  ((type "Kind of token to match.") ;; BOZO why not a stronger guard?
   &key
   (tokstream 'tokstream))

  :returns
  (mv (errmsg?   (equal errmsg? nil))
      (token     (and (iff (vl-token-p token)
                           (vl-is-token? type))
                      (iff token (vl-is-token? type)))
                 :hints(("Goal" :in-theory (enable car-of-vl-tokenlist-under-iff))))
      (new-tokstream))

  (b* ((tokens (vl-tokstream->tokens))
       ((when (atom tokens)) (mv nil nil tokstream))
       (token1 (car tokens))
       ((unless (eq type (vl-token->type token1)))
        (mv nil nil tokstream))
       (tokstream (vl-tokstream-pop)))
    (mv nil token1 tokstream))

  :prepwork
  ((local (in-theory (enable vl-is-token?)))
   (local (defthmd car-of-vl-tokenlist-under-iff
            (implies (vl-tokenlist-p x)
                     (iff (car x) (consp x)))
            :hints(("Goal" :in-theory (enable vl-tokenlist-p))))))
  ///
  ;; (defthm vl-match-token-of-vl-tokenlist-fix
  ;;   (equal (vl-match-token type :tokens (vl-tokenlist-fix tokens))
  ;;          (vl-match-token type)))

  (defthm vl-maybe-match-token-fails-gracefully
    (implies (not (vl-is-token? type))
             (equal (mv-nth 1 (vl-maybe-match-token type)) nil)))

  (defthm vl-token->type-of-vl-maybe-match-token
    (implies (vl-is-token? type)
             (equal (vl-token->type (mv-nth 1 (vl-maybe-match-token type)))
                    type)))

  (defthm vl-maybe-match-token-count-strong-on-value
    (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-maybe-match-token type)))
             (vl-tokstream-measure))
         (implies (mv-nth 1 (vl-maybe-match-token type))
                  (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-maybe-match-token type)))
                     (vl-tokstream-measure))))
    :rule-classes ((:rewrite) (:linear))))



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
           (vl-type-of-matched-token types (vl-tokstream->tokens))))

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
  (implies (and (not (equal (vl-type-of-matched-token types2 (vl-tokstream->tokens)) exclude))
                (syntaxp (quotep types))
                (syntaxp (quotep types2))
                (member-equal exclude types)
                (subsetp-equal types types2))
           (equal (vl-is-some-token? types)
                  (vl-is-some-token? (remove-equal exclude types))))
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
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token))))

(defthm magically-reduce-possible-types-from-vl-token->type-of-car-of-tokens
  (implies (and (equal (vl-token->type (car (vl-tokstream->tokens))) free-type)
                (syntaxp (quotep types))
                (syntaxp (quotep free-type))
                (member free-type types))
           (equal (vl-type-of-matched-token types (vl-tokstream->tokens))
                  (if (member free-type types)
                      free-type
                    nil)))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token))))

(defthm magically-resolve-vl-is-some-token?
  (implies (and (equal (vl-type-of-matched-token types2 (vl-tokstream->tokens)) value)
                (member-equal value types)
                value)
           (equal (vl-is-some-token? types)
                  t))
  :hints(("Goal" :in-theory (enable vl-is-some-token?
                                    vl-type-of-matched-token))))

(defthm magically-resolve-type-of-matched-token
  (implies (and (equal (vl-type-of-matched-token types2 tokens) value)
                (member-equal value types)
                value)
           (equal (vl-type-of-matched-token types tokens)
                  value))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token))))

(defthm vl-is-some-token?-under-iff
  (implies (not (member-equal nil types))
           (iff (vl-is-some-token? types)
                (vl-type-of-matched-token types (vl-tokstream->tokens))))
  :hints(("Goal" :in-theory (enable vl-type-of-matched-token
                                    vl-is-some-token?))))




(define vl-current-loc
  :short "Compatible with @(see seq).  Get the current location."
  (&key (tokstream 'tokstream))
  :returns (mv (errmsg        (not errmsg))
               (loc           vl-location-p)
               (new-tokstream (equal new-tokstream tokstream)))
  :long "<p>We just return the location of the first token, if there is one.
Or, if the token stream is empty, we just return @(see *vl-fakeloc*)</p>"
  (b* ((tokens (vl-tokstream->tokens)))
    (mv nil
        (if (consp tokens)
            (vl-token->loc (car tokens))
          *vl-fakeloc*)
        tokstream)))


(define vl-linestart-indent
  :short "Compatible with @(see seq).  If we are at the first token on a line,
          return its column number.  Otherwise return NIL."
  (&key (tokstream 'tokstream))
  :returns (mv (errmsg        (not errmsg))
               (startcol      maybe-natp :rule-classes :type-prescription)
               (new-tokstream (equal new-tokstream tokstream)))
  (b* ((tokens (vl-tokstream->tokens))
       ((unless (and (consp tokens)
                     (vl-token->breakp (car tokens))))
        (mv nil nil tokstream))
       (echar1 (car (vl-token->etext (car tokens))))
       (col1   (vl-echarpack->col (vl-echar-raw->pack echar1))))
    (mv nil col1 tokstream)))

;; (defmacro vl-copy-tokens (&key (tokstream 'tokstream))
;;   "Returns (MV ERROR TOKENS TOKENS PSTATE) for SEQ compatibility."
;;   (declare (xargs :guard t))
;;   `(let ((tokens ,tokens)
;;          (pstate ,pstate))
;;      (mv nil tokens tokens pstate)))


(define vl-match (&key
                  (tokstream 'tokstream))
  :guard (consp (vl-tokstream->tokens))
  :short "Compatible with @(see seq).  Get the first token, no matter what
kind of token it is.  Only usable when you know there is a token there (via the
guard)."
  :inline t
  :returns (mv (errmsg?   (not errmsg?))
               (token     (equal (vl-token-p token)
                                 (consp (vl-tokstream->tokens))))
               (new-tokstream))
  (b* ((tokens    (vl-tokstream->tokens))
       (tokstream (vl-tokstream-pop)))
    (mv nil (car tokens) tokstream))
  ///
  ;; (defthm vl-match-of-vl-tokenlist-fix
  ;;   (equal (vl-match :tokens (vl-tokenlist-fix tokens))
  ;;          (vl-match)))

  ;; (defthm vl-match-of-vl-parsestate-fix
  ;;   (equal (vl-match :pstate (vl-parsestate-fix pstate))
  ;;          (vl-match)))

  (local (defthm l0
           (implies (vl-tokenlist-p x)
                    (iff (consp x)
                         (car x)))))

  (defthm vl-match-under-iff
    (iff (mv-nth 1 (vl-match))
         (consp (vl-tokstream->tokens))))

  (defthm vl-match-count-strong-on-value
    (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match)))
             (vl-tokstream-measure))
         (implies (mv-nth 1 (vl-match))
                  (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match)))
                     (vl-tokstream-measure))))
    :rule-classes ((:rewrite) (:linear))
    :hints(("Goal" :expand (len (vl-tokstream->tokens)))))

  (defthm equal-of-vl-match-count
    (equal (equal (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match)))
                  (vl-tokstream-measure))
           (atom (vl-tokstream->tokens))))

  (defthm vl-token->type-of-vl-match-when-vl-is-token?
    (implies (vl-is-token? type)
             (equal (vl-token->type (mv-nth 1 (vl-match)))
                    type))
    :hints(("Goal" :in-theory (enable vl-is-token?))))

  (defthm vl-token->type-of-vl-match-when-vl-is-some-token?
    (implies (vl-type-of-matched-token types (vl-tokstream->tokens))
             (equal (vl-token->type (mv-nth 1 (vl-match)))
                    (vl-type-of-matched-token types (vl-tokstream->tokens))))
    :hints(("Goal" :in-theory (enable vl-type-of-matched-token
                                      vl-is-some-token?))))

  (defthm more-tokens-after-vl-match-because-lookahead-sees-something
    (implies (vl-lookahead-is-token? token (cdr (vl-tokstream->tokens)))
             (consp (vl-tokstream->tokens :tokstream (mv-nth 2 (vl-match)))))
    :rule-classes ((:forward-chaining :trigger-terms ((vl-lookahead-is-token? token (cdr (vl-tokstream->tokens))))))
    :hints(("Goal" :in-theory (enable vl-lookahead-is-token?)))))



(define vl-match-any
  :short "Compatible with @(see seq).  Get the first token, no matter what
kind of token it is.  Causes an error on EOF."
  (&key
   ((function symbolp)       '__function__)
   (tokstream 'tokstream))
  :inline t
  :returns
  (mv (errmsg?)
      (token)
      (new-tokstream))
  (b* ((tokens (vl-tokstream->tokens))
       ((when (atom tokens))
        (vl-parse-error "Unexpected EOF." :function function))
       (tokstream (vl-tokstream-pop)))
    (mv nil (car tokens) tokstream))
  ///
  ;; (defthm vl-match-any-of-vl-tokenlist-fix
  ;;   (equal (vl-match-any :tokens (vl-tokenlist-fix tokens))
  ;;          (vl-match-any)))

  ;; (defthm vl-match-any-of-vl-parsestate-fix
  ;;   (equal (vl-match-any :pstate (vl-parsestate-fix pstate))
  ;;          (vl-match-any)))

  (defthm vl-match-any-fails-gracefully
    (implies (mv-nth 0 (vl-match-any))
             (equal (mv-nth 1 (vl-match-any))
                    nil)))

  (defthm vl-warning-p-of-vl-match-any
    (iff (vl-warning-p (mv-nth 0 (vl-match-any)))
         (mv-nth 0 (vl-match-any))))

  (defthm vl-token-p-of-vl-match-any
    (implies (not (mv-nth 0 (vl-match-any)))
             (vl-token-p (mv-nth 1 (vl-match-any)))))

  (defthm vl-match-any-fn-count-strong-on-value
    (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-any)))
             (vl-tokstream-measure))
         (implies (mv-nth 1 (vl-match-any))
                  (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-any)))
                     (vl-tokstream-measure))))
  :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-vl-match-any-fn-count
    (equal (equal (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-any)))
                  (vl-tokstream-measure))
           (if (mv-nth 0 (vl-match-any))
               t
             nil))))

(define vl-match-any-except
  :short "Compatible with @(see seq).  Match any token that is not of the
listed types.  Causes an error on EOF."
  ((types true-listp) ;; BOZO stronger guard?
   &key
   ((function symbolp)       '__function__)
   (tokstream 'tokstream))
  :returns
  (mv (errmsg? (iff (vl-warning-p errmsg?) errmsg?))
      (token)
      (new-tokstream))
  (b* ((tokens (vl-tokstream->tokens))
       ((when (atom tokens))
        (vl-parse-error "Unexpected EOF." :function function))
       (token1 (car tokens))
       ((when (member-eq (vl-token->type token1) types))
        (mv (make-vl-warning :type :vl-parse-error
                             :msg "Parse error at ~a0: unexpected ~s1."
                             :args (list (vl-token->loc token1)
                                         (vl-token->type token1))
                             :fn function
                             :fatalp t)
            nil tokstream))
       (tokstream (vl-tokstream-pop)))
    (mv nil token1 tokstream))
  ///
  (local (in-theory (enable vl-is-some-token?)))

  ;; (defthm vl-match-any-except-of-vl-tokenlist-fix
  ;;   (equal (vl-match-any-except types :tokens (vl-tokenlist-fix tokens))
  ;;          (vl-match-any-except types)))

  ;; (defthm vl-match-any-except-of-vl-parsestate-fix
  ;;   (equal (vl-match-any-except types :pstate (vl-parsestate-fix pstate))
  ;;          (vl-match-any-except types)))

  (defthm vl-match-any-except-fails-when-vl-is-some-token?
    (iff (mv-nth 0 (vl-match-any-except types))
         (or (atom (vl-tokstream->tokens))
             (vl-is-some-token? types))))

  (defthm vl-match-any-except-fails-gracefully
    (implies (or (atom (vl-tokstream->tokens))
                 (vl-is-some-token? types))
             (equal (mv-nth 1 (vl-match-any-except types))
                    nil)))

  (defthm vl-match-any-except-when-atom-of-tokens
    (implies (atom (vl-tokstream->tokens))
             (equal (mv-nth 2 (vl-match-any-except types))
                    tokstream)))

  (defthm vl-token-p-of-vl-match-any-except
    (implies (and (not (vl-is-some-token? types))
                  (consp (vl-tokstream->tokens)))
             (vl-token-p (mv-nth 1 (vl-match-any-except types)))))

  (defthm vl-match-any-except-count-strong-on-value
    (and (<= (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-any-except types)))
             (vl-tokstream-measure))
         (implies (mv-nth 1 (vl-match-any-except types))
                  (< (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-any-except types)))
                     (vl-tokstream-measure))))
    :rule-classes ((:rewrite) (:linear)))

  (defthm equal-of-vl-match-any-except-fn-count
    (equal (equal (vl-tokstream-measure :tokstream (mv-nth 2 (vl-match-any-except types)))
                  (vl-tokstream-measure))
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

  :tag nil
  :layout :fulltree

  ((name maybe-stringp :rule-classes :type-prescription
         "The name we matched after the colon, e.g., @('foo') above.")

   (loc  vl-location-p
         "The location of this name, for mismatch reporting.")))

(defparser vl-parse-endblock-name (name blktype)
  :guard (and (stringp name) (stringp blktype))
  :count weak
  :fails :gracefully
  (seq tokstream
       (unless (and (not (eq (vl-loadconfig->edition config) :verilog-2005))
                    (vl-is-token? :vl-colon))
         (return nil))
       (:= (vl-match))
       (endname := (vl-match-token :vl-idtoken))
       (when (equal name (vl-idtoken->name endname))
         (return name))
       (return-raw
        (mv (make-vl-warning :type :vl-parse-error
                             :msg "At ~a0: mismatched ~s1 names: ~s2 vs. ~s3."
                             :args (list (vl-token->loc endname)
                                         blktype
                                         name
                                         (vl-idtoken->name endname)))
            nil
            tokstream))))


(define vl-choose-parse-error ((pos1 natp) (err1 vl-warning-p)
                               (pos2 natp) (err2 vl-warning-p))
  :returns (mv (best-pos natp :rule-classes :type-prescription)
               (best-err vl-warning-p))
  (if (<= (lnfix pos1) (lnfix pos2))
      (mv (lnfix pos1) (vl-warning-fix err1))
    (mv (lnfix pos2) (vl-warning-fix err2)))
  ///
  (defret vl-choose-parse-error-under-iff
    best-err))


(defun clause-which-flag (clause)
  (declare (xargs :mode :program))
  (b* (((when (atom clause))
        nil)
       (lit1 (car clause)))
    (case-match lit1
      (('not ('acl2::flag-is ('quote flag)))
       flag)
      (&
       (clause-which-flag (cdr clause))))))

(defun expand-only-the-flag-function-hint (clause state)
  ;; This computed hint is a much more restrictive alternative to
  ;; flag::expand-calls-computed-hint.  We look for calls ONLY of the function
  ;; whose flag we are currently on.  This was particularly useful for
  ;; statement parsing, where we have a situation sort of like this:
  ;;
  ;;   (mutual-recursion
  ;;      (defun f1 ...)
  ;;      (defun f2 ...)
  ;;      ...
  ;;      (defun fN ...)
  ;;      (defun g (args)
  ;;         (cond ((cond1 args) (f1 args))
  ;;               ((cond2 args) (f2 args))
  ;;               ...
  ;;               ((condN args) (fN args)))))
  ;;
  ;; Here, when we get to proving a theorem about G, it is a really bad idea to
  ;; use expand-calls-computed-hint on all of the clique members (which
  ;; normally works fine), because they're all being invoked on the original
  ;; arguments, so it thinks they're all suitable for expansion and just opens
  ;; them all up, leading to a massive case split.
  ;;
  ;; So the idea here is: don't open up all of the functions, only open up the
  ;; one that is explicitly mentioned in the flag::flag-is hyp.  This doesn't
  ;; seem to make much of any difference for, e.g., expression parsing, but it
  ;; makes a big difference for statements.
  (declare (xargs :mode :program :stobjs state))
  (let ((flag (clause-which-flag clause)))
    (and flag
         (let ((fn (acl2::deref-macro-name flag (macro-aliases (w state)))))
           (std::expand-calls-computed-hint clause (list fn))))))

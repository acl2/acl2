; FGL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FGL")

(include-book "interp-st-bfrs-ok")
(include-book "std/strings/decimal" :dir :system)
(set-state-ok t)

(defconst *logically-relevant-interp-st-fields*
  '(:stack :logicman :bvar-db :pathcond :constraint :constraint-db
    :equiv-contexts :reclimit)) ;; removed :errmsg

(local (in-theory (disable w)))

(defconst *fancy-ev-primitive-thms*
  '((defret interp-st-get-of-<fn>
      (implies (member (interp-st-field-fix key)
                       *logically-relevant-interp-st-fields*)
               (equal (interp-st-get key new-interp-st)
                      (interp-st-get key interp-st))))

    (defret interp-st-bfrs-ok-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (interp-st-bfrs-ok new-interp-st)))

    (defret errmsg-of-<fn>
      (implies (interp-st->errmsg interp-st)
               (equal (interp-st->errmsg new-interp-st)
                      (interp-st->errmsg interp-st))))

    (defret interp-st->errmsg-equal-unreachable-of-<fn>
      (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
               (not (equal (interp-st->errmsg new-interp-st)
                           :unreachable))))

    (defret w-state-of-<fn>
      (equal (w new-state)
             (w state)))))
(encapsulate
  (((fancy-ev-primitive * * interp-st state) => (mv * * interp-st state)
    :formals (fn args interp-st state)
    :guard (and (pseudo-fnsym-p fn)
                (true-listp args)
                (interp-st-bfrs-ok interp-st))))
  (local (define fancy-ev-primitive (fn args interp-st state)
           :returns (mv ok ans new-interp-st new-state)
           (declare (ignore fn args))
           (mv nil nil interp-st state)))
  (local (in-theory (enable fancy-ev-primitive)))
  (make-event (cons 'progn *fancy-ev-primitive-thms*)))
   
(define fancy-ev-definition ((fn pseudo-fnsym-p) state)
  :returns (mv ok
               (formals symbol-listp)
               (body pseudo-termp))
  :prepwork ((local (in-theory (disable pseudo-termp symbol-listp pseudo-term-listp
                                        acl2::pseudo-termp-opener))))
  (b* ((tab (table-alist 'fancy-ev-definitions (w state)))
       (fn (pseudo-fnsym-fix fn))
       (look (cdr (hons-assoc-equal fn tab)))
       ((when (and (eql (len look) 2)
                   (symbol-listp (first look))
                   (pseudo-termp (second look))))
        (mv t (first look) (second look)))
       ((mv ok formals body) (acl2::fn-get-def fn state))
       ((unless (and ok (pseudo-termp body)))
        (mv nil nil nil)))
    (mv t formals body)))

(set-state-ok t)

(defines fancy-ev
  (define fancy-ev ((x pseudo-termp)
                    (alist symbol-alistp)
                    (reclimit natp)
                    (interp-st interp-st-bfrs-ok)
                    state
                    hard-errp
                    aokp)
    :well-founded-relation acl2::nat-list-<
    :measure (list reclimit (pseudo-term-count x))
    :returns (mv errmsg val new-interp-st new-state)
    :verify-guards nil
    :parents (fgl-rewrite-rules)
    :short "Term evaluator used by FGL for syntaxp, bind-free, and syntax-bind interpretation."
    :long "
<p>Fancy-ev is a term evaluator capable of running terms that include functions
that access the FGL interpreter state and the ACL2 state, and even may modify
the FGL interpreter state in limited ways.  It is used for evaluating syntaxp,
bind-free, and syntax-bind forms in the FGL rewriter.</p>

<p>Fancy-ev uses @(see magic-ev-fncall) to allow it to run most functions that
do not access stobjs.  When magic-ev-fncall fails, it can also expand function
definitions and interpret their bodies.  But additionally, it calls an
attachable function @('fancy-ev-primitive') to allow it to directly execute
functions that access and/or modify the ACL2 state and FGL @('interp-st').</p>

<p>To allow a function @('my-fn') that accesses/updates @('interp-st') or
@('state') to be executable by @('fancy-ev'), there are two steps:</p>

<ul>

<li>@('(fancy-ev-add-primitive my-fn guard-form)') checks that the function
is valid as a fancy-ev primitive and that guard-form suffices to check that the
function's guard is satisfied when provided an interp-st satisfying
@('interp-st-bfrs-ok').  If so, the function/guard pair is recorded in the
table @('fancy-ev-primitives') for later use by
@('def-fancy-ev-primitives').</li>

<li>@('(def-fancy-ev-primitives my-fancy-ev-primitives-impl)') defines a
function named @('my-fancy-ev-primitives-impl') and attaches it to
@('fancy-ev-primitive').  The function is defined as a case statement on the
input function symbol where for each function/guard pair in the
@('fancy-ev-primitives') table, if the input function symbol matches that
function, it checks the given guard form and then executes the function on the
input arguments, returning its return value list and modified interp-st (if
any).  This allows all functions that were added using
@('fancy-ev-add-primitive') to be executed by @('fancy-ev').</li>
</ul>"
    (pseudo-term-case x
      :const (mv nil x.val interp-st state)
      :var (mv nil (cdr (hons-assoc-equal x.name alist)) interp-st state)
      :lambda (b* (((mv err args interp-st state)
                    (fancy-ev-list x.args alist reclimit interp-st state hard-errp aokp))
                   ((when err) (mv err nil interp-st state)))
                (fancy-ev x.body
                          (pairlis$ x.formals args)
                          reclimit interp-st state hard-errp aokp))
      :fncall (b* (((when (and** (eq x.fn 'if) (eql (len x.args) 3)))
                    (b* (((mv err test interp-st state) (fancy-ev (first x.args) alist reclimit interp-st state hard-errp aokp))
                         ((when err) (mv err nil interp-st state)))
                      (if test
                          (if (equal (first x.args) (second x.args))
                              ;; OR case
                              (mv nil test interp-st state)
                            (fancy-ev (second x.args) alist reclimit interp-st state hard-errp aokp))
                        (fancy-ev (third x.args) alist reclimit interp-st state hard-errp aokp))))
                   ((when (and** (eq x.fn 'return-last) (eql (len x.args) 3)))
                    (b* ((arg1 (first x.args)))
                      (b* (((mv interp-st state)
                            (pseudo-term-case arg1
                              :const (if (eq arg1.val 'progn)
                                         (b* (((mv ?err ?arg1 interp-st state)
                                               (fancy-ev (second x.args) alist reclimit interp-st state hard-errp aokp)))
                                           (mv interp-st state))
                                       (mv interp-st state))
                              :otherwise (mv interp-st state))))
                        (fancy-ev (third x.args) alist reclimit interp-st state hard-errp aokp))))
                   ((mv err args interp-st state) (fancy-ev-list x.args alist reclimit interp-st state hard-errp aokp))
                   ((when err) (mv err nil interp-st state)))
                (fancy-ev-fncall x.fn args reclimit interp-st state hard-errp aokp))))

  (define fancy-ev-fncall ((fn pseudo-fnsym-p)
                           (args true-listp)
                           (reclimit natp)
                           (interp-st interp-st-bfrs-ok)
                           state hard-errp aokp)
    :measure (list reclimit 0)
    :returns (mv errmsg val new-interp-st new-state)
    (b* ((fn (pseudo-fnsym-fix fn))
         (args (mbe :logic (true-list-fix args)
                    :exec args))
         ((mv ev-ok val interp-st state)
          (fancy-ev-primitive fn args interp-st state))
         ((when ev-ok) (mv nil val interp-st state))
         ((mv ev-err val)
          (acl2::magic-ev-fncall fn
                                 args
                                 state hard-errp aokp))
         ((unless ev-err) (mv nil val interp-st state))
         ((when (zp reclimit))
          (mv (msg "Recursion limit ran out calling ~x0" (pseudo-fnsym-fix fn)) nil interp-st state))
         ((mv def-ok formals body) (fancy-ev-definition fn state))
         ((unless def-ok)
          (mv (msg "No definition for ~x0" (pseudo-fnsym-fix fn)) nil interp-st state))
         ((unless (eql (len formals) (len args)))
          (mv (msg "Wrong arity for ~x0 call" (pseudo-fnsym-fix fn)) nil interp-st state)))
      (fancy-ev body (pairlis$ formals args) (1- reclimit) interp-st state hard-errp aokp)))

  (define fancy-ev-list ((x pseudo-term-listp)
                         (alist symbol-alistp)
                         (reclimit natp)
                         (interp-st interp-st-bfrs-ok)
                         state hard-errp aokp)
    :measure (list reclimit (pseudo-term-list-count x))
    :returns (mv errmsg (vals true-listp) new-interp-st new-state)
    (b* (((when (atom x))
          (mv nil nil interp-st state))
         ((mv err first interp-st state) (fancy-ev (car x) alist reclimit interp-st state hard-errp aokp))
         ((when err) (mv err nil interp-st state))
         ((mv err rest interp-st state) (fancy-ev-list (cdr x) alist reclimit interp-st state hard-errp aokp))
         ((when err) (mv err nil interp-st state)))
      (mv nil (cons first rest) interp-st state)))
  ///
  (local (in-theory (disable acl2::member-of-cons member (tau-system) pseudo-termp pseudo-term-listp
                             fancy-ev fancy-ev-fncall fancy-ev-list)))
  (defret-mutual interp-st-get-of-fancy-ev
    (defret interp-st-get-of-<fn>
      (implies (member (interp-st-field-fix key) *logically-relevant-interp-st-fields*)
               (equal (interp-st-get key new-interp-st)
                      (interp-st-get key interp-st)))
      :hints ('(:expand (<call>)))
      :fn fancy-ev)
    (defret interp-st-get-of-<fn>
      (implies (member (interp-st-field-fix key) *logically-relevant-interp-st-fields*)
               (equal (interp-st-get key new-interp-st)
                      (interp-st-get key interp-st)))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-fncall)
    (defret interp-st-get-of-<fn>
      (implies (member (interp-st-field-fix key) *logically-relevant-interp-st-fields*)
               (equal (interp-st-get key new-interp-st)
                      (interp-st-get key interp-st)))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-list))

  (defret-mutual interp-st-bfrs-ok-of-fancy-ev
    (defret interp-st-bfrs-ok-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (interp-st-bfrs-ok new-interp-st))
      :hints ('(:expand (<call>)))
      :fn fancy-ev)
    (defret interp-st-bfrs-ok-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (interp-st-bfrs-ok new-interp-st))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-fncall)
    (defret interp-st-bfrs-ok-of-<fn>
      (implies (interp-st-bfrs-ok interp-st)
               (interp-st-bfrs-ok new-interp-st))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-list))

  (defret-mutual errmsg-of-fancy-ev
    (defret errmsg-of-<fn>
      (implies (interp-st->errmsg interp-st)
               (equal (interp-st->errmsg new-interp-st)
                      (interp-st->errmsg interp-st)))
      :hints ('(:expand (<call>)))
      :fn fancy-ev)
    (defret errmsg-of-<fn>
      (implies (interp-st->errmsg interp-st)
               (equal (interp-st->errmsg new-interp-st)
                      (interp-st->errmsg interp-st)))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-fncall)
    (defret errmsg-of-<fn>
      (implies (interp-st->errmsg interp-st)
               (equal (interp-st->errmsg new-interp-st)
                      (interp-st->errmsg interp-st)))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-list))

  (defret-mutual unreachable-of-fancy-ev
    (defret unreachable-of-<fn>
      (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
               (not (equal (interp-st->errmsg new-interp-st) :unreachable)))
      :hints ('(:expand (<call>)))
      :fn fancy-ev)
    (defret unreachable-of-<fn>
      (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
               (not (equal (interp-st->errmsg new-interp-st) :unreachable)))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-fncall)
    (defret unreachable-of-<fn>
      (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
               (not (equal (interp-st->errmsg new-interp-st) :unreachable)))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-list))

  (defret-mutual w-state-of-fancy-ev
    (defret w-state-of-<fn>
      (equal (w new-state) (w state))
      :hints ('(:expand (<call>)))
      :fn fancy-ev)
    (defret w-state-of-<fn>
      (equal (w new-state) (w state))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-fncall)
    (defret w-state-of-<fn>
      (equal (w new-state) (w state))
      :hints ('(:expand (<call>)))
      :fn fancy-ev-list))

  (local (defthm true-listp-when-symbol-listp
           (implies (symbol-listp x)
                    (true-listp x))))

  (verify-guards fancy-ev
    :hints(("Goal" :in-theory (enable acl2::member-of-cons))))

  (local (in-theory (disable fancy-ev fancy-ev-list fancy-ev-fncall
                             pseudo-term-listp pseudo-termp)))

  (fty::deffixequiv-mutual fancy-ev))



(program)

(defun fancy-ev-primitive-bindings (argsvar stobjs-in formals n)
  (if (atom stobjs-in)
      nil
    (if (car stobjs-in)
        (fancy-ev-primitive-bindings argsvar (cdr stobjs-in) (cdr formals) (+ 1 n))
      `((,(car formals) (nth ,n ,argsvar))
        . ,(fancy-ev-primitive-bindings argsvar (cdr stobjs-in) (cdr formals) (+ 1 n))))))

(defun fancy-ev-primitive-formals (stobjs-in formals)
  (if (atom stobjs-in)
      nil
    (cons (or (car stobjs-in) (car formals))
          (fancy-ev-primitive-formals (cdr stobjs-in) (cdr formals)))))

(defun fancy-ev-stobj-out-bindings (stobjs-out n)
  (if (atom stobjs-out)
      nil
    (cons (or (car stobjs-out)
              (intern-in-package-of-symbol (concatenate 'string "OUT" (str::natstr n)) 'fgl-fgl))
          (fancy-ev-stobj-out-bindings (cdr stobjs-out) (+ 1 n)))))

(defun fancy-ev-stobj-out-results (stobjs-out vars)
  (if (atom stobjs-out)
      nil
    (cons (if (car stobjs-out) nil (car vars))
          (fancy-ev-stobj-out-results (cdr stobjs-out) (cdr vars)))))

(defun fancy-ev-primitive-call (argsvar fn guard state)
  (b* ((wrld (w state))
       (formals (acl2::formals fn wrld))
       (stobjs-in (acl2::stobjs-in fn wrld))
       (diff (set-difference-eq stobjs-in '(nil interp-st state)))
       ((when diff)
        (er hard? 'fancy-ev-primitive-call "~x0 takes input stobjs ~x1 -- only interp-st and state are allowed"
            fn diff))
       (stobjs-out (stobjs-out fn wrld))
       (diff (set-difference-eq stobjs-out '(nil interp-st state)))
       ((when diff)
        (er hard? 'fancy-ev-primitive-call "~x0 can modify stobjs ~x1 -- only interp-st and state may be modified"
            fn diff))
       (bindings (fancy-ev-primitive-bindings argsvar stobjs-in formals 0))
       (call-formals (fancy-ev-primitive-formals stobjs-in formals))
       ((unless (intersectp-eq '(interp-st state) stobjs-out))
        `(b* (,@bindings
              (result (mbe :logic (non-exec (,fn . ,call-formals))
                           :exec (if ,guard
                                     ,(if (consp (cdr stobjs-out))
                                          `(mv-list ,(len stobjs-out)
                                                    (,fn . ,call-formals))
                                        `(,fn . ,call-formals))
                                   (non-exec (ec-call (,fn . ,call-formals)))))))
           (mv t result interp-st state)))
       (out-bindings (fancy-ev-stobj-out-bindings stobjs-out 0))
       (results (fancy-ev-stobj-out-results stobjs-out out-bindings)))
    `(b* (,@bindings
          (,@(if (consp (cdr stobjs-out))
                 `((mv . ,out-bindings))
               out-bindings)
             (mbe :logic (,fn . ,call-formals)
                  :exec (if ,guard
                            (,fn . ,call-formals)
                          (ec-call (,fn . ,call-formals))))))
       (mv t (list . ,results) interp-st state))))

(defun fancy-ev-check-primitive-fn (fn guard state)
  (b* ((call (fancy-ev-primitive-call 'args fn guard state)))
    `(:or
      (encapsulate nil
        (local
         (with-output :stack :pop
           (define fancy-ev-primitive-test ((fn pseudo-fnsym-p)
                                            (args true-listp)
                                            (interp-st interp-st-bfrs-ok)
                                            state)
             :ignore-ok t
             :irrelevant-formals-ok t
             ,call
             ///
             (defattach fancy-ev-primitive fancy-ev-primitive-test)))))
      (with-output :stack :pop
        (value-triple
         (er hard? 'fancy-ev-check-primitive
             "The function ~x0 with guard ~x1 failed the check for a valid ~
            fancy-ev primitive.  Check the error messages above for details."
             ',fn ',guard))))))


(defmacro fancy-ev-add-primitive (fn guard)
  `(with-output
     :off (error) :stack :push
     (progn
       (make-event (fancy-ev-check-primitive-fn ',fn ',guard state))
       (table fancy-ev-primitives ',fn ',guard))))



(defun fancy-ev-primitives-cases (argsvar table state)
  (b* (((when (atom table)) nil)
       ((cons fn guard) (car table))
       (call (fancy-ev-primitive-call argsvar fn guard state)))
    `((,fn ,call)
      . ,(fancy-ev-primitives-cases argsvar (cdr table) state))))


(defun def-fancy-ev-primitives-fn (fnname state)
  (b* ((prims (table-alist 'fancy-ev-primitives (w state))))
    `(progn
       (define ,fnname ((fn pseudo-fnsym-p)
                        (args true-listp)
                        (interp-st interp-st-bfrs-ok)
                        state)
         :ignore-ok t
         :irrelevant-formals-ok t
         :returns (mv okp ans new-interp-st new-state)
         (case (pseudo-fnsym-fix fn)
           ,@(fancy-ev-primitives-cases 'args prims state)
           (otherwise (mv nil nil interp-st state)))
         ///
         (make-event (cons 'progn *fancy-ev-primitive-thms*)))
       (defattach fancy-ev-primitive ,fnname))))

(defmacro def-fancy-ev-primitives (fnname)
  `(make-event
    (def-fancy-ev-primitives-fn ',fnname state)))

(logic)

(fancy-ev-add-primitive fgl-interp-store-debug-info (not (eq msg :unreachable)))


(local
 (progn

   (define my-set-debug (val state)
     :returns new-state
     (f-put-global ':my-global-var val state)
     ///
     (defret w-of-<fn>
       (equal (w new-state) (w state))
       :hints(("Goal" :in-theory (enable w)))))

   (fancy-ev-add-primitive my-set-debug t)

   (def-fancy-ev-primitives foo)))


(local
 (defun make-interp-st-fancy-ev-primitives (keys)
   (if (atom keys)
       nil
     (let ((key (caar keys))
           (guard (cdar keys)))
       (cons `(fancy-ev-add-primitive ,(intern-in-package-of-symbol
                                        (if (eq guard t)
                                            (concatenate 'string "INTERP-ST->" (symbol-name key))
                                          (concatenate 'string "INTERP-ST->" (symbol-name key) "$INLINE"))
                                        'fgl-fgl)
                                      t)
             (if (or (member key *logically-relevant-interp-st-fields*)
                     (eq key :cgraph)
                     (eq key :errmsg))
                 (make-interp-st-fancy-ev-primitives (cdr keys))
               (cons `(fancy-ev-add-primitive ,(intern-in-package-of-symbol
                                                (if (eq guard t)
                                                    (concatenate 'string "UPDATE-INTERP-ST->" (symbol-name key))
                                                  (concatenate 'string "UPDATE-INTERP-ST->" (symbol-name key) "$INLINE"))
                                                'fgl-fgl)
                                              ,guard)
                     (make-interp-st-fancy-ev-primitives (cdr keys)))))))))
(make-event
 (cons 'progn (make-interp-st-fancy-ev-primitives
               '((:constraint-db . (constraint-db-p constraint-db))
                 (:backchain-limit . (integerp backchain-limit))
                 (:equiv-contexts . (equiv-contextsp equiv-contexts))
                 (:reclimit       . (natp reclimit))
                 (:config         . (fgl-config-p config))
                 (:flags          . (interp-flags-p flags))
                 (:next-fgarray   . (natp next-fgarray))
                 (:cgraph         . (cgraph-p cgraph))
                 (:cgraph-memo    . (cgraph-alist-p cgraph-memo))
                 (:cgraph-index   . (natp cgraph-index))
                 (:user-scratch   . (obj-alist-p user-scratch))
                 (:trace-scratch  . t)
                 (:errmsg         . t)
                 (:debug-info     . t)
                 (:debug-stack    . (major-stack-p debug-stack))))))




;; (logic)

;; (fancy-ev-add-primitive update-interp-st->cgraph$inline (cgraph-p cgraph))

;; (def-fancy-ev-primitives foo-bar)

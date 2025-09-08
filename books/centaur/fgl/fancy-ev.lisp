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

;; BOZO this is the same as ACL2's built-in defined-constant but has a corrected guard
(defun defined-constant (name w)
  (declare (xargs :guard (plist-worldp w)))
  (and (symbolp name)
       (getpropc name 'acl2::const nil w)))

(verify-termination acl2::listlis)
(verify-termination acl2::lambda-to-let)

(define fancy-translate-atom (x
                              (wrld plist-worldp))
  :returns (mv err (val pseudo-termp))
  (b* (((unless (symbolp x))
        (mv nil (pseudo-term-quote x)))
       ((when (or (keywordp x) (booleanp x)))
        (mv nil (pseudo-term-quote x)))
       (v/c (acl2::legal-variable-or-constant-namep x))
       ((unless v/c)
        (mv (msg "Not a legal variable or constant symbol: ~x0" x) nil))
       ((when (eq v/c 'acl2::constant))
        (b* ((const (defined-constant x wrld))
             ((unless const)
              (mv (msg "The symbol ~x0 has the syntax of a constant but isn't defined." x) nil))
             ((unless (and (pseudo-termp const) (pseudo-term-case const :quote)))
              (mv (msg "Programming error: the ~x0 property of ~x1 is not a quoted constant as expected." 'acl2::const x) nil)))
          (mv nil const))))
    (mv nil (pseudo-term-var x))))
            
       
(define fancy-translate-wrld-okp ((wrld plist-worldp))
  :returns (ok)
  (and (symbol-alistp
        (table-alist 'acl2::duplicate-keys-action-table
                     wrld))
       (string-alistp
        (table-alist 'acl2::inhibit-warnings-table
                     wrld)))
  ///
  (defret <fn>-implies
    (implies ok
             (and (symbol-alistp
                   (table-alist 'acl2::duplicate-keys-action-table
                                wrld))
                  (string-alistp
                   (table-alist 'acl2::inhibit-warnings-table
                                wrld))))))

(defthm acl2-count-of-strip-cadrs
  (<= (acl2-count (acl2::strip-cadrs x))
      (acl2-count x))
  :rule-classes :linear)

(local
 (encapsulate nil
   (flag::make-flag all-vars1 :local t)
   (acl2::defthm-flag-all-vars1 true-listp-of-all-vars1
     (defthm true-listp-of-all-vars1
       (implies (true-listp acl2::ans)
                (true-listp (all-vars1 acl2::term acl2::ans)))
       :hints ('(:expand ((:free (acl2::ans) (all-vars1 acl2::term acl2::ans)))))
       :flag all-vars1)
     (defthm true-listp-of-all-vars1-lst
       (implies (true-listp acl2::ans)
                (true-listp (all-vars1-lst acl2::lst acl2::ans)))
       :hints ('(:expand ((:free (acl2::ans) (all-vars1-lst acl2::lst acl2::ans)))))
       :flag all-vars1-lst))

   (acl2::defthm-flag-all-vars1 symbol-listp-of-all-vars1
     (defthm symbol-listp-of-all-vars1
       (implies (and (symbol-listp acl2::ans)
                     (pseudo-termp acl2::term))
                (symbol-listp (all-vars1 acl2::term acl2::ans)))
       :hints ('(:expand ((:free (acl2::ans) (all-vars1 acl2::term acl2::ans)))))
       :flag all-vars1)
     (defthm symbol-listp-of-all-vars1-lst
       (implies (and (symbol-listp acl2::ans)
                     (pseudo-term-listp acl2::lst))
                (symbol-listp (all-vars1-lst acl2::lst acl2::ans)))
       :hints ('(:expand ((:free (acl2::ans) (all-vars1-lst acl2::lst acl2::ans)))))
       :flag all-vars1-lst))))

(verify-termination acl2::make-lambda-term)

(local
 (encapsulate nil
   (defthm pseudo-term-listp-when-symbol-listp
     (implies (symbol-listp x)
              (pseudo-term-listp x)))
   (defthm symbol-listp-of-set-diff
     (implies (symbol-listp x)
              (symbol-listp (set-difference-equal x y)))
     :hints(("Goal" :in-theory (enable set-difference-equal))))

   (defthm symbol-listp-of-append
     (implies (and (symbol-listp x)
                   (symbol-listp y))
              (symbol-listp (append x y))))
  
   (defthm pseudo-termp-of-make-lambda-term
     (implies (and (symbol-listp formals)
                   (pseudo-term-listp actuals)
                   (pseudo-termp body)
                   (equal (len formals) (len actuals)))
              (pseudo-termp (acl2::make-lambda-term formals actuals body)))
     :hints(("Goal" :in-theory (enable acl2::make-lambda-term)
             :do-not-induct t)))))

(define mv-nth-list ((mv-var symbolp)
                        (i natp)
                        (max natp))
  :measure (nfix (- (nfix max) (nfix i)))
  :guard (<= i max)
  :returns (terms pseudo-term-listp :hyp (symbolp mv-var))
  (if (mbe :logic (zp (- (nfix max) (nfix i)))
           :exec (eql i max))
      nil
    (cons (list 'mv-nth (list 'quote i) mv-var)
          (mv-nth-list mv-var (+ 1 (lnfix i)) max)))
  ///
  (defret len-of-<fn>
    (equal (len terms) (nfix (- (nfix max) (nfix i))))))

(defthm acl2-count-of-car-last
  (implies (consp x)
           (< (acl2-count (car (last x))) (acl2-count x)))
  :rule-classes :linear)

(local
 (defthm symbol-listp-when-arglistp
   (implies (acl2::arglistp x)
            (symbol-listp x))
   :hints(("Goal" :in-theory (enable acl2::arglistp)))))

(local
 (defthm len-of-strip-cadrs
   (equal (len (acl2::strip-cadrs x))
          (len x))
   :hints(("Goal" :in-theory (enable acl2::strip-cadrs)))))

(local (in-theory (disable acl2::bind-macro-args
                           acl2::lambda-to-let
                           acl2::arglistp
                           acl2::macro-args-structurep
                           acl2::genvar
                           acl2::make-lambda-term
                           last)))
           
(with-output
  :evisc (:gag-mode '(nil 7 10 nil))
  (defines fancy-ev
    (define fancy-ev ((x pseudo-termp)
                      (alist symbol-alistp)
                      (reclimit natp)
                      (interp-st interp-st-bfrs-ok)
                      state
                      hard-errp
                      aokp)
      :well-founded-relation acl2::nat-list-<
      :measure (list reclimit 10 (pseudo-term-count x))
      :measure-debug t
      :returns (mv errmsg val new-interp-st new-state)
      :verify-guards nil
      :parents (fgl-rewrite-rules)
      :hints (("Goal" :do-not-induct t))
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
</ul>

<p>Note that fancy-ev primitives cannot invoke fancy-ev. However, a term
evaluated in fancy-ev can invoke fancy-ev (though the recursive call limit and
hard-errp/aokp flags from the term are ignored).</p>

<p>See also @(see fancy-translate).</p>

"
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
      :measure (list reclimit 10 0)
      :returns (mv errmsg val new-interp-st new-state)
      (b* ((fn (pseudo-fnsym-fix fn))
           (args (mbe :logic (true-list-fix args)
                      :exec args))
           ((mv ev-ok val interp-st state)
            (fancy-ev-primitive fn args interp-st state))
           ((when ev-ok) (mv nil val interp-st state))
           
           ((when (member-eq fn '(fancy-ev
                                  fancy-ev-fncall
                                  fancy-ev-list
                                  fancy-translate)))
            (b* (((when (zp reclimit))
                  (mv (msg "Recursion limit ran out calling ~x0" (pseudo-fnsym-fix fn)) nil interp-st state)))
              (fancy-ev-fncall-special fn args (1- reclimit) interp-st state hard-errp aokp)))

           ((mv ev-err val)
            (acl2::magic-ev-fncall fn
                                   args
                                   state hard-errp aokp))
           ((unless ev-err) (mv nil val interp-st state))
           ((mv def-ok formals body) (fancy-ev-definition fn state))
           ((unless def-ok)
            (mv (msg "No definition for ~x0 (and error while evaluating)" (pseudo-fnsym-fix fn))
                nil interp-st state))
           ((unless (eql (len formals) (len args)))
            (mv (msg "Wrong arity for ~x0 call" (pseudo-fnsym-fix fn)) nil interp-st state))
           ((when (zp reclimit))
            (mv (msg "Recursion limit ran out calling ~x0" (pseudo-fnsym-fix fn)) nil interp-st state)))
        (fancy-ev body (pairlis$ formals args) (1- reclimit) interp-st state hard-errp aokp)))

    (define fancy-ev-fncall-special ((fn pseudo-fnsym-p)
                                     (args true-listp)
                                     (reclimit natp)
                                     (interp-st interp-st-bfrs-ok)
                                     state hard-errp aokp)
      :Guard (member-eq fn '(fancy-ev
                             fancy-ev-fncall
                             fancy-ev-list
                             fancy-translate))
      :measure (list reclimit 100 0)
      :returns (mv errmsg val new-interp-st new-state)
      (b* ((fn (pseudo-fnsym-fix fn))
           (args (llist-fix args))
           ((mv errmsg val interp-st state)
            (case fn
              (fancy-ev
               (cond ((< (len args) 2)
                      (mv (msg "Not enough args in meta-call of fancy-ev with args: ~x0" args)
                          nil interp-st state))
                     ((not (and (pseudo-termp (car args))
                                (symbol-alistp (cadr args))))
                      (mv (msg "Guard violation on meta-call of fancy-ev with args: ~x0" args)
                          nil interp-st state))
                     (t (fancy-ev (car args) (cadr args) reclimit interp-st state hard-errp aokp))))
              (fancy-ev-fncall
               (cond ((< (len args) 2)
                      (mv (msg "Not enough args in meta-call of fancy-ev-fncall with args: ~x0" args)
                          nil interp-st state))
                     ((not (and (pseudo-fnsym-p (car args))
                                (true-listp (cadr args))))
                      (mv (msg "Guard violation on meta-call of fancy-ev-fncall with args: ~x0" args)
                          nil interp-st state))
                     (t (fancy-ev-fncall (car args) (cadr args) reclimit interp-st state hard-errp aokp))))
              (fancy-ev-list
               (cond ((< (len args) 2)
                      (mv (msg "Not enough args in meta-call of fancy-ev-list with args: ~x0" args)
                          nil interp-st state))
                     ((not (and (pseudo-term-listp (car args))
                                (symbol-alistp (cadr args))))
                      (mv (msg "Guard violation on meta-call of fancy-ev-list with args: ~x0" args)
                          nil interp-st state))
                     (t (fancy-ev-list (car args) (cadr args) reclimit interp-st state hard-errp aokp))))
              (fancy-translate
               (cond ((< (len args) 1)
                      (mv (msg "Not enough args in meta-call of fancy-translate: ~x0" args)
                          nil interp-st state))
                     (t (fancy-translate (car args) reclimit interp-st state hard-errp aokp))))
              (t
               (mv "impossible" nil interp-st state)))))
        (mv nil (list errmsg val 'interp-st 'state) interp-st state)))
                

    (define fancy-ev-list ((x pseudo-term-listp)
                           (alist symbol-alistp)
                           (reclimit natp)
                           (interp-st interp-st-bfrs-ok)
                           state hard-errp aokp)
      :measure (list reclimit 10 (pseudo-term-list-count x))
      :returns (mv errmsg (vals true-listp) new-interp-st new-state)
      (b* (((when (atom x))
            (mv nil nil interp-st state))
           ((mv err first interp-st state) (fancy-ev (car x) alist reclimit interp-st state hard-errp aokp))
           ((when err) (mv err nil interp-st state))
           ((mv err rest interp-st state) (fancy-ev-list (cdr x) alist reclimit interp-st state hard-errp aokp))
           ((when err) (mv err nil interp-st state)))
        (mv nil (cons first rest) interp-st state)))

    (define fancy-translate (x
                                 (reclimit natp)
                                 (interp-st interp-st-bfrs-ok)
                                 state hard-errp aokp)
      :measure (list reclimit 11 (acl2-count x))
      :returns (mv errmsg (val pseudo-termp) new-interp-st new-state)
      :parents (fancy-ev)
      :short "Pseudo-translate an ACL2 form into a term using @(see fancy-ev) to evaluate macros."
      :long "
<p>Fancy-translate allows translation of untranslated terms into translated
form, much like ACL2's @('translate') family of functions, but without many
complicated features.</p>

<p>Fancy-translate is highly simplified relative to ACL2's translate. It
doesn't check executability constraints, stobj discipline, or even arity of
function calls. It supports @('let'), @('mv-let'), and macroexpansion, but not
@('flet'), @('macrolet'), @('loop$'), @('df') values, translation of lambda$
objects, and many other complications.</p>"
      (if (fancy-translate-wrld-okp (w state))
          (fancy-translate1 x reclimit interp-st state hard-errp aokp)
        (mv (msg "Programming error: world didn't satisfy ~x0" 'fancy-translate-wrld-okp)
            nil interp-st state)))
          
    (define fancy-translate1 (x
                             (reclimit natp)
                             (interp-st interp-st-bfrs-ok)
                             state hard-errp aokp)
      :guard (fancy-translate-wrld-okp (w state))
      :measure (list reclimit 10 (acl2-count x))
      :returns (mv errmsg (val pseudo-termp) new-interp-st new-state)
      (b* ((wrld (w state))
           ((when (atom x))
            (b* (((mv err res) (fancy-translate-atom x wrld))
                 ((when err)
                  (mv (msg "Fancy-translate error (atom): ~@0" err) nil interp-st state)))
              (mv nil res interp-st state)))
           (fnsym (car x)))
        (case fnsym
          (quote (if (and (consp (cdr x))
                          (not (cddr x)))
                     (mv nil (pseudo-term-quote (cadr x)) interp-st state)
                   (mv (msg "Fancy-translate error: Improper quote object: ~x0" x)
                       nil interp-st state)))
          (let (fancy-translate-let (cdr x) reclimit interp-st state hard-errp aokp))
          (mv-let (fancy-translate-mv-let (cdr x) reclimit interp-st state hard-errp aokp))
          (t (b* (((unless (true-listp x))
                   (mv (msg "Fancy-translate error: not a true-list: ~x0" x)
                       nil interp-st state))
                  ((unless (symbolp fnsym))
                   (b* (((mv err let) (acl2::lambda-to-let x))
                        ((when err)
                         (mv (msg "Fancy-translate error (lambda-to-let): ~@0" err) nil interp-st state))
                        ((when (zp reclimit))
                         (mv (msg "Recursion limit ran out translating ~x0" x)
                             nil interp-st state)))
                     (fancy-translate1 let (1- reclimit) interp-st state hard-errp aokp)))
                  (macro-body (getpropc fnsym 'acl2::macro-body nil wrld))
                  ((unless macro-body)
                   (b* (((mv err args interp-st state)
                         (fancy-translate-args (cdr x) reclimit interp-st state hard-errp aokp))
                        ((when err)
                         (mv err nil interp-st state)))
                     (mv nil (pseudo-term-fncall fnsym args) interp-st state)))
                  (macro-args (acl2::macro-args fnsym wrld))
                  ((unless (pseudo-termp macro-body))
                   (mv (msg "Programming error: macro body of ~x0 was not a pseudo-term: ~x1"
                            fnsym macro-body)
                       nil interp-st state))
                  ((unless (acl2::macro-args-structurep macro-args))
                   (mv (msg "Programming error: macro args of ~x0 was not of the expected form: ~x1"
                            fnsym macro-args)
                       nil interp-st state))
                  ((mv ctx alist)
                   (acl2::bind-macro-args macro-args x wrld
                                          (acl2::default-state-vars nil)))
                  ((when ctx)
                   (mv (msg "~x0: ~@1" ctx alist) nil interp-st state))
                  ((unless (symbol-alistp alist))
                   (mv (msg "Programming error: bad result from bind-macro-args: ~x0" alist)
                       nil interp-st state))
                  ((when (zp reclimit))
                   (mv (msg "Recursion limit ran out translating ~x0" x)
                       nil interp-st state))
                  ((mv err expansion interp-st state)
                   (fancy-ev macro-body alist (1- reclimit) interp-st state hard-errp aokp))
                  ((when err)
                   (mv err nil interp-st state)))
               (fancy-translate1 expansion (1- reclimit) interp-st state hard-errp aokp))))))

    (define fancy-translate-args ((x true-listp)
                                  (reclimit natp)
                                  (interp-st interp-st-bfrs-ok)
                                  state hard-errp aokp)
      :guard (fancy-translate-wrld-okp (w state))
      :measure (list reclimit 10 (acl2-count x))
      :returns (mv errmsg
                   (val (and (pseudo-term-listp val)
                             (implies (not errmsg)
                                      (equal (len val) (len x)))))
                   new-interp-st new-state)
      (if (atom x)
          (mv nil nil interp-st state)
        (b* (((mv err first interp-st state)
              (fancy-translate1 (car x) reclimit interp-st state hard-errp aokp))
             ((when err)
              (mv err nil interp-st state))
             ((mv err rest interp-st state)
              (fancy-translate-args (cdr x) reclimit interp-st state hard-errp aokp)))
          (mv err (and (not err) (cons first rest)) interp-st state))))
      

    (define fancy-translate-let (x
                                 (reclimit natp)
                                 (interp-st interp-st-bfrs-ok)
                                 state hard-errp aokp)
      :guard (fancy-translate-wrld-okp (w state))
      :measure (list reclimit 10 (acl2-count x))
      :returns (mv errmsg (val pseudo-termp) new-interp-st new-state)
      ;; x is the cdr of a let form, i.e. (bindings [ decls ] body)
      (b* (((unless (and (>= (len x) 2)
                         (doublet-listp (car x))))
            (mv (msg "Fancy-translate error: invalid form for let: ~x0" `(let . ,x))
                nil interp-st state))
           (bindings (car x))
           (vars (strip-cars bindings))
           ((unless (acl2::arglistp vars))
            (mv (msg "Fancy-translate error: invalid form for let (bound variables): ~x0" `(let . ,x))
                nil interp-st state))
           (args (acl2::strip-cadrs bindings))
           ((mv err trans-args interp-st state)
            ;; relying on acl2-count-of-strip-cadrs
            (fancy-translate-args args reclimit interp-st state hard-errp aokp))
           ((when err) (mv err nil interp-st state))
           ;; ignoring declarations for now
           (body (car (last x)))
           ((mv err trans-body interp-st state)
            (fancy-translate1 body reclimit interp-st state hard-errp aokp))
           ((when err) (mv err nil interp-st state)))
        (mv nil (acl2::make-lambda-term vars trans-args trans-body) interp-st state)))

    
    (define fancy-translate-mv-let (x
                                    (reclimit natp)
                                    (interp-st interp-st-bfrs-ok)
                                    state hard-errp aokp)
      :guard (fancy-translate-wrld-okp (w state))
      :measure (list reclimit 10 (acl2-count x))
      :returns (mv errmsg (val pseudo-termp) new-interp-st new-state)
      ;; x is the cdr of an mv-let form, i.e. (bound-vars bound-expr [ decls ] body)
      (b* (((unless (and (>= (len x) 3)
                         (true-listp (car x))
                         (> (len (car x)) 1)))
            (mv (msg "Fancy-translate error: invalid form for mv-let: ~x0" `(let . ,x))
                nil interp-st state))
           (vars (car x))
           ((unless (acl2::arglistp vars))
            (mv (msg "Fancy-translate error: invalid form for mv-let (bound variables): ~x0" `(let . ,x))
                nil interp-st state))
           (bound-expr (cadr x))
           ((mv err trans-bound interp-st state)
            (fancy-translate1 bound-expr reclimit interp-st state hard-errp aokp))
           ((when err)
            (mv err nil interp-st state))
           (body (car (last x)))
           ((mv err trans-body interp-st state)
            (fancy-translate1 body reclimit interp-st state hard-errp aokp))
           ((when err)
            (mv err nil interp-st state))
           (body-vars (acl2::all-vars trans-body))
           (mv-var (acl2::genvar 'acl2::acl2-pkg "MV" nil body-vars))
           (mv-nth-lst (mv-nth-list mv-var 0 (len vars))))
        (mv nil
            (acl2::make-lambda-term
             (list mv-var) (list trans-bound)
             (acl2::make-lambda-term
              vars mv-nth-lst trans-body))
            interp-st state)))
                               
           
           
                  
           
    ///
    (local (in-theory (disable acl2::member-of-cons member (tau-system) pseudo-termp pseudo-term-listp
                               fancy-ev fancy-ev-fncall fancy-ev-list
                               fancy-translate fancy-translate1 fancy-translate-args fancy-translate-let fancy-translate-mv-let)))
    (std::defret-mutual-generate interp-st-get-of-<fn>
      :rules ((t (:add-concl (implies (member (interp-st-field-fix key) *logically-relevant-interp-st-fields*)
                                      (equal (interp-st-get key new-interp-st)
                                             (interp-st-get key interp-st)))))
              (t (:add-keyword :hints ('(:expand (<call>)))))))

    (std::defret-mutual-generate interp-st-bfrs-ok-of-<fn>
      :rules ((t (:add-concl (implies (interp-st-bfrs-ok interp-st)
                                      (interp-st-bfrs-ok new-interp-st))))
              (t (:add-keyword :hints ('(:expand (<call>)))))))

    (std::defret-mutual-generate errmsg-of-<fn>
      :rules ((t (:add-concl (implies (interp-st->errmsg interp-st)
                                      (equal (interp-st->errmsg new-interp-st)
                                             (interp-st->errmsg interp-st)))))
              (t (:add-keyword :hints ('(:expand (<call>)))))))

    (std::defret-mutual-generate unreachable-of-<fn>
      :rules ((t (:add-concl (implies (not (equal (interp-st->errmsg interp-st) :unreachable))
                                      (not (equal (interp-st->errmsg new-interp-st) :unreachable)))))
              (t (:add-keyword :hints ('(:expand (<call>)))))))

    (std::defret-mutual-generate w-state-of-<fn>
      :rules ((t (:add-concl (equal (w new-state) (w state))))
              (t (:add-keyword :hints ('(:expand (<call>)))))))

    (local (defthm true-listp-when-symbol-listp
             (implies (symbol-listp x)
                      (true-listp x))))

    (local (defthm pseudo-fnsym-p-reqs
             (implies (and (symbolp x)
                           (not (equal x 'quote)))
                      (pseudo-fnsym-p x))
             :hints(("Goal" :in-theory (enable pseudo-fnsym-p)))))

    (local (in-theory (disable table-alist)))

    (local (Defthm doublet-listp-implies-alistp
             (implies (doublet-listp x)
                      (alistp x))))

    (local (Defthm doublet-listp-implies-all->=-len
             (implies (doublet-listp x)
                      (acl2::all->=-len x 2))
             :hints(("Goal" :induct t)
                    (and stable-under-simplificationp
                         '(:expand ((acl2::>=-len (car x) 2)
                                    (acl2::>=-len (cdar x) 1)))))))
    
    (verify-guards fancy-ev
      :hints(("Goal" :in-theory (enable acl2::member-of-cons)
              :do-not-induct t))
      :guard-debug t)

    (local (in-theory (disable pseudo-term-listp pseudo-termp)))

    (fty::deffixequiv-mutual fancy-ev)))


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
       (bindings (fancy-ev-primitive-bindings '__tmp_args__ stobjs-in formals 0))
       (call-formals (fancy-ev-primitive-formals stobjs-in formals))
       ((unless (intersectp-eq '(interp-st state) stobjs-out))
        `(b* ((__tmp_args__ ,argsvar)
              ,@bindings
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
    `(b* ((__tmp_args__ ,argsvar)
          ,@bindings
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

   (def-fancy-ev-primitives foo)

   (define test-fancy-translate (x (reclimit natp) state hard-errp aokp)
     ;; this is all just to show interp-st-bfrs-ok of create-interp-st
     :guard-hints (("goal" :in-theory (disable create-interp-st)
                    :expand ((:free (var) (aignet::nbalist-boundp var nil)))
                    :do-not '(preprocess)))
     (with-local-stobj interp-st
       (mv-let (err val interp-st state)
         (fancy-translate x reclimit interp-st state hard-errp aokp)
         (mv err val state))))
   
   ;; Test
   (make-event
    (b* ((form '(b* (((unless (and (>= (len x) 2)
                                   (doublet-listp (car x))))
                      (mv (msg "Fancy-translate error: invalid form for let: ~x0" `(let . ,x))
                          nil interp-st state))
                     (bindings (car x))
                     (vars (strip-cars bindings))
                     ((unless (acl2::arglistp vars))
                      (mv (msg "Fancy-translate error: invalid form for let (bound variables): ~x0" `(let . ,x))
                          nil interp-st state))
                     (args (acl2::strip-cadrs bindings))
                     ((mv err trans-args interp-st state)
                      ;; relying on acl2-count-of-strip-cadrs
                      (fancy-translate-args args reclimit interp-st state hard-errp aokp))
                     ((when err) (mv err nil interp-st state))
                     ;; ignoring declarations for now
                     (body (car (last x)))
                     ((mv err trans-body interp-st state)
                      (fancy-translate body reclimit interp-st state hard-errp aokp))
                     ((when err) (mv err nil interp-st state)))
                  (mv nil (acl2::make-lambda-term vars trans-args trans-body) interp-st state)))
         ((er ftr-body)
          (test-fancy-translate form 1000 state t t))
         ((er tr-body)
          (acl2::translate form t nil nil 'test (w state) state)))
      (value `(thm (equal ,ftr-body ,tr-body) :hints (("goal" :in-theory nil))))))
   ))


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
                                                (if (or (eq guard t) (eq key :errmsg))
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
                 (:cgraph-memo    . (cgraph-memo-p cgraph-memo))
                 (:cgraph-index   . (natp cgraph-index))
                 (:user-scratch   . (obj-alist-p user-scratch))
                 (:trace-scratch  . t)
                 (:trace-depth    . (natp trace-depth))
                 (:trace-alist    . (trace-alist-p trace-alist))
                 (:trace-stack    . (trace-alistlist-p trace-stack))
                 (:tracespecs     . (true-list-listp tracespecs))
                 (:errmsg         . t)
                 (:debug-info     . t)
                 (:debug-stack    . (major-stack-p debug-stack))
                 (:rewrite-rules  . (alistp rewrite-rules))
                 (:binder-rules   . (alistp binder-rules))
                 (:branch-merge-rules . (alistp branch-merge-rules))
                 (:congruence-rules . (true-listp congruence-rules))))))



;; (logic)

;; (fancy-ev-add-primitive update-interp-st->cgraph$inline (cgraph-p cgraph))

;; (def-fancy-ev-primitives foo-bar)

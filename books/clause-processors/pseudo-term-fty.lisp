; Pseudo-term-fix.lisp: Fixing function for pseudo-terms, transparent to evaluators.

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

(in-package "ACL2")

(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/fty/fty-sum-casemacro" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "ev-find-rules")
(local (include-book "std/lists/take" :dir :system))
(local (include-book "ev-ind"))
(local (std::add-default-post-define-hook :fix))

(defthm pseudo-termp-car-when-pseudo-term-listp
  (implies (pseudo-term-listp x)
           (pseudo-termp (car x)))
  :hints(("Goal" :in-theory (enable pseudo-term-listp))))

(defthm pseudo-term-listp-cdr-when-pseudo-term-listp
  (implies (pseudo-term-listp x)
           (pseudo-term-listp (cdr x)))
  :hints(("Goal" :in-theory (enable pseudo-term-listp))))

(defxdoc pseudo-term-fty
  :parents (pseudo-termp)
  :short "Overview of FTY support for pseudo-terms."
  :long "<p>The book \"clause-processors/pseudo-term-fty\" defines a fixing
function and convenient accessors and constructors for @(see
fty::fty-discipline) support for pseudo-terms.  It also provides macros that
generate appropriate theorems about evaluators allowing them to understand the
new accessors and constructors.</p>

<h3>Usage</h3>
<p>We treat the pseudo-term type as a sum of five kinds of products:</p>

<ul>
<li>@(':null'), encompassing the unique pseudo-term @('NIL') as well as
 (ill-formed) non-symbol atoms and calls with non-symbol atom function names;
has no field</li>

<li>@(':var'), encompassing non-nil symbols; field: @('name')</li>

<li>@(':quote'), conses whose car is @('quote'); field: @('val')</li>

<li>@('fncall'), conses whose car is a non-quote symbol; fields: @('fn') and @('args')</li>

<li>@('lambda'), conses whose car is a cons; fields: @('formals'), @('body'), and @('args').</li>
</ul>

<p>Each of these product kinds has a constructor that uses the typical naming
convention; e.g., to make a lambda, use @('(pseudo-term-lambda formals body
args)').  The accessors also use the usual naming convention (e.g.,
@('pseudo-term-var->name')).  There is also a @(see B*) binder for each such
constructor that allows access to the fields using dotted notation; e.g.:</p>
@({
 (b* (((pseudo-lambda x))) (list x.formals x.body x.args))
 })

<p>An alternative constructor @('(pseudo-term-call fn args)') can create either
@(':fncall') or @(':lambda') kinds; its @('fn') argument is of type @(see
pseudo-fn) which can be either a function symbol (@(see pseudo-fnsym)) or
lambda (@(see pseudo-lambda)).  The function of a @(':fncall') or
@(':lambda') object can also be accessed with @('pseudo-term-call->fn').</p>

<p>The @(':null') and @(':quote') kinds both simply have constant values.  A
function @('pseudo-term-const->val') is provided that accesses that value; that
is, it returns the value of a @(':quote') object or NIL for a @(':null')
object.  We don't provide a constructor @('pseudo-term-const') since
@('pseudo-term-quote') will do just as well.</p>

<p>The macro @(see pseudo-term-case) can be used to conveniently branch on the kind
of term and access the fields; see its documentation for examples.</p>


<h3>Evaluator support</h3>

<p>The macro @(see def-ev-pseudo-term-fty-support) admits several theorems about an evaluator, enabling reasoning about evaluation over the provided constructors and accessors.  See its documentation for details.</p>

<p>Another macro, @(see def-ev-pseudo-term-congruence), admits only a subset of the theorems produced by @(see def-ev-pseudo-term-fty-support), proving a pseudo-term-equiv congruence for the evaluator but no rules pertaining to the FTY-style accessors and updaters.</p>

")

(define remove-non-symbols (x)
  (if (atom x)
      nil
    (if (symbolp (car x))
        (cons (car x)
              (remove-non-symbols (cdr x)))
      (remove-non-symbols (cdr x))))
  ///
  (defthm symbol-listp-of-remove-non-symbols
    (symbol-listp (remove-non-symbols x)))

  (defthm remove-non-symbols-when-symbol-listp
    (implies (symbol-listp x)
             (equal (remove-non-symbols x) x))))

(define remove-corresp-non-symbols (x (y true-listp))
  (if (atom x)
      nil
    (if (symbolp (car x))
        (cons (car y)
              (remove-corresp-non-symbols (cdr x) (cdr y)))
      (remove-corresp-non-symbols (cdr x) (cdr y))))
  ///

  (defthm pseudo-term-listp-of-remove-corresp-non-symbols
    (implies (pseudo-term-listp y)
             (pseudo-term-listp (remove-corresp-non-symbols x y))))

  (defthm len-of-remove-corresp-non-symbols
    (equal (len (remove-corresp-non-symbols x y))
           (len (remove-non-symbols x)))
    :hints(("Goal" :in-theory (enable remove-non-symbols))))

  (defthm remove-corresp-non-symbols-when-symbol-listp
    (implies (symbol-listp x)
             (equal (remove-corresp-non-symbols x y)
                    (take (len x) y))))

  (defthm lookup-in-remove-non-symbols-alist
    (implies (symbolp x)
             (equal (assoc x (pairlis$ (remove-non-symbols formals)
                                       (remove-corresp-non-symbols formals actuals)))
                    (assoc x (pairlis$ formals actuals))))
    :hints(("Goal" :in-theory (enable remove-non-symbols)))))

(defines pseudo-term-fix
  (define pseudo-term-fix ((x pseudo-termp))
    :parents (pseudo-term-fty)
    :short "Fixing function for pseudo-terms that supports FTY-style discipline
            and is transparent to evaluators."
    :verify-guards nil
    :measure (acl2-count x)
    :returns (new-x pseudo-termp)
    :inline t
    (mbe :logic
         (cond ((atom x)
                (and (symbolp x) x))
               ((eq (car x) 'quote) (list 'quote (cadr x)))
               ((symbolp (car x))
                (cons (car x) (pseudo-term-list-fix (cdr x))))
               ((atom (car x)) nil)
               (t (let* ((body (pseudo-term-fix (third (car x))))
                         (formals1 (cadr (car x)))
                         (actuals1 (pseudo-term-list-fix (cdr x)))
                         (formals (remove-non-symbols formals1))
                         (actuals (remove-corresp-non-symbols formals1 actuals1)))
                    (cons (list 'lambda formals body) actuals))))
         :exec x))

  (define pseudo-term-list-fix ((x pseudo-term-listp))
    :parents (pseudo-term-fty)
    :short "Fixing function for pseudo-term lists that supports FTY-style discipline
            and is transparent to evaluators."
    :measure (acl2-count x)
    :returns (new-x pseudo-term-listp)
    :inline t
    (mbe :logic (if (atom x)
                    nil
                  (cons (pseudo-term-fix (car x))
                        (pseudo-term-list-fix (cdr x))))
         :exec x))

  :flag-local nil
  ///

  (local (in-theory (disable pseudo-term-fix
                             pseudo-term-list-fix)))



  (local (defthm equal-plus-const
           (implies (and (syntaxp (and (quotep a) (quotep b)))
                         (acl2-numberp b))
                    (equal (equal (+ a c) b)
                           (equal (fix c) (- b a))))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0)
                  (not (consp x)))))

  (defthm-pseudo-term-fix-flag
    (defthm pseudo-term-fix-when-pseudo-termp
      (implies (pseudo-termp x)
               (equal (pseudo-term-fix x) x))
      :hints ('(:expand ((pseudo-term-fix x))))
      :flag pseudo-term-fix)
    (defthm pseudo-term-list-fix-when-pseudo-term-listp
      (implies (pseudo-term-listp x)
               (equal (pseudo-term-list-fix x) x))
      :hints ('(:expand ((pseudo-term-list-fix x))))
      :flag pseudo-term-list-fix))

  (defthm len-of-pseudo-term-list-fix
    (equal (len (pseudo-term-list-fix x))
           (len x))
    :hints (("Goal" :induct (len x)
             :in-theory (enable len)
             :expand ((pseudo-term-list-fix x)))))

  (defthm consp-of-pseudo-term-list-fix
    (equal (consp (pseudo-term-list-fix x))
           (consp x))
    :hints (("goal" :expand ((pseudo-term-list-fix x)))))

  (verify-guards pseudo-term-fix$inline)

  (fty::deffixtype pseudo-term
    :pred pseudo-termp
    :fix pseudo-term-fix
    :equiv pseudo-term-equiv
    :define t :forward t)

  (fty::deffixtype pseudo-term-list
    :pred pseudo-term-listp
    :fix pseudo-term-list-fix
    :equiv pseudo-term-list-equiv
    :define t :forward t)

  (fty::deffixcong pseudo-term-list-equiv
    pseudo-term-list-equiv
    (remove-corresp-non-symbols formals args) args
    :hints(("Goal" :in-theory (enable remove-corresp-non-symbols
                                      pseudo-term-list-fix))))

  (fty::deffixcong pseudo-term-list-equiv
    pseudo-term-list-equiv (cons x y) y
    :hints(("Goal" :in-theory (enable pseudo-term-list-fix))))

  (fty::deffixcong pseudo-term-equiv
    pseudo-term-list-equiv (cons x y) x
    :hints(("Goal" :in-theory (enable pseudo-term-list-fix))))

  (defthm car-of-pseudo-term-list-fix
    (equal (car (pseudo-term-list-fix x))
           (pseudo-term-fix (car x)))
    :hints(("Goal" :expand ((pseudo-term-list-fix x)))))

  (defthm cdr-of-pseudo-term-list-fix
    (equal (cdr (pseudo-term-list-fix x))
           (pseudo-term-list-fix (cdr x)))
    :hints(("Goal" :expand ((pseudo-term-list-fix x)))))

  (defthm pseudo-term-list-fix-of-cons
    (equal (pseudo-term-list-fix (cons a b))
           (cons (pseudo-term-fix a)
                 (pseudo-term-list-fix b)))
    :hints(("Goal" :expand ((pseudo-term-list-fix (cons a b)))))))



(defevaluator base-ev base-ev-list () :namedp t)

(local (def-ev-ind base-ev base-ev-list))


(local
 (defthm-base-ev-flag
   (defthm base-ev-of-remove-non-symbols
     (equal (base-ev x (pairlis$ (remove-non-symbols formals)
                                 (remove-corresp-non-symbols formals actuals)))
            (base-ev x (pairlis$ formals actuals)))
     :hints('(:in-theory (enable base-ev-of-nonsymbol-atom
                                 base-ev-of-bad-fncall
                                 base-ev-of-fncall-args)))
     :flag base-ev)
   (defthm base-ev-list-of-remove-non-symbols
     (equal (base-ev-list x (pairlis$ (remove-non-symbols formals)
                                      (remove-corresp-non-symbols formals actuals)))
            (base-ev-list x (pairlis$ formals actuals)))
     :flag base-ev-list)))

(local
 (defthm base-ev-lst-of-remove-corresp-non-symbols
   (equal (base-ev-list (remove-corresp-non-symbols x y) a)
          (remove-corresp-non-symbols x (base-ev-list y a)))
   :hints(("Goal" :in-theory (enable remove-corresp-non-symbols)))))


(defthm-base-ev-flag
  (defthm base-ev-of-pseudo-term-fix
    (equal (base-ev (pseudo-term-fix x) a)
           (base-ev x a))
    :hints('(:in-theory (enable base-ev-of-nonsymbol-atom
                                base-ev-of-bad-fncall
                                base-ev-of-fncall-args)
             :expand ((pseudo-term-fix x))))
    :flag base-ev)
  (defthm base-ev-list-of-pseudo-term-list-fix
    (equal (base-ev-list (pseudo-term-list-fix x) a)
           (base-ev-list x a))
    :hints ('(:expand ((pseudo-term-list-fix x))))
    :flag base-ev-list))

(defthm base-ev-list-of-kwote-lst
  (equal (base-ev-list (kwote-lst x) a)
         (true-list-fix x)))


(defxdoc def-ev-pseudo-term-congruence
  :parents (pseudo-term-fty)
  :short "Prove that @(see pseudo-term-fix) is transparent to an evaluator and
          that the evaluator thus has a @('pseudo-term-equiv') congruence on its
          first argument."
  :long "<p>See also @(see def-ev-pseudo-term-fty-support), which you may which
to use instead since this macro only provides a subset of the theorems
introduced by it.</p>")

(defmacro def-ev-pseudo-term-congruence (ev ev-list)
  `(progn
     (fty::deffixcong pseudo-term-equiv equal (,ev x a) x
       :hints (("goal" :use ((:functional-instance base-ev-of-pseudo-term-fix
                              (base-ev ,ev)
                              (base-ev-list ,ev-list))))))
     (fty::deffixcong pseudo-term-list-equiv equal (,ev-list x a) x
       :hints (("goal" :use ((:functional-instance base-ev-list-of-pseudo-term-list-fix
                              (base-ev ,ev)
                              (base-ev-list ,ev-list))))))))

(local (defevaluator foo-ev foo-ev-list ((if a b c) (equal x y)) :namedp t))
(local (in-theory (enable foo-ev-of-nonsymbol-atom
                          foo-ev-of-fncall-args
                          foo-ev-of-bad-fncall)))
(local (def-ev-pseudo-term-congruence foo-ev foo-ev-list))


(define pseudo-term-kind ((x pseudo-termp))
  :parents (pseudo-term-fty)
  :short "Return the kind of a pseudo-term input (a keyword symbol)."
  :inline t
  :returns (kind symbolp :rule-classes :type-prescription)
  (b* ((x (pseudo-term-fix x))
       ((when (atom x)) (if x :var :null))
       (fn (car x))
       ((when (eq fn 'quote)) :quote)
       ((when (consp fn)) :lambda))
    :fncall)
  ///
  (defthm pseudo-term-kind-possibilities
    (or (equal (pseudo-term-kind x) :null)
        (equal (pseudo-term-kind x) :var)
        (equal (pseudo-term-kind x) :quote)
        (equal (pseudo-term-kind x) :lambda)
        (equal (pseudo-term-kind x) :fncall))
    :rule-classes ((:forward-chaining :trigger-terms ((pseudo-term-kind x))))))


(defxdoc pseudo-var
  :parents (pseudo-term-fty)
  :short "Type of a variable symbol used in the FTY support for pseudo-terms.")

(define pseudo-var-p (x)
  :parents (pseudo-var)
  (and x (symbolp x))
  ///
  (defthm pseudo-var-p-compound-recognizer
    (equal (pseudo-var-p x)
           (and x (symbolp x)))
    :rule-classes :compound-recognizer))

(define pseudo-var-fix ((x pseudo-var-p))
  :parents (pseudo-var)
  :returns (new-x pseudo-var-p :rule-classes :type-prescription)
  (mbe :logic (if (pseudo-var-p x) x 'x)
       :exec x)
  ///
  (defthm pseudo-var-fix-when-pseudo-var-p
    (implies (pseudo-var-p x)
             (equal (pseudo-var-fix x) x)))

  (fty::deffixtype pseudo-var :pred pseudo-var-p :fix pseudo-var-fix :equiv pseudo-var-equiv :define t))

(defxdoc pseudo-fnsym
  :parents (pseudo-term-fty)
  :short "Type of a function symbol used in the FTY support for pseudo-terms.")

(define pseudo-fnsym-p (x)
  :parents (pseudo-fnsym)
  (and (symbolp x) (not (eq x 'quote)))
  ///
  (defthm pseudo-fnsym-p-compound-recognizer
    (implies (pseudo-fnsym-p x)
             (symbolp x))
    :rule-classes :compound-recognizer))

(define pseudo-fnsym-fix ((x pseudo-fnsym-p))
  :parents (pseudo-fnsym)
  :returns (new-x pseudo-fnsym-p :rule-classes (:rewrite (:type-prescription :typed-term new-x)))
  (mbe :logic (and (pseudo-fnsym-p x) x)
       :exec x)
  ///
  (defthm pseudo-fnsym-fix-when-pseudo-fnsym-p
    (implies (pseudo-fnsym-p x)
             (equal (pseudo-fnsym-fix x) x)))

  (fty::deffixtype pseudo-fnsym :pred pseudo-fnsym-p :fix pseudo-fnsym-fix :equiv pseudo-fnsym-equiv :define t)

  (defthm not-quote-of-pseudo-fnsym-fix
    (not (equal (pseudo-fnsym-fix x) 'quote))))

(define pseudo-lambda-p (x)
  :parents (pseudo-lambda)
  (and (true-listp x)
       (eql (len x) 3)
       (eq (car x) 'lambda)
       (symbol-listp (cadr x))
       (pseudo-termp (caddr x)))
  ///
  (defthm pseudo-lambda-p-compound-recognizer
    (implies (pseudo-lambda-p x)
             (and (consp x) (true-listp x)))
    :rule-classes :compound-recognizer))

(define pseudo-lambda-fix ((x pseudo-lambda-p))
  :parents (pseudo-lambda)
  :returns (lambda pseudo-lambda-p :rule-classes (:rewrite (:type-prescription :typed-term lambda)))
  :prepwork ((local (in-theory (enable pseudo-lambda-p))))
  (mbe :logic (b* ((formals (cadr x))
                   (body (caddr x)))
                (list 'lambda
                      (remove-non-symbols formals)
                      (pseudo-term-fix body)))
       :exec x)
  ///
  (local (defthm simplify-+
           (implies (and (syntaxp (and (quotep a) (quotep c)))
                         (acl2-numberp c))
                    (equal (equal (+ a b) c)
                           (equal (fix b) (- c a))))))

  (local (defthm len-equal-0
           (equal (equal (len x) 0) (atom x))))

  (defthm pseudo-lambda-fix-when-pseudo-lambda-p
    (implies (pseudo-lambda-p x)
             (equal (pseudo-lambda-fix x) x)))

  (fty::deffixtype pseudo-lambda :pred pseudo-lambda-p :fix pseudo-lambda-fix :equiv pseudo-lambda-equiv :define t))

(define pseudo-lambda->formals ((x pseudo-lambda-p))
  :parents (pseudo-lambda)
  :returns (formals symbol-listp)
  :guard-hints (("goal" :in-theory (enable pseudo-lambda-p)))
  :hooks ((:fix :hints(("Goal" :in-theory (enable pseudo-lambda-fix)))))
  (mbe :logic (remove-non-symbols (cadr x))
       :exec (cadr x)))

(define pseudo-lambda->body ((x pseudo-lambda-p))
  :parents (pseudo-lambda)
  :returns (body pseudo-termp)
  :guard-hints (("goal" :in-theory (enable pseudo-lambda-p)))
  :hooks ((:fix :hints(("Goal" :in-theory (enable pseudo-lambda-fix)))))
  (mbe :logic (pseudo-term-fix (caddr x))
       :exec (caddr x)))

(define pseudo-lambda ((formals symbol-listp)
                       (body pseudo-termp))
  :parents (pseudo-term-fty)
  :short "Type of, and constructor for, a lambda function, used in the FTY support for pseudo-terms."
  :returns (lambda pseudo-lambda-p
             :hints(("Goal" :in-theory (enable pseudo-lambda-p)))
             :rule-classes (:rewrite (:type-prescription :typed-term lambda)))
  (mbe :logic (list 'lambda
                    (remove-non-symbols formals)
                    (pseudo-term-fix body))
       :exec (list 'lambda formals body))
  ///
  (defthm pseudo-lambda->formals-of-pseudo-lambda
    (equal (pseudo-lambda->formals (pseudo-lambda formals body))
           (remove-non-symbols formals))
    :hints(("Goal" :in-theory (enable pseudo-lambda->formals))))

  (defthm pseudo-lambda->body-of-pseudo-lambda
    (equal (pseudo-lambda->body (pseudo-lambda body body))
           (pseudo-term-fix body))
    :hints(("Goal" :in-theory (enable pseudo-lambda->body))))

  (defthm pseudo-lambda-of-accessors
    (equal (pseudo-lambda (pseudo-lambda->formals x)
                          (pseudo-lambda->body x))
           (pseudo-lambda-fix x))
    :hints(("Goal" :in-theory (enable pseudo-lambda->formals
                                      pseudo-lambda->body
                                      pseudo-lambda-fix))))

  (def-b*-binder pseudo-lambda
    :body
    (std::da-patbind-fn 'pseudo-lambda
                        '((formals . pseudo-lambda->formals)
                          (body . pseudo-lambda->body))
                        args forms rest-expr)))


(defxdoc pseudo-fn
  :parents (pseudo-term-fty)
  :short "Type of a function (either symbol or lambda), used in pseudo-term FTY support.")

(define pseudo-fn-p (x)
  :parents (pseudo-fn)
  :prepwork ((local (in-theory (enable pseudo-lambda-p pseudo-fnsym-p))))
  (if (consp x)
      (pseudo-lambda-p x)
    (pseudo-fnsym-p x))
  ///
  (defthm pseudo-fn-p-when-consp
    (implies (and (pseudo-fn-p x)
                  (consp x))
             (pseudo-lambda-p x)))

  (defthm pseudo-fn-p-when-not-consp
    (implies (and (pseudo-fn-p x)
                  (not (consp x)))
             (pseudo-fnsym-p x)))

  (defthm pseudo-fn-p-when-lambda
    (implies (pseudo-lambda-p x)
             (pseudo-fn-p x)))

  (defthm pseudo-fn-p-when-fnsym
    (implies (pseudo-fnsym-p x)
             (pseudo-fn-p x))))

(define pseudo-fn-fix ((x pseudo-fn-p))
  :parents (pseudo-fn)
  :returns (new-x pseudo-fn-p)
  :prepwork ((local (in-theory (enable pseudo-fn-p))))
  (mbe :logic (if (consp x)
                  (pseudo-lambda-fix x)
                (pseudo-fnsym-fix x))
       :exec x)
  ///
  (defthm pseudo-fn-fix-when-pseudo-fn-p
    (implies (pseudo-fn-p x)
             (equal (pseudo-fn-fix x) x)))

  (defthm pseudo-fn-fix-when-consp
    (implies (consp x)
             (equal (pseudo-fn-fix x)
                    (pseudo-lambda-fix x))))

  (defthm pseudo-fn-fix-when-not-consp
    (implies (not (consp x))
             (equal (pseudo-fn-fix x)
                    (pseudo-fnsym-fix x))))

  (fty::deffixtype pseudo-fn :pred pseudo-fn-p :fix pseudo-fn-fix :equiv pseudo-fn-equiv :define t))



(define pseudo-term-null ()
  :parents (pseudo-term-fty)
  :short "Constructor for null pseudo-terms.  Just returns NIL."
  :returns (term pseudo-termp)
  nil
  ///
  (defthm kind-of-pseudo-term-null
    (equal (pseudo-term-kind (pseudo-term-null)) :null))

  (defthm base-ev-of-pseudo-term-null
    (equal (base-ev (pseudo-term-null) a) nil))

  (defthm base-ev-when-pseudo-term-null
    (implies (equal (pseudo-term-kind x) :null)
             (equal (base-ev x a) nil))
    :hints (("goal" :use ((:instance base-ev-of-pseudo-term-fix))
             :in-theory (e/d (pseudo-term-kind)
                             (base-ev-of-pseudo-term-fix)))))

  (defthmd pseudo-term-fix-when-pseudo-term-null
    (implies (equal (pseudo-term-kind x) :null)
             (equal (pseudo-term-fix x)
                    (pseudo-term-null)))
    :hints(("Goal" :in-theory (enable pseudo-term-fix pseudo-term-kind))))

  ;; useless
  (def-b*-binder pseudo-term-null
    :body
    (std::da-patbind-fn 'pseudo-term-null
                        nil
                        args forms rest-expr)))


(define pseudo-term-quote->val ((x pseudo-termp))
  :parents (pseudo-term-quote)
  :short "Accessor for the value of quote pseudo-terms."
  :guard (eq (pseudo-term-kind x) :quote)
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind)))
  (cadr (pseudo-term-fix x))
  ///
  (defthm base-ev-when-pseudo-term-quote
    (implies (equal (pseudo-term-kind x) :quote)
             (equal (base-ev x a)
                    (pseudo-term-quote->val x)))
    :hints (("goal" :use ((:instance base-ev-of-pseudo-term-fix))
             :in-theory (e/d (pseudo-term-kind)
                             (base-ev-of-pseudo-term-fix))))))


(define pseudo-term-quote (val)
  :parents (pseudo-term-fty)
  :short "Constructor for :quote psuedo-terms."
  :returns (term pseudo-termp)
  :prepwork ((local (in-theory (enable pseudo-term-kind
                                       pseudo-term-quote->val
                                       pseudo-termp))))
  (list 'quote val)
  ///
  (defthm kind-of-pseudo-term-quote
    (equal (pseudo-term-kind (pseudo-term-quote val)) :quote))

  (defthm pseudo-term-quote->val-of-pseudo-term-quote
    (equal (pseudo-term-quote->val (pseudo-term-quote val)) val))

  (defthm pseudo-term-quote-of-accessors
    (implies (equal (pseudo-term-kind x) :quote)
             (equal (pseudo-term-quote (pseudo-term-quote->val x))
                    (pseudo-term-fix x)))
    :hints(("Goal" :in-theory (enable pseudo-term-kind pseudo-term-quote->val)
            :expand ((pseudo-term-fix x)))))

  (defthm base-ev-of-pseudo-term-quote
    (equal (base-ev (pseudo-term-quote val) a) val))

  (def-b*-binder pseudo-term-quote
    :body
    (std::da-patbind-fn 'pseudo-term-quote
                        '((val . pseudo-term-quote->val))
                        args forms rest-expr)))

(define pseudo-term-var->name ((x pseudo-termp))
  :parents (pseudo-term-var)
  :short "Accessor for the name of pseudo-term variables."
  :guard (eq (pseudo-term-kind x) :var)
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind)))
  :returns (name pseudo-var-p :rule-classes :type-prescription)
  :hooks ((:fix :hints(("Goal" :expand ((pseudo-term-fix x))
                        :in-theory (enable pseudo-term-kind)))))
  (mbe :logic (pseudo-var-fix (and (eq (pseudo-term-kind x) :var) x))
       :exec x)
  ///
  (defthm base-ev-when-pseudo-term-var
    (implies (equal (pseudo-term-kind x) :var)
             (equal (base-ev x a)
                    (cdr (assoc (pseudo-term-var->name x) a))))
    :hints (("goal" :expand ((pseudo-term-fix x))
             :in-theory (enable pseudo-var-p pseudo-term-kind)))))

(define pseudo-term-var ((name pseudo-var-p))
  :parents (pseudo-term-fty)
  :short "Constructor for variable (@(':var')) pseudo-terms."
  :returns (term pseudo-termp)
  :prepwork ((local (in-theory (enable pseudo-term-kind
                                       pseudo-term-var->name
                                       pseudo-termp))))
  (pseudo-var-fix name)
  ///

  (defthm kind-of-pseudo-term-var
    (equal (pseudo-term-kind (pseudo-term-var name)) :var))

  (defthm pseudo-term-var->name-of-pseudo-term-var
    (equal (pseudo-term-var->name (pseudo-term-var name))
           (pseudo-var-fix name)))

  (defthm pseudo-term-var-of-accessors
    (implies (equal (pseudo-term-kind x) :var)
             (equal (pseudo-term-var (pseudo-term-var->name x))
                    (pseudo-term-fix x)))
    :hints(("Goal" :in-theory (enable pseudo-term-kind pseudo-term-var->name)
            :expand ((pseudo-term-fix x)))))

  (defthm base-ev-of-pseudo-term-var
    (equal (base-ev (pseudo-term-var name) a)
           (cdr (assoc (pseudo-var-fix name) a))))

  (def-b*-binder pseudo-term-var
    :body
    (std::da-patbind-fn 'pseudo-term-var
                        '((name . pseudo-term-var->name))
                        args forms rest-expr)))




(define pseudo-term-call->args ((x pseudo-termp))
  :parents (pseudo-term-call
            pseudo-term-fncall
            pseudo-term-lambda)
  :short "Accessor for the arguments of a lambda or function call pseudo-term."
  :guard (member-eq (pseudo-term-kind x) '(:fncall :lambda))
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind)))
  :returns (args pseudo-term-listp
                 :hints(("Goal" :in-theory (enable pseudo-term-kind)
                         :expand ((pseudo-term-fix x)))))
  (mbe :logic (and (or (eq (pseudo-term-kind x) :lambda)
                       (eq (pseudo-term-kind x) :fncall))
                   (cdr (pseudo-term-fix x)))
       :exec (cdr x))
  ///
  (defthm acl2-count-of-pseudo-term-call->args
    (implies (or (equal (pseudo-term-kind x) :lambda)
                 (equal (pseudo-term-kind x) :fncall))
             (< (acl2-count (pseudo-term-call->args x)) (acl2-count (pseudo-term-fix x))))
    :hints(("Goal" :in-theory (enable pseudo-term-kind)))
    :rule-classes ((:linear :trigger-terms ((acl2-count (pseudo-term-call->args x)))))))

(defxdoc pseudo-term-fncall->args
  :parents (pseudo-term-fncall)
  :short "Alias for @(see pseudo-term-call->args).")

(defxdoc pseudo-term-lambda->args
  :parents (pseudo-term-lambda)
  :short "Alias for @(see pseudo-term-call->args).")

(defmacro pseudo-term-fncall->args (x) `(pseudo-term-call->args ,x))
(defmacro pseudo-term-lambda->args (x) `(pseudo-term-call->args ,x))
(add-macro-alias pseudo-term-fncall->args pseudo-term-call->args)
(add-macro-alias pseudo-term-lambda->args pseudo-term-call->args)

(define pseudo-term-fncall->fn ((x pseudo-termp))
  :parents (pseudo-term-fncall)
  :short "Access the function symbol of a function call pseudo-term."
  :guard (eq (pseudo-term-kind x) :fncall)
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind)))
  :returns (fn pseudo-fnsym-p
               :hints(("Goal" :in-theory (enable pseudo-term-kind
                                                 pseudo-fnsym-p)
                       :expand ((pseudo-term-fix x)))))
  (mbe :logic (and (eq (pseudo-term-kind x) :fncall)
                   (car (pseudo-term-fix x)))
       :exec (car x))
  ///
  (defthm symbolp-of-pseudo-term-fncall->fn
    (symbolp (pseudo-term-fncall->fn x))
    :rule-classes :type-prescription)

  (defthm not-quote-of-pseudo-term-fncall->fn
    (not (equal (pseudo-term-fncall->fn x) 'quote))))

(define pseudo-term-fncall ((fn pseudo-fnsym-p)
                            (args pseudo-term-listp))
  :parents (pseudo-term-fty)
  :short "Constructor for function call (@(':fncall')) pseudo-terms."
  :returns (term pseudo-termp)
  (cons (pseudo-fnsym-fix fn)
        (pseudo-term-list-fix args))
  ///

  (defthm kind-of-pseudo-term-fncall
    (equal (pseudo-term-kind (pseudo-term-fncall fn args)) :fncall)
    :hints(("Goal" :in-theory (enable pseudo-term-kind)
            :expand ((:free (a b) (pseudo-term-fix (cons a b)))))))

  (defthm pseudo-term-call->args-of-pseudo-term-fncall
    (equal (pseudo-term-call->args (pseudo-term-fncall fn args))
           (pseudo-term-list-fix args))
    :hints(("Goal" :in-theory (enable pseudo-term-call->args pseudo-term-kind)
            :expand ((:free (a b) (pseudo-term-fix (cons a b)))))))

  (defthm pseudo-term-fncall->fn-of-pseudo-term-fncall
    (equal (pseudo-term-fncall->fn (pseudo-term-fncall fn args))
           (pseudo-fnsym-fix fn))
    :hints(("Goal" :in-theory (enable pseudo-term-fncall->fn
                                      pseudo-term-kind)
            :expand ((:free (a b) (pseudo-term-fix (cons a b)))))))

  ;; this is kind of a yucky way to do it but it will work without having to
  ;; prove a whole new list of theorems for each evaluator
  (defthm base-ev-of-pseudo-term-fncall
    (equal (base-ev (pseudo-term-fncall fn args) a)
           (base-ev (cons (pseudo-fnsym-fix fn) args) a))
    :hints(("Goal" :in-theory (enable base-ev-of-fncall-args))))

  (defthm base-ev-when-pseudo-term-fncall
    (implies (and (equal (pseudo-term-kind x) :fncall)
                  (equal new-x (cons (pseudo-term-fncall->fn x)
                                   (pseudo-term-call->args x)))
                  (syntaxp (not (equal new-x x))))
             (equal (base-ev x a)
                    (base-ev new-x a)))
    :hints (("goal" :use ((:instance base-ev-of-pseudo-term-fix))
             :in-theory (e/d (pseudo-term-kind
                              pseudo-term-fncall->fn
                              pseudo-term-call->args)
                             (base-ev-of-pseudo-term-fix)))))

  (defthm pseudo-term-fncall-of-accessors
    (implies (equal (pseudo-term-kind x) :fncall)
             (equal (pseudo-term-fncall (pseudo-term-fncall->fn x)
                                        (pseudo-term-call->args x))
                    (pseudo-term-fix x)))
    :hints(("Goal" :in-theory (enable pseudo-term-kind
                                      pseudo-term-fncall->fn
                                      pseudo-term-call->args
                                      pseudo-fnsym-p)
            :expand ((pseudo-term-fix x)))))

  (def-b*-binder pseudo-term-fncall
    :body
    (std::da-patbind-fn 'pseudo-term-fncall
                        '((fn . pseudo-term-fncall->fn)
                          (args . pseudo-term-call->args))
                        args forms rest-expr)))


(define pseudo-term-lambda->fn ((x pseudo-termp))
  :parents (pseudo-term-lambda)
  :short "Accessor for the function of a lambda call pseudo-term."
  :guard (eq (pseudo-term-kind x) :lambda)
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind pseudo-lambda-fix)))
  :returns (fn pseudo-lambda-p
               :hints(("Goal" :in-theory (enable pseudo-term-kind)
                       :expand ((pseudo-term-fix x)))))
  :hooks ((:fix :hints(("Goal" :in-theory (enable pseudo-lambda-fix pseudo-term-fix pseudo-term-kind)))))
  (mbe :logic (pseudo-lambda-fix (and (eq (pseudo-term-kind x) :lambda)
                                      (car x)))
       :exec (car x)))

(define pseudo-term-call->fn ((x pseudo-termp))
  :parents (pseudo-term-call
            pseudo-term-fncall
            pseudo-term-lambda)
  :short "Accessor for the function of a function call or lambda call pseduo-term."
  :guard (member-eq (pseudo-term-kind x) '(:fncall :lambda))
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind)))
  :returns (fn pseudo-fn-p
               :hints(("Goal" :in-theory (enable pseudo-term-kind
                                                 pseudo-fnsym-p
                                                 pseudo-lambda-p)
                       :expand ((pseudo-term-fix x)))))
  (mbe :logic (and (or (eq (pseudo-term-kind x) :lambda)
                       (eq (pseudo-term-kind x) :fncall))
                   (car (pseudo-term-fix x)))
       :exec (car x))
  ///

  (defthm not-quote-of-pseudo-term-call->fn
    (not (equal (pseudo-term-call->fn x) 'quote)))

  (defthm pseudo-term-call->fn-when-lambda
    (implies (eq (pseudo-term-kind x) :lambda)
             (equal (pseudo-term-call->fn x)
                    (pseudo-term-lambda->fn x)))
    :hints(("Goal" :in-theory (enable pseudo-term-fix
                                      pseudo-lambda-fix
                                      pseudo-term-lambda->fn
                                      pseudo-term-kind))))

  (defthm pseudo-term-call->fn-when-fncall
    (implies (eq (pseudo-term-kind x) :fncall)
             (equal (pseudo-term-call->fn x)
                    (pseudo-term-fncall->fn x)))
    :hints(("Goal" :in-theory (enable pseudo-term-fix
                                      pseudo-term-fncall->fn
                                      pseudo-term-kind)))))


(define pseudo-term-lambda->formals ((x pseudo-termp))
  :parents (pseudo-term-lambda)
  :short "Accessor for the lambda formals of a lambda call pseudo-term."
  :guard (eq (pseudo-term-kind x) :lambda)
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind
                                           pseudo-lambda->formals
                                           pseudo-term-lambda->fn
                                           pseudo-lambda-fix)))
  :returns (formals symbol-listp :rule-classes (:rewrite :type-prescription))
  :hooks ((:fix :hints(("Goal" :in-theory (enable pseudo-term-fix)))))
  (mbe :logic (and (eq (pseudo-term-kind x) :lambda)
                   (remove-non-symbols (cadr (car x))))
       :exec (cadr (car x)))
  ///

  (defthm len-of-pseudo-term-lambda->formals
    (implies (equal (pseudo-term-kind x) :lambda)
             (equal (len (pseudo-term-lambda->formals x))
                    (len (pseudo-term-call->args x))))
    :hints(("Goal" :in-theory (enable pseudo-term-kind
                                      pseudo-term-lambda->fn
                                      pseudo-lambda->formals
                                      pseudo-lambda-fix
                                      pseudo-term-call->args)
            :expand ((pseudo-term-fix x)))))

  (defthm pseudo-lambda->formals-of-pseudo-term-lambda->fn
    (equal (pseudo-lambda->formals (pseudo-term-lambda->fn x))
           (pseudo-term-lambda->formals x))
    :hints(("Goal" :in-theory (enable pseudo-lambda->formals
                                      pseudo-term-lambda->fn
                                      pseudo-lambda-fix
                                      pseudo-term-kind
                                      pseudo-term-fix)))))

(define pseudo-term-lambda->body ((x pseudo-termp))
  :parents (pseudo-term-lambda)
  :short "Accessor for the lambda body of a lambda call pseudo-term."
  :guard (eq (pseudo-term-kind x) :lambda)
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind
                                           pseudo-lambda->body
                                           pseudo-term-lambda->fn
                                           pseudo-lambda-fix)))
  :returns (body pseudo-termp
               :hints(("Goal" :in-theory (enable pseudo-term-kind)
                       :expand ((pseudo-term-fix x)))))
  :hooks ((:fix :hints(("Goal" :in-theory (enable pseudo-term-fix)))))
  (mbe :logic (and (eq (pseudo-term-kind x) :lambda)
                   (pseudo-term-fix (caddr (car x))))
       :exec (caddr (car x)))
  ///

  (defthm pseudo-lambda->body-of-pseudo-term-lambda->fn
    (equal (pseudo-lambda->body (pseudo-term-lambda->fn x))
           (pseudo-term-lambda->body x))
    :hints(("Goal" :in-theory (enable pseudo-lambda->body
                                      pseudo-term-lambda->fn
                                      pseudo-lambda-fix
                                      pseudo-term-kind
                                      pseudo-term-fix))))

  (defthm acl2-count-of-pseudo-term-lambda->body
    (implies (equal (pseudo-term-kind x) :lambda)
             (< (acl2-count (pseudo-term-lambda->body x))
                (acl2-count (pseudo-term-fix x))))
    :hints(("Goal" :in-theory (enable pseudo-term-kind)
            :expand ((pseudo-term-fix x))))
    :rule-classes ((:linear :trigger-terms ((acl2-count (pseudo-term-lambda->body x)))))))


(define pseudo-term-lambda ((formals symbol-listp)
                            (body pseudo-termp)
                            (args pseudo-term-listp))
  :parents (pseudo-term-fty)
  :short "Constructor for a lambda call (@(':lambda')) pseudo-term."
  :guard (equal (len args) (len formals))
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind
                                           pseudo-lambda)))
  :returns (term pseudo-termp
                 :hints(("Goal" :in-theory (enable pseudo-lambda))))
  (mbe :logic (cons (pseudo-lambda formals body)
                    (remove-corresp-non-symbols formals (pseudo-term-list-fix args)))
       :exec (cons (list 'lambda formals body) args))
  ///

  (defthm kind-of-pseudo-term-lambda
    (equal (pseudo-term-kind (pseudo-term-lambda formals body args)) :lambda)
    :hints(("Goal" :in-theory (enable pseudo-term-kind)
            :expand ((:free (a b) (pseudo-term-fix (cons a b)))))))

  (local (defthm kind-when-consp-car
           (implies (consp (car x))
                    (equal (pseudo-term-kind x) :lambda))
           :hints(("Goal" :in-theory (enable pseudo-term-kind)
                   :expand ((pseudo-term-fix x))))))

  (defthm pseudo-term-lambda->fn-of-pseudo-term-lambda
    (equal (pseudo-term-lambda->fn (pseudo-term-lambda formals body args))
           (pseudo-lambda formals body))
    :hints(("Goal" :in-theory (enable pseudo-term-lambda->fn))))

  ;; (defthm pseudo-term-call->fn-of-pseudo-term-lambda
  ;;   (equal (pseudo-term-call->fn (pseudo-term-lambda formals body args))
  ;;          (pseudo-lambda formals body))
  ;;   :hints(("Goal" :in-theory (disable pseudo-term-lambda))))

  (defthm pseudo-term-call->args-of-pseudo-term-lambda
    (equal (pseudo-term-call->args (pseudo-term-lambda formals body args))
           (remove-corresp-non-symbols formals (pseudo-term-list-fix args)))
    :hints(("Goal" :in-theory (enable pseudo-term-call->args
                                      pseudo-lambda)
            :expand ((:free (a b) (pseudo-term-fix (cons a b)))))))

  (defthm pseudo-term-lambda->formals-of-pseudo-term-lambda
    (equal (pseudo-term-lambda->formals (pseudo-term-lambda formals body args))
           (remove-non-symbols formals))
    :hints(("Goal" :in-theory (enable pseudo-term-lambda->formals
                                      pseudo-lambda)
            :expand ((:free (a b) (pseudo-term-fix (cons a b)))))))

  (defthm pseudo-term-lambda->body-of-pseudo-term-lambda
    (equal (pseudo-term-lambda->body (pseudo-term-lambda formals body args))
           (pseudo-term-fix body))
    :hints(("Goal" :in-theory (enable pseudo-term-lambda->body
                                      pseudo-lambda)
            :expand ((:free (a b) (pseudo-term-fix (cons a b)))))))

  (defthm base-ev-of-pseudo-term-lambda
    (equal (base-ev (pseudo-term-lambda formals body args) a)
           (base-ev body (pairlis$ formals (base-ev-list args a))))
    :hints(("Goal" :in-theory (enable base-ev-of-lambda
                                      pseudo-lambda))))

  (local (defthm consp-car-fix-when-kind-lambda
           (iff (equal (pseudo-term-kind x) :lambda)
                (consp (car (pseudo-term-fix x))))
           :hints(("Goal" :in-theory (enable pseudo-term-kind)))))

  (local (defthm consp-by-car
           (implies (car X)
                    (consp x))
           :rule-classes :forward-chaining))

  (defthm base-ev-when-pseudo-term-lambda
    (implies (equal (pseudo-term-kind x) :lambda)
             (equal (base-ev x a)
                    (base-ev (pseudo-term-lambda->body x)
                             (pairlis$ (pseudo-term-lambda->formals x)
                                       (base-ev-list (pseudo-term-call->args x) a)))))
    :hints (("goal" :use ((:instance base-ev-of-pseudo-term-fix))
             :in-theory (e/d (pseudo-term-lambda->body
                              pseudo-term-lambda->formals
                              pseudo-term-call->args
                              pseudo-term-fix)
                             (base-ev-of-pseudo-term-fix)))))

  (defthm pseudo-term-lambda-of-accessors
    (implies (equal (pseudo-term-kind x) :lambda)
             (equal (pseudo-term-lambda (pseudo-term-lambda->formals x)
                                        (pseudo-term-lambda->body x)
                                        (pseudo-term-call->args x))
                    (pseudo-term-fix x)))
    :hints(("Goal" :in-theory (enable pseudo-term-kind
                                      pseudo-lambda
                                      pseudo-term-lambda->formals
                                      pseudo-term-lambda->body
                                      pseudo-term-call->args)
            :expand ((pseudo-term-fix x)))))

  (def-b*-binder pseudo-term-lambda
    :body
    (std::da-patbind-fn 'pseudo-term-lambda
                        '((formals . pseudo-term-lambda->formals)
                          (body . pseudo-term-lambda->body)
                          (fn   . pseudo-term-lambda->fn)
                          (args . pseudo-term-call->args))
                        args forms rest-expr)))


(define pseudo-fn-args-p ((fn pseudo-fn-p)
                          (args pseudo-term-listp))
  (or (atom fn)
      (eql (len (pseudo-lambda->formals fn)) (len args)))
  ///
  (defthm pseudo-fn-args-p-when-not-consp
    (implies (not (consp fn))
             (pseudo-fn-args-p fn args)))

  (defthmd pseudo-fn-args-p-when-consp
    (implies (consp fn)
             (equal (pseudo-fn-args-p fn args)
                    (equal (len args) (len (pseudo-lambda->formals fn))))))

  (defthm pseudo-fn-args-p-of-pseudo-term-call-accs
    (pseudo-fn-args-p (pseudo-term-call->fn x)
                      (pseudo-term-call->args x))
    :hints(("Goal" :in-theory (enable pseudo-term-kind
                                      pseudo-term-fix
                                      pseudo-term-call->fn
                                      pseudo-term-call->args
                                      pseudo-lambda->formals
                                      pseudo-lambda-fix
                                      pseudo-term-lambda->fn))))

  (defthm pseudo-fn-args-p-of-pseudo-term-lambda-accs
    (implies (equal (pseudo-term-kind x) :lambda)
             (pseudo-fn-args-p (pseudo-term-lambda->fn x)
                               (pseudo-term-call->args x)))
    :hints(("Goal" :in-theory (enable pseudo-term-kind
                                      pseudo-term-fix
                                      pseudo-term-call->fn
                                      pseudo-term-call->args
                                      pseudo-lambda->formals
                                      pseudo-lambda-fix
                                      pseudo-term-lambda->fn))))

  (defthm pseudo-fn-args-p-by-length-when-len-reducible
    (implies (and (equal len (len x))
                  (bind-free
                   (and (consp len)
                        (eq (car len) 'len)
                        (not (equal (cadr len) x))
                        `((y . ,(cadr len))))
                   (y))
                  (equal len (len y)))
             (equal (pseudo-fn-args-p fn x)
                    (pseudo-fn-args-p fn y))))

  (defthm pseudo-fn-args-p-when-equal-length
    (implies (and (pseudo-fn-args-p fn y)
                  (equal (len x) (len y)))
             (pseudo-fn-args-p fn x))))

(local (defthm pseudo-term-listp-of-take
         (implies (pseudo-term-listp x)
                  (pseudo-term-listp (take n x)))
         :hints(("Goal" :in-theory (enable take)))))

(define pseudo-fn-args-fix ((fn pseudo-fn-p)
                            (args pseudo-term-listp))
  :returns (new-args pseudo-term-listp)
  :guard (pseudo-fn-args-p fn args)
  :prepwork ((local (in-theory (enable pseudo-fn-args-p))))
  (mbe :logic (if (atom fn)
                  (pseudo-term-list-fix args)
                (take (len (pseudo-lambda->formals fn)) (pseudo-term-list-fix args)))
       :exec args)
  ///
  (defthm pseudo-fn-args-fix-when-pseudo-fn-args-p
    (implies (pseudo-fn-args-p fn args)
             (equal (pseudo-fn-args-fix fn args)
                    (pseudo-term-list-fix args)))))

(define pseudo-term-call ((fn pseudo-fn-p)
                          (args pseudo-term-listp))
  :parents (pseudo-term-fty)
  :short "Constructor that produces either a function call or lambda call pseudo-term,
          depending whether the given function is a function symbol or lambda."
  :guard (pseudo-fn-args-p fn args)
  :returns (term pseudo-termp)
  :guard-hints (("goal" :in-theory (enable pseudo-lambda->formals
                                           pseudo-lambda->body
                                           pseudo-term-lambda
                                           pseudo-lambda
                                           pseudo-fn-p
                                           pseudo-lambda-p
                                           pseudo-fn-args-p-when-consp
                                           pseudo-term-fncall)))

  (mbe :logic
       (if (consp fn)
           (pseudo-term-lambda (pseudo-lambda->formals fn)
                               (pseudo-lambda->body fn)
                               args)
         (pseudo-term-fncall fn args))
       :exec (cons fn args))
  ///
  (defthm kind-of-pseudo-term-call
    (or (equal (pseudo-term-kind (pseudo-term-call fn args)) :fncall)
        (equal (pseudo-term-kind (pseudo-term-call fn args)) :lambda))
    :rule-classes ((:forward-chaining :trigger-terms ((pseudo-term-kind (pseudo-term-call fn args))))))

  (defthm pseudo-term-call->fn-of-pseudo-term-call
    (equal (pseudo-term-call->fn (pseudo-term-call fn args))
           (pseudo-fn-fix fn))
    :hints(("Goal" :in-theory (enable pseudo-term-call->fn))))

  (defthm pseudo-term-call->args-of-pseudo-term-call
    (equal (pseudo-term-call->args (pseudo-term-call fn args))
           (pseudo-fn-args-fix fn args))
    :hints(("Goal" :in-theory (enable pseudo-fn-args-fix))))

  (defthm pseudo-term-call-when-function
    (implies (not (consp fn))
             (equal (pseudo-term-call fn args)
                    (pseudo-term-fncall fn args))))

  (defthm pseudo-term-call-when-lambda
    (implies (consp fn)
             (equal (pseudo-term-call fn args)
                    (pseudo-term-lambda (pseudo-lambda->formals fn)
                                        (pseudo-lambda->body fn)
                                        args))))

  (local (defthm kind-when-consp-of-pseudo-term-call->fn
           (implies (consp (pseudo-term-call->fn x))
                    (equal (pseudo-term-kind x) :lambda))
           :hints(("Goal" :in-theory (enable pseudo-term-call->fn
                                             pseudo-term-kind)))))

  (local (defthm kind-when-not-consp-of-pseudo-term-call->fn
           (implies (and (not (consp (pseudo-term-call->fn x)))
                         (consp (pseudo-term-fix x))
                         (not (equal (car (pseudo-term-fix x)) 'quote)))
                    (equal (pseudo-term-kind x) :fncall))
           :hints(("Goal" :in-theory (enable pseudo-term-call->fn
                                             pseudo-term-kind
                                             pseudo-term-fix)))))

  (defthm pseudo-term-call-of-accessors
    (implies (or (equal (pseudo-term-kind x) :lambda)
                 (equal (pseudo-term-kind x) :fncall))
             (equal (pseudo-term-call (pseudo-term-call->fn x)
                                      (pseudo-term-call->args x))
                    (pseudo-term-fix x)))
    :hints(("Goal" :in-theory (enable ;; pseudo-term-call->fn ;; pseudo-term-call->args
                                      pseudo-term-kind
                                      ;; pseudo-term-fncall
                                      ;; pseudo-term-lambda
                                      ;; pseudo-lambda->formals
                                      ;; pseudo-lambda->body
                                      ))))

  (defthmd base-ev-of-pseudo-term-call
    (implies (syntaxp (not (equal a ''nil)))
             (equal (base-ev (pseudo-term-call fn args) a)
                    (base-ev (pseudo-term-call fn
                                               (kwote-lst (base-ev-list args a)))
                             nil)))
    :hints(("Goal" :in-theory (enable base-ev-of-fncall-args))))

  (defthmd base-ev-when-pseudo-term-call
    (implies (and (or (equal (pseudo-term-kind x) :lambda)
                      (equal (pseudo-term-kind x) :fncall))
                  (syntaxp (not (and (consp x) (eq (car x) 'pseudo-term-call)))))
             (equal (base-ev x a)
                    (base-ev (pseudo-term-call (pseudo-term-call->fn x)
                                               (kwote-lst
                                                (base-ev-list (pseudo-term-call->args x) a)))
                             nil)))
    :hints (("goal" :use ((:instance base-ev-of-pseudo-term-call
                           (fn (pseudo-term-call->fn x))
                           (args (pseudo-term-call->args x))))
             :in-theory (disable base-ev-of-pseudo-term-call pseudo-term-call))))

  (def-b*-binder pseudo-term-call
    :body
    (std::da-patbind-fn 'pseudo-term-call
                        '((fn   . pseudo-term-call->fn)
                          (args . pseudo-term-call->args))
                        args forms rest-expr)))

(define pseudo-term-const->val ((x pseudo-termp))
  :parents (pseudo-term-quote
            pseudo-term-null)
  :short "Accessor for the value of a null or quote pseudo-term."
  :guard (member-eq (pseudo-term-kind x) '(:quote :null))
  :guard-hints (("goal" :in-theory (enable pseudo-term-kind
                                           pseudo-term-quote->val)))
  (mbe :logic (and (eq (pseudo-term-kind x) :quote)
                   (pseudo-term-quote->val x))
       :exec (cadr x))
  ///
  (defthm pseudo-term-const->val-when-quote
    (implies (equal (pseudo-term-kind x) :quote)
             (equal (pseudo-term-const->val x)
                    (pseudo-term-quote->val x))))

  (defthm pseudo-term-const->val-when-not-quote
    (implies (not (equal (pseudo-term-kind x) :quote))
             (equal (pseudo-term-const->val x) nil)))

  (def-b*-binder pseudo-term-const
    :body
    (std::da-patbind-fn 'pseudo-term-const
                        '((val . pseudo-term-const->val))
                        args forms rest-expr)))


(defxdoc pseudo-term-case
  :parents (pseudo-term-fty)
  :short "Case macro for pseudo-term objects."
  :long "
<p>This macro can be used to conveniently branch on the kind of a pseudo-term
and access its fields.  It supports the five basic kinds of pseudo-term and
their fields as well as the extra pseudo-kinds @(':call') and @(':const') as
described in @(see pseudo-term-fty). Among them, the following examples show
all the cases and all the accessors that can be used in each case.</p>

@({
 (pseudo-term-case x
    :const (list 'quote x.val)
    :var (list 'quote (cdr (assoc x.name a)))
    :call (list x.fn (eval-list x.args a)))

 (pseudo-term-case x
    :null (list 'null)
    :quote (list 'quote x.val)
    :var (list 'var x.name)
    :lambda (list 'lambda x.fn x.formals x.body x.args)
    :fncall (list 'fncall x.fn x.args))

 (pseudo-term-case x
   :var nil
   :call (ground-term-listp x.args)
   :otherwise t)
 })"
 )


(defmacro pseudo-term-case (var-or-expr &rest args)
  (fty::kind-casemacro-fn var-or-expr args
                          '(pseudo-term-case
                             pseudo-term-kind
                             (:null pseudo-term-null)
                             (:quote pseudo-term-quote)
                             (:const (:null :quote) pseudo-term-const)
                             (:var pseudo-term-var)
                             (:fncall pseudo-term-fncall)
                             (:lambda pseudo-term-lambda)
                             (:call (:fncall :lambda) pseudo-term-call))))

(defines pseudo-term-count
  (define pseudo-term-count ((x pseudo-termp))
    :parents (pseudo-term-fty)
    :short "Measure for recursion over pseudo-terms"
    :measure (acl2-count (pseudo-term-fix x))
    :hints (("goal" :expand ((pseudo-term-list-fix x))))
    :returns (count posp :rule-classes :type-prescription)
    (pseudo-term-case x
      :fncall (+ 1 (pseudo-term-list-count x.args))
      :lambda (+ 2 (pseudo-term-list-count x.args)
                 (pseudo-term-count x.body))
      :otherwise 1))
  (define pseudo-term-list-count ((x pseudo-term-listp))
    :parents (pseudo-term-count)
    :short "Measure for recursion over pseudo-term lists"
    :measure (acl2-count (pseudo-term-list-fix x))
    :returns (count posp :rule-classes :type-prescription)
    (if (atom x)
        1
      (+ 1 (pseudo-term-count (car x))
         (pseudo-term-list-count (cdr x)))))
  ///
  (fty::deffixequiv-mutual pseudo-term-count
    :hints ((and stable-under-simplificationp
                 '(:expand ((pseudo-term-list-fix x))))))

  (defthm pseudo-term-count-of-pseudo-term-lambda->body
    (implies (equal (pseudo-term-kind x) :lambda)
             (< (pseudo-term-count (pseudo-term-lambda->body x))
                (pseudo-term-count x)))
    :hints (("goal" :expand ((pseudo-term-count x))))
    :rule-classes :linear)

  (defthm pseudo-term-list-count-of-pseudo-term-call->args
    (implies (or (equal (pseudo-term-kind x) :lambda)
                 (equal (pseudo-term-kind x) :fncall))
             (< (pseudo-term-list-count (acl2::pseudo-term-call->args x))
                (pseudo-term-count x)))
    :hints (("goal" :expand ((pseudo-term-count x))))
    :rule-classes :linear)

  (defthm pseudo-term-count-of-pseudo-term-lambda
    (< (+ (pseudo-term-count body) (pseudo-term-list-count
                                    (remove-corresp-non-symbols formals args)))
       (pseudo-term-count (pseudo-term-lambda formals body args)))
    :hints (("goal" :expand ((pseudo-term-count (pseudo-term-lambda formals body args)))))
    :rule-classes :linear)

  (defthm pseudo-term-count-of-pseudo-term-fncall
    (< (pseudo-term-list-count args)
       (pseudo-term-count (pseudo-term-fncall fn args)))
    :hints (("goal" :expand ((pseudo-term-count (pseudo-term-fncall fn args)))))
    :rule-classes :linear)

  (defthm pseudo-term-count-of-pseudo-term-call
    (< (pseudo-term-list-count
        (pseudo-fn-args-fix fn args))
       (pseudo-term-count (pseudo-term-call fn args)))
    :hints(("Goal" :in-theory (enable pseudo-term-call pseudo-fn-args-fix)))
    :rule-classes ((:linear :trigger-terms ((pseudo-term-count (pseudo-term-call fn args))))))

  (defthm pseudo-term-list-count-of-cdr-weak
    (<= (pseudo-term-list-count (cdr x)) (pseudo-term-list-count x))
    :rule-classes :linear)

  (defthm pseudo-term-list-count-of-cdr
    (implies (consp x)
             (< (pseudo-term-list-count (cdr x)) (pseudo-term-list-count x)))
    :rule-classes :linear)

  (defthm pseudo-term-count-of-car-weak
    (<= (pseudo-term-count (car x)) (pseudo-term-list-count x))
    :rule-classes :linear)

  (defthm pseudo-term-count-of-car
    (implies (consp x)
             (< (pseudo-term-count (car x)) (pseudo-term-list-count x)))
    :rule-classes :linear)

  (defthm pseudo-term-list-count-of-cons
    (< (+ (pseudo-term-count x) (pseudo-term-list-count y)) (pseudo-term-list-count (cons x y)))
    :hints (("goal" :expand ((pseudo-term-list-count (cons x y)))))
    :rule-classes :linear))

(define pair-vars ((vars symbol-listp) vals)
  :guard (equal (len vars) (len vals))
  :returns (subst alistp)
  (if (atom vars)
      nil
    (if (and (mbt (symbolp (car vars))) (car vars))
        (cons (cons (car vars) (car vals))
              (pair-vars (cdr vars) (cdr vals)))
      (pair-vars (cdr vars) (cdr vals))))
  ///
  (defthm lookup-in-pair-vars
    (implies (pseudo-var-p v)
             (equal (cdr (hons-assoc-equal v (pair-vars vars vals)))
                    (cdr (hons-assoc-equal v (pairlis$ vars vals)))))
    :hints(("Goal" :in-theory (enable pairlis$))))

  (defthm assoc-in-pair-vars
    (implies (pseudo-var-p v)
             (equal (cdr (assoc v (pair-vars vars vals)))
                    (cdr (assoc v (pairlis$ vars vals)))))
    :hints(("Goal" :in-theory (enable pairlis$))))

  (defthm-base-ev-flag
    (defthm base-ev-of-pair-vars
      (equal (base-ev x (pair-vars vars vals))
             (base-ev x (pairlis$ vars vals)))
      :hints('(:in-theory (enable base-ev-of-nonsymbol-atom
                                  base-ev-of-bad-fncall
                                  base-ev-of-fncall-args)))
      :flag base-ev)
    (defthm base-ev-list-of-pair-vars
      (equal (base-ev-list x (pair-vars vars vals))
             (base-ev-list x (pairlis$ vars vals)))
      :flag base-ev-list)))


(defxdoc def-ev-pseudo-term-fty-support
  :parents (pseudo-term-fty)
  :short "Admit theorems about an evaluator that allow reasoning about FTY-style
          accessors and constructors for pseudo-terms."
  :long "

<p>The following call admits rules describing how evaluator @('my-eval')
operates over FTY-style pseudo-term accessors and constructors:</p>
 @({
 (def-ev-pseudo-term-fty-support my-eval my-eval-list)
 })
")

(defconst *def-ev-pseudo-term-fty-support-template*
  '(encapsulate nil
     (local (in-theory (enable . <disabled-ev-rules>)))

     (def-ev-pseudo-term-congruence <ev> <ev-list>)

     (defthm <ev>-when-pseudo-term-null
       (implies (equal (pseudo-term-kind x) :null)
                (equal (<ev> x a) nil))
       :hints (("goal" :use ((:functional-instance base-ev-when-pseudo-term-null
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-of-pseudo-term-null
       (equal (<ev> (pseudo-term-null) a) nil)
       :hints (("goal" :use ((:functional-instance base-ev-of-pseudo-term-null
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-when-pseudo-term-quote
       (implies (equal (pseudo-term-kind x) :quote)
                (equal (<ev> x a)
                       (pseudo-term-quote->val x)))
       :hints (("goal" :use ((:functional-instance base-ev-when-pseudo-term-quote
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-of-pseudo-term-quote
       (equal (<ev> (pseudo-term-quote val) a) val)
       :hints (("goal" :use ((:functional-instance base-ev-of-pseudo-term-quote
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-when-pseudo-term-var
       (implies (equal (pseudo-term-kind x) :var)
                (equal (<ev> x a)
                       (cdr (assoc (pseudo-term-var->name x) a))))
       :hints (("goal" :use ((:functional-instance base-ev-when-pseudo-term-var
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-of-pseudo-term-var
       (equal (<ev> (pseudo-term-var name) a)
              (cdr (assoc (pseudo-var-fix name) a)))
       :hints (("goal" :use ((:functional-instance base-ev-of-pseudo-term-var
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-when-pseudo-term-fncall
       (implies (and (equal (pseudo-term-kind x) :fncall)
                     (equal new-x (cons (pseudo-term-fncall->fn x)
                                        (pseudo-term-call->args x)))
                     (syntaxp (not (equal new-x x))))
                (equal (<ev> x a)
                       (<ev> new-x a)))
       :hints (("goal" :use ((:functional-instance base-ev-when-pseudo-term-fncall
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-of-pseudo-term-fncall
       (equal (<ev> (pseudo-term-fncall fn args) a)
              (<ev> (cons (pseudo-fnsym-fix fn) args) a))
       :hints (("goal" :use ((:functional-instance base-ev-of-pseudo-term-fncall
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-when-pseudo-term-lambda
       (implies (equal (pseudo-term-kind x) :lambda)
                (equal (<ev> x a)
                       (<ev> (pseudo-term-lambda->body x)
                             (pairlis$ (pseudo-term-lambda->formals x)
                                       (<ev-list> (pseudo-term-call->args x) a)))))
       :hints (("goal" :use ((:functional-instance base-ev-when-pseudo-term-lambda
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-of-pseudo-term-lambda
       (equal (<ev> (pseudo-term-lambda formals body args) a)
              (<ev> body (pairlis$ formals (<ev-list> args a))))
       :hints (("goal" :use ((:functional-instance base-ev-of-pseudo-term-lambda
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))
     
     (defthmd <ev>-of-pseudo-term-call
       (implies (syntaxp (not (equal a ''nil)))
                (equal (<ev> (pseudo-term-call fn args) a)
                       (<ev> (pseudo-term-call fn
                                               (kwote-lst (<ev-list> args a)))
                             nil)))
       :hints (("goal" :use ((:functional-instance base-ev-of-pseudo-term-call
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthmd <ev>-when-pseudo-term-call
       (implies (and (or (equal (pseudo-term-kind x) :lambda)
                         (equal (pseudo-term-kind x) :fncall))
                     (syntaxp (not (and (consp x) (eq (car x) 'pseudo-term-call)))))
                (equal (<ev> x a)
                       (<ev> (pseudo-term-call (pseudo-term-call->fn x)
                                               (kwote-lst
                                                (<ev-list> (pseudo-term-call->args x) a)))
                             nil)))
       :hints (("goal" :use ((:functional-instance base-ev-when-pseudo-term-call
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev>-of-pair-vars
       (equal (<ev> x (pair-vars vars vals))
              (<ev> x (pairlis$ vars vals)))
       :hints (("goal" :use ((:functional-instance base-ev-of-pair-vars
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))

     (defthm <ev-list>-of-pair-vars
       (equal (<ev-list> x (pair-vars vars vals))
              (<ev-list> x (pairlis$ vars vals)))
       :hints (("goal" :use ((:functional-instance base-ev-list-of-pair-vars
                              (base-ev <ev>)
                              (base-ev-list <ev-list>))))))))

(defun def-ev-pseudo-term-fty-support-fn (ev ev-list world)
  (declare (Xargs :mode :program))
  (b* ((bad-fncall-rule (ev-find-bad-fncall-rule ev world))
       (nonsymbol-atom-rule (ev-find-nonsymbol-atom-rule ev world))
       (fncall-rule (ev-find-fncall-generic-rule ev world))
       ((unless (and bad-fncall-rule nonsymbol-atom-rule fncall-rule))
        (er hard? 'def-ev-pseudo-term-fty-support-fn
            "Couldn't find the right rules to enable -- is ~x0 an evaluator?" ev)))
    (acl2::template-subst
     *def-ev-pseudo-term-fty-support-template*
     :atom-alist `((<ev> . ,ev)
                   (<ev-list> . ,ev-list)
                   (<disabled-ev-rules> . ,(list fncall-rule bad-fncall-rule nonsymbol-atom-rule)))
     :str-alist `(("<EV>" . ,(symbol-name ev))
                  ("<EV-LIST>" . ,(symbol-name ev-list)))
     :pkg-sym ev)))

(defmacro def-ev-pseudo-term-fty-support (ev ev-list)
  `(make-event
    (def-ev-pseudo-term-fty-support-fn ',ev ',ev-list (w state))))


;; Alternative to kwote-lst that produces (pseudo-term-quote elt) instead of (list 'quote elt).
(defthmd kwote-lst-redef
  (equal (kwote-lst x)
         (if (atom x)
             nil
           (cons (pseudo-term-quote (car x))
                 (kwote-lst (cdr x)))))
  :hints(("Goal" :in-theory (enable pseudo-term-quote)))
  :rule-classes :definition)


(local
 (progn
   (defevaluator next-ev next-ev-lst ((if a b c) (return-last a b c) (equal x y)) :namedp t)
   (def-ev-pseudo-term-fty-support next-ev next-ev-lst)))

(local
 (progn
   (defevaluator other-ev other-ev-lst ((if a b c) (return-last a b c) (equal x y)) :namedp nil)
   (def-ev-pseudo-term-fty-support other-ev other-ev-lst)))

; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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

(in-package "SV")
(include-book "../svex/compose")
(include-book "../svex/eval")
(include-book "../svex/env-ops")
(include-book "tools/match-tree" :dir :system)
(include-book "std/alists/fast-alist-clean" :dir :System)
(include-book "std/alists/fal-extract" :dir :system)
(local (include-book "centaur/misc/fast-alists" :dir :system))
(local (include-book "centaur/misc/equal-sets" :dir :System))
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "std/lists/top" :dir :system))
(local (in-theory (disable acl2-count
                           pick-a-point-subset-strategy
                           double-containment)))


(defxdoc svex-decomp
  :parents (sv)
  :short "Proving that a decomposition is equivalent to some whole."
  :long "<p>Here is an example, from \"svex/tutorial/boothpipe.lisp\", showing
how to use @('svdecomp-hints') to prove a decomposition theorem:</p>

@({
 (defthm boothmul-decomp-is-boothmul
   (implies (boothmul-direct-autohyps)
            (b* ( ;; Run the first part of the circuit to get the partial products
                 (in-alist1  (boothmul-step1-autoins))
                 (out-alist1 (sv::svtv-run (boothmul-step1) in-alist1))

                 ;; Get the results from the output and stick them into an
                 ;; input alist for step2.  Some control signals from the
                 ;; original input alist also are needed.
                 (in-alist2 (boothmul-step2-alist-autoins (append out-alist1 in-alist1)))

                 ;; Run the second part of the circuit on the results from the
                 ;; first part, summing the partial products.
                 (out-alist2 (sv::svtv-run (boothmul-step2) in-alist2))

                 ;; Separately, run the original circuit.
                 (orig-in-alist  (boothmul-direct-autoins))
                 (orig-out-alist (sv::svtv-run (boothmul-direct) orig-in-alist)))

              (equal
               ;; The final answer from running the decomposed circuit the second
               ;; time, after feeding its partial products back into itself.
               (cdr (assoc 'o out-alist2))

               ;; The answer from running the original circuit.
               (cdr (assoc 'o orig-out-alist)))))
   :hints((sv::svdecomp-hints :hyp (boothmul-direct-autohyps)
                                :g-bindings (boothmul-direct-autobinds))))
 })

<p>The @('svdecomp-hints') first gives a theory hint that allows ACL2 to
efficiently open the @('svtv-run') calls and process the goal into a form on
which some special-purpose meta rules can operate.  When this is done it enters
a theory containing only those meta rules.  The meta rules find svex
decompositions and re-compose them together so that, if all goes well, you're
left with the equivalence of two evaluations of svex expressions.  In the best
case, those svex expressions are equal, in which case the proof finishes there.
However, often there are syntactic differences between the expressions.  Then,
we call GL to prove the two evaluations equivalent.  To do this, we need a type
hypothesis and symbolic bindings for the variables.  These are provided by the
@(':hyp') and @(':g-bindings') argument to @('svdecomp-hints').</p>

<p>Additional optional arguments:</p>

<ul>
<li>@(':enable') simply adds a
list of rules to the theory used in the first step, before the meta rules are
used.  This is useful because the conclusion of the theorem must be in a
particular form, described below, for the meta rules to work.  If the statement
of the theorem uses special-purpose functions to (say) construct alists or
compare outputs, the theory may need to be augmented with rules to rewrite
these functions away so that the meta rule can work.</li>

<li>@(':rewrite-limit') sets the limit on the number of passes of rewriting to
do on the resulting svex expressions.  In some cases it might be useful to set
this to 0, to disable rewriting.  Using this keyword argument actually sets the
state global variable @('sv::svdecomp-rewrite-limit'), which sets the limit for
future calls as well.</li>
</ul>

<h5>What can the meta rules handle?</h5>

<p>The core algorithm of the meta rule operates on a call of @('svex-eval'),
@('svexlist-eval'), or @('svex-alist-eval') in which some of the values bound
to variables in the environment are also calls of @('svex-eval').  If its
operation is successful, it results in an evaluation with an environment that
does not bind any calls of @('svex-eval').  It does this by basically applying
the following rule, @('svex-eval-of-svex-compose'), in reverse:</p>
@({
  (equal (svex-eval (svex-compose x a) env)
         (svex-eval x (append (svex-alist-eval a env) env)))
  })

<p>The meta rule supposes that the top-level evaluation is equivalent to the
RHS of the above rule for some term @('env') and quoted value @('a'), and tries
to determine @('env') and @('a') for which this is the case.  This would be
relatively easy if the RHS was in a form that matched the above, but in
practice the @('svex-alist-eval') term is represented instead as several
explicit cons pairs with @('svex-eval') cdrs, the ordering among the keys is
inconsistent, and in some places a subset of @('env') is used in place of the
whole thing.</p>

<p>This re-composition is usually best done at the top level, so the meta rules
trigger on any of the following:</p>
<ul>
<li>@({(equal (svex-eval (quote sv1) env1) (svex-eval (quote sv2) env2))})</li>
<li>@({(equal (svexlist-eval (quote sv1) env1) (svexlist-eval (quote sv2) env2))})</li>
<li>@({(equal (svex-alist-eval (quote sv1) env1) (svex-alist-eval (quote sv2) env2))})</li>
</ul>

<p>The @('env') terms in the above may take the following forms, where
@('env1'), @('env2') are recursively matched:</p>
<ul>
<li>@({(quote val)})</li>
<li>@({(cons (cons (quote var) val) env1)})</li>
<li>@({(cons (quote (var . val)) env1)})</li>
<li>@({(binary-append env1 env2)})</li>
<li>@({(svex-alist-eval (quote svalist) e)})</li>
</ul>

")

(defxdoc decomp.lisp :parents (svex-decomp))
(local (xdoc::set-default-parents decomp.lisp))

(define pseudo-term-fix ((x pseudo-termp))
  :returns (xx pseudo-termp)
  (mbe :logic (and (pseudo-termp x) x)
       :exec x)
  ///
  (defthm pseudo-term-fix-when-pseudo-termp
    (implies (pseudo-termp x)
             (equal (pseudo-term-fix x) x)))

  (deffixtype pseudo-term :pred pseudo-termp :Fix pseudo-term-fix :equiv pseudo-term-equiv
    :define t))

(local (in-theory (disable pseudo-termp pseudo-term-listp)))
(defsection pseudo-termp

  (local (in-theory (enable pseudo-termp pseudo-term-listp)))

  (Defthm pseudo-termp-of-quote
    (pseudo-termp (list 'quote x))))



(fty::defmap svdecomp-symenv :key-type svar :val-type pseudo-term
  :true-listp t)

(defun svdecomp-equal (a b)
  (declare (xargs :guard t))
  (equal a b))



(acl2::defevaluator svdecomp-ev svdecomp-ev-lst
  ((not a)
   (if a b c)
   (implies a b)
   (cons a b)
   (Equal a b)
   (svdecomp-equal a b)
   (car a) (cdr a)
   (svex-alist-eval x env)
   (svexlist-eval x env)
   (svex-eval x env)
   (hons-assoc-equal a b)
   (binary-append a b))
  :namedp t)

(local
 (progn
   (defthm svar-alist-p-when-svdecomp-symenv-p
     (implies (svdecomp-symenv-p x)
              (svar-alist-p x))
     :hints(("Goal" :in-theory (enable svdecomp-symenv-p
                                       svar-alist-p))))

   (defthm svdecomp-symenv-fix-of-svar-alist-fix
     (equal (svdecomp-symenv-fix (svar-alist-fix x))
            (svdecomp-symenv-fix x))
     :hints(("Goal" :in-theory (enable svdecomp-symenv-fix
                                       svar-alist-fix))))

   (defrefinement svar-alist-equiv svdecomp-symenv-equiv
     :hints (("Goal" :use ((:instance svdecomp-symenv-fix-of-svar-alist-fix)
                           (:instance svdecomp-symenv-fix-of-svar-alist-fix (x y)))
              :in-theory (disable svdecomp-symenv-fix-of-svar-alist-fix))))))

;;(std::add-default-post-define-hook :fix)

;; Lying to the fixtype engine, telling it to prove svar-alist congruences for
;; formals guarded with svdecomp-symenv-p.
(local (deffixtype svdecomp-symenv-svar-alist :pred svdecomp-symenv-p
         :fix svar-alist-fix :equiv svar-alist-equiv))

(local (std::add-default-post-define-hook :fix))

(define svar-lookup ((k svar-p) (x svar-alist-p))
  :prepwork ((local (in-theory (enable svar-alist-p svar-alist-fix))))
  (mbe :logic
       (if (atom x)
           nil
         (if (and (consp (car x))
                  (svar-p (caar x))
                  (equal (svar-fix k) (caar x)))
             (car x)
           (svar-lookup k (cdr x))))
       :exec (hons-get k x))
  ///
  (defthm svar-lookup-of-cons
    (equal (svar-lookup k (cons a b))
           (if (and (consp a) (svar-p (car a))
                    (svar-equiv (car a) k))
               a
             (svar-lookup k b))))

  (defthm svar-lookup-of-atom
    (implies (not (consp x))
             (equal (svar-lookup k x) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm svar-lookup-of-append
    (equal (svar-lookup k (append a b))
           (or (svar-lookup k a)
               (svar-lookup k b))))

  (defthm svar-lookup-of-svex-alist-fix
    (iff (svar-lookup k (svex-alist-fix x))
         (svar-lookup k x))
    :hints(("Goal" :in-theory (enable svex-alist-fix))))

  (defthm svar-lookup-of-svex-env-fix
    (iff (svar-lookup k (svex-env-fix x))
         (svar-lookup k x))
    :hints(("Goal" :in-theory (enable svex-env-fix)))))

(define svdecomp-ev-symenv ((x svdecomp-symenv-p) env)
  :prepwork ((local (in-theory (enable svdecomp-symenv-p
                                       svar-alist-fix))))
  :returns (res svar-alist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (cons (cons (caar x)
                    (svdecomp-ev (cdar x) env))
              (svdecomp-ev-symenv (cdr x) env))
      (svdecomp-ev-symenv (cdr x) env)))
  ///
  (defthm eval-lookup-of-svdecomp-ev-symenv
    (equal (svar-lookup k (svdecomp-ev-symenv x env))
           (and (svar-lookup k x)
                (cons (svar-fix k) (svdecomp-ev (cdr (svar-lookup k x)) env))))
    :hints(("Goal" :in-theory (enable svar-lookup)))))



(define map-alist-const-keys-to-val-terms ((x svex-env-p))
  :prepwork ((local (in-theory (enable svex-env-fix))))
  :returns (res svdecomp-symenv-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (cons (cons (caar x)
                    (list 'quote (4vec-fix (cdar x))))
              (map-alist-const-keys-to-val-terms (cdr x)))
      (map-alist-const-keys-to-val-terms (cdr x))))
  ///
  (defthm eval-lookup-of-map-alist-const-keys-to-val-terms
    (let ((al (map-alist-const-keys-to-val-terms x)))
      (implies (svar-lookup k (svex-env-fix x))
               (equal (svdecomp-ev (cdr (svar-lookup k al)) env)
                      (cdr (svar-lookup k (svex-env-fix x)))))))

  (defthm lookup-exists-of-map-alist-const-keys-to-val-terms
    (iff (svar-lookup k (map-alist-const-keys-to-val-terms x))
         (svar-lookup k (svex-env-fix x))))

  (defthm svdecomp-ev-symenv-of-map-alist-const-keys-to-val-terms
    (equal (svdecomp-ev-symenv (map-alist-const-keys-to-val-terms x) env)
           (svex-env-fix x))
    :hints(("Goal" :in-theory (enable svdecomp-ev-symenv)))))


(local (defthm match-tree-is-subst-tree-for-pseudo-termp
         (b* (((mv ok alist) (acl2::match-tree pat x alist)))
           (implies ok
                    (equal (pseudo-termp x)
                           (pseudo-termp (acl2::subst-tree pat alist)))))
         :hints(("Goal" :in-theory (enable acl2::match-tree-is-subst-tree)))))

(local (defthm match-tree-is-subst-tree-for-svdecomp-ev
         (b* (((mv ok alist) (acl2::match-tree pat x alist)))
           (implies ok
                    (equal (svdecomp-ev x a)
                           (svdecomp-ev (acl2::subst-tree pat alist) a))))
         :hints(("Goal" :in-theory (enable acl2::match-tree-is-subst-tree)))))


(define svex-alist-evaluation-to-symenv ((x svex-alist-p) (env pseudo-termp))
  :hooks ((:fix :omit (env)
           :hints(("Goal" :in-theory (enable svex-alist-fix)))))
  :returns (al (and (svar-alist-p al)
                    (implies (pseudo-termp env) (svdecomp-symenv-p al))))
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (svex-alist-evaluation-to-symenv (cdr x) env))
       ((cons var svex) (car x)))
    ;; Performance note: this does some perhaps unnecessary consing. To reduce
    ;; this we could have an svdecomp-symenv instead map variables to a sum
    ;; type that is either just any old term or specifically an svex
    ;; evaluation, but my guess is that's not worth the refactoring effort.
    (cons (cons var
                `(svex-eval (quote ,(svex-fix svex)) ,env))
          (svex-alist-evaluation-to-symenv (cdr x) env)))
  ///
  (defthm eval-lookup-of-svex-alist-evaluation-to-symenv
    (b* ((al (svex-alist-evaluation-to-symenv x env)))
      (equal (svdecomp-ev (cdr (svar-lookup k al)) a)
             (and (svar-lookup k x)
                  (svex-eval (cdr (svar-lookup k x))
                             (svdecomp-ev env a))))))

  (defthm lookup-exists-of-svex-alist-evaluation-to-symenv
    (b* ((al (svex-alist-evaluation-to-symenv x env)))
      (iff (svar-lookup k al)
           (svar-lookup k x))))

  (defthm svdecomp-ev-symenv-of-svex-alist-evaluation-to-symenv
    (b* ((al (svex-alist-evaluation-to-symenv x env)))
      (equal (svdecomp-ev-symenv al a)
             (svex-alist-eval x (svdecomp-ev env a))))
    :hints(("Goal" :in-theory (enable svdecomp-ev-symenv
                                      svex-alist-eval)))))





(defthm svar-lookup-svex-alist-eval
  (equal (svar-lookup k (svex-alist-eval x env))
         (and (svar-lookup k x)
              (cons (svar-fix k)
                    (svex-eval (cdr (svar-lookup k x)) env))))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-fix))))


(defthm svdecomp-ev-symenv-of-append
  (equal (svdecomp-ev-symenv (append a b) env)
         (append (svdecomp-ev-symenv a env)
                 (svdecomp-ev-symenv b env)))
  :hints(("Goal" :in-theory (enable svdecomp-ev-symenv))))

(define map-alist-term-keys-to-val-terms ((x pseudo-termp))
  ;; '(list (cons 'a (foo a c))
  ;;        (cons 'b b)
  ;;        (cons 'c d))
  ;; ->  ((a . (foo a c)) (b . b) (c . d))
  :prepwork (;; (local (acl2::def-match-tree-rewrites
             ;;          (cons (cons (quote (:? var)) (:? val))
             ;;                (:? rest))
             ;;          :prefix acons-))
             ;; (local (acl2::def-match-tree-rewrites
             ;;          (acl2::binary-append (:? first) (:? rest))
             ;;          :prefix app-))
             ;; (local (acl2::def-match-tree-rewrites
             ;;          (svex-alist-eval (quote (:? svalist)) (:? env))
             ;;          :prefix svaev-))
             (local (defthm match-tree-is-subst-tree-for-svar-lookup
                      (b* (((mv ok alist) (acl2::match-tree pat x alist)))
                        (implies ok
                                 (equal (svar-lookup k x)
                                        (svar-lookup k (acl2::subst-tree pat alist)))))
                      :hints(("Goal" :in-theory (enable acl2::match-tree-is-subst-tree)))))
             (local (defthm match-tree-is-subst-tree-for-acl2-count
                      (b* (((mv ok alist) (acl2::match-tree pat x alist)))
                        (implies ok
                                 (equal (acl2-count x)
                                        (acl2-count (acl2::subst-tree pat alist)))))
                      :hints(("Goal" :in-theory (enable acl2::match-tree-is-subst-tree)))))
             (local (in-theory (disable assoc-equal
                                        ;acl2::consp-under-iff-when-true-listp
                                        ))))
  :verify-guards nil
  :returns (mv err (al (and (implies (pseudo-termp x) (svdecomp-symenv-p al))
                            (svar-alist-p al))))
  :measure (acl2-count x)
  :hooks nil
  (b* (((acl2::when-match x (quote (:? rest-al)))
        (if (svex-env-p rest-al)
            (mv nil (map-alist-const-keys-to-val-terms rest-al))
          (mv (msg "Malformed environment: ~x0~%" rest-al) nil)))
       ((acl2::when-match x (cons (cons (quote (:? var)) (:? val))
                                    (:? rest)))
        (b* (((unless (svar-p var))
              (mv (msg "Wrong type for variable: ~x0~%" var) nil))
             ((mv err rest)
              (map-alist-term-keys-to-val-terms rest)))
          (mv err (cons (cons var val) rest))))
       ((acl2::when-match x (cons (quote ((:? var) . (:? val)))
                                  (:? rest)))
        (b* (((unless (svar-p var))
              (mv (msg "Wrong type for variable: ~x0~%" var) nil))
             ((mv err rest)
              (map-alist-term-keys-to-val-terms rest)))
          (mv err (cons (cons var (list 'quote val)) rest))))
       ((acl2::when-match x (acl2::binary-append (:? first) (:? rest)))
        (b* (((mv err first) (map-alist-term-keys-to-val-terms first))
             ((when err) (mv err nil))
             ((mv err rest) (map-alist-term-keys-to-val-terms rest))
             ((when err) (mv err nil)))
          (mv nil (append first rest))))
       ((acl2::when-match x (svex-alist-eval (quote (:? svalist)) (:? env)))
        (b* (((unless (svex-alist-p svalist))
              (mv (msg "Malformed svex alist: ~x0~%" svalist) nil)))
          (mv nil (svex-alist-evaluation-to-symenv svalist env)))))
    (mv (msg "Failed to parse ~x0 as an alist term~%" x)
        nil))
  ///
  (verify-guards map-alist-term-keys-to-val-terms)

  (local (in-theory (disable (:d map-alist-term-keys-to-val-terms))))
  (local (set-default-hints
          '((and (equal (car id) '(0))
                 '(:induct (map-alist-term-keys-to-val-terms x)
                   :expand ((map-alist-term-keys-to-val-terms x)))))))

  (defthmd lookup-exists-of-map-alist-term-keys-to-val-terms
    (b* (((mv err al) (map-alist-term-keys-to-val-terms x)))
      (implies (not err)
               (iff (svar-lookup k al)
                    (svar-lookup k (svdecomp-ev x a))))))

  (defthm lookup-exists-of-map-alist-term-keys-to-val-terms-1
    (b* (((mv err al) (map-alist-term-keys-to-val-terms x)))
      (implies (and (not err)
                    (svar-lookup k (svdecomp-ev x a)))
               (svar-lookup k al)))
    :hints (("goal" :use lookup-exists-of-map-alist-term-keys-to-val-terms)))

  (defthm lookup-exists-of-map-alist-term-keys-to-val-terms-2
    (b* (((mv err al) (map-alist-term-keys-to-val-terms x)))
      (implies (and (not err)
                    (not (svar-lookup k (svdecomp-ev x a))))
               (not (svar-lookup k al))))
    :hints (("Goal" :use lookup-exists-of-map-alist-term-keys-to-val-terms)))

  (defthm eval-lookup-of-map-alist-term-keys-to-val-terms
    (b* (((mv err al) (map-alist-term-keys-to-val-terms x)))
      (implies (and (not err)
                    (svar-lookup k (svdecomp-ev x env)))
               (equal (svdecomp-ev (cdr (svar-lookup k al)) env)
                      (cdr (svar-lookup k (svdecomp-ev x env)))))))

  (defthm svdecomp-ev-symenv-of-map-alist-term-keys-to-val-terms
    (b* (((mv err al) (map-alist-term-keys-to-val-terms x)))
      (implies (not err)
               (equal (svdecomp-ev-symenv al env)
                      (svdecomp-ev x env))))
    :hints(("Goal" :in-theory (enable svdecomp-ev-symenv)))))



(defalist envmap :key-type pseudo-termp :val-type svex-alist-p)

(defalist svex-alist-alist :val-type svex-alist-p)

(local
 (progn
   (defthm svex-alist-alist-p-when-envmap-p
     (implies (envmap-p x)
              (svex-alist-alist-p x))
     :hints(("Goal" :in-theory (enable envmap-p svex-alist-alist-p))))


   (defthm svex-alist-p-of-envmap-lookup
     (implies (svex-alist-alist-p x)
              (svex-alist-p (cdr (hons-assoc-equal k x))))
     :hints(("Goal" :in-theory (enable svex-alist-alist-p))))

   (fty::deffixcong svex-alist-alist-equiv svex-alist-equiv (cdr (hons-assoc-equal k x)) x
     :hints(("Goal" :in-theory (enable svex-alist-alist-fix))))

   (defthm envmap-fix-of-svex-alist-alist-fix
     (equal (envmap-fix (svex-alist-alist-fix x))
            (envmap-fix x))
     :hints(("Goal" :in-theory (enable envmap-fix
                                       svex-alist-alist-fix))))

   (defrefinement svex-alist-alist-equiv envmap-equiv
     :hints (("Goal" :use ((:instance envmap-fix-of-svex-alist-alist-fix)
                           (:instance envmap-fix-of-svex-alist-alist-fix (x y)))
              :in-theory (disable envmap-fix-of-svex-alist-alist-fix))))))

(local (deffixtype envmap-svex-alist-alist :pred envmap-p
         :fix svex-alist-alist-fix :equiv svex-alist-alist-equiv))

(define svdecomp-ev-envmap ((x envmap-p) env)
  :returns (res svex-env-p)
  :prepwork ((local (in-theory (enable svex-alist-alist-fix))))
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (append (ec-call (svex-alist-eval (cdar x) (svdecomp-ev (caar x) env)))
                (svdecomp-ev-envmap (cdr x) env))
      (svdecomp-ev-envmap (cdr x) env))))

(define envmap-entry-to-term-alist ((x svex-alist-p) (env pseudo-termp))
  :returns (xal (and (implies (pseudo-termp env) (svdecomp-symenv-p xal))
                     (svar-alist-p xal)))
  :prepwork ((local (in-theory (enable svex-alist-fix))))
  :hooks ((:fix :args (x)))
  (b* (((when (atom x)) nil)
       ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
        (envmap-entry-to-term-alist (cdr x) env)))
    (cons (cons (caar x) `(svex-eval (quote ,(svex-fix (cdar x))) ,env))
          (envmap-entry-to-term-alist (cdr x) env)))
  ///
  (defthm eval-of-envmap-entry-to-term-alist
    (equal (svdecomp-ev-symenv (envmap-entry-to-term-alist x env) a)
           (svex-alist-eval x (svdecomp-ev env a)))
    :hints(("Goal" :in-theory (enable svex-alist-eval svdecomp-ev-symenv))))

  (defthmd lookup-in-envmap-entry-to-term-alist
    (iff (svar-lookup k (envmap-entry-to-term-alist x env))
         (svar-lookup k x)))

  (defthm no-lookup-when-not-in-svex-alist-fix
    (implies (not (svar-lookup k x))
             (not (svar-lookup k (envmap-entry-to-term-alist x env))))
    :hints(("Goal" :in-theory (enable lookup-in-envmap-entry-to-term-alist)))))



(define envmap-to-term-alist ((x envmap-p))
  :returns (xal (and (implies (envmap-p x) (svdecomp-symenv-p xal))
                     (svar-alist-p xal)))
  :prepwork ((local (in-theory (enable svex-alist-alist-fix))))
  (if (atom x)
      nil
    (if (mbt (consp (car x)))
        (append (envmap-entry-to-term-alist (cdar x) (caar x))
                (envmap-to-term-alist (cdr x)))
      (envmap-to-term-alist (cdr x))))
  ///
  (defthm eval-of-envmap-to-term-alist
    (equal (svdecomp-ev-symenv (envmap-to-term-alist x) a)
           (svdecomp-ev-envmap x a))
    :hints(("Goal" :in-theory (enable svdecomp-ev-envmap svdecomp-ev-symenv))))

  (defthm envmap-to-term-alist-of-append
    (equal (envmap-to-term-alist (append a b))
           (append (envmap-to-term-alist a)
                   (envmap-to-term-alist b)))))

(local
 (fty::deffixcong svex-alist-equiv svex-equiv (cdr (svar-lookup k x)) x
   :hints(("Goal" :in-theory (enable svex-alist-fix svar-lookup)))))





(define svar-alist-keys ((x svar-alist-p))
  :prepwork ((local (in-theory (enable svar-alist-fix))))
  :returns (vars svarlist-p)
  (if (atom x)
      nil
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        (cons (caar x)
              (svar-alist-keys (cdr x)))
      (svar-alist-keys (cdr x))))
  ///
  (defthm svar-alist-keys-of-append
    (Equal (svar-alist-keys (append a b))
           (append (svar-alist-keys a)
                   (svar-alist-keys b))))

  (fty::deffixcong svex-env-equiv equal (svar-alist-keys x) x
    :hints(("Goal" :in-theory (enable svar-alist-keys svex-env-fix))))

  (fty::deffixcong svex-alist-equiv equal (svar-alist-keys x) x
    :hints(("Goal" :in-theory (enable svar-alist-keys svex-alist-fix)))))

(define envmap->svex-alist ((envmap envmap-p))
  :prepwork ((local (in-theory (enable svex-alist-alist-fix))))
  :returns (svalist svex-alist-p)
  (if (atom envmap)
      nil
    (if (mbt (consp (car envmap)))
        (append (svex-alist-fix (cdar envmap))
                (envmap->svex-alist (cdr envmap)))
      (envmap->svex-alist (cdr envmap))))
  ///
  (defthm envmap->svex-alist-of-append
    (equal (envmap->svex-alist (append a b))
           (append (envmap->svex-alist a)
                   (envmap->svex-alist b))))

  (defthm envmap->svex-alist-of-atom
    (implies (not (consp envmap))
             (equal (envmap->svex-alist envmap) nil))
    :rule-classes ((:rewrite :backchain-limit-lst 0)))

  (defthm svar-lookup-of-envmap-to-term-alist-under-iff
    (iff (svar-lookup k (envmap-to-term-alist x))
         (svar-lookup k (envmap->svex-alist x)))
    :hints(("Goal" :in-theory (enable envmap-to-term-alist
                                      lookup-in-envmap-entry-to-term-alist)))))



(local
 (defsection-progn alist-collect-compositions-lemmas

   (defthm member-alist-keys-envmap->svex-alist-remove-assoc
     (implies (not (member k (svar-alist-keys (envmap->svex-alist envmap))))
              (not (member k (svar-alist-keys (envmap->svex-alist
                                               (acl2::hons-remove-assoc key envmap))))))
     :hints(("Goal" :in-theory (enable  envmap->svex-alist
                                        acl2::hons-remove-assoc))))

   (defthm intersectp-alist-keys-envmap->svex-alist-remove-assoc
     (implies (not (intersectp keys (svar-alist-keys (envmap->svex-alist envmap))))
              (not (intersectp keys (svar-alist-keys (envmap->svex-alist
                                                      (acl2::hons-remove-assoc key envmap))))))
     :hints ((acl2::set-reasoning)))

   (defthm intersectp-alist-keys-envmap->svex-alist-remove-assoc2
     (implies (not (intersectp (svar-alist-keys (envmap->svex-alist envmap)) keys))
              (not (intersectp (svar-alist-keys (envmap->svex-alist
                                                 (acl2::hons-remove-assoc key envmap))) keys
                                                 )))
     :hints ((acl2::set-reasoning)))

   (defthm no-duplicatesp-alist-keys-envmap->svex-alist-remove-assoc
     (implies (no-duplicatesp (svar-alist-keys (envmap->svex-alist envmap)))
              (no-duplicatesp (svar-alist-keys (envmap->svex-alist
                                                (acl2::hons-remove-assoc key envmap)))))
     :hints(("Goal" :in-theory (enable  envmap->svex-alist
                                        acl2::hons-remove-assoc))))

   (defthm member-alist-keys-envmap->svex-alist-lookup
     (implies (not (member k (svar-alist-keys (envmap->svex-alist envmap))))
              (not (member k (svar-alist-keys (cdr (hons-assoc-equal key envmap))))))
     :hints(("Goal" :in-theory (enable  envmap->svex-alist
                                        acl2::hons-remove-assoc))))

   (defthm member-alist-keys-envmap->svex-alist-lookup-clean
     (implies (not (member k (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))
              (not (member k (svar-alist-keys (cdr (hons-assoc-equal key envmap))))))
     :hints(("Goal" :use ((:instance member-alist-keys-envmap->svex-alist-lookup
                           (envmap (fast-alist-clean envmap)))))))

   (defthm intersectp-alist-keys-envmap->svex-alist-lookup
     (implies (not (intersectp keys (svar-alist-keys (envmap->svex-alist envmap))))
              (not (intersectp keys (svar-alist-keys (cdr (hons-assoc-equal key envmap))))))
     :hints ((acl2::set-reasoning)))

   (defthm no-duplicates-alist-keys-envmap->svex-alist-lookup
     (implies (no-duplicatesp (svar-alist-keys (envmap->svex-alist envmap)))
              (no-duplicatesp (svar-alist-keys (cdr (hons-assoc-equal key envmap)))))
     :hints(("Goal" :in-theory (enable  envmap->svex-alist))))

   (defthm no-duplicates-alist-keys-envmap->svex-alist-lookup-clean
     (implies (no-duplicatesp (svar-alist-keys (envmap->svex-alist
                                                (fast-alist-clean envmap))))
              (no-duplicatesp (svar-alist-keys (cdr (hons-assoc-equal key envmap)))))
     :hints (("goal" :use ((:instance no-duplicates-alist-keys-envmap->svex-alist-lookup
                            (envmap (fast-alist-clean envmap)))))))

   (defthm intersectp-alist-keys-envmap->svex-alist-lookup-clean
     (implies (not (intersectp keys (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))
              (not (intersectp keys (svar-alist-keys (cdr (hons-assoc-equal key envmap))))))
     :hints (("goal" :use ((:instance intersectp-alist-keys-envmap->svex-alist-lookup
                            (envmap (fast-alist-clean envmap)))))))


   (defthm intersectp-alist-keys-of-envmap-entry-and-rest
     (implies (no-duplicatesp (svar-alist-keys (envmap->svex-alist envmap)))
              (not (INTERSECTP-EQUAL
                    (SVAR-ALIST-KEYS
                     (ENVMAP->SVEX-ALIST (ACL2::HONS-REMOVE-ASSOC key envmap)))
                    (SVAR-ALIST-KEYS (CDR (HONS-ASSOC-EQUAL key ENVMAP))))))
     :hints(("Goal" :in-theory (enable envmap->svex-alist acl2::hons-remove-assoc))))

   (defthm intersectp-alist-keys-of-envmap-entry-and-rest-clean
     (implies (no-duplicatesp (svar-alist-keys (envmap->svex-alist
                                                (fast-alist-clean envmap))))
              (not (INTERSECTP-EQUAL
                    (SVAR-ALIST-KEYS
                     (ENVMAP->SVEX-ALIST (ACL2::HONS-REMOVE-ASSOC
                                          key
                                          (fast-alist-clean envmap))))
                    (SVAR-ALIST-KEYS (CDR (HONS-ASSOC-EQUAL key ENVMAP))))))
     :hints(("Goal" :use ((:instance intersectp-alist-keys-of-envmap-entry-and-rest
                           (envmap (fast-alist-clean envmap)))))))


   (defthm lookup-in-svex-alist-alist-fix
     (equal (hons-assoc-equal x (svex-alist-alist-fix y))
            (and (hons-assoc-equal x y)
                 (cons x (svex-alist-fix (cdr (hons-assoc-equal x y))))))
     :hints(("Goal" :in-theory (enable svex-alist-alist-fix))))

   (defthm svex-alist-alist-fix-of-fast-alist-fork
     (equal (svex-alist-alist-fix (fast-alist-fork x y))
            (fast-alist-fork (svex-alist-alist-fix x) (svex-alist-alist-fix y)))
     :hints(("Goal" :in-theory (enable svex-alist-alist-fix))))

   (defun final-cdr (x)
     (if (atom x)
         x
       (final-cdr (cdr x))))


   (defthm cdr-last-of-svex-alist-alist-fix
     (equal (final-cdr (svex-alist-alist-fix x))
            (final-cdr x))
     :hints(("Goal" :in-theory (enable last svex-alist-alist-fix)
             :induct (svex-alist-alist-fix x))))

   (defthm cdr-last-is-final-cdr
     (implies (consp x)
              (equal (cdr (last x))
                     (final-cdr x))))

   (defthm consp-of-svex-alist-alist-fix
     (equal (consp (svex-alist-alist-fix x))
            (consp (acl2::alist-fix x)))
     :hints(("Goal" :in-theory (enable svex-alist-alist-fix))))

   (defthm svex-alist-alist-fix-when-atom
     (implies (not (consp (acl2::alist-fix x)))
              (equal (svex-alist-alist-fix x)
                     (final-cdr x)))
     :hints(("Goal" :in-theory (enable svex-alist-alist-fix)))
     :rule-classes ((:rewrite :backchain-limit-lst 0)))

   (defthm svex-alist-alist-fix-of-hons-remove-assoc
     (equal (svex-alist-alist-fix (acl2::hons-remove-assoc k x))
            (acl2::hons-remove-assoc k (svex-alist-alist-fix x)))
     :hints(("Goal" :in-theory (enable svex-alist-alist-fix))))

   (defthm fast-alist-clean-of-svex-alist-alist-fix
     (equal (fast-alist-clean (svex-alist-alist-fix x))
            (svex-alist-alist-fix (fast-alist-clean x)))
     :hints (("goal" :in-theory (e/d (acl2::fast-alist-clean-by-remove-assoc
                                      svex-alist-alist-fix
                                      last)
                                     (fast-alist-clean)))))

   (defthmd member-svar-alist-keys
     (iff (member k (svar-alist-keys x))
          (and (svar-p k)
               (svar-lookup k x)))
     :hints(("Goal" :in-theory (enable svar-alist-keys svar-lookup))))

   (defthm intersecting-keys-by-svar-lookup
     (implies (and (svar-lookup k a)
                   (svar-lookup k b))
              (intersectp-equal (svar-alist-keys a)
                                (svar-alist-keys b)))
     :hints(("Goal" :in-theory (enable svar-lookup svar-alist-keys
                                       member-svar-alist-keys))))




   (encapsulate nil
     (local
      (defthm svar-lookup-when-lookup-remove
        (implies (svar-lookup k (envmap->svex-alist
                                 (acl2::hons-remove-assoc env envmap)))
                 (svar-lookup k (envmap->svex-alist envmap)))
        :hints(("Goal" :in-theory (enable envmap->svex-alist acl2::hons-remove-assoc)))
        :rule-classes :forward-chaining))

     (local
      (defthm svar-lookup-when-lookup-in-assoc
        (implies (svar-lookup k (cdr (hons-assoc-equal env envmap)))
                 (svar-lookup k (envmap->svex-alist envmap)))
        :hints(("Goal" :in-theory (enable envmap->svex-alist hons-assoc-equal)))
        :rule-classes :forward-chaining))

     (defthm svar-lookup-in-envmap-lookup
       (implies (and (no-duplicatesp (svar-alist-keys (envmap->svex-alist envmap)))
                     (svar-lookup k (cdr (hons-assoc-equal env envmap))))
                (equal (svar-lookup k (svex-alist-fix (cdr (hons-assoc-equal env envmap))))
                       (svar-lookup k (envmap->svex-alist envmap))))
       :hints(("Goal" :in-theory (enable envmap->svex-alist
                                         hons-assoc-equal))))

     (defthm svar-lookup-in-envmap-lookup-clean
       (implies (and (no-duplicatesp (svar-alist-keys (envmap->svex-alist
                                                       (fast-alist-clean envmap))))
                     (svar-lookup k (cdr (hons-assoc-equal env envmap))))
                (equal (svar-lookup k (svex-alist-fix
                                       (cdr (hons-assoc-equal env envmap))))
                       (svar-lookup k (envmap->svex-alist
                                       (fast-alist-clean envmap)))))
       :hints (("goal" :use ((:instance svar-lookup-in-envmap-lookup
                              (envmap (fast-alist-clean envmap)))))))




     (defthm duplicate-keys-when-lookup-in-remove
       (implies (and (svar-lookup k (envmap->svex-alist (acl2::hons-remove-assoc env envmap)))
                     (svar-lookup k (cdr (hons-assoc-equal env envmap))))
                (not (no-duplicatesp (svar-alist-keys (envmap->svex-alist envmap)))))
       :hints(("Goal" :in-theory (enable envmap->svex-alist
                                         hons-assoc-equal
                                         acl2::hons-remove-assoc))))


     (defthm svar-lookup-in-envmap-to-term-lookup
       (implies (and (no-duplicatesp (svar-alist-keys (envmap->svex-alist envmap)))
                     (svar-lookup k (cdr (hons-assoc-equal env envmap))))
                (equal (svar-lookup k (envmap-entry-to-term-alist
                                       (cdr (hons-assoc-equal env envmap))
                                       env))
                       (svar-lookup k (envmap-to-term-alist envmap))))
       :hints(("Goal" :in-theory (enable envmap->svex-alist
                                         envmap-to-term-alist
                                         hons-assoc-equal
                                         lookup-in-envmap-entry-to-term-alist))))

     (defthm svar-lookup-in-envmap-to-term-lookup-clean
       (implies (and (no-duplicatesp (svar-alist-keys (envmap->svex-alist
                                                       (fast-alist-clean envmap))))
                     (svar-lookup k (cdr (hons-assoc-equal env envmap))))
                (equal (svar-lookup k (envmap-entry-to-term-alist
                                       (cdr (hons-assoc-equal env envmap))
                                       env))
                       (svar-lookup k (envmap-to-term-alist (fast-alist-clean envmap)))))
       :hints (("goal" :use ((:instance svar-lookup-in-envmap-to-term-lookup
                              (envmap (fast-alist-clean envmap))))))))

   (defthm svar-lookup-in-envmap-remove
     (implies (and (no-duplicatesp (svar-alist-keys (envmap->svex-alist envmap)))
                   (no-duplicatesp (alist-keys envmap))
                   (case-split (not (svar-lookup k (cdr (hons-assoc-equal env envmap))))))
              (equal (svar-lookup k (envmap->svex-alist
                                     (acl2::hons-remove-assoc env envmap)))
                     (svar-lookup k (envmap->svex-alist envmap))))
     :hints(("Goal" :in-theory (enable envmap->svex-alist
                                       hons-assoc-equal
                                       acl2::hons-remove-assoc))))


   (defthm alist-keys-of-remove-assoc
     (equal (alist-keys (acl2::hons-remove-assoc k x))
            (remove k (alist-keys x)))
     :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc))))

   (defthm no-duplicatesp-of-remove
     (implies (no-duplicatesp x)
              (no-duplicatesp (remove k x)))
     :hints(("Goal" :in-theory (enable remove))))

   (defthm no-duplicate-alist-keys-of-fast-alist-clean
     (no-duplicatesp (alist-keys (fast-alist-clean x)))
     :hints(("Goal" :in-theory (e/d (acl2::fast-alist-clean-by-remove-assoc)
                                    (fast-alist-clean)))))

   (defthm no-svar-lookup-in-remove-assoc
     (implies (and (no-duplicatesp (alist-keys envmap))
                   (not (svar-lookup k (envmap->svex-alist envmap))))
              (not (svar-lookup k (envmap->svex-alist (acl2::hons-remove-assoc env envmap)))))
     :hints(("Goal" :in-theory (enable acl2::hons-remove-assoc envmap->svex-alist))))

   (defthm no-svar-lookup-in-lookup
     (implies (not (svar-lookup k (envmap->svex-alist envmap)))
              (and (not (svar-lookup k (svex-alist-fix (cdr (hons-assoc-equal env envmap)))))
                   (not (svar-lookup k (cdr (hons-assoc-equal env envmap))))))
     :hints(("Goal" :in-theory (enable hons-assoc-equal envmap->svex-alist))))

   (defthm no-svar-lookup-in-lookup-clean
     (implies (not (svar-lookup k (envmap->svex-alist (fast-alist-clean envmap))))
              (and (not (svar-lookup k (svex-alist-fix (cdr (hons-assoc-equal env envmap)))))
                   (not (svar-lookup k (cdr (hons-assoc-equal env envmap))))))
     :hints(("Goal" :use ((:instance no-svar-lookup-in-lookup
                           (envmap (fast-alist-clean envmap)))))))

   (defthm svar-lookup-in-envmap-to-term-remove
     (implies (and (no-duplicatesp (svar-alist-keys (envmap->svex-alist envmap)))
                   (no-duplicatesp (alist-keys envmap))
                   (case-split (not (svar-lookup k (cdr (hons-assoc-equal env envmap))))))
              (equal (svar-lookup k (envmap-to-term-alist
                                     (acl2::hons-remove-assoc env envmap)))
                     (svar-lookup k (envmap-to-term-alist envmap))))
     :hints(("Goal" :in-theory (enable envmap->svex-alist
                                       envmap-to-term-alist
                                       lookup-in-envmap-entry-to-term-alist
                                       hons-assoc-equal
                                       acl2::hons-remove-assoc))))


   (defthm envmap->svar-alist-of-alist-fix
     (equal (envmap->svex-alist (acl2::alist-fix x))
            (envmap->svex-alist x))
     :hints(("Goal" :in-theory (enable envmap->svex-alist))))

   (defthm envmap-p-of-fast-alist-fork
     (implies (and (envmap-p a)
                   (envmap-p b))
              (envmap-p (fast-alist-fork a b)))
     :hints(("Goal" :in-theory (enable envmap-p))))

   (defthm envmap-p-of-fast-alist-clean
     (implies (envmap-p x)
              (envmap-p (fast-alist-clean x)))
     :hints(("Goal" :in-theory (enable envmap-p))))

   (defthm svdecomp-symenv-p-of-fast-alist-fork
     (implies (and (svdecomp-symenv-p a)
                   (svdecomp-symenv-p b))
              (svdecomp-symenv-p (fast-alist-fork a b)))
     :hints(("Goal" :in-theory (enable svdecomp-symenv-p))))

   (defthm final-cdr-of-svdecomp-symenv-p
     (implies (svdecomp-symenv-p x)
              (equal (final-cdr x) nil))
     :hints(("Goal" :in-theory (enable svdecomp-symenv-p))))

   (defthm svdecomp-symenv-p-of-fast-alist-clean
     (implies (svdecomp-symenv-p x)
              (svdecomp-symenv-p (fast-alist-clean x)))
     :hints(("Goal" :in-theory (enable svdecomp-symenv-p))))

   (encapsulate nil
     (local (defthm hons-assoc-equal-of-svar-fix-when-svar-alist-p
              (implies (svar-alist-p y)
                       (equal (hons-assoc-equal k y)
                              (and (svar-p k)
                                   (svar-lookup k y))))
              :hints(("Goal" :in-theory (enable svar-alist-p svar-lookup)))))

     (defthm svar-lookup-of-fast-alist-fork
       (implies (and (svar-alist-p x) (svar-alist-p y))
                (equal (svar-lookup k (fast-alist-fork x y))
                       (or (svar-lookup k y)
                           (svar-lookup k x))))
       :hints(("Goal" :in-theory (enable svar-lookup svar-alist-p))))

     (defthm svar-alist-p-when-atom
       (implies (not (consp x))
                (svar-alist-p x))
       :hints(("Goal" :in-theory (enable svar-alist-p)))
       :rule-classes ((:rewrite :backchain-limit-lst 0)))

     (defthm svar-lookup-of-fast-alist-clean
       (implies (svar-alist-p x)
                (equal (svar-lookup k (fast-alist-clean x))
                       (svar-lookup k x))))

     (defthm no-duplicate-svar-alist-keys-of-fast-alist-fork
       (implies (and (no-duplicatesp (svar-alist-keys y))
                     (svar-alist-p x)
                     (Svar-alist-p y))
                (no-duplicatesp (svar-alist-keys (fast-alist-fork x y))))
       :hints(("Goal" :in-theory (enable svar-alist-p svar-alist-keys
                                         member-svar-alist-keys))))

     (defthm no-duplicate-svar-alist-keys-of-fast-alist-clean
       (implies (svar-alist-p x)
                (no-duplicatesp (svar-alist-keys (fast-alist-clean x))))
       :hints(("Goal" :in-theory (enable svar-alist-keys)))))))


(acl2::defquant svdecomp-4vec-termp (x)
  (forall a
          (4vec-p (svdecomp-ev x a)))
  :rewrite :direct)

(defsection alist-collect-compositions
  :parents nil

  ;; (defthm fast-alist-clean-of-svex-alist-alist-fix
  ;;   (equal (envmap->svex-alist (fast-alist-clean (svex-alist-alist-fix x)))
  ;;          (envmap->svex-alist (fast-alist-clean x)))
  ;;   :hints(("Goal" :in-theory (e/d (acl2::fast-alist-clean-by-remove-assoc
  ;;                                   svex-alist-alist-fix
  ;;                                   envmap->svex-alist)
  ;;                                  (fast-alist-clean)))))

  ;; x is an alist some of whose values may be svex-eval terms.  We collect a base
  ;; env, consisting of the pairs whose values are not svex-eval-terms, and a
  ;; mapping from distinct svex-eval environments to svex term alists.  The union
  ;; of the svex-alist-evals of those svex term alists along with the base env is
  ;; equivalent to the original alist.
  (define alist-collect-compositions-aux ((x svdecomp-symenv-p)
                                          (base-env svdecomp-symenv-p)
                                          (envmap envmap-p "maps env terms to svex alists"))
    :progn t
    :parents nil
    :prepwork ((local (acl2::def-match-tree-rewrites
                        (svex-eval (quote (:? svex)) (:? env))
                        :prefix sveval-))
               (local (defthm match-tree-is-subst-tree-for-svar-lookup
                        (b* (((mv ok alist) (acl2::match-tree pat x alist)))
                          (implies ok
                                   (equal (svar-lookup k x)
                                          (svar-lookup k (acl2::subst-tree pat alist)))))
                        :hints(("Goal" :in-theory (enable acl2::match-tree-is-subst-tree)))))
               (local (in-theory (enable svar-alist-fix
                                         svar-alist-p
                                         svex-alist-alist-fix))))
    :returns (mv err
                 (base-env1 svdecomp-symenv-p
                            :hyp (and (svdecomp-symenv-p base-env)
                                      (svdecomp-symenv-p x)))
                 (envmap1 envmap-p
                          :hyp (and (envmap-p envmap)
                                    (svdecomp-symenv-p x))))
    (b* (((when (atom x)) (mv nil (svar-alist-fix base-env)
                              (svex-alist-alist-fix envmap)))
         ((unless (mbt (and (consp (car x)) (svar-p (caar x)))))
          (alist-collect-compositions-aux (cdr x) base-env envmap))
         ((acl2::when-match (cdar x) (svex-eval (quote (:? svex)) (:? env)))
          (b* (((unless (svex-p svex))
                (mv (msg "Bad svex: ~x0~%" svex) nil nil))
               (new-al (cons (cons (caar x) svex)
                             (svex-alist-fix (cdr (hons-get env envmap))))))
            (alist-collect-compositions-aux
             (cdr x) base-env (hons-acons env new-al envmap))))
         ((acl2::when-match (cdar x) (quote (:? val)))
          (b* (((unless (4vec-p val))
                (mv (msg "Bad constant: ~x0~%" val) nil nil))
               ;; Consider a quoted constant to be an svex-eval of a constant
               ;; under the empty environment.
               (svex (svex-quote val))
               (env ''nil)
               (new-al (cons (cons (caar x) svex)
                             (svex-alist-fix (cdr (hons-get env envmap))))))
            (alist-collect-compositions-aux
             (cdr x) base-env (hons-acons env new-al envmap)))))
      (alist-collect-compositions-aux
       (cdr x) (cons (mbe :logic (cons (caar x) (cdar x))
                          :exec (car x))
                     base-env) envmap))
         ;; ((unless (svar-p (caar x)))
         ;;  (mv (msg "Bad key: ~x0~%") nil nil))

    ///
    (local (in-theory (disable svar-alist-p fast-alist-clean
                               ;acl2::consp-under-iff-when-true-listp
                               (:d alist-collect-compositions-aux))))
    (local
     (progn
       (defthm alists-collect-compositions-aux-preserves-no-duplicate-keys
         (b* (((mv ?err ?base-env1 ?envmap1)
               (alist-collect-compositions-aux x base-env envmap)))
           (implies (no-duplicatesp
                     (append (svar-alist-keys x)
                             (svar-alist-keys base-env)
                             (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))
                    (no-duplicatesp
                     (append (svar-alist-keys base-env1)
                             (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap1)))))))
         :hints (("Goal"
                  :induct (alist-collect-compositions-aux x base-env envmap)
                  :expand ((svar-alist-keys x)
                           (:with acl2::fast-alist-clean-by-remove-assoc
                            (:free (a b) (fast-alist-clean (cons a b))))
                           (fast-alist-clean nil)
                           (:free (a b) (svar-alist-keys (cons a b)))
                           (:free (a b) (envmap->svex-alist (cons a b)))
                           (alist-collect-compositions-aux x base-env envmap)))))

       (defthm alists-collect-compositions-aux-preserves-base-env-lookup
         (b* (((mv ?err ?base-env1 ?envmap1)
               (alist-collect-compositions-aux x base-env envmap)))
           (implies (and (svar-lookup k base-env)
                         (not err)
                         (force
                          (no-duplicatesp
                           (append (svar-alist-keys x)
                                   (svar-alist-keys base-env)
                                   (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))))
                    (equal (svar-lookup k base-env1)
                           (svar-lookup k base-env))))
         :hints (("Goal" :in-theory (e/d (member-svar-alist-keys))
                  :induct (alist-collect-compositions-aux x base-env envmap)
                  :expand ((svar-alist-keys x)
                           (:with acl2::fast-alist-clean-by-remove-assoc
                            (:free (a b) (fast-alist-clean (cons a b))))
                           (:free (a b) (svar-alist-keys (cons a b)))
                           (:free (a b) (envmap->svex-alist (cons a b)))
                           (alist-collect-compositions-aux x base-env envmap)))))

       (defthm alists-collect-compositions-aux-preserves-envmap-lookup
         (b* (((mv ?err ?base-env1 ?envmap1)
               (alist-collect-compositions-aux x base-env envmap)))
           (implies (and (svar-lookup k (envmap->svex-alist
                                         (fast-alist-clean envmap)))
                         (not err)
                         (force
                          (no-duplicatesp
                           (append (svar-alist-keys x)
                                   (svar-alist-keys base-env)
                                   (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))))
                    (equal (svar-lookup k (envmap->svex-alist
                                           (fast-alist-clean envmap1)))
                           (svar-lookup k (envmap->svex-alist
                                           (fast-alist-clean envmap))))))
         :hints (("Goal" :in-theory (e/d (member-svar-alist-keys))
                  :induct (alist-collect-compositions-aux x base-env envmap)
                  :expand ((svar-alist-keys x)
                           (:with acl2::fast-alist-clean-by-remove-assoc
                            (:free (a b) (fast-alist-clean (cons a b))))
                           (:free (a b) (svar-alist-keys (cons a b)))
                           (:free (a b) (envmap->svex-alist (cons a b)))
                           (alist-collect-compositions-aux x base-env envmap)))))

       (defthm alists-collect-compositions-aux-preserves-envmap-to-term-lookup
         (b* (((mv ?err ?base-env1 ?envmap1)
               (alist-collect-compositions-aux x base-env envmap)))
           (implies (and (svar-lookup k (envmap->svex-alist
                                         (fast-alist-clean envmap)))
                         (not err)
                         (force
                          (no-duplicatesp
                           (append (svar-alist-keys x)
                                   (svar-alist-keys base-env)
                                   (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))))
                    (equal (svar-lookup k (envmap-to-term-alist
                                           (fast-alist-clean envmap1)))
                           (svar-lookup k (envmap-to-term-alist
                                           (fast-alist-clean envmap))))))
         :hints (("Goal" :in-theory (e/d (member-svar-alist-keys
                                          lookup-in-envmap-entry-to-term-alist))
                  :induct (alist-collect-compositions-aux x base-env envmap)
                  :expand ((svar-alist-keys x)
                           (:with acl2::fast-alist-clean-by-remove-assoc
                            (:free (a b) (fast-alist-clean (cons a b))))
                           (:free (a b) (svar-alist-keys (cons a b)))
                           (:free (a b) (envmap->svex-alist (cons a b)))
                           (:free (a b) (envmap-to-term-alist (cons a b)))
                           (:free (a b env) (envmap-entry-to-term-alist (cons a b) env))
                           (alist-collect-compositions-aux x base-env envmap)))))

       (defthm alists-collect-compositions-aux-not-base-env-from-envmap
         (b* (((mv ?err ?base-env1 ?envmap1)
               (alist-collect-compositions-aux x base-env envmap)))
           (implies (and (svar-lookup k (envmap->svex-alist
                                         (fast-alist-clean envmap)))
                         (not err)
                         (force
                          (no-duplicatesp
                           (append (svar-alist-keys x)
                                   (svar-alist-keys base-env)
                                   (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))))
                    (not (svar-lookup k base-env1))))
         :hints (("goal" :use alists-collect-compositions-aux-preserves-no-duplicate-keys
                  :in-theory (disable alists-collect-compositions-aux-preserves-no-duplicate-keys)
                  :do-not-induct t)))

       (defthm intersecting-keys-by-svar-lookup-2
         (implies (and (svar-lookup k b)
                       (svar-lookup k a))
                  (intersectp-equal (svar-alist-keys a)
                                    (svar-alist-keys b)))
         :hints(("Goal" :in-theory (enable svar-lookup svar-alist-keys
                                           member-svar-alist-keys))))

       (defthm alists-collect-compositions-aux-not-envmap-from-base-env
         (b* (((mv ?err ?base-env1 ?envmap1)
               (alist-collect-compositions-aux x base-env envmap)))
           (implies (and (svar-lookup k base-env)
                         (not err)
                         (force
                          (no-duplicatesp
                           (append (svar-alist-keys x)
                                   (svar-alist-keys base-env)
                                   (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))))
                    (not (svar-lookup k (envmap->svex-alist (fast-alist-clean envmap1))))))
         :hints (("goal" :use alists-collect-compositions-aux-preserves-no-duplicate-keys
                  :in-theory (disable alists-collect-compositions-aux-preserves-no-duplicate-keys)
                  :do-not-induct t)))


       (defthm alists-collect-compositions-aux-new-envmap-lookup
         (b* (((mv ?err ?base-env1 ?envmap1)
               (alist-collect-compositions-aux x base-env envmap)))
           (implies (and (svar-lookup k (envmap->svex-alist (fast-alist-clean envmap1)))
                         (not (svar-lookup k (envmap->svex-alist (fast-alist-clean envmap))))
                         (not err)
                         (force
                          (no-duplicatesp
                           (append (svar-alist-keys x)
                                   (svar-alist-keys base-env)
                                   (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))))
                    (equal (svdecomp-ev
                            (cdr (svar-lookup k (envmap-to-term-alist (fast-alist-clean envmap1))))
                            a)
                           (svdecomp-ev (cdr (svar-lookup k x)) a))))
         :hints (("Goal" :in-theory (e/d (member-svar-alist-keys))
                  :induct (alist-collect-compositions-aux x base-env envmap)
                  :expand ((svar-alist-keys x)
                           (:with acl2::fast-alist-clean-by-remove-assoc
                            (:free (a b) (fast-alist-clean (cons a b))))
                           (svar-lookup k x)
                           (:free (a b) (svar-alist-keys (cons a b)))
                           (:free (a b) (envmap->svex-alist (cons a b)))
                           (:free (a b) (envmap-to-term-alist (cons a b)))
                           (:free (a b env) (envmap-entry-to-term-alist (cons a b) env))
                           (alist-collect-compositions-aux x base-env envmap)))
                 (and stable-under-simplificationp
                      '(:in-theory (enable acl2::fast-alist-clean-by-remove-assoc
                                           envmap->svex-alist)))))

       (defthm alists-collect-compositions-aux-new-base-env-lookup
         (b* (((mv ?err ?base-env1 ?envmap1)
               (alist-collect-compositions-aux x base-env envmap)))
           (implies (and (case-split (not (svar-lookup k (envmap->svex-alist
                                                          (fast-alist-clean envmap1)))))
                         (not (svar-lookup k base-env))
                         (not err)
                         (force
                          (no-duplicatesp
                           (append (svar-alist-keys x)
                                   (svar-alist-keys base-env)
                                   (svar-alist-keys (envmap->svex-alist (fast-alist-clean envmap)))))))
                    (equal (svar-lookup k base-env1)
                           (svar-lookup k x))))
         :hints (("Goal" :in-theory (e/d (member-svar-alist-keys))
                  :induct (alist-collect-compositions-aux x base-env envmap)
                  :expand ((svar-alist-keys x)
                           (:with acl2::fast-alist-clean-by-remove-assoc
                            (:free (a b) (fast-alist-clean (cons a b))))
                           (svar-lookup k x)
                           (:free (a b) (svar-alist-keys (cons a b)))
                           (:free (a b) (envmap->svex-alist (cons a b)))
                           (alist-collect-compositions-aux x base-env envmap)))
                 (and stable-under-simplificationp
                      '(:in-theory (enable acl2::fast-alist-clean-by-remove-assoc
                                           envmap->svex-alist))))))))



  (define alist-collect-compositions ((x svdecomp-symenv-p))
    :progn t
    :returns (mv err
                 (base-env svdecomp-symenv-p :hyp :guard)
                 (envmap envmap-p :hyp :guard))
    :prepwork ((local (in-theory (e/d ()
                                      (fast-alist-clean
                                       acl2::hons-dups-p)))))
    (b* ((x (fast-alist-free (fast-alist-clean (svar-alist-fix x))))
         ((mv err base-env envmap)
          (alist-collect-compositions-aux x nil nil)))
      (mv err base-env (fast-alist-clean envmap)))
    ///

    (defthm alist-collect-compositions-envmap-lookup-eval
      (b* (((mv ?err ?base-env ?envmap) (alist-collect-compositions x)))
        (implies (and (svar-lookup k (envmap->svex-alist envmap))
                      (not err))
                 (equal (svdecomp-ev
                         (cdr (svar-lookup k (envmap-to-term-alist envmap)))
                         a)
                        (svdecomp-ev (cdr (svar-lookup k x)) a)))))


    (defthm eval-lookup-in-envmap-entry-to-term-alist
      (implies (svar-lookup k (svex-alist-fix svalist))
               (equal (svdecomp-ev (cdr (svar-lookup k (envmap-entry-to-term-alist
                                                        svalist env)))
                                   a)
                      (svex-eval (cdr (svar-lookup k svalist))
                                 (svdecomp-ev env a))))
      :hints(("Goal" :in-theory (enable envmap-entry-to-term-alist
                                        svar-lookup svex-alist-fix))))

    (defthm 4vec-p-lookup-in-envmap-to-term-alist
      (implies (svar-lookup k (envmap->svex-alist envmap))
               (4vec-p (svdecomp-ev (cdr (svar-lookup k (envmap-to-term-alist envmap))) a)))
      :hints(("Goal" :in-theory (enable envmap-to-term-alist
                                        envmap->svex-alist
                                        lookup-in-envmap-entry-to-term-alist))))

    (defthm alist-collect-compositions-envmap-implies-4vec-term
      (b* (((mv ?err ?base-env ?envmap) (alist-collect-compositions x)))
        (implies (and (svar-lookup k (envmap->svex-alist envmap))
                      (not err))
                 (svdecomp-4vec-termp (cdr (svar-lookup k x)))))
      :hints (("goal" :in-theory (disable alist-collect-compositions))
              (acl2::witness :ruleset svdecomp-4vec-termp-witnessing)
              (and stable-under-simplificationp
                   '(:use ((:instance alist-collect-compositions-envmap-lookup-eval
                            (a a0)))
                     :in-theory (disable alist-collect-compositions-envmap-lookup-eval
                                         alist-collect-compositions))))
      :rule-classes :forward-chaining)

    (defthm alist-collect-compositions-base-env-lookup
      (b* (((mv ?err ?base-env ?envmap) (alist-collect-compositions x)))
        (implies (and (case-split (not (svar-lookup k (envmap->svex-alist envmap))))
                      (not err))
                 (equal (svar-lookup k base-env)
                        (svar-lookup k x)))))))

(local
 (defthm svar-lookup-in-svdecomp-ev-envmap
   (equal (svar-lookup k (svdecomp-ev-envmap envmap a))
          (and (svar-lookup k (envmap->svex-alist envmap))
               (cons (svar-fix k)
                     (svdecomp-ev (cdr (svar-lookup k (envmap-to-term-alist envmap))) a))))
   :hints(("Goal" :in-theory (enable svdecomp-ev-envmap envmap-to-term-alist
                                     envmap->svex-alist
                                     lookup-in-envmap-entry-to-term-alist)))))




(defmacro quote-4vec-x ()
  `'',(4vec-x))

;; (define svdecomp-symenv-lookup ((k svar-p) (x svdecomp-symenv-p))
;;   (mbe :logic (if (atom x)
;;                   nil
;;                 (if (and (consp (car x))
;;                          (equal (svar-fix (caar x)) (svar-fix k)))
;;                     (cons (svar-fix (caar x)) (cdar x))
;;                   (svdecomp-symenv-lookup k (cdr x))))
;;        :exec (hons-get k x))
;;   ///
;;   (deffixequiv svdecomp-symenv-lookup :args (k))

;;   (defthm eval-of-svdecomp-symenv-lookup
;;     (implies (svdecomp-symenv-lookup k env)
;;              (equal (svdecomp-ev (cdr (svdecomp-symenv-lookup k env)) a)
;;                     (cdr (svar-lookup (svar-fix k) (svdecomp-ev-symenv env a)))))
;;     :hints(("Goal" :in-theory (enable svdecomp-ev-symenv))))

;;   (defthm lookup-in-svdecomp-ev-symenv-iff-symenv-lookup
;;     (implies (svar-p k)
;;              (iff (svar-lookup k (svdecomp-ev-symenv env a))
;;                   (svdecomp-symenv-lookup k env)))
;;     :hints(("Goal" :in-theory (enable svdecomp-ev-symenv))))

(local
 (defthm pseudo-termp-lookup-in-svdecomp-symenv-p
   (implies (svdecomp-symenv-p x)
            (pseudo-termp (cdr (svar-lookup k x))))
   :hints(("Goal" :in-theory (enable svar-lookup)))))

(define svdecomp-env-extract ((keys svarlist-p) (env svdecomp-symenv-p))
  :prepwork ((local (in-theory (enable svarlist-p svarlist-fix))))
  :returns (res svdecomp-symenv-p :hyp (svdecomp-symenv-p env))
  (if (atom keys)
      nil
    (cons (cons (svar-fix (car keys))
                (let ((look (svar-lookup (car keys) env)))
                  (if look (cdr look) (quote-4vec-x))))
          (svdecomp-env-extract (cdr keys) env)))
  ///

  (local (defthm car-of-svar-lookup
           (equal (car (svar-lookup k env))
                  (and (svar-lookup k env) (svar-fix k)))
           :hints(("Goal" :in-theory (enable svar-lookup)))))

  (defthm svar-lookup-in-svdecomp-env-extract
    (equal (svar-lookup k (svdecomp-env-extract keys env))
           (and (member (svar-fix k) (svarlist-fix keys))
                (or (svar-lookup k env)
                    (cons (svar-fix k) (quote-4vec-x)))))
    :hints(("Goal" :in-theory (enable svar-lookup))))

  ;; (defthm alist-keys-of-svdecomp-ev-symenv
  ;;   (equal (svar-alist-keys (svdecomp-ev-symenv env a))
  ;;          (svar-alist-keys env))
  ;;   :hints(("Goal" :in-theory (enable svdecomp-ev-symenv svar-alist-keys))))

  ;; (defthm svarlist-p-alist-keys-of-svdecomp-symenv
  ;;   (implies (svdecomp-symenv-p env)
  ;;            (svarlist-p (alist-keys env)))
  ;;   :hints(("Goal" :in-theory (enable svdecomp-symenv-p))))

  (defthm svex-env-lookup-in-svdecomp-ev-symenv
    (equal (svex-env-lookup k (svdecomp-ev-symenv env a))
           (let ((pair (svar-lookup k env)))
             (if pair
                 (4vec-fix (svdecomp-ev (cdr pair) a))
               (4vec-x))))
    :hints(("Goal" :in-theory (enable svex-env-lookup svdecomp-ev-symenv svar-lookup))))

  (defthm eval-of-svdecomp-env-extract
    (svex-env-equiv (svdecomp-ev-symenv (svdecomp-env-extract keys env) a)
                    (svex-env-extract keys (svdecomp-ev-symenv env a)))
    :hints(("Goal" :in-theory (enable svdecomp-ev-symenv
                                      svex-env-extract
                                      svarlist-p
                                      alist-keys))))

  (defthm keys-of-svdecomp-env-extract
    (equal (svar-alist-keys (svdecomp-env-extract keys env))
           (svarlist-fix keys))
    :hints(("Goal" :in-theory (enable svar-alist-keys)))))

(local
 (defthm collect-vars-of-alist-vals
   (set-equiv (svexlist-vars (svex-alist-vals x))
              (svex-alist-vars x))
   :hints(("Goal" :in-theory (enable svexlist-vars svex-alist-vals svex-alist-vars)))))

(define envmap-entry-extract-env ((x svex-alist-p) (env svdecomp-symenv-p))
  :returns (res svdecomp-symenv-p :hyp (svdecomp-symenv-p env))
  (b* ((keys (mergesort (cwtime (svexlist-collect-vars (svex-alist-vals x))))))
    (with-fast-alist env (svdecomp-env-extract keys env)))
  ///
  (defthm svex-alist-eval-under-envmap-entry-extract-env
    (equal (svex-alist-eval x (svdecomp-ev-symenv (envmap-entry-extract-env x env) a))
           (svex-alist-eval x (svdecomp-ev-symenv env a))))

  (defthm lookup-vars-subset-of-alist-vars
    (subsetp (svex-vars (cdr (svar-lookup k x)))
             (svex-alist-vars x))
    :hints(("Goal" :in-theory (enable svex-alist-vars))))

  (defthm eval-lookup-in-svdecomp-ev-symenv
    (equal (svex-eval (cdr (svar-lookup k x))
                      (svdecomp-ev-symenv
                       (envmap-entry-extract-env x env) a))
           (svex-eval (cdr (svar-lookup k x ))
                      (svdecomp-ev-symenv env a))))

  (defthm keys-of-envmap-entry-extract-env
    (set-equiv (svar-alist-keys (envmap-entry-extract-env x env))
               (svex-alist-vars x)))

  (local (defthm svex-env-lookup-in-terms-of-svar-lookup
           (equal (svex-env-lookup k x)
                  (let ((pair (svar-lookup k x)))
                    (if pair
                        (4vec-fix (cdr pair))
                      (4vec-x))))
           :hints(("Goal" :in-theory (enable svex-env-lookup svar-lookup
                                             svex-env-fix)))))
  (defthm ev-lookup-of-envmap-entry-extract-env
    (implies (member (svar-fix k) (svex-alist-vars x))
             (4vec-equiv (svdecomp-ev (cdr (svar-lookup k (envmap-entry-extract-env x env))) a)
                         (svex-env-lookup k (svdecomp-ev-symenv env a))))))

(local
 (progn
   (defthm 4vec-p-lookup-in-svex-env
     (implies (and (svex-env-p x)
                   (svar-lookup k x))
              (4vec-p (cdr (svar-lookup k x))))
     :hints(("Goal" :in-theory (enable svex-env-p))))

   (defthm svar-alist-p-when-svex-env-p
     (implies (svex-env-p x)
              (svar-alist-p x))
     :hints(("Goal" :in-theory (enable svex-env-p svar-alist-p))))))


;; this should also maybe be somewhere else
(define svex-env-compat-union ((x svex-env-p)
                               (y svex-env-p))
  :prepwork ((local (in-theory (enable svex-env-fix))))
  :returns (mv err (union svex-env-p))
  :hooks ((:fix :hints (("goal" :induct (svex-env-compat-union x y)
                         :expand ((svex-env-compat-union x y)
                                  (svex-env-compat-union (svex-env-fix x) y)
                                  (svex-env-compat-union x (svex-env-fix y)))))))
  (b* (((when (atom x)) (mv nil (svex-env-fix y)))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x))))) (svex-env-compat-union (cdr x) y))
       ((cons var val) (car x))
       (val (4vec-fix val))
       (look (svar-lookup var (svex-env-fix y)))
       ((unless (or (not look)
                    (equal (4vec-fix (cdr look)) val)))
        (mv (msg "Mismatch: key ~x0, val ~x1 versus ~x2~%"  var val (4vec-fix (cdr look))) nil)))
    (svex-env-compat-union (cdr x) (if look y (hons-acons var val y))))
  ///

  (defthm svar-lookup-in-svex-env-fix
    (equal (svar-lookup k (svex-env-fix env))
           (and (svar-lookup k env)
                (cons (svar-fix k) (4vec-fix (cdr (svar-lookup k env))))))
    :hints(("Goal" :in-theory (enable svar-lookup svex-env-fix))))

  (defthm lookup-in-compat-union-2
    (b* (((mv err union) (svex-env-compat-union x y)))
      (implies (and (svar-lookup k (svex-env-fix y))
                    (not err))
               (equal (svar-lookup k union)
                      (svar-lookup k (svex-env-fix y))))))

  (local (defthm 4vec-p-lookup-in-svex-env
           (implies (and (svex-env-p x)
                         (svar-lookup k x))
                    (4vec-p (cdr (svar-lookup k x))))
           :hints(("Goal" :in-theory (enable svex-env-p)))))

  (local (defthm car-of-svar-lookup
           (equal (car (svar-lookup k env))
                  (and (svar-lookup k env) (svar-fix k)))
           :hints(("Goal" :in-theory (enable svar-lookup)))))

  ;; (local (in-theory (enable svar-lookup)))

  (defthm lookup-in-compat-union-1
    (b* (((mv err union) (svex-env-compat-union x y)))
      (implies (and (svar-lookup k (svex-env-fix x))
                    (not err))
               (equal (svar-lookup k union)
                      (svar-lookup k (svex-env-fix x)))))
    :hints(("Goal" :in-theory (enable svex-env-fix))))

  (defthm lookup-in-compat-union-neither
    (b* (((mv ?err union) (svex-env-compat-union x y)))
      (implies (and (not (svar-lookup k (svex-env-fix x)))
                    (not (svar-lookup k (svex-env-fix y))))
               (equal (svar-lookup k union) nil)))
    :hints(("Goal" :in-theory (enable svex-env-fix))))

  (local (in-theory (disable svex-env-compat-union)))

  (local (defthm svex-env-lookup-redef
           (equal (svex-env-lookup k x)
                  (let ((pair (svar-lookup k (svex-env-fix x))))
                    (if pair
                        (cdr pair)
                      (4vec-x))))
           :hints(("Goal" :in-theory (enable svex-env-lookup svar-lookup svex-env-fix)))))

  (defthmd compat-union-reduce-to-append
    (b* (((mv err union) (svex-env-compat-union x y)))
      (implies (not err)
               (svex-envs-similar union (append x y))))
    :hints ((acl2::witness :ruleset svex-envs-similar-witnessing)
            (and stable-under-simplificationp
                 '(:cases ((svar-lookup k0 (svex-env-fix y)))))))

  (local (in-theory (enable member-svar-alist-keys)))

  (defthm-svex-eval-flag
    (defthm svex-eval-compat-union-when-vars-in-first
      (b* (((mv err union) (svex-env-compat-union env env2)))
        (implies (and (subsetp (svex-vars x) (svar-alist-keys (svex-env-fix env)))
                      (not err))
                 (equal (svex-eval x union)
                        (svex-eval x env))))
      :hints ('(:expand ((:free (env) (svex-eval x env))
                         (svex-vars x))))
      :flag expr)
    (defthm svexlist-eval-compat-union-when-vars-in-first
      (b* (((mv err union) (svex-env-compat-union env env2)))
        (implies (and (subsetp (svexlist-vars x) (svar-alist-keys (svex-env-fix env)))
                      (not err))
                 (equal (svexlist-eval x union)
                        (svexlist-eval x env))))
      :hints ('(:expand ((:free (env) (svexlist-eval x env))
                         (svexlist-vars x))))
      :flag list))

  (defthm svex-alist-eval-compat-union-when-vars-in-first
    (b* (((mv err union) (svex-env-compat-union env env2)))
        (implies (and (subsetp (svex-alist-vars x) (svar-alist-keys (svex-env-fix env)))
                      (not err))
                 (equal (svex-alist-eval x union)
                        (svex-alist-eval x env))))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars))))


  (defthm-svex-eval-flag
    (defthm svex-eval-compat-union-when-vars-in-second
      (b* (((mv err union) (svex-env-compat-union env env2)))
        (implies (and (subsetp (svex-vars x) (svar-alist-keys (svex-env-fix env2)))
                      (not err))
                 (equal (svex-eval x union)
                        (svex-eval x env2))))
      :hints ('(:expand ((:free (env) (svex-eval x env))
                         (svex-vars x)))
              (and stable-under-simplificationp
                   '(:in-theory (enable svex-env-lookup))))
      :flag expr)
    (defthm svexlist-eval-compat-union-when-vars-in-second
      (b* (((mv err union) (svex-env-compat-union env env2)))
        (implies (and (subsetp (svexlist-vars x) (svar-alist-keys (svex-env-fix env2)))
                      (not err))
                 (equal (svexlist-eval x union)
                        (svexlist-eval x env2))))
      :hints ('(:expand ((:free (env) (svexlist-eval x env))
                         (svexlist-vars x))))
      :flag list))

  (defthm svex-alist-eval-compat-union-when-vars-in-second
    (b* (((mv err union) (svex-env-compat-union env env2)))
        (implies (and (subsetp (svex-alist-vars x) (svar-alist-keys (svex-env-fix env2)))
                      (not err))
                 (equal (svex-alist-eval x union)
                        (svex-alist-eval x env2))))
    :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-vars))))

  (local (in-theory (enable svex-env-compat-union)))

  (defthm alist-keys-of-svex-env-compat-union
    (b* (((mv err union) (svex-env-compat-union env env2)))
      (implies (not err)
               (set-equiv (svar-alist-keys union)
                          (append (svar-alist-keys (svex-env-fix env))
                                  (svar-alist-keys (svex-env-fix env2))))))
    :hints(("Goal" :in-theory (enable svex-alist-keys svarlist-fix svar-lookup)
            :induct t)
           (acl2::witness :ruleset acl2::set-reasoning-no-consp))))


(define svdecomp-symenv-compat-union ((x svdecomp-symenv-p) (y svdecomp-symenv-p))
  :prepwork ((local (in-theory (enable svar-alist-fix))))
  :returns (mv err (union svdecomp-symenv-p :hyp :guard))
  (b* (((when (atom x)) (mv nil (svar-alist-fix y)))
       ((unless (mbt (and (consp (car x)) (svar-p (caar x))))) (svdecomp-symenv-compat-union (cdr x) y))
       ((cons var val) (car x))
       (look (svar-lookup var (svar-alist-fix y)))
       ((unless (or (not look)
                    (equal (cdr look) val)))
        (mv (msg "Mismatch: key ~x0, val ~x1 versus ~x2~%"  var val (cdr look)) nil)))
    (svdecomp-symenv-compat-union (cdr x) (if look y (hons-acons var val y))))
  ///

  (local (defthm car-of-svar-lookup
           (equal (car (svar-lookup k env))
                  (and (svar-lookup k env) (svar-fix k)))
           :hints(("Goal" :in-theory (enable svar-lookup)))))

  (defthm svdecomp-symenv-compat-union-error-cond
    (b* (((mv symerr ?symunion) (svdecomp-symenv-compat-union x y))
         ((mv err ?union) (svex-env-compat-union (svdecomp-ev-symenv x a)
                                                (svdecomp-ev-symenv y a))))
      (implies (not symerr)
               (not err)))
    :hints(("Goal" :in-theory (enable svex-env-compat-union
                                      svdecomp-ev-symenv))))

  (defthm eval-svdecomp-symenv-compat-union
    (b* (((mv symerr ?symunion) (svdecomp-symenv-compat-union x y))
         ((mv ?err ?union) (svex-env-compat-union (svdecomp-ev-symenv x a)
                                                  (svdecomp-ev-symenv y a))))
      (implies (not symerr)
               (svex-env-equiv (svdecomp-ev-symenv symunion a)
                               union)))
    :hints(("Goal" :in-theory (enable svdecomp-ev-symenv
                                      svex-env-compat-union))))

  ;; (defthm lookup-exists-in-svdecomp-symenv-compat-union
  ;;   (b* (((mv symerr ?symunion) (svdecomp-symenv-compat-union x y)))
  ;;     (implies (not symerr)
  ;;              (iff (svar-lookup k symunion)
  ;;                   (or (svar-lookup k x)
  ;;                       (svar-lookup k y)))))
  ;;   :hints (("goal" :induct (svdecomp-symenv-compat-union x y))))

  (defthm lookup-in-svdecomp-symenv-compat-union-when-in-y
    (b* (((mv symerr ?symunion) (svdecomp-symenv-compat-union x y)))
      (implies (and (not symerr)
                    (svar-lookup k y))
               (equal (svar-lookup k symunion)
                      (svar-lookup k y))))
    :hints(("Goal" :in-theory (enable svar-lookup))))

  (defthm lookup-in-svdecomp-symenv-compat-union-when-not-in-y
    (b* (((mv symerr ?symunion) (svdecomp-symenv-compat-union x y)))
      (implies (and (not symerr)
                    (case-split (not (svar-lookup k y))))
               (equal (svar-lookup k symunion)
                      (svar-lookup k x)))))

  (defthm lookup-in-svdecomp-symenv-compat-union-when-in-x
    (b* (((mv symerr ?symunion) (svdecomp-symenv-compat-union x y)))
      (implies (and (not symerr)
                    (svar-lookup k x))
               (equal (svar-lookup k symunion)
                      (svar-lookup k x))))
    :hints(("Goal" :in-theory (enable svar-lookup))))

  (defthm lookup-in-svdecomp-symenv-compat-union-when-not-in-x
    (b* (((mv symerr ?symunion) (svdecomp-symenv-compat-union x y)))
      (implies (and (not symerr)
                    (case-split (not (svar-lookup k x))))
               (equal (svar-lookup k symunion)
                      (svar-lookup k y)))))

  (local (defthm list-car-when-cdr-is-nil
           (implies (and (consp x) (not (Cdr x)))
                    (equal (list (car x)) x))))


  ;; (defthm eval-lookup-in-symenv-compat-union
  ;;   (b* (((mv symerr ?symunion) (svdecomp-symenv-compat-union x y))
  ;;        ((mv ?err ?union) (svex-env-compat-union (svdecomp-ev-symenv x a)
  ;;                                                 (svdecomp-ev-symenv y a))))
  ;;    (implies (and (not symerr)
  ;;                  (svdecomp-symenv-p x)
  ;;                  (svdecomp-symenv-p y)
  ;;                  (svar-lookup k symunion))
  ;;             (4vec-equiv (svdecomp-ev (cdr (svar-lookup k symunion)) a)
  ;;                         (cdr (svar-lookup k union)))))
  ;;   :hints(("Goal" :in-theory (enable svdecomp-ev-symenv
  ;;                                     svex-env-compat-union))))


  ;; (local (defthmd svdecomp-symenv-lookup-iff-member-svarlist-fix-keys
  ;;          (iff (svdecomp-symenv-lookup k env)
  ;;               (member (svar-fix k) (svarlist-fix (alist-keys env))))
  ;;          :hints(("Goal" :in-theory (enable svdecomp-symenv-lookup
  ;;                                            svarlist-fix
  ;;                                            alist-keys)))))

  ;; (defthm svarlist-p-alist-keys-fo-svdecomp-symenv
  ;;   (implies (svdecomp-symenv-p x)
  ;;            (svarlist-p (alist-keys x)))
  ;;   :hints(("Goal" :in-theory (enable svdecomp-symenv-p
  ;;                                     svarlist-p
  ;;                                     alist-keys))))

  (defthm alist-keys-of-svdecomp-symenv-compat-union
    (b* (((mv err union) (svdecomp-symenv-compat-union env env2)))
      (implies (not err)
               (set-equiv (svar-alist-keys union)
                          (append (svar-alist-keys env)
                                  (svar-alist-keys env2)))))
    :hints(("Goal" :in-theory (enable svar-alist-keys svarlist-fix)
            :induct t)
           (acl2::witness :ruleset acl2::set-reasoning-no-consp)
           (and stable-under-simplificationp
                '(:in-theory (enable member-svar-alist-keys))))))




(define envmap-extract-union-env ((envmap envmap-p))
  :returns (mv err (union svdecomp-symenv-p :hyp :guard))
  :verify-guards nil
  :prepwork ((local (in-theory (enable svex-alist-alist-fix))))
  (b* (((when (atom envmap)) (mv nil nil))
       ((unless (mbt (consp (car envmap))))
        (envmap-extract-union-env (cdr envmap)))
       ((mv err env-alist) (map-alist-term-keys-to-val-terms (caar envmap)))
       ((when err) (mv err nil))
       (first-env (envmap-entry-extract-env (cdar envmap) env-alist))
       ((mv err rest-env) (envmap-extract-union-env (cdr envmap)))
       ((when err) (mv err rest-env)))
    (svdecomp-symenv-compat-union first-env rest-env))
  ///
  (verify-guards envmap-extract-union-env)

  (defthm svex-alist-vars-of-append
    (set-equiv (svex-alist-vars (append a b))
               (append (svex-alist-vars a) (svex-alist-vars b)))
    :hints(("Goal" :in-theory (enable svex-alist-vars))))


  (defthm keys-of-envmap-extract-union-env
    (b* (((mv err union) (envmap-extract-union-env envmap)))
      (implies (not err)
               (set-equiv (svar-alist-keys union)
                          (svex-alist-vars (envmap->svex-alist envmap)))))
    :hints(("Goal" :in-theory (enable envmap->svex-alist
                                      svdecomp-ev-symenv))))

  (defthm lookup-exists-of-envmap-extract-union-env
    (b* (((mv err union) (envmap-extract-union-env envmap)))
      (implies (not err)
               (iff (svar-lookup k union)
                    (member (svar-fix k)
                            (svex-alist-vars (envmap->svex-alist envmap))))))
    :hints(("Goal" :use ((:instance member-svar-alist-keys
                          (x (mv-nth 1 (envmap-extract-union-env envmap)))
                          (k (svar-fix k))))
            :in-theory (disable member-svar-alist-keys)
            :do-not-induct t)))

  (defthm svex-env-fix-of-svar-alist-fix
    (equal (svex-env-fix (svar-alist-fix x))
           (svex-env-fix x))
    :hints(("Goal" :in-theory (enable svar-alist-fix svex-env-fix))))

  (defrefinement svar-alist-equiv svex-env-equiv
    :hints (("goal" :use ((:instance svex-env-fix-of-svar-alist-fix)
                          (:instance svex-env-fix-of-svar-alist-fix (x y)))
             :in-theory (disable svex-env-fix-of-svar-alist-fix))))



  (defthm svar-alist-keys-of-svdecomp-ev-symenv
    (equal (svar-alist-keys (svdecomp-ev-symenv x a))
           (svar-alist-keys x))
    :hints(("Goal" :in-theory (enable svar-alist-keys svdecomp-ev-symenv))))

  (defthm envmap-extract-union-env-correct
    (b* (((mv err union) (envmap-extract-union-env envmap))
         (svalist (envmap->svex-alist envmap)))
      (implies (not err)
               (equal (svex-alist-eval svalist (svdecomp-ev-symenv union a))
                      (svdecomp-ev-envmap envmap a))))
    :hints(("Goal" :in-theory (enable svdecomp-ev-envmap
                                      svex-alist-eval
                                      envmap->svex-alist))))

  (defthm envmap-extract-union-env-correct-lookup-exists
    (b* (((mv err union) (envmap-extract-union-env envmap))
         (svalist (envmap->svex-alist envmap)))
      (implies (and (not err)
                    (svar-lookup k svalist))
               (equal (svex-eval (cdr (svar-lookup k svalist))
                                 (svdecomp-ev-symenv union a))
                      (cdr (svar-lookup k (svdecomp-ev-envmap envmap a))))))
    :hints (("goal" :in-theory (disable envmap-extract-union-env
                                        envmap-extract-union-env-correct
                                        svar-lookup-in-svdecomp-ev-envmap)
             :use ((:instance envmap-extract-union-env-correct))))))

(local
 (encapsulate nil
   ;; (local (defthm svex-env-lookup-of-append
   ;;          (equal (svex-env-lookup k (append a b))
   ;;                 (if (svar-lookup k a)
   ;;                     (svex-env-lookup k a)
   ;;                   (svex-env-lookup k b)))
   ;;          :hints(("Goal" :in-theory (enable svex-env-lookup svar-lookup svex-env-fix)))))

   (defcong svex-envs-similar svex-envs-similar (append a b) 2
     :hints ((acl2::Witness :ruleset svex-envs-similar-witnessing)))))




;; Goal: transform a term representing an svex evaluation environment env into two parts:
;;   - svalist, a concrete svex alist, and
;;   - env1, a term representing another environment,
;; such that (eval env a) is svex-envs-similar to
;;        (append (svex-alist-eval svalist (eval env1 a)) (eval env1 a))
;; That is, for any svex x, (svex-eval x (eval env a)) is equivalent to
;;               (svex-eval (svex-compose x svalist) (eval env1 a)).

;; Steps:
;; 1. Parse the term into an alist mapping (concrete) variables (svars) to
;;    terms representing their bindings.
;;    Implementation: map-alist-term-keys-to-val-terms.

;; 2. From that alist, look for pairs of the form (var . (svex-eval svex env))
;;    where svex is quoted.  Collect a mapping (env . ((var1 . svex1) ...))
;;    i.e. a mapping from environments to the var/svex pairs.
;;    Remove pairs of this form from the environment.
;;    Implementation: alist-collect-compositions.

;; 3. For each environment term mapped in the step above, parse it into an
;;    alist as in step 1, then extract the variables used in the svex alist
;;    that it is mapped to.  Union this with all other such environments,
;;    ensuring that there are no conflicting bindings.
;;    Implementation: envmap-extract-union-env.

;; 4. Union this environment with the base environment left from step 2.
;;    Implementation: svdecomp-symenv-compat-union.

;; 5. Return svalist, the union of all the svex alists bound in the env map,
;;    and env1, the full environment from step 4.

(define svex-decomp-process-env-term ((x svdecomp-symenv-p) (vars svarlist-p))
  :returns (mv err (sval svex-alist-p) (symenv svdecomp-symenv-p :hyp :guard))
  :hooks ((:fix :args (vars)))
  (b* (;; ((mv err xsymenv) (map-alist-term-keys-to-val-terms (hons-copy x)))
       ;; ((when err) (mv err nil nil))
       (xsymenv (with-fast-alist x (svdecomp-env-extract vars x)))
       ((mv err base-env envmap) (alist-collect-compositions xsymenv))
       ((when err) (mv err nil nil))
       ((mv err envunion) (envmap-extract-union-env envmap))
       ((when err) (mv err nil nil))
       ((mv err fullenv) (svdecomp-symenv-compat-union base-env envunion))
       ((when err) (mv err nil nil)))
    (mv nil (envmap->svex-alist envmap) fullenv))
  ///
  (local (defthm svex-env-lookup-in-terms-of-svar-lookup
           (equal (svex-env-lookup k x)
                  (let ((pair (svar-lookup k x)))
                    (if pair
                        (4vec-fix (cdr pair))
                      (4vec-x))))
           :hints(("Goal" :in-theory (enable svex-env-lookup svar-lookup
                                             svex-env-fix)))))

  (local (in-theory (disable LOOKUP-IN-SVDECOMP-SYMENV-COMPAT-UNION-WHEN-NOT-IN-Y
                             LOOKUP-IN-SVDECOMP-SYMENV-COMPAT-UNION-WHEN-IN-Y)))


  (acl2::defexample svdecomp-4vec-termp-ex
    :pattern (svdecomp-ev x a)
    :templates (a)
    :instance-rulename svdecomp-4vec-termp-instancing)

  (local (defthm 4vec-p-of-svar-lookup-by-svdecomp-4vec-termp
           (implies (and (SVDECOMP-4VEC-TERMP
                          (CDR
                           (SVAR-LOOKUP
                            K
                            (SVDECOMP-ENV-EXTRACT VARS x))))
                         (member (svar-fix k) (svarlist-fix vars))
                         (svar-lookup k (svdecomp-ev-symenv x a)))
                    (4vec-p (svdecomp-ev (cdr (svar-lookup k x)) a)))
           :hints ((acl2::witness :ruleset svdecomp-4vec-termp-ex))))

  (defthm svex-decomp-process-env-correct
    (b* (((mv err sval symenv) (svex-decomp-process-env-term x vars))
         (env (svdecomp-ev-symenv symenv a)))
      (implies (And (not err)
                    (member (svar-fix k) (svarlist-fix vars)))
               (and (implies (svar-lookup k sval)
                             (4vec-equiv (svex-eval (cdr (svar-lookup k sval)) env)
                                         (svex-env-lookup k (svdecomp-ev-symenv x a))))
                    (implies (not (svar-lookup k sval))
                             (and (svar-lookup k symenv)
                                  (4vec-equiv (svdecomp-ev (cdr (svar-lookup k symenv)) a)
                                              (svex-env-lookup k (svdecomp-ev-symenv x a))))))))
    :hints (("goal" :do-not-induct t))
    :otf-flg t)

  (local (in-theory (disable svex-decomp-process-env-term)))

  (defthm-svex-eval-flag
    (defthm svex-eval-with-svex-decomp-process-env
      (b* (((mv err sval symenv) (svex-decomp-process-env-term env1 vars))
           (env (svdecomp-ev-symenv symenv a)))
        (implies (And (not err)
                      (double-rewrite (subsetp (svex-vars x) (svarlist-fix vars))))
                 (equal (svex-eval x (append (svex-alist-eval sval env)
                                             env))
                        (svex-eval x (svdecomp-ev-symenv env1 a)))))
      :hints ('(:expand ((:free (env) (svex-eval x env))
                         (svex-vars x))))
      :flag expr)
    (defthm svexlist-eval-with-svex-decomp-process-env
      (b* (((mv err sval symenv) (svex-decomp-process-env-term env1 vars))
           (env (svdecomp-ev-symenv symenv a)))
        (implies (And (not err)
                      (double-rewrite (subsetp (svexlist-vars x) (svarlist-fix vars))))
                 (equal (svexlist-eval x (append (svex-alist-eval sval env)
                                             env))
                        (svexlist-eval x (svdecomp-ev-symenv env1 a)))))
      :hints ('(:expand ((:free (env) (svexlist-eval x env))
                         (svexlist-vars x))))
      :flag list))

  (local (in-theory (enable svex-decomp-process-env-term))))

(define svdecomp-symenv->term ((x svdecomp-symenv-p))
  :prepwork ((local (in-theory (enable svar-alist-fix))))
  :returns (xx pseudo-termp :hyp :guard)
  (if (atom x)
      ''nil
    (if (mbt (and (consp (car x)) (svar-p (caar x))))
        `(cons (cons ',(svar-fix (caar x)) ,(cdar x))
               ,(svdecomp-symenv->term (cdr x)))
      (svdecomp-symenv->term (cdr x))))
  ///
  (defthm svdecomp-ev-of-svdecomp-symenv->term
    (equal (svdecomp-ev (svdecomp-symenv->term x) a)
           (svdecomp-ev-symenv x a))
    :hints(("Goal" :in-theory (enable svdecomp-ev-symenv)))))



(define svdecomp-normalize-svexlist-eval ((x svexlist-p)
                                          (env svdecomp-symenv-p)
                                          (rec-limit natp))
  :returns (mv (newx svexlist-p)
               (newenv svdecomp-symenv-p :hyp (svdecomp-symenv-p env)))
  :hooks ((:fix :args (x rec-limit)))
  :measure (nfix rec-limit)
  (b* (((when (zp rec-limit))
        (mv (svexlist-fix x) env))
       (vars (mergesort (cwtime (svexlist-collect-vars x))))
       ((mv err svalist env1) (cwtime (svex-decomp-process-env-term env vars)))
       ((when err)
        (cw "Svdecomp error: ~@0~%" err)
        (mv (svexlist-fix x) env))
       ((when (atom svalist))
        ;; no more svex-evals to extract
        ;; (b* ((- (cw "masks: ~x0~%"
        ;;             (let ((masks (svexlist-mask-alist x)))
        ;;               (list (hons-assoc-equal 'fdmul::u masks)
        ;;                     (hons-assoc-equal '(concat 1 fdmul::u '(0 . -1)) masks))))))
          (mv (svexlist-fix x) env1))
       (newx (with-fast-alist svalist
               (cwtime (svexlist-compose x svalist)))))
    (clear-memoize-table 'svex-compose)
    (svdecomp-normalize-svexlist-eval newx env1 (1- rec-limit)))
  ///

  (defthm svdecomp-normalize-svex-eval-correct
    (b* (((mv newx newenv) (svdecomp-normalize-svexlist-eval x env rec-limit)))
      (equal (svexlist-eval newx (svdecomp-ev-symenv newenv a))
             (svexlist-eval x (svdecomp-ev-symenv env a))))
    :hints (("goal" :induct t)
            (And stable-under-simplificationp
                 '(:use ((:instance svexlist-eval-with-svex-decomp-process-env
                          (env1 env) (vars (mergesort (svexlist-collect-vars x)))))
                   :in-theory (e/d (svex-alist-eval)
                                   (svexlist-eval-with-svex-decomp-process-env))))))

  (defthm svdecomp-normalize-svex-eval-correct-single
    (b* (((mv newx newenv) (svdecomp-normalize-svexlist-eval (list x) env rec-limit)))
      (equal (svex-eval (car newx) (svdecomp-ev-symenv newenv a))
             (svex-eval x (svdecomp-ev-symenv env a))))
    :hints (("goal" :use ((:instance svdecomp-normalize-svex-eval-correct
                           (x (list x))))
             :in-theory (disable svdecomp-normalize-svex-eval-correct)
             :expand ((:free (x env) (svexlist-eval (mv-nth 0 x) env)))
             :do-not-induct t)))


  (defthm len-of-svdecomp-normalize-svexlist-eval-newx
    (equal (len (mv-nth 0 (svdecomp-normalize-svexlist-eval x env rec-limit)))
           (len x))
    :hints (("goal" :induct t)))

  (defthm consp-of-svdecomp-normalize-svexlist-eval-newx
    (equal (consp (mv-nth 0 (svdecomp-normalize-svexlist-eval x env rec-limit)))
           (consp x))
    :hints (("goal" :use len-of-svdecomp-normalize-svexlist-eval-newx
             :in-theory (disable len-of-svdecomp-normalize-svexlist-eval-newx)
             :cases ((consp x))
             :do-not-induct t))))

;; ;; Normalizing (single) svex evals...
;; (define svdecomp-normalize-svex-eval ((x svex-p) (env svdecomp-symenv-p) (rec-limit natp))
;;   :returns (newx pseudo-termp :hyp (svdecomp-symenv-p env))
;;   :hooks ((:fix :args (x rec-limit)))
;;   :measure (nfix rec-limit)
;;   (b* (((when (zp rec-limit))
;;         `(svex-eval ',(svex-rewrite-top x) ,(svdecomp-symenv->term env)))
;;        (vars (svex-collect-vars x))
;;        ((mv err svalist env1) (svex-decomp-process-env-term env vars))
;;        ((when err)
;;         (cw "Svdecomp error: ~@0~%" err)
;;         `(svex-eval ',(svex-rewrite-top x) ,(svdecomp-symenv->term env)))
;;        ((when (atom svalist))
;;         ;; no more svex-evals to extract
;;         `(svex-eval ',(svex-rewrite-top x) ,(svdecomp-symenv->term env1))))
;;     (svdecomp-normalize-svex-eval
;;      (with-fast-alist svalist (svex-compose x svalist)) env1 (1- rec-limit)))
;;   ///

;;   (defthm svdecomp-normalize-svex-eval-correct
;;     (equal (svdecomp-ev (svdecomp-normalize-svex-eval x env rec-limit) a)
;;            (svex-eval x (svdecomp-ev-symenv env a)))
;;     :hints (("goal" :induct t)
;;             (And stable-under-simplificationp
;;                  '(:use ((:instance svex-eval-with-svex-decomp-process-env
;;                           (env1 env) (vars (svex-collect-vars x))))
;;                    :in-theory (e/d (svex-alist-eval)
;;                                    (svex-eval-with-svex-decomp-process-env)))))))


(define svdecomp-svex-eval-metafun ((x pseudo-termp))
  :hooks nil
  :returns (newx pseudo-termp :hyp :guard)
  (b* (((acl2::unless-match x (svex-eval (quote (:? svex)) (:? env)))
        ;; fail, probably svex not quoted
        (cw "svdecomp-svex-eval-meta failed, probably running on non-concrete svex~%")
        x)
       ((unless (svex-p svex))
        (cw "svdecomp-svex-eval-meta failed because the svex was not svex-p~%")
        x)
       ((mv err symenv) (map-alist-term-keys-to-val-terms env))
       ((when err)
        (cw "svdecomp-svex-eval-meta failed to process the environment term: ~@0~%" err)
        x)
       ((mv newsvexlist newenv)
        (svdecomp-normalize-svexlist-eval (list svex) symenv 10)))
    `(svex-eval ',(car newsvexlist) ,(svdecomp-symenv->term newenv)))
  ///
  (defthmd svdecomp-svex-eval-meta
    (equal (svdecomp-ev x a)
           (svdecomp-ev (svdecomp-svex-eval-metafun x) a))
    :rule-classes ((:meta :trigger-fns (svex-eval)))))

(define svdecomp-svexlist-eval-metafun ((x pseudo-termp))
  :hooks nil
  :returns (newx pseudo-termp :hyp :guard)
  (b* (((acl2::unless-match x (svexlist-eval (quote (:? svexes)) (:? env)))
        ;; fail, probably svex not quoted
        (cw "svdecomp-svexlist-eval-meta failed, probably running on non-concrete svex~%")
        x)
       ((unless (svexlist-p svexes))
        (cw "svdecomp-svexlist-eval-meta failed because the svexlist was not svexlist-p~%")
        x)
       ((mv err symenv) (map-alist-term-keys-to-val-terms env))
       ((when err)
        (cw "svdecomp-svex-eval-meta failed to process the environment term: ~@0~%" err)
        x)
       ((mv newsvexes newenv)
        (svdecomp-normalize-svexlist-eval svexes symenv 10)))
    `(svexlist-eval ',newsvexes ,(svdecomp-symenv->term newenv)))
  ///
  (defthmd svdecomp-svexlist-eval-meta
    (equal (svdecomp-ev x a)
           (svdecomp-ev (svdecomp-svexlist-eval-metafun x) a))
    :rule-classes ((:meta :trigger-fns (svex-eval)))))

(local (defthm svex-alist-eval-of-pairlis$
         (implies (and (equal (len keys) (len vals))
                       (svarlist-p keys))
                  (equal (svex-alist-eval (pairlis$ keys vals) env)
                         (pairlis$ keys (svexlist-eval vals env))))
         :hints(("Goal" :in-theory (enable svex-alist-eval pairlis$
                                           svexlist-eval
                                           svarlist-fix)))))
(local (defthm pairlis-of-svexlist-eval
         (equal (pairlis$ (svex-alist-keys x)
                          (svexlist-eval (svex-alist-vals x) env))
                (svex-alist-eval x env))
         :hints(("Goal" :in-theory (enable svex-alist-eval svexlist-eval
                                           svex-alist-keys
                                           svex-alist-vals)))))

(define svdecomp-svex-alist-eval-metafun ((x pseudo-termp))
  :hooks nil
  :returns (newx pseudo-termp :hyp :guard)
  (b* (((acl2::unless-match x (svex-alist-eval (quote (:? svexal)) (:? env)))
        ;; fail, probably svex not quoted
        (cw "svdecomp-svexlist-eval-meta failed, probably running on non-concrete svex~%")
        x)
       ((unless (svex-alist-p svexal))
        (cw "svdecomp-svexlist-eval-meta failed because the svexlist was not svexlist-p~%")
        x)
       ((mv err symenv) (map-alist-term-keys-to-val-terms env))
       ((when err)
        (cw "svdecomp-svex-eval-meta failed to process the environment term: ~@0~%" err)
        x)
       ((mv newsvexes newenv)
        (svdecomp-normalize-svexlist-eval (svex-alist-vals svexal) symenv 10)))
    `(svex-alist-eval ',(pairlis$ (svex-alist-keys svexal) newsvexes)
                      ,(svdecomp-symenv->term newenv)))
  ///
  (defthmd svdecomp-svex-alist-eval-meta
    (equal (svdecomp-ev x a)
           (svdecomp-ev (svdecomp-svex-alist-eval-metafun x) a))
    :rule-classes ((:meta :trigger-fns (svex-eval)))))



(defines svex-find-a-difference
  (define svex-find-a-difference ((x svex-p)
                                  (y svex-p)
                                  (code integerp)
                                  (ctx-depth natp))
    :measure (svex-count x)
    :returns (mv diff context (ctx-frames natp :rule-classes :type-prescription))
    :verify-guards nil
    (b* (((unless (and (eq (svex-kind x) :call)
                       (eq (svex-kind y) :call)))
          (mv (list x y) nil 0))
         ((svex-call x) x)
         ((svex-call y) y)
         ((unless (and (eq x.fn y.fn)
                       (eql (len x.args) (len y.args))))
          (mv (list x y) nil 0))
         ((when (hons-equal x.args y.args))
          (cw "note: equal~%")
          (mv (list x y) nil 0))
         ((mv diff context ctx-frames)
          (svexlist-find-a-difference (svex-call->args x)
                                      (svex-call->args y)
                                      code ctx-depth))
         ((when (eql ctx-frames (lnfix ctx-depth)))
          (mv diff (list x y) (+ 1 ctx-frames))))
      (mv diff context (+ 1 ctx-frames))))

  (define svexlist-find-a-difference ((x svexlist-p)
                                      (y svexlist-p)
                                      (code integerp)
                                      (ctx-depth natp))
    :guard (and (eql (len x) (len y))
                (not (equal x y)))
    :measure (svexlist-count x)
    :returns (mv diffinfo context (ctx-frames natp :rule-classes :type-prescription))
    (b* (((unless (mbt (consp x)))
          (mv nil nil 0))
         ((when (hons-equal (car x) (car y)))
          (svexlist-find-a-difference (cdr x) (cdr y) code ctx-depth))
         ((when (hons-equal (cdr x) (cdr y)))
          (svex-find-a-difference (car x) (car y) code ctx-depth)))
      (if (logbitp 0 code)
          (svexlist-find-a-difference (cdr x) (cdr y) (ash code -1) ctx-depth)
        (svex-find-a-difference (car x) (car y) (ash code -1) ctx-depth))))
  ///
  (verify-guards svex-find-a-difference))


#||
(define svex-find-random-diff ((x svex-p)
                               (y svex-p)
                               (ctx-depth natp))
  :prepwork ((defttag svex-find-random-diff)
             (remove-untouchable acl2::create-state t))
  (with-local-state
    (mv-let (res state)
      (b* (((mv code state) (random$ (expt 2 32) state))
           (- (cw "code: ~x0~%" code))
           ((mv diff context &) (svex-find-a-difference x y code ctx-depth)))
        (mv (list diff context) state))
      res)))
||#

(defthm svexlist-p-of-nthcdr
  (implies (svexlist-p x)
           (svexlist-p (nthcdr n x)))
  :hints(("Goal" :in-theory (enable nthcdr))))

(defthm svexlist-p-of-take
  (implies (and (svexlist-p x)
                (<= (nfix n) (len x)))
           (svexlist-p (take n x)))
  :hints(("Goal" :in-theory (enable acl2::take
                                    svexlist-p))))


(defthm svexlist-eval-of-nthcdr
  (equal (svexlist-eval (nthcdr n x) env)
         (nthcdr n (svexlist-eval x env)))
  :hints(("Goal" :in-theory (enable nthcdr svexlist-eval)
          :induct (nthcdr n x)
          :expand ((svexlist-eval x env)))))

(defthm svexlist-eval-of-take
  (implies (<= (nfix n) (len x))
           (equal (svexlist-eval (take n x) env)
                  (take n (svexlist-eval x env))))
  :hints(("Goal" :in-theory (enable svexlist-eval take)
          :induct (take n x)
          :expand ((svexlist-eval x env)))))

(local (defthm +-collect-consts
         (implies (syntaxp (and (quotep a)
                                (quotep b)))
                  (equal (+ a b c) (+ (+ a b) c)))))

(local (defthm nthcdr-of-append
         (implies (equal (nfix n) (len x))
                  (equal (nthcdr n (append x y))
                         y))
         :hints(("Goal" :in-theory (enable nthcdr append len)
                 :induct (nthcdr n x)))))

(local (defthm take-of-append
         (implies (equal (nfix n) (len x))
                  (equal (take n (append x y))
                         (list-fix x)))
         :hints(("Goal" :in-theory (enable append len)))))

(local (fty::deffixcong svexlist-equiv svexlist-equiv (append a b) a
         :hints(("Goal" :in-theory (enable append svexlist-fix)))))
(local (fty::deffixcong svexlist-equiv svexlist-equiv (append a b) b
         :hints(("Goal" :in-theory (enable append)))))

(define svexlists-rewrite-until-same ((x svexlist-p) (y svexlist-p) (limit natp))
  :returns (mv (xx svexlist-p)
               (yy svexlist-p))
  :measure (nfix limit)
  (b* (((when (zp limit))
        (cw "svexlists-rewrite-until-same: limit ran out.  Total size: ~x0, x: ~x1, y: ~x2~%"
            (svexlist-opcount (append x y))
            (svexlist-opcount x) (svexlist-opcount y))
        (mv (svexlist-fix x) (svexlist-fix y)))
       ((when (hons-equal (svexlist-fix x) (svexlist-fix y)))
        (cw "svexlists-rewrite-until-same: success~%")
        (mv (svexlist-fix x) (svexlist-fix y)))
       (rw (svexlist-rewrite-top (append x y) :verbosep t))
       (len (len x))
       (newx (take len rw))
       (newy (nthcdr len rw))
       ((when (and (hons-equal newx (svexlist-fix x))
                   (hons-equal newy (svexlist-fix y))))
        (cw "svexlists-rewrite-until-same: fail, sizes: ~x0, ~x1~%"
            (svexlist-opcount newx) (svexlist-opcount newy))
        (mv newx newy)))
    (svexlists-rewrite-until-same newx newy (1- limit)))
  ///
  (defthm svexlists-rewrite-until-same-correct
    (b* (((mv newx newy) (svexlists-rewrite-until-same x y limit)))
      (and (equal (svexlist-eval newx env)
                  (svexlist-eval x env))
           (equal (svexlist-eval newy env)
                  (svexlist-eval y env))))
    :hints (("goal" :induct (svexlists-rewrite-until-same x y limit))
            (and stable-under-simplificationp
                 '(:use ((:instance svexlist-eval-of-take
                          (n (len x)) (x (svexlist-rewrite-top (append x y))))
                         (:instance svexlist-eval-of-nthcdr
                          (n (len x)) (x (svexlist-rewrite-top (append x y)))))
                   :in-theory (disable svexlist-eval-of-take
                                       svexlist-eval-of-nthcdr)))))

  (local (defthm plus-minus
           (equal (+ x (- x) y)
                  (+ 0 y))))

  (defthm len-of-svexlists-rewrite-until-same
    (b* (((mv newx newy) (svexlists-rewrite-until-same x y limit)))
      (and (equal (len newx) (len x))
           (equal (len newy) (len y))))
    :hints (("goal" :induct (svexlists-rewrite-until-same x y limit))
            (and stable-under-simplificationp
                 '(:use ((:instance acl2::len-of-take
                          (acl2::n (len x))
                          (acl2::xs (svexlist-rewrite-top (append x y))))
                         (:instance acl2::len-of-nthcdr
                          (acl2::n (len x))
                          (acl2::l (svexlist-rewrite-top (append x y))))
                         (:instance len-of-svexlist-fix)
                         (:instance len-of-svexlist-fix (x y)))
                   :in-theory (disable acl2::len-of-take
                                       acl2::len-of-nthcdr
                                       len-of-svexlist-fix)))))

  (defthm consp-of-svexlists-rewrite-until-same
    (b* (((mv newx newy) (svexlists-rewrite-until-same x y limit)))
      (and (equal (consp newx) (consp x))
           (equal (consp newy) (consp y))))
    :hints (("goal" :use len-of-svexlists-rewrite-until-same
             :do-not-induct t
             :in-theory (e/d ()
                             (len-of-svexlists-rewrite-until-same
                              svexlists-rewrite-until-same
;ACL2::CONSP-UNDER-IFF-WHEN-TRUE-LISTP
                              )))
            '(:cases ((consp x)))
            '(:cases ((consp y))))))

(define svdecomp-svex?-eval-compare-term (x y ;; either both svexes, svexlists, svex-alists
                                            (env1 svdecomp-symenv-p)
                                            (env2 svdecomp-symenv-p)
                                            eval-fn)
  :returns (eq pseudo-termp :hyp (and (svdecomp-symenv-p env1)
                                      (svdecomp-symenv-p env2)
                                      (symbolp eval-fn)
                                      (not (eq eval-fn 'quote)))
               :hints(("Goal" :in-theory (enable pseudo-termp))))
  :hooks nil
  (if (And (hons-equal x y)
           (hons-equal env1 env2))
      (prog2$ (cw "Resulting svexes are equal~%")
              ''t)
    (prog2$ (cw "Resulting svexes aren't equal~%")
            `(svdecomp-equal (,eval-fn ',x ,(svdecomp-symenv->term env1))
                             (,eval-fn ',y ,(svdecomp-symenv->term env2)))))
  ///
  (defthm svdecomp-svex?-eval-compare-term-correct
    (equal (svdecomp-ev (svdecomp-svex?-eval-compare-term
                         x y env1 env2 eval-fn)
                        a)
           (equal (svdecomp-ev `(,eval-fn ',x ,(svdecomp-symenv->term env1)) a)
                  (svdecomp-ev `(,eval-fn ',y ,(svdecomp-symenv->term env2)) a)))))

(define svdecomp-get-rewrite-limit (state)
  :returns (limit natp :rule-classes :type-prescription)
  (if (boundp-global 'svdecomp-rewrite-limit state)
      (nfix (f-get-global 'svdecomp-rewrite-limit state))
    5))


(define svdecomp-equal-svex-evals-metafun ((x pseudo-termp) mfc state)
  :hooks nil
  :returns (newx pseudo-termp :hyp :guard)
  (declare (ignorable mfc))
  (b* (((acl2::when-match x (equal (svex-eval (quote (:? svex1)) (:? env1))
                                   (svex-eval (quote (:? svex2)) (:? env2))))
        (cwtime
         (b* (((mv env1 env2)
               (mbe :logic (mv env1 env2)
                    ;; better than hons-copying them separately?
                    :exec (let ((pair (hons env1 env2)))
                            (mv (car pair) (cdr pair)))))
              ((unless (and (svex-p svex1) (svex-p svex2)))
               (cw "svdecomp-svex-eval-meta failed because the svex was not svex-p~%")
               x)
              ((mv err symenv1) (map-alist-term-keys-to-val-terms env1))
              ((when err)
               (acl2::fmt-to-comment-window
                "svdecomp-svex-eval-meta failed to process the environment term: ~@0~%"
                `((#\0 . ,err)) 0 '(nil 8 10 nil) nil)
               x)
              ((mv err symenv2) (map-alist-term-keys-to-val-terms env2))
              ((when err)
               (cw "svdecomp-svex-eval-meta failed to process the environment term: ~@0~%" err)
               x)
              ((mv newsvexlist1 newenv1) (cwtime (svdecomp-normalize-svexlist-eval (list svex1) symenv1 10)
                                                 :mintime 1))
              ((mv newsvexlist2 newenv2) (cwtime (svdecomp-normalize-svexlist-eval (list svex2) symenv2 10)
                                                 :mintime 1))
              (limit (svdecomp-get-rewrite-limit state))
              ((mv newsvexlist1 newsvexlist2)
               (cwtime (svexlists-rewrite-until-same newsvexlist1 newsvexlist2 limit)
                       :mintime 1))
              (newsvex1 (nth 0 newsvexlist1))
              (newsvex2 (nth 0 newsvexlist2)))
           (if (hons-equal newenv1 newenv2)
               (cw "Environments are equal.~%")
             (cw "Environments differ~%"))
           (if (hons-equal newsvex1 newsvex2)
               (cw "Svexes are equal.~%")
             (cw "Svexes differ.~%")
             ;; (b* ((diff (svex-find-random-diff newsvex1 newsvex2 3))
             ;;      ((list (list s1 s2) (list ctx1 ctx2)) diff)
             ;;      (masks (svexlist-mask-alist (append newsvexlist1 newsvexlist2)))
             ;;      (mask1 (svex-mask-lookup s1 masks))
             ;;      (mask2 (svex-mask-lookup s2 masks))
             ;;      (mask3 (svex-mask-lookup ctx1 masks))
             ;;      (mask4 (svex-mask-lookup ctx2 masks)))
             ;; (acl2::fmt-to-comment-window
             ;;  "Svexes differ: ~x0~%"
             ;;  `((#\0 . ,(list (list (str::hexify mask1) (str::hexify mask2))
             ;;                  (list s1 s2)
             ;;                  (list (str::hexify mask3) (str::hexify mask4))
             ;;                  (list ctx1 ctx2))))
             ;;  0 '(nil 10 10 nil) nil))
             )
           (svdecomp-svex?-eval-compare-term newsvex1 newsvex2 newenv1 newenv2 'svex-eval))
         :name svdecomp-equal-svex-evals-metafun)))
    ;; fail silently; probably just some random equal term
    x)
  ///
  (local (defthm svex-eval-of-nth-equal
           (implies (< (nfix n) (len x))
                    (equal (svex-eval (nth n x) env)
                           (nth n (svexlist-eval x env))))
           :hints(("Goal" :expand ((svexlist-eval x env))
                   :in-theory (enable nth)))))

  (defthmd svdecomp-equal-svex-evals-meta
    (equal (svdecomp-ev x a)
           (svdecomp-ev (svdecomp-equal-svex-evals-metafun x mfc state) a))
    :hints(("Goal" :in-theory (disable nth acl2::nth-when-zp)))
    :rule-classes ((:meta :trigger-fns (equal)))))


(define svdecomp-equal-svexlist-evals-metafun ((x pseudo-termp) mfc state)
  :hooks nil
  :returns (newx pseudo-termp :hyp :guard)
  (declare (ignorable mfc))
  (b* (((acl2::when-match x (equal (svexlist-eval (quote (:? svexes1)) (:? env1))
                                     (svexlist-eval (quote (:? svexes2)) (:? env2))))
        (cwtime
         (b* (((unless (and (svexlist-p svexes1) (svexlist-p svexes2)))
               (cw "svdecomp-equal-svexlist-evals-meta failed because the svex was not svex-p~%")
               x)
              ((mv err symenv1) (map-alist-term-keys-to-val-terms env1))
              ((when err)
               (cw "svdecomp-equal-svexlist-evals-meta failed to process the environment term: ~@0~%" err)
               x)
              ((mv err symenv2) (map-alist-term-keys-to-val-terms env2))
              ((when err)
               (cw "svdecomp-equal-svexlist-evals-meta failed to process the environment term: ~@0~%" err)
               x)
              ((mv newsvexes1 newenv1) (svdecomp-normalize-svexlist-eval svexes1 symenv1 10))
              ((mv newsvexes2 newenv2) (svdecomp-normalize-svexlist-eval svexes2 symenv2 10))
              (limit (svdecomp-get-rewrite-limit state))
              ((mv newsvexes1 newsvexes2) (svexlists-rewrite-until-same newsvexes1 newsvexes2 limit)))
           (svdecomp-svex?-eval-compare-term newsvexes1 newsvexes2 newenv1 newenv2 'svexlist-eval))
         :name svdecomp-equal-svexlist-evals-metafun)))
    ;; fail silently; probably just some random equal term
    x)

  ///
  (defthmd svdecomp-equal-svexlist-evals-meta
    (equal (svdecomp-ev x a)
           (svdecomp-ev (svdecomp-equal-svexlist-evals-metafun x mfc state) a))
    :rule-classes ((:meta :trigger-fns (equal)))))



(define svdecomp-equal-svex-alist-evals-metafun ((x pseudo-termp) mfc state)
  :hooks nil
  :returns (newx pseudo-termp :hyp :guard)
  (declare (ignorable mfc))
  (b* (((acl2::when-match x (equal (svex-alist-eval (quote (:? svexes1)) (:? env1))
                                   (svex-alist-eval (quote (:? svexes2)) (:? env2))))
        (cwtime
         (b* (((unless (and (svex-alist-p svexes1) (svex-alist-p svexes2)))
               (cw "svdecomp-equal-svex-alist-evals-meta failed because the svex was not svex-p~%")
               x)
              ((mv err symenv1) (map-alist-term-keys-to-val-terms env1))
              ((when err)
               (cw "svdecomp-equal-svex-alist-evals-meta failed to process the environment term: ~@0~%" err)
               x)
              ((mv err symenv2) (map-alist-term-keys-to-val-terms env2))
              ((when err)
               (cw "svdecomp-equal-svex-alist-evals-meta failed to process the environment term: ~@0~%" err)
               x)
              ((mv newsvexes1 newenv1)
               (svdecomp-normalize-svexlist-eval (svex-alist-vals svexes1) symenv1 10))
              ((mv newsvexes2 newenv2)
               (svdecomp-normalize-svexlist-eval (svex-alist-vals svexes2) symenv2 10))
              (limit (svdecomp-get-rewrite-limit state))
              ((mv newsvexes1 newsvexes2)
               (svexlists-rewrite-until-same newsvexes1 newsvexes2 limit))
              (svexal1 (pairlis$ (svex-alist-keys svexes1) newsvexes1))
              (svexal2 (pairlis$ (svex-alist-keys svexes2) newsvexes2)))
           (svdecomp-svex?-eval-compare-term svexal1 svexal2 newenv1 newenv2 'svex-alist-eval))
         :name svdecomp-equal-svex-alist-evals-metafun)))
    ;; fail silently; probably just some random equal term
    x)

  ///
  (defthmd svdecomp-equal-svex-alist-evals-meta
    (equal (svdecomp-ev x a)
           (svdecomp-ev (svdecomp-equal-svex-alist-evals-metafun x mfc state) a))
    :rule-classes ((:meta :trigger-fns (equal)))))


(defthm assoc-in-svex-alist-eval
  (equal (assoc-equal k (svex-alist-eval x env))
         (and (svar-p k)
              (let ((look (hons-assoc-equal k (svex-alist-fix x))))
                (and look
                     (cons k (svex-eval (cdr look) env))))))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-fix))))

(defthm hons-assoc-in-svex-alist-eval
  (equal (hons-assoc-equal k (svex-alist-eval x env))
         (and (svar-p k)
              (let ((look (hons-assoc-equal k (svex-alist-fix x))))
                (and look
                     (cons k (svex-eval (cdr look) env))))))
  :hints(("Goal" :in-theory (enable svex-alist-eval svex-alist-fix))))


(local (defthm lookup-in-svex-alist-fix-when-not-svar-p
         (implies (not (svar-p k))
                  (not (hons-assoc-equal k (svex-alist-fix x))))
         :hints(("Goal" :in-theory (enable svex-alist-fix)))))

(defthm fal-extract-of-svex-alist-eval
  (equal (acl2::fal-extract vars (svex-alist-eval x env))
         (svex-alist-eval (acl2::fal-extract vars (svex-alist-fix x)) env))
  :hints(("Goal" :in-theory (enable acl2::fal-extract svex-alist-eval svex-alist-fix)
          :induct (len vars))))

(defthm alistp-of-svex-alist-eval
  (alistp (svex-alist-eval x env))
  :hints(("Goal" :in-theory (enable svex-alist-eval))))

(defthm alistp-of-acons
  (equal (alistp (cons (cons k v) x))
         (alistp x)))

(defthmd assoc-of-append
  (implies (alistp a)
           (equal (assoc k (append a b))
                  (or (assoc k a) (assoc k b)))))

(defthmd assoc-of-acons
  (equal (assoc key (cons (cons k v) a))
         (if (equal key k)
             (cons k v)
           (assoc key a))))

(defthmd assoc-of-nil
  (equal (assoc key nil)
         nil))

(defthmd hons-assoc-equal-of-acons
  (equal (hons-assoc-equal key (cons (cons k v) a))
         (if (equal key k)
             (cons k v)
           (hons-assoc-equal key a))))

(defthmd hons-assoc-equal-of-nil
  (equal (hons-assoc-equal key nil)
         nil))

;; make sure these rulesets exist but don't redefine them
(add-to-ruleset! svtv-execs nil)
(add-to-ruleset! svtv-autoins nil)
(add-to-ruleset! svtv-autohyps nil)
(add-to-ruleset! svtv-alist-autohyps nil)
(add-to-ruleset! svtv-alist-autoins nil)

#||
(defthmd fal-extract-open-cons
  (equal (acl2::fal-extract (cons k rest) al)
         (let ((pair (hons-assoc-equal k al))
               (rest (acl2::fal-extract rest al)))
           (if pair
               (cons pair rest)
             rest))))

(defthmd fal-extract-done
  (equal (acl2::fal-extract nil al) nil))

(defthmd cons-onto-svex-alist-eval
  (implies (and (svar-p k) (svex-p v))
           (equal (cons (cons k (svex-eval v env))
                        (svex-alist-eval sva env))
                  (svex-alist-eval (cons (cons k v) sva) env)))
  :hints(("Goal" :in-theory (enable svex-alist-eval))))

(defthmd cons-onto-svex-alist-eval-append
  (implies (and (svar-p k) (svex-p v))
           (equal (cons (cons k (svex-eval v env))
                        (append (svex-alist-eval sva env) rest))
                  (append (svex-alist-eval (cons (cons k v) sva) env)
                          rest)))
  :hints(("Goal" :in-theory (enable svex-alist-eval))))

(defthmd cons-svex-evals-into-svex-alist-eval
  (implies (and (svar-p k) (svex-p v)
                (svar-p k2) (svex-p v2))
           (equal (cons (cons k (svex-eval v env))
                        (cons (cons k2 (svex-eval v2 env)) rest))
                  (append (svex-alist-eval (list (cons k v) (cons k2 v2)) env)
                          rest)))
  :hints(("Goal" :in-theory (enable svex-alist-eval))))

||#



;; NOTE: requires GL to be loaded
(defmacro svdecomp-hints (&key hyp
                               g-bindings
                               enable
                               rewrite-limit)
  `'(:computed-hint-replacement
     ((if stable-under-simplificationp
          (let ((state ,(if rewrite-limit
                           `(f-put-global 'svdecomp-rewrite-limit ,rewrite-limit state)
                          'state)))
            (value '(:in-theory (acl2::e/d**
                                 (svdecomp-equal-svex-alist-evals-meta
                                  svdecomp-equal-svexlist-evals-meta
                                  svdecomp-equal-svex-evals-meta)))))
        (value nil))
      (and stable-under-simplificationp
           '(:in-theory (acl2::e/d**
                         ((:ruleset svtv-execs)
                          (:ruleset svtv-autoins)
                          (:ruleset svtv-autohyps)
                          (:ruleset svtv-alist-autoins)
                          (:ruleset svtv-alist-autohyps)
                          ,@enable))))
      (if stable-under-simplificationp
          (acl2::gl-hint :hyp ',hyp
                         :concl (acl2::disjoin clause)
                         :g-bindings ,g-bindings)
        (value nil)))
     :in-theory (acl2::e/d**
                 (svtv-run
                  (:ruleset svtv-execs)
                  (:ruleset svtv-autoins)
                  (:ruleset svtv-autohyps)
                  (:ruleset svtv-alist-autoins)
                  (:ruleset svtv-alist-autohyps)
                  assoc-in-svex-alist-eval
                  hons-assoc-in-svex-alist-eval
                  alistp-of-svex-alist-eval
                  assoc-of-append
                  acl2::hons-assoc-equal-append
                  assoc-of-acons
                  hons-assoc-equal-of-acons
                  assoc-of-nil
                  hons-assoc-equal-of-nil
                  alistp-of-acons
                  car-cons
                  cdr-cons
                  return-type-of-svex-alist-eval-for-symbolic
                  svexlist-eval-for-symbolic
                  fal-extract-of-svex-alist-eval
                  ;; fal-extract-open-cons
                  ;; fal-extract-done
                  ;; cons-onto-svex-alist-eval
                  ;; cons-onto-svex-alist-eval-append
                  ;; cons-svex-evals-into-svex-alist-eval

                  ;; Note: Need all functions used in processing the svtv->outexprs
                  ;; into the evaluated svex alists here
                  (hons-assoc-equal)
                  (svex-alist-fix)
                  (car) (cdr)
                  (svar-p)
                  (svex-p)
                  (svtv->outexprs)
                  (svarlist-fix)
                  (mergesort)
                  (difference)
                  (alistp)
                  (svex-alist-keys)
                  (append)
                  (consp)
                  (assoc)
                  (acl2::fal-extract)
                  svex-alist-eval-svex-env-equiv-congruence-on-env
                  svexlist-eval-svex-env-equiv-congruence-on-env
                  svex-eval-svex-env-equiv-congruence-on-env
                  svex-env-fix-under-svex-env-equiv
                  ,@enable))))

(defxdoc svdecomp-hints
  :parents (svex-decomp)
  :short "Hint used for svex hardware model recomposition proofs -- see @(see
          svex-decomp).")

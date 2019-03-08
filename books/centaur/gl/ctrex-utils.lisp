; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "GL")
(include-book "bvar-db")
(include-book "gl-util")
(include-book "def-gl-rewrite")
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "bfr")
(include-book "bfr-sat")
(include-book "centaur/aig/misc" :dir :system)
(include-book "param")
(include-book "centaur/misc/vecs-ints" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "generic-geval")
(include-book "general-objects")
(include-book "glcp-config")
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "std/alists/alist-defuns" :dir :system)
(local (include-book "std/basic/arith-equivs" :dir :system))
(set-state-ok t)

;; To-satisfying-assign-spec generates the same satisfying assignment as
;; to-satisfying-assign given the same lst and bdd, except that when a
;; variable's value is irrelevant (car and cdr are equal), we put X in the list
;; instead of T or NIL.
(defun to-satisfying-assign-spec (lst bdd)
  (declare (xargs :hints (("goal" :in-theory (enable acl2-count)))))
  (cond ((atom bdd) lst)
        ((eq (cdr bdd) nil) (cons t (to-satisfying-assign-spec lst (car bdd))))
        ((eq (car bdd) nil) (cons nil (to-satisfying-assign-spec lst (cdr bdd))))
        ((hqual (car bdd) (cdr bdd))
         (cons 'x (to-satisfying-assign-spec (cdr lst) (car bdd))))
        (t (cons (car lst) (to-satisfying-assign-spec
                            (cdr lst)
                            (if (car lst) (car bdd) (cdr bdd)))))))


(std::defaggregate glcp-bit-ctrex
  ((descrip) ;; message
   (env)
   (gvar-alist)
   (dont-care-spec))
  :layout :fulltree)

(std::defaggregate glcp-obj-ctrex
  ((descrip) ;; message
   (genv) ;; both boolean and gvar assignments
   (obj-alist)
   (dont-care-spec))
  :layout :fulltree)

(defun n-satisfying-assigns-and-specs (n hyp-bdd bdd bound state)
  (declare (ignorable hyp-bdd))
  (if (zp n)
      (value nil)
    (b* (((mv rand state) (acl2::random$ (ash 1 bound) state))
         (lst (acl2::nat-to-v rand bound))
         ;; From when we passed in the unparametrized counterexample BDD:
;;          (assign (to-satisfying-assign lst bdd))
;;          (assign-spec (to-satisfying-assign-spec lst bdd))
         (assign (to-satisfying-assign lst bdd))
         (assign-spec (to-satisfying-assign-spec lst (acl2::from-param-space hyp-bdd bdd)))
         ((er rest) (n-satisfying-assigns-and-specs (1- n) hyp-bdd bdd bound state)))
      (value (cons (make-glcp-bit-ctrex
                    :descrip "generated randomly:"
                    :env assign
                    :dont-care-spec assign-spec)
                   rest)))))

(defthm n-satisfying-assigns-does-not-fail
  (not (mv-nth 0 (n-satisfying-assigns-and-specs n hyp-bdd bdd bound state))))


(defun vars-onto-alist (vars val al)
  (if (atom vars)
      al
    (if (hons-get (car vars) al)
        (vars-onto-alist (cdr vars) val al)
      (vars-onto-alist (cdr vars) val (hons-acons (car vars) val al)))))








(defun glcp-gen-assignments (ctrex-info config state)
  (b* (((glcp-config config)))
    (if (and (bfr-mode) ;; AIG mode
             (bfr-counterex-mode)) ;; alist counterexample mode
        (b* ((al (acl2::aig-extract-iterated-assigns-alist config.param-bfr 10))
             ;; Careful: al is memoized so we can't steal it.
             (cex-alist (hons-shrink-alist (append al ctrex-info) nil)))
          (value (list (make-glcp-bit-ctrex
                        :descrip "counterexample from SAT:"
                        :env (vars-onto-alist
                              ;; WRONG:
                              ;; Hmm, logically this isn't really well-typed,
                              ;; because alist consists of real g-objects whereas
                              ;; shape-spec-indices wants shape-specs.  But in the
                              ;; AIG case, parametrization doesn't do anything, so
                              ;; this works.  If we were to apply this in cases
                              ;; where alist was not generated by parametrizing a
                              ;; shape-spec-alist, this would need to be changed.

                              ;; Actually, parametrization gets rid of any AIG
                              ;; variables that are constrained to concrete values.
                              ;; So we need to reproduce the parametrized binding
                              ;; alist here.
                              (shape-spec-indices (strip-cdrs config.shape-spec-alist)) nil
                              cex-alist)))))
      (b* ((bound (shape-spec-max-bvar-list (strip-cdrs config.shape-spec-alist)))
           ((er assigns) (n-satisfying-assigns-and-specs
                          (max 0 (- config.n-counterexamples 2)) config.param-bfr ctrex-info bound state))
           (nils (acl2::nat-to-v 0 bound))
           (ts (acl2::nat-to-v -1 bound)))
        (value (take config.n-counterexamples
                     (list* (make-glcp-bit-ctrex
                             :descrip "generated by assigning 0/NIL to all possible bits:"
                             :env (to-satisfying-assign nils ctrex-info)
                             :dont-care-spec (to-satisfying-assign-spec
                                              nils (acl2::from-param-space config.param-bfr ctrex-info)))
                            (make-glcp-bit-ctrex
                             :descrip "generated by assigning 1/T to all possible bits:"
                             :env (to-satisfying-assign ts ctrex-info)
                             :dont-care-spec (to-satisfying-assign-spec
                                              ts (acl2::from-param-space config.param-bfr ctrex-info)))
                            assigns)))))))

(defun glcp-ctrex-complete-single-assign (string bfr-env alist hyp-bdd)
  (if (and (bfr-mode)
           (bfr-counterex-mode))
      (b* ((al (acl2::aig-extract-iterated-assigns-alist hyp-bdd 10))
           ;; Careful: al is memoized so we can't steal it.
           (cex-alist (hons-shrink-alist (append al bfr-env) nil)))
        (make-glcp-bit-ctrex
         :descrip string
         :env (vars-onto-alist
               (shape-spec-indices (strip-cdrs alist)) nil
               cex-alist)))
    (b* ((nils (acl2::nat-to-v 0 (shape-spec-max-bvar-list (strip-cdrs alist)))))
      (make-glcp-bit-ctrex
       :descrip string
       :env (to-satisfying-assign nils bfr-env)
       :dont-care-spec (to-satisfying-assign-spec
                        nils (acl2::from-param-space hyp-bdd bfr-env))))))



(defthm glcp-gen-assignments-does-not-fail
  (not (mv-nth 0 (glcp-gen-assignments ctrex-info config state))))


(defun pos-fix (x)
  (if (posp x) x 1))


(defun gl-ctrex-def (fn state)
  (declare (xargs :stobjs state
                  :guard (symbolp fn)))
  (b* ((tab (table-alist 'gl-ctrex-defs (w state)))
       (look (cdr (hons-assoc-equal fn tab)))
       ((when (equal (len look) 2))
        (b* (((list formals body) look))
          (mv t formals body))))
    (acl2::fn-get-def fn state)))


(mutual-recursion
 (defun magicer-ev (x alist clk state hard-errp aokp)
   (declare (xargs :guard (and (natp clk)
                               (pseudo-termp x)
                               (symbol-alistp alist))
                   :well-founded-relation acl2::nat-list-<
                   :measure (list clk (acl2-count x))
                   :hints(("Goal" :in-theory (enable nfix)))
                   :verify-guards nil
                   :stobjs state))
   (cond ((not x) (mv nil nil))
         ((atom x)
          (mv nil (cdr (hons-assoc-equal x alist))))
         ((eq (car x) 'quote) (mv nil (cadr x)))
         ((zp clk) (mv "clock ran out" nil))
         ((consp (car x))
          (b* (((mv err args)
                (magicer-ev-lst (cdr x) alist clk state hard-errp aokp))
               ((when err)
                (mv err nil))
               (new-alist (pairlis$ (cadar x) args)))
            (magicer-ev (caddar x) new-alist clk state hard-errp aokp)))
         ((eq (car x) 'if)
          (b* (((mv err test)
                (magicer-ev (cadr x) alist clk state hard-errp aokp))
               ((when err) (mv err nil)))
            (if test
                (magicer-ev (caddr x) alist clk state hard-errp aokp)
              (magicer-ev (cadddr x) alist clk state hard-errp aokp))))
         ((and (eq (car x) 'return-last)
               (quotep (cadr x)))
          (b* ((fnsym (cadr (cadr x))))
            (case fnsym
              (progn (b* (((mv err args)
                           (magicer-ev-lst (cddr x) alist clk state hard-errp
                                           aokp))
                          ((when err) (mv err nil)))
                       (mv nil (cadr args))))
              (otherwise
               (magicer-ev (fourth x) alist clk state hard-errp aokp)))))
         (t (b* (((mv err args)
                  (magicer-ev-lst (cdr x) alist clk state hard-errp aokp))
                 ((when err)
                  (mv err nil))
                 (fn (car x))
                 ((mv ev-err val)
                  (acl2::magic-ev-fncall fn args state hard-errp aokp))
                 ((unless ev-err) (mv nil val))
                 ((mv ok formals body) (gl-ctrex-def fn state))
                 ((unless ok) (mv (acl2::msg
                                   "can't execute and no definition: ~x0 ~@1~%"
                                   fn (if (eq ev-err t) "" ev-err))
                                  nil)))
              (magicer-ev body (pairlis$ formals args) (1- clk) state hard-errp
                          aokp)))))

 (defun magicer-ev-lst (x alist clk state hard-errp aokp)
   (declare (xargs :guard (and (posp clk)
                               (pseudo-term-listp x)
                               (symbol-alistp alist))
                   :measure (list (pos-fix clk) (acl2-count x))
                   :stobjs state))
   (if (endp x)
       (mv nil nil)
     (b* (((mv err first) (magicer-ev (car x) alist clk state hard-errp aokp))
          ((when err) (mv err nil))
          ((mv err rest) (magicer-ev-lst (cdr x) alist clk state hard-errp aokp))
          ((when err) (mv err nil)))
       (mv nil (cons first rest))))))

(defun set-gl-ctrex-def-fn (fn formals body state)
  (declare (xargs :mode :program :stobjs state))
  (b* (((er tr-body) (acl2::translate body t t t 'set-gl-ctrex-def (w state) state)))
    (value `(table gl-ctrex-defs ',fn '(,formals ,tr-body)))))

(defmacro set-gl-ctrex-def (fn formals body)
  `(make-event (set-gl-ctrex-def-fn ',fn ',formals ',body state)))



(mutual-recursion
 (defun magic-geval (x env state)
   (declare (xargs :guard (consp env)
                   :stobjs state
                   :measure (acl2-count x)
                   :hints (("goal" :in-theory '(measure-for-geval atom)))))
   (if (atom x)
       ;; Every atom represents itself.
       (mv nil x)
     (pattern-match x

       ;; A Concrete is like an escape sequence; we take (cdr x) as a concrete
       ;; object even if it looks symbolic.
       ((g-concrete obj) (mv nil obj))

       ;; Boolean
       ((g-boolean bool) (mv nil (bfr-eval bool (car env))))

       ((g-integer bits) (mv nil (bfr-list->s (acl2::list-fix bits) (car env))))

       ;; If-then-else.
       ((g-ite test then else)
        (b* (((mv err test) (magic-geval test env state))
             ((unless err)
              (if test
                  (magic-geval then env state)
                (magic-geval else env state))))
          (mv err nil)))

       ;; Apply: Unevaluated function call.
       ((g-apply fn args)
        (b* (((mv err args) (magic-geval args env state))
             ((when err) (mv err nil))
             (term (cons fn (ec-call (kwote-lst args)))))
          (mv-let (err val)
            (ec-call (magicer-ev term nil 10000 state t t))
            (if err
                (mv err nil)
              (mv nil val)))))

       ;; Var: untyped variable.
       ((g-var name)   (mv nil (cdr (het name (cdr env)))))

       ;; Conses where the car is not a recognized flag represent conses.
       (& (b* (((mv err car) (magic-geval (car x) env state))
               ((when err) (mv err nil))
               ((mv err cdr) (magic-geval (cdr x) env state))
               ((when err) (mv err nil)))
            (mv nil (cons car cdr)))))))
 (defun magic-geval-list (x env state)
   (declare (xargs :guard (consp env)
                   :stobjs state
                   :measure (acl2-count x)))
   (if (atom x)
       (mv nil nil)
     (b* (((mv err val) (magic-geval (car x) env state))
          ((when err) (mv err nil))
          ((mv err rest) (magic-geval (car x) env state))
          ((when err) (mv err nil)))
       (mv nil (cons val rest))))))

(defun gl-bit-abstract (bfr bfr-alist n)
  (declare (xargs :guard (natp n)))
  (b* ((n (lnfix n))
       ((when (booleanp bfr))
        (mv bfr bfr-alist n))
       (res (hons-get bfr bfr-alist))
       ((when res)
        (mv (cdr res) bfr-alist n)))
    (mv n (hons-acons bfr n bfr-alist) (1+ n))))

(defthm gl-bit-abstract-new-n-type
  (natp (mv-nth 2 (gl-bit-abstract bfr bfr-alist n)))
  :rule-classes :type-prescription)

(defun gl-bitlist-abstract (bfrs bfr-alist n)
  (declare (xargs :guard (natp n)))
  (b* (((when (atom bfrs))
        (mv nil bfr-alist (lnfix n)))
       ((mv first bfr-alist n) (gl-bit-abstract (car bfrs) bfr-alist n))
       ((mv rest bfr-alist n) (gl-bitlist-abstract (cdr bfrs) bfr-alist n)))
    (mv (cons first rest) bfr-alist n)))

(defthm gl-bitlist-abstract-new-n-type
  (natp (mv-nth 2 (gl-bitlist-abstract bfrs bfr-alist n)))
  :rule-classes :type-prescription)

(defun gl-bitlistlist-abstract (bfr-lists bfr-alist n)
  (declare (xargs :guard (natp n)))
  (b* (((when (atom bfr-lists))
        (mv nil bfr-alist (lnfix n)))
       ((mv first bfr-alist n) (gl-bitlist-abstract (car bfr-lists) bfr-alist n))
       ((mv rest bfr-alist n) (gl-bitlistlist-abstract (cdr bfr-lists) bfr-alist n)))
    (mv (cons first rest) bfr-alist n)))

(defthm gl-bitlistlist-abstract-new-n-type
  (natp (mv-nth 2 (gl-bitlistlist-abstract bfrs bfr-alist n)))
  :rule-classes :type-prescription)

(mutual-recursion
 (defun gobj-abstract (x bfr-alist n)
   (declare (xargs :guard (natp n)
                   :verify-guards nil))
   (if (atom x)
       (mv x bfr-alist (lnfix n))
     (case (tag x)
       (:g-boolean (b* (((mv bit bfr-alist n)
                         (gl-bit-abstract (g-boolean->bool x) bfr-alist n)))
                     (mv (g-boolean bit) bfr-alist n)))
       (:g-integer (b* (((mv bits bfr-alist n)
                         (gl-bitlist-abstract (g-integer->bits x) bfr-alist n)))
                     (mv (g-integer bits) bfr-alist n)))
       (:g-concrete (mv x bfr-alist (lnfix n)))
       (:g-ite (b* (((mv test bfr-alist n)
                     (gobj-abstract (g-ite->test x) bfr-alist n))
                    ((mv then bfr-alist n)
                     (gobj-abstract (g-ite->then x) bfr-alist n))
                    ((mv else bfr-alist n)
                     (gobj-abstract (g-ite->else x) bfr-alist n)))
                 (mv (g-ite test then else) bfr-alist n)))
       (:g-var (mv x bfr-alist (lnfix n)))
       (:g-apply (b* (((mv args bfr-alist n)
                       (gobjlist-abstract (g-apply->args x) bfr-alist n)))
                   (mv (g-apply (g-apply->fn x) args) bfr-alist n)))
       (otherwise (b* (((mv car bfr-alist n)
                        (gobj-abstract (car x) bfr-alist n))
                       ((mv cdr bfr-alist n)
                        (gobj-abstract (cdr x) bfr-alist n)))
                    (mv (cons car cdr) bfr-alist n))))))

 (defun gobjlist-abstract (x bfr-alist n)
   (declare (xargs :guard (natp n)))
   (b* (((when (atom x)) (mv x bfr-alist (lnfix n)))
        ((mv car bfr-alist n)
         (gobj-abstract (car x) bfr-alist n))
        ((mv cdr bfr-alist n)
         (gobjlist-abstract (cdr x) bfr-alist n)))
     (mv (cons car cdr) bfr-alist n))))


(flag::make-flag gobj-abstract-flg gobj-abstract)

(defthm-gobj-abstract-flg
  (defthm gobj-abstract-new-n-type
    (natp (mv-nth 2 (gobj-abstract x bfr-alist n)))
    :hints ('(:expand ((gobj-abstract x bfr-alist n))))
    :flag gobj-abstract)
  (defthm gobjlist-abstract-new-n-type
    (natp (mv-nth 2 (gobjlist-abstract x bfr-alist n)))
    :hints ('(:expand ((gobjlist-abstract x bfr-alist n))))
    :flag gobjlist-abstract))

(verify-guards gobj-abstract)

(defun gobj-abstract-top (x)
  (declare (xargs :guard t))
  (b* (((mv x al &) (gobj-abstract x nil 0)))
    (fast-alist-free al)
    x))

(defun gobjlist-abstract-top (x)
  (declare (xargs :guard t))
  (b* (((mv x al &) (gobjlist-abstract x nil 0)))
    (fast-alist-free al)
    x))




(defun bool-to-bit (x)
  (cond ((eq x t) 1)
        ((eq x nil) 0)
        (t x)))


(defun nth-list-bits (x lst)
  (if (atom x)
      nil
    (cons (bool-to-bit (nth (car x) lst))
          (nth-list-bits (cdr x) lst))))

(defun nth-list-list-bits (x lst)
  (if (atom x)
      nil
    (cons (nth-list-bits (car x) lst)
          (nth-list-list-bits (cdr x) lst))))


;; For each index N in an shape spec, this substitutes the Nth value found in
;; lst.  In the number case, it substitutes 1 and 0 for booleans.
(defund inspec-show-assign-spec (x lst)
  (if (atom x)
      x
    (pattern-match x
      ((g-concrete &) x)
      ((g-boolean b) (g-boolean (nth b lst)))
      ((g-integer bits) (g-integer (nth-list-bits bits lst)))
      ((g-ite if then else)
       (g-ite (inspec-show-assign-spec if lst)
              (inspec-show-assign-spec then lst)
              (inspec-show-assign-spec else lst)))
      ((g-apply fn args) (g-apply fn (inspec-show-assign-spec args lst)))
      ((g-var &) x)
      (& (cons (inspec-show-assign-spec (car x) lst)
               (inspec-show-assign-spec (cdr x) lst))))))


(def-glcp-ctrex-rewrite ((equal x y) t) (x y)
  :test (symbolp x))
(def-glcp-ctrex-rewrite ((equal x y) t) (x y)
  :test (quotep y))
(def-glcp-ctrex-rewrite ((equal x y) t) (y x)
  :test (symbolp y))
(def-glcp-ctrex-rewrite ((equal x y) t) (y x)
  :test (quotep x))
(def-glcp-ctrex-rewrite
  ((logcar x) 1)
  ((logbitp 0 x) t))
(def-glcp-ctrex-rewrite
  ((logcar x) 0)
  ((logbitp 0 x) nil))
(def-glcp-ctrex-rewrite
  ((logbitp n x) t)
  (x (logior (ash 1 n) x))
  :test (and (quotep n) (symbolp x)))
(def-glcp-ctrex-rewrite
  ((logbitp n x) t)
  (x (logior (ash 1 n) x))
  :test (quotep n))
(def-glcp-ctrex-rewrite
  ((logbitp n x) nil)
  (x (logand (lognot (ash 1 n)) x))
  :test (quotep n))
(def-glcp-ctrex-rewrite
  ((logbitp n (logcdr x)) v)
  ((logbitp (+ 1 (nfix n)) x) v))
(def-glcp-ctrex-rewrite
  ((logbitp n (logtail m x)) v)
  ((logbitp (+ (nfix m) (nfix n)) x) v))
(def-glcp-ctrex-rewrite
  ((integerp x) t)
  (x (ifix x)))
(def-glcp-ctrex-rewrite
  ((integerp x) nil)
  (x (if (integerp x) nil x)))


;; (glcp-ctrex-rewrite 10
;;                     '((equal (logcar (logcdr (logcdr x))) '1) 't)
;;                     (table-alist 'glcp-ctrex-rewrites (w state))
;;                     state)


(mutual-recursion
 (defun gobj->term-partial (x bfr-env)
   (declare (xargs :guard t
                   :measure (acl2-count x)
                   :hints (("goal" :in-theory '(measure-for-geval atom)
                            :expand ((general-concretep x)
                                     (gobject-hierarchy-lite x))))
                   :guard-hints (("goal" :expand ((gobject-hierarchy-lite x))))))
   (if (general-concretep x)
       (kwote x)
     (pattern-match x
       ((g-boolean bool) (kwote (bfr-eval bool bfr-env)))

       ((g-integer bits) (kwote (bfr-list->s (acl2::list-fix bits) bfr-env)))

       ((g-ite test then else)
        (list 'if
              (gobj->term-partial test bfr-env)
              (gobj->term-partial then bfr-env)
              (gobj->term-partial else bfr-env)))

       ((g-var name) name)

       ((g-apply fn args)
        (and (not (eq fn 'quote))
             (cons fn (gobj-list->terms-partial args bfr-env))))

       (& ;; cons
        (list 'cons
              (gobj->term-partial (car x) bfr-env)
              (gobj->term-partial (cdr x) bfr-env))))))

 (defun gobj-list->terms-partial (x bfr-env)
   (declare (xargs :guard t
                   :measure (acl2-count x)))
   (if (atom x)
       nil
     (cons (gobj->term-partial (car x) bfr-env)
           (gobj-list->terms-partial (cdr x) bfr-env)))))


(defun unquote-lst (x)
  (declare (xargs :guard (and (pseudo-term-listp x)
                              (acl2::quote-listp x))))
  (if (atom x)
      nil
    (cons (acl2::unquote (car x))
          (unquote-lst (cdr x)))))

(mutual-recursion
 ;; Like magic-ev but constructs a partially-evaluated term by evaluating
 ;; ground calls.
 ;; A little bit wrong with respect to a regular pseudo-term evaluator because
 ;; if the alist doesn't bind a variable, it's effectively bound to itself.
 (defun magic-ev-partial (x alist state hard-errp aokp)
   (declare (xargs :guard (and (pseudo-termp x)
                               (symbol-alistp alist)
                               (pseudo-term-listp (strip-cdrs alist)))
                   :measure (acl2-count x)
                   :hints(("Goal" :in-theory (enable nfix)))
                   :verify-guards nil
                   :stobjs state))
   (cond ((not x) nil)
         ((atom x) (let ((look (assoc x alist)))
                     (if look (cdr look) x)))
         ((eq (car x) 'quote) x)
         ((consp (car x))
          (b* ((args
                (magic-ev-partial-lst (cdr x) alist state hard-errp aokp))
               (new-alist (pairlis$ (cadar x) args)))
            (magic-ev-partial (caddar x) new-alist state hard-errp aokp)))
         ((eq (car x) 'if)
          (b* ((test
                (magic-ev-partial (cadr x) alist state hard-errp aokp)))
            (if (quotep test)
                (if (cadr test)
                    (magic-ev-partial (caddr x) alist state hard-errp aokp)
                  (magic-ev-partial (cadddr x) alist state hard-errp
                                    aokp))
              (b* ((then
                    (magic-ev-partial (caddr x) alist state hard-errp aokp))
                   (else
                    (magic-ev-partial (cadddr x) alist state hard-errp aokp)))
                (if (equal then else)
                    then
                  `(if ,test ,then ,else))))))
         (t (b* ((args
                  (magic-ev-partial-lst (cdr x) alist state hard-errp aokp))
                 (fn (car x))
                 ((unless (acl2::quote-listp args)) (cons fn args))
                 ((mv ev-err val)
                  (acl2::magic-ev-fncall fn (unquote-lst args) state hard-errp aokp))
                 ((unless ev-err) (kwote val)))
              (cons fn args)))))

 (defun magic-ev-partial-lst (x alist state hard-errp aokp)
   (declare (xargs :guard (and (pseudo-term-listp x)
                               (symbol-alistp alist)
                               (pseudo-term-listp (strip-cdrs alist)))
                   :measure (acl2-count x)
                   :stobjs state))
   (if (endp x)
       nil
     (cons (magic-ev-partial (car x) alist state hard-errp aokp)
           (magic-ev-partial-lst (cdr x) alist state hard-errp aokp)))))


(flag::make-flag magic-ev-partial-flg magic-ev-partial)

(defthm pseudo-term-listp-strip-cdrs-pairlis
  (implies (pseudo-term-listp vals)
           (pseudo-term-listp (strip-cdrs (pairlis$ keys vals)))))

(defthm-magic-ev-partial-flg
  (defthm pseudo-termp-of-magic-ev-partial
    (implies (and (pseudo-termp x)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-termp (magic-ev-partial x alist state hard-errp aokp)))
    :flag magic-ev-partial)
  (defthm pseudo-term-listp-of-magic-ev-partial-lst
    (implies (and (pseudo-term-listp x)
                  (pseudo-term-listp (strip-cdrs alist)))
             (pseudo-term-listp (magic-ev-partial-lst x alist state hard-errp aokp)))
    :flag magic-ev-partial-lst))


(encapsulate nil
  (local (defthm consp-cdr-when-quote
           (implies (and (equal (car x) 'quote)
                         (pseudo-termp x))
                    (consp (cdr x)))
           :hints(("Goal" :in-theory (enable pseudo-termp)))))
  (verify-guards magic-ev-partial))







(define glcp-ctrex-subst-lhses ((subst alistp) pairs)
  :returns (new-lhses (implies (acl2::pseudo-term-substp subst)
                               (pseudo-term-listp new-lhses)))
  (if (atom pairs)
      nil
    (b* (((unless (and (consp (car pairs))
                       (pseudo-termp (caar pairs))))
          (glcp-ctrex-subst-lhses subst (cdr pairs)))
         (lhs (caar pairs)))
      (cons (hons-copy (acl2::substitute-into-term lhs subst))
            ;; (acl2::substitute-into-list (car pairs) subst)
            (glcp-ctrex-subst-lhses subst (cdr pairs))))))

#!acl2
(defthm symbol-alistp-of-unify-const
  (implies (and (symbol-alistp alist)
                (pseudo-termp pat))
           (symbol-alistp (mv-nth 1 (unify-const pat term alist))))
  :hints(("Goal" :in-theory (enable unify-const))))

#!acl2
(defthm-simple-one-way-unify-flag symbol-alistp-of-simple-one-way-unify
  (defthm symbol-alistp-of-simple-one-way-unify
    (implies (and (symbol-alistp alist)
                  (pseudo-termp pat))
             (symbol-alistp (mv-nth 1 (simple-one-way-unify
                                       pat term alist))))
    :hints ('(:expand ((:free (term) (simple-one-way-unify pat term alist))
                       (:free (term) (simple-one-way-unify nil term alist)))))
    :flag simple-one-way-unify)
  (defthm symbol-alistp-of-simple-one-way-unify-lst
    (implies (and (symbol-alistp alist)
                  (pseudo-term-listp pat))
             (symbol-alistp (mv-nth 1 (simple-one-way-unify-lst
                                       pat term alist))))
    :hints ('(:expand ((simple-one-way-unify-lst pat term alist)
                       (simple-one-way-unify-lst nil term alist))))
    :flag simple-one-way-unify-lst))

#!acl2
(defthm pseudo-term-substp-of-unify-const
  (implies (and (pseudo-term-substp alist)
                (pseudo-termp pat))
           (pseudo-term-substp (mv-nth 1 (unify-const pat term alist))))
  :hints(("Goal" :in-theory (enable unify-const))))

#!acl2
(defthm-simple-one-way-unify-flag pseudo-term-substp-of-simple-one-way-unify
  (defthm pseudo-term-substp-of-simple-one-way-unify
    (implies (and (pseudo-term-substp alist)
                  (pseudo-termp pat)
                  (pseudo-termp term))
             (pseudo-term-substp (mv-nth 1 (simple-one-way-unify
                                       pat term alist))))
    :hints ('(:expand ((:free (term) (simple-one-way-unify pat term alist))
                       (:free (term) (simple-one-way-unify nil term alist)))))
    :flag simple-one-way-unify)
  (defthm pseudo-term-substp-of-simple-one-way-unify-lst
    (implies (and (pseudo-term-substp alist)
                  (pseudo-term-listp pat)
                  (pseudo-term-listp term))
             (pseudo-term-substp (mv-nth 1 (simple-one-way-unify-lst
                                       pat term alist))))
    :hints ('(:expand ((simple-one-way-unify-lst pat term alist)
                       (simple-one-way-unify-lst nil term alist))))
    :flag simple-one-way-unify-lst))

;; This makes a graph which has an edge x,y if x matches the lhs of the "from"
;; part of a ctrex rule and y is the corresponding substitution of the "to"
;; part, and the :test (if any) is satisfied.

;; For this to make sense, we are assuming that ctrex rewrite rules have
;; relatively inconsequential RHSes: the RHS of the "from" doesn't occur in the
;; LHS of the "to", and doesn't play any part in the test.  Existing ctrex
;; rewrite rules seem to all satisfy these assumptions.  We will add checks to
;; def-glcp-ctrex-rule to enforce them.

(define glcp-ctrex-rule-dependencies ((lhs pseudo-termp) rule state)
  :returns (new-lhses pseudo-term-listp)
  (b* (((unless (and (consp rule)
                     (consp (cdr rule))
                     (consp (car rule))
                     (consp (cdr (car rule)))))
        nil)
       ((list* (list pat-lhs ?pat-rhs) cond subst-pairs) rule)
       ((unless (and (pseudo-termp pat-lhs)
                     (pseudo-termp cond)
                     (mbt (pseudo-termp lhs))))
        nil)
       ((mv ok alist) (acl2::simple-one-way-unify pat-lhs lhs nil))
       ((unless ok) nil)
       ((mv ev-err ok) (acl2::magic-ev cond alist state t t))
       ((unless (and (not ev-err) ok)) nil))
    (glcp-ctrex-subst-lhses alist subst-pairs)))

(define glcp-ctrex-rules-dependencies ((lhs pseudo-termp) rules state)
  :returns (new-lhses pseudo-term-listp)
  (b* (((when (atom rules)) nil))
    (append (glcp-ctrex-rule-dependencies lhs (car rules) state)
            (glcp-ctrex-rules-dependencies lhs (cdr rules) state))))



(defines glcp-ctrex-term-dependency-map
  (define glcp-ctrex-term-dependency-map ((x pseudo-termp)
                                          (reclimit natp)
                                          (rule-table alistp)
                                          (graph "mapping of terms to their dependencies")
                                          (stack true-listp "for debugging")
                                          state)
    :well-founded-relation acl2::nat-list-<
    :measure (list reclimit 0)
    :returns (new-graph (implies (and (pseudo-term-list-listp graph)
                                      (pseudo-termp x))
                                 (pseudo-term-list-listp new-graph)))
    (b* (((when (or (atom x) (eq (car x) 'quote))) graph)
         ((when (hons-get x graph)) graph)
         ((when (zp reclimit))
          (cw "glcp-ctrex-term-dependency-map: recursion limit ran out -- loop
               in rules?  Last 1000 stack entries: ~x0~%"
              (take 1000 stack))
          graph)
         (fn (car x))
         (rules (and (symbolp fn) ;; not lambda
                     (cdr (assoc fn rule-table))))
         (deps (glcp-ctrex-rules-dependencies x rules state))
         (graph (hons-acons x deps graph))
         (stack (cons x stack)))
      (glcp-ctrex-termlist-dependency-map deps (1- reclimit) rule-table graph stack state)))
  (define glcp-ctrex-termlist-dependency-map ((x pseudo-term-listp)
                                              (reclimit natp)
                                              (rule-table alistp)
                                              (graph)
                                              (stack true-listp)
                                              state)
    :measure (list reclimit (len x))
    :returns (new-graph (implies (and (pseudo-term-list-listp graph)
                                      (pseudo-term-listp x))
                                 (pseudo-term-list-listp new-graph)))
    (b* (((when (atom x)) graph)
         (graph (glcp-ctrex-term-dependency-map (car x) reclimit rule-table graph stack state)))
      (glcp-ctrex-termlist-dependency-map (cdr x) reclimit rule-table graph stack state))))




(define glcp-ctrex-bvar-db-entry-to-term-dep-map ((n natp)
                                                  ctrex-assign
                                                  term-depgraph
                                                  (rule-table alistp)
                                                  bvar-db
                                                  state)
  :returns (mv (lhsterm pseudo-termp)
               (new-term-depgraph (implies (pseudo-term-list-listp term-depgraph)
                                           (pseudo-term-list-listp new-term-depgraph))))
  :guard (and (<= (base-bvar bvar-db) n)
              (< n (next-bvar bvar-db)))
  (b* ((gobj (get-bvar->term n bvar-db))              ;; gobj to assign that value
       (term (gobj->term-partial gobj ctrex-assign))  ;; term from that gobj with Boolean variable vals concretized
       ((unless (pseudo-termp term))
        (cw "Error: some object used in an IF produced an ill-formed term: ~x0~%" term)
        (mv nil term-depgraph))
       (lhsterm (hons-copy (magic-ev-partial term nil state t t)))   ;; evaluation of parts without variables
       (term-depgraph
        (glcp-ctrex-term-dependency-map lhsterm 100000 rule-table term-depgraph nil state)))
    (mv lhsterm term-depgraph)))

(define glcp-ctrex-bvar-db-to-term-dep-map ((n natp)
                                            ctrex-assign
                                            unparam-ctrex-assign
                                            term-vals
                                            term-depgraph
                                            (rule-table alistp)
                                            bvar-db
                                            state)
  :guard (and (<= (base-bvar bvar-db) n)
              (<= n (next-bvar bvar-db)))
  :measure (nfix (- (next-bvar bvar-db) (nfix n)))
  :returns (mv (term-val-map (implies (alistp term-vals) (alistp term-val-map))
                             "maps some terms from the term-map to Boolean values")
               (new-term-depgraph (implies (pseudo-term-list-listp term-depgraph)
                                           (pseudo-term-list-listp new-term-depgraph))))
  (b* (((when (mbe :logic (zp (- (next-bvar bvar-db) (nfix n)))
                   :exec (eql (next-bvar bvar-db) n)))
        (mv term-vals term-depgraph))
       ((mv lhsterm term-depgraph)
        (glcp-ctrex-bvar-db-entry-to-term-dep-map n ctrex-assign term-depgraph rule-table bvar-db state))
       (bvar-val (bfr-lookup n unparam-ctrex-assign))
       (term-vals (if lhsterm
                      (cons (cons lhsterm bvar-val) term-vals)
                    term-vals)))
    (glcp-ctrex-bvar-db-to-term-dep-map
     (1+ (lnfix n)) ctrex-assign unparam-ctrex-assign
     term-vals term-depgraph rule-table bvar-db state)))


(define glcp-ctrex-reverse-map-term-deps ((term pseudo-termp)
                                          (deps pseudo-term-listp)
                                          (term-revgraph pseudo-term-list-listp))
  :returns (new-term-revgraph pseudo-term-list-listp :hyp :guard)
  :prepwork ((local (defthm pseudo-term-listp-of-lookup
                      (implies (pseudo-term-list-listp x)
                               (pseudo-term-listp (cdr (hons-assoc-equal k x))))
                      :hints(("Goal" :in-theory (enable hons-assoc-equal))))))
  (b* (((when (atom deps)) term-revgraph)
       (term-revgraph (hons-acons (car deps)
                                  (cons term (cdr (hons-get (car deps) term-revgraph)))
                                  term-revgraph)))
    (glcp-ctrex-reverse-map-term-deps term (cdr deps) term-revgraph)))
       

(define glcp-ctrex-reverse-term-dep-map ((term-depgraph pseudo-term-list-listp)
                                         (term-revgraph pseudo-term-list-listp))
  :returns (new-term-revgraph pseudo-term-list-listp :hyp :guard)
  :prepwork ((local (defthm pseudo-term-list-listp-of-fast-alist-fork
                      (implies (and (pseudo-term-list-listp x)
                                    (pseudo-term-list-listp y))
                               (pseudo-term-list-listp (fast-alist-fork x y)))))
             (local (defthm cdr-last-when-pseudo-term-list-listp
                      (implies (pseudo-term-list-listp x)
                               (equal (cdr (last x)) nil)))))
  (b* (((when (atom term-depgraph))
        (fast-alist-clean term-revgraph))
       ((cons term deps) (car term-depgraph))
       (term-revgraph (glcp-ctrex-reverse-map-term-deps term deps term-revgraph)))
    (glcp-ctrex-reverse-term-dep-map (cdr term-depgraph) term-revgraph)))




(defines glcp-ctrex-dep-value-eval
  (define glcp-ctrex-dep-value-eval ((term pseudo-termp)
                                     (x pseudo-termp)
                                     (val)
                                     (term-vals alistp)
                                     state)
    :measure (acl2-count term)
    (b* (((when (quotep term)) (cadr term))
         ((when (equal term x)) val)
         (look (hons-get term term-vals))
         ((when look) (cdr look))
         ((when (atom term))
          (cw "glcp-ctrex-dep-value-eval: not found: ~x0~%" term))
         (args (glcp-ctrex-dep-value-eval-list (cdr term) x val term-vals state))
         ((mv err val)
          (ec-call (magicer-ev (cons (car term) (kwote-lst args)) nil 10000 state t t)))
         ((when err)
          (cw "error evaluating call of ~x0 on args ~x1: ~@2~%"
              (car term) args (if (eq err t) "(no error message)" err))))
      val))

  (define glcp-ctrex-dep-value-eval-list ((terms pseudo-term-listp)
                                          (x pseudo-termp)
                                          val
                                          (term-vals alistp)
                                          state)
    (b* (((when (atom terms)) nil))
      (cons (glcp-ctrex-dep-value-eval (car terms) x val term-vals state)
            (glcp-ctrex-dep-value-eval-list (cdr terms) x val term-vals state)))))
         
         
          



;; This derives the constant substitution based on the unifying term
;; substitution.  The input alist is transformed by replacing quote terms with
;; the values, x with val, and any term bound in term-vals with its value.
(define glcp-ctrex-dep-value-subst ((subst-alist acl2::pseudo-term-substp)
                                    (x pseudo-termp)
                                    (val)
                                    (term-vals alistp)
                                    state)
  :returns (const-subst-alist symbol-alistp)
  :guard-hints (("goal" :in-theory (enable acl2::pseudo-term-substp)))
  (b* (((when (atom subst-alist)) nil)
       ((unless (and (consp (car subst-alist))
                     (mbt (symbolp (caar subst-alist)))))
        (glcp-ctrex-dep-value-subst (cdr subst-alist) x val term-vals state))
       ((cons var term) (car subst-alist))
       ;; (term (hons-copy term))
       (value (glcp-ctrex-dep-value-eval term x val term-vals state)))
    (cons (cons var value)
          (glcp-ctrex-dep-value-subst (cdr subst-alist) x val term-vals state))))

(define glcp-ctrex-dep-derive-term-value-from-rule-substs ((x pseudo-termp)
                                                           (val)
                                                           (term-vals alistp)
                                                           (subst-alist symbol-alistp)
                                                           (const-subst-alist symbol-alistp)
                                                           (subst-pairs)
                                                           (rule)
                                                           state)
  (b* (((when (atom subst-pairs))
        val)
       ((unless (and (consp (car subst-pairs))
                     (consp (cdr (car subst-pairs)))
                     (pseudo-termp (caar subst-pairs))
                     (pseudo-termp (cadar subst-pairs))))
        (cw "Programming error: bad pair ~x0 in rule ~x1~%" (car subst-pairs) rule)
        (glcp-ctrex-dep-derive-term-value-from-rule-substs
         x val term-vals subst-alist const-subst-alist (cdr subst-pairs) rule state))
       ((list lhs rhs) (car subst-pairs))
       (lhs (acl2::substitute-into-term lhs subst-alist))
       ((unless (hons-equal lhs x))
        (glcp-ctrex-dep-derive-term-value-from-rule-substs
         x val term-vals subst-alist const-subst-alist (cdr subst-pairs) rule state))
       ;; To actually get the appropriate value for the RHS is tricky: The
       ;; substitution alist binds variables found in the RHS to terms likely
       ;; including the value that is being assigned to the original lhs and
       ;; also x itself.  The const-subst-alist gives (hopefully) the
       ;; appropriate valuations for these variables, derived by modifying the
       ;; subst-alist to replace x with val and any terms present in term-vals
       ;; with their values as well.
       ((mv ev-err rhs-val) (ec-call (magicer-ev rhs const-subst-alist 10000 state t t)))
       ((when ev-err)
        (cw "Error evaluating RHS ~x0 in rule ~x1 in counterexample generation: ~@2~%"
            rhs rule (if (eq ev-err t) "(no error message)" ev-err))
        val))
    (glcp-ctrex-dep-derive-term-value-from-rule-substs
     x rhs-val term-vals subst-alist const-subst-alist (cdr subst-pairs) rule state)))


(define glcp-ctrex-dep-derive-term-value-from-rule ((x pseudo-termp)
                                                    (val)
                                                    (dep-pair pseudo-term-listp)
                                                    (term-vals alistp)
                                                    rule
                                                    state)
  (b* (((unless (and (consp rule)
                     (consp (cdr rule))
                     (consp (car rule))
                     (consp (cdr (car rule)))))
        (cw "programming error: bad rule ~x0~%" rule)
        val)
       ((list* pair cond subst-pairs) rule)
       ((unless (and (pseudo-term-listp pair)
                     (pseudo-termp cond)
                     (mbt (pseudo-termp x))))
        (cw "programming error: bad rule (not pseudo-termps) ~x0~%" rule)
        val)
       ((mv ok alist) (acl2::simple-one-way-unify-lst pair dep-pair nil))
       ((unless ok) val)
       ((mv ev-err ok) (acl2::magic-ev cond alist state t t))
       ((unless (and (not ev-err) ok))
        val)
       (const-alist (glcp-ctrex-dep-value-subst alist x val term-vals state)))
    (glcp-ctrex-dep-derive-term-value-from-rule-substs
     x val term-vals alist const-alist subst-pairs rule state)))



(define glcp-ctrex-dep-derive-term-value-from-rules ((x pseudo-termp)
                                                     (val)
                                                     (dep-pair pseudo-term-listp)
                                                     (term-vals alistp)
                                                     rules
                                                     state)
  :returns (new-val)
  (b* (((when (atom rules)) val)
       (val (glcp-ctrex-dep-derive-term-value-from-rule
             x val dep-pair term-vals (car rules) state)))
    (glcp-ctrex-dep-derive-term-value-from-rules
     x val dep-pair term-vals (cdr rules) state)))



(define glcp-ctrex-dep-derive-term-value ((x pseudo-termp)
                                          (val)
                                          (dep pseudo-termp)
                                          (term-vals alistp)
                                          (rule-table alistp)
                                          state)
  :returns (new-val)
  (b* (((when (or (atom dep)
                  (eq (car dep) 'quote)
                  (not (symbolp (car dep)))))
        (cw "Programming error: ~x0 supposedly depends on ~x1 which is not a function call term~%"
            x dep)
        val)
       (rules (cdr (assoc (car dep) rule-table)))
       (dep-val (cdr (hons-get dep term-vals))))
    (glcp-ctrex-dep-derive-term-value-from-rules
     x val (list dep (list 'quote dep-val)) term-vals rules state)))


(define glcp-ctrex-deps-derive-term-value ((x pseudo-termp)
                                           (val)
                                           (deps pseudo-term-listp)
                                           (term-vals alistp)
                                           (rule-table alistp)
                                           state)
  :returns (new-val)
  (b* (((when (atom deps)) val)
       (val (glcp-ctrex-dep-derive-term-value x val (car deps) term-vals
                                              rule-table state)))
    (glcp-ctrex-deps-derive-term-value x val (cdr deps) term-vals rule-table state)))
 
       


(define glcp-ctrex-check-term-values-check ((x pseudo-termp)
                                            (term-vals alistp)
                                            state)
  :returns (mv mismatch eval-val)
  (b* (((when (or (atom x)
                  (eq (car x) 'quote)))
        ;; no problem
        (mv nil nil))
       (assigned-val (cdr (hons-get x term-vals)))
       (arg-vals (glcp-ctrex-dep-value-eval-list (cdr x) nil nil term-vals state))
       ((mv ev-err eval-val)
        (ec-call (magicer-ev (cons (car x) (kwote-lst arg-vals))
                             nil 10000 state t t)))
       ((when ev-err)
        (cw "Error evaluating ~x0 on args ~x1 in glcp-ctrex-term-values-check ~@2~%"
            (car x) arg-vals (if (eq ev-err t) "(no error message)" ev-err))
        (mv t :evaluation-error))
       ((when (equal eval-val assigned-val)) (mv nil nil)))
    (mv t eval-val)))

(local (defthm len-equal-0
         (equal (equal (len x) 0)
                (atom x))))

(local (defthm len-set-difference-decreases-weak
         (<= (len (set-difference$ a (cons c b)))
             (len (set-difference$ a b)))
         :hints(("Goal" :in-theory (enable set-difference$)))
         :rule-classes :linear))

(local (defthm len-set-difference-decreases-strong
         (implies (and (not (member c b))
                       (member c a))
                  (< (len (set-difference$ a (cons c b)))
                     (len (set-difference$ a b))))
         :hints(("Goal" :in-theory (enable set-difference$)))
         :rule-classes :linear))

(local (defthmd len-set-difference-does-not-decrease-lemma
         (implies (or (member c b)
                      (not (member c a)))
                  (equal (len (set-difference$ a (cons c b)))
                         (len (set-difference$ a b))))
         :hints(("Goal" :in-theory (enable set-difference$)))))

(local (defthm len-set-difference-does-not-decrease-rw
         (iff (equal (len (set-difference$ a (cons c b)))
                     (len (set-difference$ a b)))
              (or (member c b)
                  (not (member c a))))
         :hints(("Goal" :in-theory (enable set-difference$
                                           len-set-difference-does-not-decrease-lemma)))))

(local (defthm member-alist-keys
         (iff (member k (alist-keys x))
              (hons-assoc-equal k x))
         :hints(("Goal" :in-theory (enable alist-keys)))))
         
(local (defthm pseudo-term-listp-of-lookup-in-pseudo-term-list-listp
         (implies (pseudo-term-list-listp x)
                  (pseudo-term-listp (cdr (hons-assoc-equal k x))))
         :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

(local (defthm len-set-difference-of-superset
         (implies (subsetp a b)
                  (<= (len (set-difference$ x b))
                      (len (set-difference$ x a))))
         :hints(("Goal" :in-theory (enable set-difference$)))
         :rule-classes :linear))


(defines glcp-ctrex-check-term-values
  (define glcp-ctrex-check-term-values ((x pseudo-termp)
                                        (term-revgraph pseudo-term-list-listp)
                                        (seen)
                                        (stack)
                                        (term-vals alistp)
                                        state)
    :measure (list (len (set-difference$ (alist-keys term-revgraph)
                                         (alist-keys seen)))
                   0 1)
    :well-founded-relation acl2::nat-list-<
    :verify-guards nil
    :returns (new-seen)
    :hints(("Goal" :in-theory (enable alist-keys)))
    (b* (((when (hons-get x seen))
          seen)
         (val-look (hons-get x term-vals))
         ((unless val-look)
          (cw "glcp-ctrex-check-term-values confusion: ~x0 hasn't been assigned yet~%" x)
          seen)
         (seen (hons-acons x nil seen))
         ((mv mismatch eval-val) (glcp-ctrex-check-term-values-check x term-vals state))
         ((unless mismatch)
          ;; The evaluation was the same as the assignment, so we won't check
          ;; dependencies.
          seen)
         (deps (cdr (hons-get x term-revgraph)))
         ((unless deps)
          ;; Terminal.  If there is a mismatch here, show the trace.
          (cw "GLCP ctrex check: term ~x0 mismatched its assigned value ~x1; actual value ~x2.
               Assignment stack: ~x3.  Assignment that caused this mismatch is at the bottom
               of the stack."
              x (cdr val-look) eval-val stack)
          seen)
         (stack (cons (list x (cdr val-look) eval-val) stack)))
      (glcp-ctrex-check-termlist-values deps term-revgraph seen stack term-vals state)))
  (define glcp-ctrex-check-termlist-values ((x pseudo-term-listp)
                                            (term-revgraph pseudo-term-list-listp)
                                            (seen)
                                            (stack)
                                            (term-vals alistp)
                                            state)
    :measure (list (len (set-difference$ (alist-keys term-revgraph)
                                         (alist-keys seen)))
                   (len x) 0)
    :returns (new-seen)
    (b* (((when (atom x)) seen)
         (seen
          (b* ((new-seen
                (glcp-ctrex-check-term-values
                 (car x) term-revgraph seen stack term-vals state)))
            (if (mbt (<= (len (set-difference$ (alist-keys term-revgraph)
                                               (alist-keys new-seen)))
                         (len (set-difference$ (alist-keys term-revgraph)
                                               (alist-keys seen)))))
                new-seen
              seen))))
      (glcp-ctrex-check-termlist-values (cdr x) term-revgraph seen stack term-vals state)))
  ///
  (std::defret-mutual glcp-ctrex-check-term-values-seen-increases-lemma
    (std::defret glcp-ctrex-check-term-values-seen-increases-lemma
      (subsetp (alist-keys seen) (alist-keys new-seen))
      :hints ('(:expand (<call>)
                :in-theory (enable alist-keys)))
      :fn glcp-ctrex-check-term-values)
    (std::defret glcp-ctrex-check-termlist-values-seen-increases-lemma
      (subsetp (alist-keys seen) (alist-keys new-seen))
      :hints ('(:expand (<call>)))
      :fn glcp-ctrex-check-termlist-values))

  (std::defret glcp-ctrex-check-term-values-seen-increases
    (<= (len (set-difference$ (alist-keys term-revgraph)
                              (alist-keys new-seen)))
        (len (set-difference$ (alist-keys term-revgraph)
                              (alist-keys seen))))
    :hints (("Goal" :use glcp-ctrex-check-term-values-seen-increases-lemma
             :in-theory (disable glcp-ctrex-check-term-values-seen-increases-lemma)))
    :fn glcp-ctrex-check-term-values
    :rule-classes :linear)
  
  (verify-guards glcp-ctrex-check-term-values))

(defines glcp-ctrex-resolve-term-values
  (define glcp-ctrex-resolve-term-values ((x pseudo-termp)
                                          (term-revgraph pseudo-term-list-listp)
                                          (seen)
                                          (term-vals alistp)
                                          (rule-table alistp)
                                          state)
    :measure (list (len (set-difference$ (alist-keys term-revgraph)
                                         (alist-keys seen)))
                   0 1)
    :well-founded-relation acl2::nat-list-<
    :hints(("Goal" :in-theory (enable alist-keys)
            :do-not-induct t))
    :verify-guards nil
    :returns (mv (new-seen)
                 (new-term-vals (implies (alistp term-vals) (alistp new-term-vals))))
    (b* (((when (hons-get x seen))
          (mv seen term-vals))
         (deps (cdr (hons-get x term-revgraph)))
         (seen (hons-acons x nil seen))
         ((mv seen term-vals)
          (glcp-ctrex-resolve-termlist-values deps term-revgraph seen term-vals rule-table state))
         (value-look (hons-get x term-vals))
         (new-val (glcp-ctrex-deps-derive-term-value
                   x
                   (cdr value-look)
                   deps term-vals rule-table state))
         (- (and (consp value-look)
                 (not (equal (cdr value-look) new-val))
                 (cw "Warning: ~x0 was previously assigned value ~x1 but a dependency set it to ~x2 instead.~%"
                     x (cdr value-look) new-val)))
         (term-vals (if value-look term-vals (hons-acons x new-val term-vals))))
      ;; Check the assignment to see if it ruins anything...
      (fast-alist-free (glcp-ctrex-check-termlist-values deps
                                                         term-revgraph nil
                                                         (list (list x new-val))
                                                         term-vals state))
      (mv seen term-vals)))
  (define glcp-ctrex-resolve-termlist-values ((x pseudo-term-listp)
                                              (term-revgraph pseudo-term-list-listp)
                                              (seen)
                                              (term-vals alistp)
                                              (rule-table alistp)
                                              state)
    :measure (list (len (set-difference$ (alist-keys term-revgraph)
                                         (alist-keys seen)))
                   (len x) 0)
    :returns (mv (new-seen)
                 (new-term-vals (implies (alistp term-vals) (alistp new-term-vals))))
    (b* (((when (atom x)) (mv seen term-vals))
         ((mv seen term-vals)
          (b* (((mv new-seen new-term-vals)
                (glcp-ctrex-resolve-term-values
                 (car x) term-revgraph seen term-vals rule-table state)))
            (if (mbt (<= (len (set-difference$ (alist-keys term-revgraph)
                                               (alist-keys new-seen)))
                         (len (set-difference$ (alist-keys term-revgraph)
                                               (alist-keys seen)))))
                (mv new-seen new-term-vals)
              (mv seen term-vals)))))
      (glcp-ctrex-resolve-termlist-values (cdr x) term-revgraph seen term-vals rule-table state)))
  ///
  
  (std::defret-mutual glcp-ctrex-resolve-term-values-seen-increases-lemma
    (std::defret glcp-ctrex-resolve-term-values-seen-increases-lemma
      (subsetp (alist-keys seen) (alist-keys new-seen))
      :hints ('(:expand (<call>)
                :in-theory (enable alist-keys)))
      :fn glcp-ctrex-resolve-term-values)
    (std::defret glcp-ctrex-resolve-termlist-values-seen-increases-lemma
      (subsetp (alist-keys seen) (alist-keys new-seen))
      :hints ('(:expand (<call>)))
      :fn glcp-ctrex-resolve-termlist-values))

  (std::defret glcp-ctrex-resolve-term-values-seen-increases
    (<= (len (set-difference$ (alist-keys term-revgraph)
                              (alist-keys new-seen)))
        (len (set-difference$ (alist-keys term-revgraph)
                              (alist-keys seen))))
    :hints (("Goal" :use glcp-ctrex-resolve-term-values-seen-increases-lemma
             :in-theory (disable glcp-ctrex-resolve-term-values-seen-increases-lemma)))
    :fn glcp-ctrex-resolve-term-values
    :rule-classes :linear)

  (verify-guards glcp-ctrex-resolve-term-values))



(define glcp-ctrex-collect-bad-terminal-terms (term-depgraph
                                               bad-terms-acc)
  (b* (((when (atom term-depgraph)) bad-terms-acc)
       (bad-terms-acc
        (if (or (atom (car term-depgraph))
                (atom (caar term-depgraph))
                (consp (cdar term-depgraph)))
            bad-terms-acc
          (cons (caar term-depgraph) bad-terms-acc))))
    (glcp-ctrex-collect-bad-terminal-terms (cdr term-depgraph) bad-terms-acc)))

(define glcp-ctrex-collect-var-alist (term-vals var-alist-acc)
  (b* (((when (atom term-vals)) var-alist-acc)
       (var-alist-acc
        (if (or (atom (car term-vals))
                (not (symbolp (caar term-vals))))
            var-alist-acc
          (cons (car term-vals) var-alist-acc))))
    (glcp-ctrex-collect-var-alist (cdr term-vals) var-alist-acc)))

(define glcp-ctrex-revmap-variable-keys ((x pseudo-term-list-listp)
                                         (acc symbol-listp))
  :returns (res symbol-listp :hyp (symbol-listp acc))
  (if (atom x)
      acc
    (glcp-ctrex-revmap-variable-keys
     (cdr x)
     (if (and (consp (car x))
              (symbolp (caar x)))
         (cons (caar x) acc)
       acc))))


(define glcp-ctrex-process-bvar-db-depgraph ((ctrex-assign)
                                             (unparam-ctrex-assign)
                                             bvar-db
                                             state)
  :prepwork ((local (defthm pseudo-term-listp-of-hons-union1
                      (implies (and (pseudo-term-listp acc)
                                    (pseudo-term-listp x))
                               (pseudo-term-listp (acl2::hons-union1 x al acc)))))
             (local (defthm pseudo-term-listp-of-hons-union2
                      (implies (and (pseudo-term-listp acc)
                                    (pseudo-term-listp x))
                               (pseudo-term-listp (acl2::hons-union2 x y acc)))))
             (local (defthm pseudo-term-listp-of-hons-union
                      (implies (and (pseudo-term-listp x)
                                    (pseudo-term-listp y))
                               (pseudo-term-listp (acl2::hons-union x y)))
                      :hints(("Goal" :in-theory (enable acl2::hons-union)))))

             (local (defthm pseudo-term-listp-alist-keys-of-pseudo-term-list-listp
                      (implies (pseudo-term-list-listp x)
                               (pseudo-term-listp (alist-keys x)))
                      :hints(("Goal" :in-theory (enable alist-keys)))))
             (local (in-theory (enable get-global)))
             (local (defthm pseudo-term-listp-when-symbol-listp
                      (implies (symbol-listp x)
                               (pseudo-term-listp x)))))
  (b* ((rule-table (table-alist 'glcp-ctrex-rewrite (w state)))
       (rule-table (if (alistp rule-table)
                       rule-table
                     (pairlis$ (alist-keys rule-table)
                               (alist-vals rule-table))))
       ((mv term-vals      ;; maps top-level bvar-db terms to values
            term-depgraph) ;; maps terms to other terms whose value they induce via rules
        (glcp-ctrex-bvar-db-to-term-dep-map
         (base-bvar bvar-db) ctrex-assign unparam-ctrex-assign
         nil nil rule-table bvar-db state))
       (term-vals (make-fast-alist term-vals))
       ;; (- (cw "term-vals first 1000: ~x0~%" (take 1000 term-vals)))
       (term-revgraph ;; maps terms to other terms that might affect their value
        (glcp-ctrex-reverse-term-dep-map term-depgraph nil))
       (- (obs-cw "stats:~%depgraph length: ~x0~%revgraph length: ~x1~%bvar-db entries: ~x2~%"
              (len term-depgraph) (len term-revgraph) (len term-vals)))
       ((mv seen term-vals)
        (glcp-ctrex-resolve-termlist-values (glcp-ctrex-revmap-variable-keys term-revgraph nil)
                                            term-revgraph
                                            nil ;; seen
                                            term-vals
                                            rule-table
                                            state))
       (- (obs-cw "nodes traversed: ~x0~%updates: ~x1~%" (len seen) (len term-vals)))
       (- (fast-alist-free seen))
       (term-vals (fast-alist-clean term-vals))
       (- (obs-cw "number of terms assigned values: ~x0~%" (len term-vals)))
       (var-alist (glcp-ctrex-collect-var-alist term-vals nil))
       ;; (bad-terminals (glcp-ctrex-collect-bad-terminal-terms term-depgraph nil))
       ;; (- (and bad-terminals
       ;;         (cw "The following non-variable terms had no rules allowing them
       ;;               to induce values on other terms -- so they are goo ~
       ;;               candidates for additional counterexample rewrite rules: ~
       ;;               ~x0~%"
       ;;             bad-terminals)))
       )
    (fast-alist-free term-vals)
    (make-fast-alist var-alist)))










;; Legacy version of glcp-ctrex-process-bvar-db




(defun glcp-ctrex-subst-pairs (subst pairs)
  (if (atom pairs)
      nil
    (b* (((list lhs rhs) (car pairs)))
      (cons (list (acl2::substitute-into-term lhs subst)
                  `((lambda ,(strip-cars subst) ,rhs) . ,(strip-cdrs subst)))
            ;; (acl2::substitute-into-list (car pairs) subst)
            (glcp-ctrex-subst-pairs subst (cdr pairs))))))

;; Applies a rule to go from a lhs<-rhs pair to a list of such pairs
(defun glcp-ctrex-apply-rule (pair rule state)
  (declare (xargs :stobjs state :verify-guards nil))
  (b* (((list* pat-pair cond subst-pairs)
        rule)
       ((mv ok alist) (acl2::simple-one-way-unify-lst pat-pair pair nil))
       ((unless ok) (mv nil nil))
       ((mv ev-err ok) (acl2::magic-ev cond alist state t t))
       ((when (and (not ev-err) ok))
        (mv t (glcp-ctrex-subst-pairs alist subst-pairs))))
    (mv nil nil)))

;; Tries the available rules on the pair, using the first one that works
(defun glcp-ctrex-apply-rules (pair rules state)
  (declare (xargs :stobjs state :verify-guards nil))
  (b* (((when (atom rules)) (mv nil nil))
       ((mv ok new-pairs) (glcp-ctrex-apply-rule pair (car rules) state))
       ((when ok) (mv ok new-pairs)))
    (glcp-ctrex-apply-rules pair (cdr rules) state)))

;; Recursively rewrites a pair into a list of pairs using the ctrex rules
(mutual-recursion
 (defun glcp-ctrex-rewrite (limit pair rule-table state)
   (declare (xargs :stobjs state :verify-guards nil
                   :measure (list limit 0)))
   (b* (((list lhs rhs) pair)
        (pair (list (magic-ev-partial lhs nil state t t) rhs)) ;; (magic-ev-partial-lst pair nil state t t))
        ((when (zp limit)) (list pair))
        (lhs (car pair))
        ((when (atom lhs)) (list pair))
        (fn (car lhs))
        (rules (cdr (assoc fn rule-table)))
        ((mv ok new-pairs) (glcp-ctrex-apply-rules pair rules state))
        ((unless ok) (list pair)))
     (glcp-ctrex-rewrite-list (1- limit) new-pairs rule-table state)))
 (defun glcp-ctrex-rewrite-list (limit pairs rule-table state)
   (declare (xargs :stobjs state :verify-guards nil
                   :well-founded-relation acl2::nat-list-<
                   :measure (list limit (len pairs))))
   (if (atom pairs)
       nil
     (append (glcp-ctrex-rewrite limit (car pairs) rule-table state)
             (glcp-ctrex-rewrite-list limit (cdr pairs) rule-table state)))))

;; Given a list of lhs<-rhs pairs (already rewritten), updates g-var assignment
;; for each variable present on an LHS to the evaluation of the term on the RHS.
(defun glcp-ctrex-update-assigns (pairs var-alist state)
  (declare (xargs :stobjs state
                  :verify-guards nil))
  (b* (((when (atom pairs)) var-alist)
       (pair1 (car pairs))
       ((list lhs rhs) pair1)
       ((unless (symbolp lhs))
        (and (not (and (consp lhs)
                       (eq (car lhs) 'quote)))
             (cw "failed ctrex assignment:~%lhs:~%~x0~%rhs:~%~x1~%"
                 lhs rhs))
        (glcp-ctrex-update-assigns (cdr pairs) var-alist state))
       ((mv ev-err rhs-val) (magicer-ev rhs var-alist 10000 state t t))
       ((when ev-err)
        (cw "Error evaluating RHS in counterexample generation: ~@0~%"
            (if (eq ev-err t) "T" ev-err))
        (glcp-ctrex-update-assigns (cdr pairs) var-alist state)))
    (glcp-ctrex-update-assigns (cdr pairs) (hons-acons lhs rhs-val var-alist) state)))

(local (in-theory (enable* acl2::arith-equiv-forwarding)))
;; Iterates up the bvar-db list chronologically, given a counterexample
;; assignment (a bfr environment).  Builds up a variable alist by applying
;; rewrites to simplify the assignments induced by the bvar-db.
;; (defun glcp-ctrex-set-vars1 (n ctrex-assign unparam-ctrex-assign
;;                                rule-table bvar-db state)
;;   (declare (xargs :stobjs (state bvar-db)
;;                   :guard (natp n)
;;                   :verify-guards nil
;;                   :measure (nfix n)))
;;   (b* (((when (<= (the integer (lnfix n))
;;                   (the integer (base-bvar bvar-db))))
;;         nil)
;;        (n (1- n))
;;        (var-alist (glcp-ctrex-set-vars1
;;                    n ctrex-assign unparam-ctrex-assign
;;                    rule-table bvar-db state))
;;        (bvar-val (bfr-lookup n unparam-ctrex-assign))
;;        (gobj (get-bvar->term n bvar-db))
;;        (term (gobj->term-partial gobj ctrex-assign))
;;        (lhs1 (magic-ev-partial term nil state t t))
;;        (pair (list lhs1 (kwote bvar-val)))
;;        (assign-pairs (glcp-ctrex-rewrite 10000 pair rule-table state))
;;        (gregs3 (nth 3 (nth 4 (cdr (assoc 'uc::st var-alist)))))
;;        (var-alist (glcp-ctrex-update-assigns assign-pairs var-alist state))
;;        (gregs3-new (nth 3 (nth 4 (cdr (assoc 'uc::st var-alist))))))
;;     (and (not (equal gregs3 gregs3-new))
;;          (cw "gregs3: prev ~x0 new ~x1~%pair: ~x2~%assigns: ~x3~%gobj: ~x4"
;;              gregs3 gregs3-new pair assign-pairs gobj))
;;     var-alist))


(defun glcp-ctrex-set-one-var (n ctrex-assign unparam-ctrex-assign
                                 rule-table var-alist bvar-db state)
  (declare (xargs :stobjs (state bvar-db)
                  :guard (natp n)
                  :verify-guards nil))
  (b* ((bvar-val (bfr-lookup n unparam-ctrex-assign)) ;; value of Boolean variable from ctrex
       (gobj (get-bvar->term n bvar-db))              ;; gobj to assign that value
       (term (gobj->term-partial gobj ctrex-assign))  ;; term from that gobj with Boolean variable vals concretized
       (lhs1 (magic-ev-partial term nil state t t))   ;; evaluation of parts without variables
       (pair (list lhs1 (kwote bvar-val)))
       (assign-pairs (glcp-ctrex-rewrite 10000 pair rule-table state)))
    (glcp-ctrex-update-assigns assign-pairs var-alist state)))

;; For each boolean var -> term assigned in the bvar db, rewrite the term<-val
;; assignment to get some number of gvar<-val assignments, and collect them.
(defun glcp-ctrex-set-vars1 (n ctrex-assign unparam-ctrex-assign
                               rule-table var-alist bvar-db state)
  (declare (xargs :stobjs (state bvar-db)
                  :guard (natp n)
                  :verify-guards nil
                  :measure (nfix n)))
  (b* (((when (<= (the integer (lnfix n))
                  (the integer (base-bvar bvar-db))))
        var-alist)
       (n (1- n))
       (var-alist (glcp-ctrex-set-vars1
                   n ctrex-assign unparam-ctrex-assign
                   rule-table var-alist bvar-db state)))
    (glcp-ctrex-set-one-var n ctrex-assign unparam-ctrex-assign
                            rule-table var-alist bvar-db state)))

;; Tries to assign values to G variables based on their assignments to Boolean
;; values in the bvar-db.  Makes two passes, since the values assigned to
;; variables may affect other variables.  Could do more, but two seems like a
;; sensible choice.  The initial var-alist is usually empty but in special
;; cases may contain pre-set gvars.
(defun glcp-ctrex-process-bvar-db-legacy (ctrex-assign unparam-assign bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :verify-guards nil))
  (b* ((rule-table (table-alist 'glcp-ctrex-rewrite (w state)))
       (var-alist (glcp-ctrex-set-vars1 (next-bvar bvar-db)
                                        ctrex-assign
                                        unparam-assign
                                        rule-table nil bvar-db state)))
    (glcp-ctrex-set-vars1 (next-bvar bvar-db)
                          ctrex-assign
                          unparam-assign
                          rule-table var-alist bvar-db state)))



(defun glcp-apply-ctrex-transform-to-var-alist (var-alist transform state)
  (declare (xargs :stobjs (state) :guard t))
  (b* ((term (list transform (kwote var-alist)))
       ((mv err val) (ec-call (acl2::magic-ev term nil state t t)))
       (- (and err (cw "Failed to execute the counterexample transformation ~x0~%Error: ~@1~%Term: ~x2"
                       transform (if (eq err t) "(t)" err) term))))
    (if err var-alist val)))





(define glcp-ctrex-process-bvar-db ((ctrex-assign)
                                    (unparam-ctrex-assign)
                                    (config glcp-config-p)
                                    bvar-db
                                    state)
  (b* (((glcp-config config)))
    (if (eq config.term-level-counterexample-scheme :depgraph)
        (glcp-ctrex-process-bvar-db-depgraph
         ctrex-assign unparam-ctrex-assign bvar-db state)
      (ec-call (glcp-ctrex-process-bvar-db-legacy
                ctrex-assign unparam-ctrex-assign bvar-db state)))))
                                     


(defun glcp-ctrex-bits-to-objs (assign gobj-alist bvar-db config state)
  (declare (xargs :stobjs (bvar-db state)
                  :guard (and (glcp-bit-ctrex-p assign)
                              (glcp-config-p config))
                  :verify-guards nil))
  (b* (((glcp-bit-ctrex assign) assign)
       ((glcp-config config))
       (unparam-ctrex-assign (bfr-unparam-env config.param-bfr assign.env))
       (var-alist (bfr-case :bdd (glcp-ctrex-process-bvar-db assign.env
                                                             unparam-ctrex-assign
                                                             config
                                                             bvar-db
                                                             state)
                    :aig (acl2::with-fast-alists
                           (assign.env unparam-ctrex-assign)
                           ;; same as above
                           (glcp-ctrex-process-bvar-db assign.env
                                                       unparam-ctrex-assign
                                                       config
                                                       bvar-db
                                                       state))))
       (transform-var-alist (glcp-apply-ctrex-transform-to-var-alist var-alist config.ctrex-transform state))
       (env (cons assign.env (make-fast-alist transform-var-alist)))
       ((mv err alist) (magic-geval gobj-alist env state)))
    (make-glcp-obj-ctrex
     :descrip assign.descrip
     :genv env
     :obj-alist (if err :unknown alist)
     :dont-care-spec (inspec-show-assign-spec config.shape-spec-alist assign.dont-care-spec))))





(defthm glcp-obj-ctrex-p-of-glcp-ctrex-bits-to-objs
  (glcp-obj-ctrex-p (glcp-ctrex-bits-to-objs assign gobj-alist bvar-db config state))
  :hints(("goal" :in-theory (disable glcp-ctrex-process-bvar-db
                                     glcp-apply-ctrex-transform-to-var-alist
                                     magic-geval
                                     inspec-show-assign-spec))))



(defun glcp-bit-to-obj-ctrexamples (assigns gobj-alist bvar-db config state)
  (declare (xargs :stobjs (bvar-db state)
                  :verify-guards nil))
  (if (atom assigns)
      nil
    (cons (glcp-ctrex-bits-to-objs
           (car assigns) gobj-alist bvar-db config state)
          (glcp-bit-to-obj-ctrexamples (cdr assigns) gobj-alist bvar-db config state))))

(defun glcp-gen-ctrexes (ctrex-info bvar-db config state)
  (declare (xargs :stobjs (bvar-db state) :verify-guards nil))
  (b* (((er assigns) (glcp-gen-assignments ctrex-info config state))
       ((glcp-config config)))
    (value (glcp-bit-to-obj-ctrexamples
            assigns
            (gobj-alist-to-param-space
             (shape-spec-to-gobj config.shape-spec-alist) config.param-bfr)
            bvar-db config state))))

(defthm glcp-gen-ctrexes-does-not-fail
  (not (mv-nth 0 (glcp-gen-ctrexes ctrex-info bvar-db config state)))
  :hints(("Goal" :in-theory (disable glcp-gen-assignments glcp-bit-to-obj-ctrexamples))))

(in-theory (disable glcp-gen-ctrexes))

;; Collects violated assumptions in the bvar-db.
(defun glcp-ctrex-check-bvar-db (n env unparam-env bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :guard (and (natp n)
                              (consp env)
                              (<= n (next-bvar bvar-db)))
                  ; :verify-guards nil
                  :measure (nfix n)))
  (b* (((when (<= (lnfix n) (base-bvar bvar-db))) nil)
       (n (1- (lnfix n)))
       (rest (glcp-ctrex-check-bvar-db n env unparam-env bvar-db state))
       (gobj (get-bvar->term n bvar-db))
       (bvalue (bfr-lookup n unparam-env))
       ((mv er gvalue) (magic-geval gobj env state))
       ;; ((when (and (not er) (iff bvalue gvalue)))
       ;;  rest)
       (partial (gobj->term-partial gobj (car env)))
       ((when er)
        (cw "Couldn't evaluate bvar-db term: ~x0, error: ~@1~%"
            partial (if (eq er t) "T" er))
        rest))
    (cons (list (if (iff bvalue gvalue) "GOOD" "FAIL") partial bvalue gobj n) rest)))

(defun glcp-pretty-print-bvar-db-violations (pairs)
  (declare (xargs :guard t))
  (b* (((when (atom pairs)) nil)
       ((unless (true-listp (car pairs)))
        (glcp-pretty-print-bvar-db-violations (cdr pairs))))
    (and (equal (caar pairs) "FAIL")
         (or (cw "~x0 should be ~x1~%" (cadar pairs) (caddar pairs))
             (cw "gobj: ~x0~%" (gobj-abstract-top (ec-call (nth 3 (car pairs)))))))
    (glcp-pretty-print-bvar-db-violations (cdr pairs))))

(defun quote-if-needed (obj)
  (declare (xargs :mode :logic :guard t))
  (if (or (booleanp obj)
          (keywordp obj)
          (acl2-numberp obj)
          (characterp obj)
          (stringp obj))
      obj
    (list 'quote obj)))

(defun bindings-quote-if-needed (bindings)
  (declare (xargs :guard (true-list-listp bindings)))
  (if (atom bindings)
      nil
    (cons (list (caar bindings)
                (quote-if-needed (cadar bindings)))
          (bindings-quote-if-needed (cdr bindings)))))

(std::deflist glcp-obj-ctrexlist-p (x)
  (glcp-obj-ctrex-p x))

(defun glcp-pretty-print-assignments (n ctrexes concl execp param-bfr bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :guard (and (natp n)
                              (glcp-obj-ctrexlist-p ctrexes)
                              (pseudo-termp concl))))
  (if (atom ctrexes)
      nil ;; (value nil)
    (b* (((glcp-obj-ctrex ctr) (car ctrexes))
         (bindings (ec-call (bindings-quote-if-needed ctr.obj-alist)))
         (- (if (bfr-mode)
                (cw "Example ~x2, ~@0~%Assignment:~%~x1~%~%" ctr.descrip bindings n)
              (cw "Example ~x3, ~@0~%Template:~%~x1~%Assignment:~%~x2~%~%"
                  ctr.descrip ctr.dont-care-spec bindings n)))

         ((unless (and execp (consp ctr.genv)))
          (glcp-pretty-print-assignments (1+ n) (cdr ctrexes) concl execp param-bfr
                                     bvar-db state))

         (unparam-env (bfr-unparam-env param-bfr (car ctr.genv)))
         ((acl2::with-fast unparam-env))
         (bvar-db-info (glcp-ctrex-check-bvar-db
                        (next-bvar bvar-db) ctr.genv unparam-env bvar-db
                        state))
         ;;(state (f-put-global 'bvar-db-info bvar-db-info state))
         (- (and (hons-assoc-equal "FAIL" bvar-db-info)
                 ;; bozo make error message better
                 (not (cw "Some IF test terms were assigned inconsistent values:~%"))
                 (glcp-pretty-print-bvar-db-violations bvar-db-info)))
         (- (cw "Running conclusion to verify the counterexample.~%"))
         ;; ((acl2::cmp concl-term)
         ;;  (acl2::translate-cmp
         ;;   concl t t t 'glcp-print-ctrexamples (w state)
         ;;   (default-state-vars state)))

         ;; ctr.obj-alist is actually of the form
         ;; ((var0 val0) (var1 val1)...) --
         ;; change it to ((var0 . val0) (var1 . val1) ...)
         (alist (pairlis$ (acl2::alist-keys ctr.obj-alist)
                          (acl2::alist-keys (acl2::alist-vals ctr.obj-alist))))
         ((mv err val)
          (ec-call (acl2::magic-ev concl alist state t t)))
         ((mv err val)
          (if (not err)
              (mv err val)
            (progn$
             (cw "Failed to execute the counterexample: ~@0~%"
                 (if (eq err t) "(t)" err))
             (cw "Trying to logically simulate it...~%")
             (ec-call (magicer-ev concl alist 10000 state t t)))))
         ((when err)
          (cw "Evaluating the counterexample failed: ~@0~%"
              (if (eq err t) "(t)" err))
          ;; (value nil)
          ))
      (if val
          (cw "False counterexample!  See :xdoc gl::false-counterexamples.~%")
        (cw "Counterexample verified.~%"))
      (glcp-pretty-print-assignments (1+ n) (cdr ctrexes) concl execp param-bfr
                                     bvar-db state))))


(defun glcp-print-ctrexamples (ctrexes warn-err type concl execp param-bfr bvar-db state)
  (declare (xargs :stobjs (state bvar-db)
                  :guard (and (glcp-obj-ctrexlist-p ctrexes)
                              (pseudo-termp concl))))
  (b* ((- (cw "
*** SYMBOLIC EXECUTION ~@0 ***: ~@1 found." warn-err type))
       (- (and ctrexes
               (if (and (bfr-mode)
                        (bfr-counterex-mode))
                   (cw "~%Showing the example produced by SAT.~%~%")
                 (cw "
Showing ~x0 examples. Each example consists of a template and a
concrete assignment.  The template shows a class of examples, and the
concrete assignment represents a specific example from that
class:~%~%" (len ctrexes))))))
    (glcp-pretty-print-assignments 1 ctrexes concl execp param-bfr bvar-db state)))


    


;; (defun glcp-apply-ctrex-transform-to-each (ctrexes transform state)
;;   (declare (xargs :stobjs (state)
;;                   :guard (glcp-obj-ctrexlist-p ctrexes)))
;;   (b* (((when (atom ctrexes)) nil)
;;        (term (list transform (kwote (car ctrexes))))
       
;;        ((mv err val) (ec-call (acl2::magic-ev term nil state t t)))
;;        (- (and err (cw "Failed to execute the counterexample transformation ~x0~%Error: ~@1~%Term: ~x2"
;;                        transform (if (eq err t) "(t)" err) term)))
;;        (val (if err (car ctrexes) val)))
;;     (cons val (glcp-apply-ctrex-transform-to-each (cdr ctrexes) transform state))))


(defun glcp-gen/print-ctrexamples (ctrex-info ;; bdd or alist
                                   warn/err type config bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :verify-guards nil))
  (b* (((glcp-config config) config)
       (state (acl2::f-put-global 'glcp-var-bindings config.shape-spec-alist state))
       (state (acl2::f-put-global 'glcp-counterex ctrex-info state))
       ((er ctrexes) (glcp-gen-ctrexes ctrex-info bvar-db config state))
       (state (acl2::f-put-global 'glcp-counterex-assignments ctrexes state)))
    (value (glcp-print-ctrexamples
            ctrexes warn/err type
            config.top-level-term
            config.exec-ctrex
            config.param-bfr
            bvar-db state))))


(defun glcp-print-single-ctrex (bfr-env warn/err type config bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :verify-guards nil))
  (b* (((glcp-config config) config)
       (assign (glcp-ctrex-complete-single-assign
                type bfr-env config.shape-spec-alist config.param-bfr))
       (ctrexes (glcp-bit-to-obj-ctrexamples
                 (list assign)
                 (gobj-alist-to-param-space
                  (shape-spec-to-gobj config.shape-spec-alist)
                  config.param-bfr)
                 bvar-db config state)))
    (glcp-print-ctrexamples
     ctrexes warn/err type
     config.top-level-term
     config.exec-ctrex
     config.param-bfr
     bvar-db state)))



(defun translate-and-logically-evaluate-fn (form alist state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((er translated-form)
        (acl2::translate form t t t 'translate-and-logically-evaluate (w state) state))
       ((mv err ans) (acl2::magic-ev translated-form alist state nil t)))
    (mv err ans state)))

(defun translate-and-very-logically-evaluate-fn (form alist clock state)
  (declare (xargs :stobjs state :mode :program))
  (b* (((er translated-form)
        (acl2::translate form t t t 'translate-and-logically-evaluate (w state) state))
       ((mv err ans) (magicer-ev translated-form alist clock state nil t)))
    (mv err ans state)))

(defmacro translate-and-very-logically-evaluate (form &key alist (clock '10000))
  `(translate-and-very-logically-evaluate-fn ',form ,alist state ,clock))

(defmacro translate-and-logically-evaluate (form &key alist)
  `(translate-and-logically-evaluate-fn ',form ,alist state))

(defun gl-ctrex-alist-fn (n state)
  (declare (xargs :stobjs state :verify-guards nil))
  (b* ((obj-alist (glcp-obj-ctrex->obj-alist (nth n (@ glcp-counterex-assignments)))))
    (pairlis$ (strip-cars obj-alist)
              (acl2::strip-cadrs obj-alist))))

(defmacro gl-ctrex-alist (&optional (n '0))
  `(gl-ctrex-alist-fn ,n state))



;; (defun v1v2 (v)
;;   (mv (logand v #x33333333)
;;       (logand (ash v -2) #x33333333)))

;; (def-gl-thm fast-logcount-32-correct
;;   :hyp   (unsigned-byte-p 32 x)
;;   :concl (equal (let* ((v (- x (logand (ash x -1) #x55555555)))
;;                        (mv (v1v2 v))
;;                        (v1 (mv-nth 0 mv))
;;                        (v2 (mv-nth 1 mv))
;;                        (v (+ v1 v2)))
;;                   (ash (32* (logand (+ v (ash v -4)) #xF0F0F0F)
;;                             #x1010101)
;;                        -24))
;;                 (logcount (if (or (eql x #xabc) (eql x #xddd0)) (+ 1 x) x)))
;;   :g-bindings `((x ,(g-int 0 1 33))))

;; (translate-and-logically-evaluate
;;  (list :impl (let* ((v (- x (logand (ash x -1) #x55555555)))
;;                     (mv (v1v2 v))
;;                     (v1 (mv-nth 0 mv))
;;                     (v2 (mv-nth 1 mv))
;;                     (v (+ v1 v2)))
;;                (ash (32* (logand (+ v (ash v -4)) #xF0F0F0F)
;;                          #x1010101)
;;                     -24))
;;        :spec (logcount (if (or (eql x #xabc) (eql x #xddd0)) (+ 1 x) x)))
;;  :alist (gl-ctrex-alist 0))
 

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
(include-book "def-gl-rewrite")
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "clause-processors/meta-extract-user" :dir :system)
(include-book "bfr")
(include-book "bfr-sat")
(include-book "centaur/aig/misc" :dir :system)
(include-book "param")
(include-book "centaur/misc/vecs-ints" :dir :system)
(include-book "std/misc/two-nats-measure" :dir :system)
(include-book "generic-geval")
(include-book "glcp-config")
(include-book "centaur/misc/hons-extra" :dir :system)
(local (include-book "centaur/misc/arith-equivs" :dir :system))
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

(defun nat-list-max (x)
  (declare (xargs :guard (nat-listp x)
                  :guard-hints (("goal" :in-theory (enable nat-listp)))))
  (if (atom x)
      0
    (max (+ 1 (lnfix (car x)))
         (nat-list-max (cdr x)))))



(mutual-recursion
 (defun shape-spec-max-bvar (x)
   (declare (xargs :guard (shape-specp x)
                   :verify-guards nil))
   (if (atom x)
       0
     (case (tag x)
       (:g-number (b* ((num (g-number->num x))
                       ((list rn rd in id) num))
                    (max (nat-list-max rn)
                         (max (nat-list-max rd)
                              (max (nat-list-max in)
                                   (nat-list-max id))))))
       (:g-integer (max (+ 1 (lnfix (g-integer->sign x)))
                        (nat-list-max (g-integer->bits x))))
       (:g-integer? (max (+ 1 (lnfix (g-integer?->sign x)))
                         (max (+ 1 (lnfix (g-integer?->intp x)))
                              (nat-list-max (g-integer?->bits x)))))
       (:g-boolean (+ 1 (lnfix (g-boolean->bool x))))
       (:g-concrete 0)
       (:g-var 0)
       (:g-ite (max (shape-spec-max-bvar (g-ite->test x))
                    (max (shape-spec-max-bvar (g-ite->then x))
                         (shape-spec-max-bvar (g-ite->else x)))))
       (:g-call (shape-spec-max-bvar-list (g-call->args x)))
       (otherwise (max (shape-spec-max-bvar (car x))
                       (shape-spec-max-bvar (cdr x)))))))
 (defun shape-spec-max-bvar-list (x)
   (declare (xargs :guard (shape-spec-listp x)))
   (if (atom x)
       0
     (max (shape-spec-max-bvar (car x))
          (shape-spec-max-bvar-list (cdr x))))))



(defun glcp-gen-assignments (ctrex-info alist hyp-bdd n state)
  (if (and (bfr-mode) ;; AIG mode
           (bfr-counterex-mode)) ;; alist counterexample mode
      (b* ((al (acl2::aig-extract-iterated-assigns-alist hyp-bdd 10))
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
                            (shape-spec-indices (strip-cdrs alist)) nil
                            cex-alist)))))
    (b* ((bound (shape-spec-max-bvar-list (strip-cdrs alist)))
         ((er assigns) (n-satisfying-assigns-and-specs
                        (max 0 (- n 2)) hyp-bdd ctrex-info bound state))
         (nils (acl2::nat-to-v 0 bound))
         (ts (acl2::nat-to-v -1 bound)))
      (value (take n
                   (list* (make-glcp-bit-ctrex
                           :descrip "generated by assigning 0/NIL to all possible bits:"
                           :env (to-satisfying-assign nils ctrex-info)
                           :dont-care-spec (to-satisfying-assign-spec
                                            nils (acl2::from-param-space hyp-bdd ctrex-info)))
                          (make-glcp-bit-ctrex
                           :descrip "generated by assigning 1/T to all possible bits:"
                           :env (to-satisfying-assign ts ctrex-info)
                           :dont-care-spec (to-satisfying-assign-spec
                                            ts (acl2::from-param-space hyp-bdd ctrex-info)))
                          assigns))))))

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
  (not (mv-nth 0 (glcp-gen-assignments n hyp-bdd bdd bound state))))


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
          (mv nil (cdr (assoc-eq x alist))))
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

       ;; Number.  This is the hairy case.  Can represent all ACL2-NUMBERPs,
       ;; but naturals are more compact than integers, which are more compact
       ;; than rationals, which are more compact than complexes.  Denominators
       ;; are coerced to 1 if they evaluate to 0 -- ugly.
       ((g-number num)
        (b* (((mv real-num
                  real-denom
                  imag-num
                  imag-denom)
              (break-g-number num)))
          (flet ((uval (n env)
                       (bfr-list->u n (car env)))
                 (sval (n env)
                       (bfr-list->s n (car env))))
            (mv nil (components-to-number (sval real-num env)
                                          (uval real-denom env)
                                          (sval imag-num env)
                                          (uval imag-denom env))))))

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
       (:g-number (b* (((mv bits bfr-alist n)
                        (gl-bitlistlist-abstract (g-number->num x) bfr-alist n)))
                    (mv (g-number bits) bfr-alist n)))
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
      ((g-number n) (g-number (nth-list-list-bits n lst)))
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
                   :hints (("goal" :in-theory '(measure-for-geval atom)))))
   (if (atom x)
       (kwote x)
     (pattern-match x
       ((g-concrete obj) (kwote obj))

       ((g-boolean bool) (kwote (bfr-eval bool bfr-env)))

       ((g-number num)
        (b* (((mv real-num
                  real-denom
                  imag-num
                  imag-denom)
              (break-g-number num)))
          (flet ((uval (n env)
                       (bfr-list->u n env))
                 (sval (n env)
                       (bfr-list->s n env)))
            (kwote
             (components-to-number (sval real-num bfr-env)
                                   (uval real-denom bfr-env)
                                   (sval imag-num bfr-env)
                                   (uval imag-denom bfr-env))))))

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

(defun glcp-ctrex-subst-pairs (subst pairs)
  (if (atom pairs)
      nil
    (cons (acl2::substitute-into-list (car pairs) subst)
          (glcp-ctrex-subst-pairs subst (cdr pairs)))))

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
   (b* ((pair (magic-ev-partial-lst pair nil state t t))
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
                   rule-table var-alist bvar-db state))
       (bvar-val (bfr-lookup n unparam-ctrex-assign))
       (gobj (get-bvar->term n bvar-db))
       (term (gobj->term-partial gobj ctrex-assign))
       (lhs1 (magic-ev-partial term nil state t t))
       (pair (list lhs1 (kwote bvar-val)))
       (assign-pairs (glcp-ctrex-rewrite 10000 pair rule-table state)))
    (glcp-ctrex-update-assigns assign-pairs var-alist state)))

;; Tries to assign values to G variables based on their assignments to Boolean
;; values in the bvar-db.  Makes two passes, since the values assigned to
;; variables may affect other variables.  Could do more, but two seems like a
;; sensible choice.  The initial var-alist is usually empty but in special
;; cases may contain pre-set gvars.
(defun glcp-ctrex-set-vars (ctrex-assign unparam-assign var-alist bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :verify-guards nil))
  (b* ((rule-table (table-alist 'glcp-ctrex-rewrite (w state)))
       (var-alist (glcp-ctrex-set-vars1 (next-bvar bvar-db)
                                        ctrex-assign
                                        unparam-assign
                                        rule-table var-alist bvar-db state)))
    (glcp-ctrex-set-vars1 (next-bvar bvar-db)
                          ctrex-assign
                          unparam-assign
                          rule-table var-alist bvar-db state)))

(defun glcp-ctrex-bits-to-objs (assign sspec-alist gobj-alist param-bfr bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :guard (glcp-bit-ctrex-p assign)
                  :verify-guards nil))
  (b* (((glcp-bit-ctrex assign) assign)
       (unparam-ctrex-assign (bfr-unparam-env param-bfr assign.env))
       (var-alist (bfr-case :bdd (glcp-ctrex-set-vars assign.env unparam-ctrex-assign
                                                      assign.gvar-alist
                                                      bvar-db state)
                            :aig (acl2::with-fast-alists
                                  (assign.env unparam-ctrex-assign)
                                   ;; same as above
                                   (glcp-ctrex-set-vars assign.env unparam-ctrex-assign
                                                        assign.gvar-alist
                                                        bvar-db state))))
       (env (cons assign.env var-alist))
       ((mv err alist) (magic-geval gobj-alist env state)))
    (make-glcp-obj-ctrex
     :descrip assign.descrip
     :genv env
     :obj-alist (if err :unknown alist)
     :dont-care-spec (inspec-show-assign-spec sspec-alist assign.dont-care-spec))))



(defun glcp-bit-to-obj-ctrexamples (assigns sspec-alist gobj-alist param-bfr bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :verify-guards nil))
  (if (atom assigns)
      nil
    (cons (glcp-ctrex-bits-to-objs
           (car assigns) sspec-alist gobj-alist param-bfr bvar-db state)
          (glcp-bit-to-obj-ctrexamples (cdr assigns) sspec-alist gobj-alist
                                       param-bfr bvar-db state))))

(defun glcp-gen-ctrexes (ctrex-info alist param-bfr n bvar-db state)
  (declare (xargs :stobjs (bvar-db state) :verify-guards nil))
  (b* (((er assigns) (glcp-gen-assignments ctrex-info alist param-bfr n state)))
    (value (glcp-bit-to-obj-ctrexamples
            assigns alist
            (gobj-alist-to-param-space
             (shape-spec-to-gobj alist) param-bfr)
            param-bfr bvar-db state))))

(defthm glcp-gen-ctrexes-does-not-fail
  (not (mv-nth 0 (glcp-gen-ctrexes n param-bfr bdd bound bvar-db state)))
  :hints(("Goal" :in-theory (disable glcp-gen-assignments))))

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



(defun glcp-gen/print-ctrexamples (ctrex-info ;; bdd or alist
                                   warn/err type config bvar-db state)
  (declare (xargs :stobjs (bvar-db state)
                  :verify-guards nil))
  (b* (((glcp-config config) config)
       (state (acl2::f-put-global 'glcp-var-bindings config.shape-spec-alist state))
       (state (acl2::f-put-global 'glcp-counterex ctrex-info state))
       ((er ctrexes) (glcp-gen-ctrexes ctrex-info
                                       config.shape-spec-alist
                                       config.param-bfr
                                       config.nexamples
                                       bvar-db state))
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
                 config.shape-spec-alist
                 (gobj-alist-to-param-space
                  (shape-spec-to-gobj config.shape-spec-alist)
                  config.param-bfr)
                 config.param-bfr
                 bvar-db state)))
    (glcp-print-ctrexamples
     ctrexes warn/err type
     config.top-level-term
     config.exec-ctrex
     config.param-bfr
     bvar-db state)))

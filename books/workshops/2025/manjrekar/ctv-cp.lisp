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
; Original author: Mayank Manjrekar <mayank.manjrekar2@arm.com>

(in-package "COMPRESS")

(include-book "projects/arm/utils/rtl-utils" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "meta/pseudo-termp-lemmas" :dir :system)
(include-book "match-tree-when")

(define pseudo-term-fix (x)
  :returns (x pseudo-termp)
  (if (pseudo-termp x)
      x
    nil)
  ///
  (defthm pseudo-term-fix-involutive
    (equal (pseudo-term-fix (pseudo-term-fix x))
           (pseudo-term-fix x)))
  (defthm pseudo-term-fix-is-okay
    (implies (pseudo-termp x)
             (equal (pseudo-term-fix x) x)))
  )

(deffixtype pseudo-term
  :pred pseudo-termp
  :fix pseudo-term-fix
  :equiv pseudo-termp-equiv
  :define t
  :forward t)

(define pseudo-term-list-fix (x)
  :returns (x pseudo-term-listp)
  (if (consp x)
      (cons (pseudo-term-fix (car x)) (pseudo-term-list-fix (cdr x)))
    nil)
  ///
  (defthm pseudo-term-list-fix-involutive
    (equal (pseudo-term-list-fix (pseudo-term-list-fix x))
           (pseudo-term-list-fix x)))
  (defthm pseudo-termp-fix-is-okay
    (implies (pseudo-term-listp x)
             (equal (pseudo-term-list-fix x) x)))
  )

(deffixtype pseudo-term-list
  :pred pseudo-term-listp
  :fix pseudo-term-list-fix
  :equiv pseudo-term-list-equiv
  :define t
  :forward t)

(define pseudo-term-subst-fix (x)
  :returns (x pseudo-term-substp)
  (if (atom x)
      nil
    (if (consp (car x))
        (cons (cons (symbol-fix (caar x)) (pseudo-term-fix (cdar x)))
              (pseudo-term-subst-fix (cdr x)))
      (pseudo-term-subst-fix (cdr x))))
  ///
  (defthm pseudo-term-subst-fix-involutive
    (equal (pseudo-term-subst-fix (pseudo-term-subst-fix x))
           (pseudo-term-subst-fix x)))
  (defthm pseudo-term-subst-fix-is-okay
    (implies (pseudo-term-substp x)
             (equal (pseudo-term-subst-fix x) x))
    :hints (("Goal" :in-theory (e/d (pseudo-term-substp) ())))))

(deffixtype pseudo-term-subst
  :pred pseudo-term-substp
  :fix pseudo-term-subst-fix
  :equiv pseudo-term-subst-equiv
  :define t
  :forward t)

;;; Defining the evaluator!
(defevaluator mev mev-lst
  ((typespec-check ts x)
   (if a b c)
   (equal a b)
   (not a)
   (iff a b)
   (implies a b)
   (mv-nth a b)
   (cons a b)
   (bits a b c)
   (bitn a n)
   (setbits v1 w e s v2)
   (setbitn v1 w e v2)
   (binary-logxor a b)
   (binary-logior a b)
   (binary-logand a b)
   (ash x n)
   (binary-+ a b)
   (integerp x))
  :namedp t)

(def-meta-extract mev mev-lst)

;; Assuming (mev-meta-extract-global-facts), meta-extract-formula produces a theorem
(local
 (defthm mev-formula
   (implies (and (mev-meta-extract-global-facts)
                 (equal (w st) (w state)))
            (mev (meta-extract-formula name st) a))
   :hints(("Goal" :use ((:instance mev-meta-extract-global-badguy-sufficient
                         (obj (list :formula name))))))))

(local
 (defthm mev-fn-get-def
   (b* (((mv ok formals body) (fn-get-def fn st)))
     (implies (and ok
                   (mev-meta-extract-global-facts)
                   (equal (w st) (w state))
                   (equal (len args) (len formals)))
              (equal (mev (cons fn args) a)
                     (mev body (pairlis$ formals
                                             (mev-lst args a))))))
   :hints(("Goal" :in-theory (e/d (mev-of-fncall-args
                                   match-tree-opener-theory
                                   match-tree-alist-opener-theory)
                                  (mev-formula
                                   meta-extract-global-fact+
                                   meta-extract-formula
                                   take))
                  :use ((:instance mev-formula
                         (name fn)
                         (st st)
                         (a (pairlis$ (mv-nth 1 (fn-get-def fn st))
                                      (mev-lst args a)))))))))

;; A bit-value: It is either concrete (0 or 1) or symbolic expression, (:s v n),
;; in which case it's interpretation is equal to (bitn v n).
(deftagsum bv
 (:v ((v bitp)))
 (:bit ((v symbolp)
        (n natp))))

;; A bit-value-form: It either represents a normal bit-value, or full-adder sum
;; or carry bit, i.e., for example, the interpretation of (:fas a b c) is
;; (logxor a b c)
(deftagsum bvf
  (:bv ((bv bv)))
  (:fas ((a bvf)
         (b bvf)
         (c bvf)))
  (:fac ((a bvf)
         (b bvf)
         (c bvf))))

;; A bit-value-form which should be shifted left by a "sh" amount.
(defprod bvfs
  ((bvf bvf)
   (sh natp)))

;; A list of shifted bit-value-forms
(deflist bvfsl
  :elt-type bvfs
  :true-listp t)

;; A pseudo-term-subst is a mapping between symbols and expressions
;; (pseudo-termp's). A `context` is a list of such substituations. To
;; "evaluate" a term under a context, we need to sequentially apply the
;; substitution at the top of the context.
;; Note: we assume that the pseudo-terms in a context do not contain a
;; lambda-form, i.e., no nested substitions. The clause-processor will
;; fail if there is such a term in the context.
(deflist context
  :elt-type pseudo-term-subst
  :true-listp t)

;; We now define the interpretations of the above objects:
(define interp-bv ((bv bv-p))
  :returns (r pseudo-termp)
  (if (mbt (bv-p bv))
      (case (bv-kind bv)
        (:v (kwote (bv-v->v bv)))
        (:bit `(bitn ,(bv-bit->v bv) ,(kwote (bv-bit->n bv)))))
    (kwote 0)))

(local-defthm bvf-acl2-fas-count-lemmas
  (implies (and (bvf-p x)
                (equal (bvf-kind x) :fas))
           (and (< (acl2-count (bvf-fas->a x))
                   (acl2-count x))
                (< (acl2-count (bvf-fas->b x))
                   (acl2-count x))
                (< (acl2-count (bvf-fas->c x))
                   (acl2-count x))))
  :hints (("Goal" :in-theory (e/d (bvf-fas->a bvf-fas->b bvf-fas->c
                                   bvf-kind) ())
                  :expand ((bvf-p x))))
  :rule-classes :linear)

(local-defthm bvf-acl2-fac-count-lemmas
  (implies (and (bvf-p x)
                (equal (bvf-kind x) :fac))
           (and (< (acl2-count (bvf-fac->a x))
                   (acl2-count x))
                (< (acl2-count (bvf-fac->b x))
                   (acl2-count x))
                (< (acl2-count (bvf-fac->c x))
                   (acl2-count x))))
  :hints (("Goal" :in-theory (e/d (bvf-fac->a bvf-fac->b bvf-fac->c
                                   bvf-kind) ())
                  :expand ((bvf-p x))))
  :rule-classes :linear)

(define interp-bvf ((bvf bvf-p))
  :returns (r pseudo-termp)
  (if (mbt (bvf-p bvf))
      (case (bvf-kind bvf)
        (:bv (interp-bv (bvf-bv->bv bvf)))
        (:fas `(binary-logxor (binary-logxor ,(interp-bvf (bvf-fas->a bvf)) ,(interp-bvf (bvf-fas->b bvf)))
                              ,(interp-bvf (bvf-fas->c bvf))))
        (:fac `(binary-logior (binary-logior (binary-logand ,(interp-bvf (bvf-fac->a bvf)) ,(interp-bvf (bvf-fac->b bvf)))
                                             (binary-logand ,(interp-bvf (bvf-fac->a bvf)) ,(interp-bvf (bvf-fac->c bvf))))
                              (binary-logand ,(interp-bvf (bvf-fac->b bvf)) ,(interp-bvf (bvf-fac->c bvf))))))
    (kwote 0)))

(define interp-bvfs ((bvfs bvfs-p))
  :returns (r pseudo-termp)
  `(ash ,(interp-bvf (bvfs->bvf bvfs)) ,(kwote (bvfs->sh bvfs))))

(define interp-bvfsl ((bvfsl bvfsl-p))
  :returns (r pseudo-termp)
  (if (atom bvfsl)
      (kwote 0)
    `(binary-+ ,(interp-bvfs (car bvfsl)) ,(interp-bvfsl (cdr bvfsl)))))

(local-defthm alistp-of-match-tree-alist
  (implies (alistp al)
           (alistp (match-tree-alist pat term al)))
  :hints (("Goal" :in-theory (e/d (match-tree-alist) ()))))

(local-defthm assoc-equal-of-alistp-gives-consp
  (implies (and (alistp al)
                (assoc-equal x al))
           (consp (assoc-equal x al))))

(local-defthm alistp-of-match-tree-mv-nth-1
  (implies (alistp al)
           (alistp (mv-nth 1 (match-tree pat term al))))
  :hints (("Goal" :in-theory (e/d (match-tree) ()))))

(local-defthm symbol-list-p-union
  (implies (and (symbol-listp x)
                (symbol-listp y))
           (symbol-listp (union-equal x y))))


;; The following function is the main workhorse of ctv-cp
;; clause-processor. Given a term `term` and a bit position n, it tries to
;; obtain a bit-value-form corresponding to (bitn term n) -- the first return
;; value indicates whether it was able to do so. Additionally, when `needint`
;; is t, it ensures that term is syntactially an integer assuming that the list
;; of symbols in the third return value are also integers.
;; Note: we are assuming that we will not see any lambda expressions
;; (let-bindings) in the term
;; Note: currently this function only recognizes the following forms to parse
;; adder sum and carry expressions:
;; (binary-logxor x y)
;; (binary-logxor (binary-logxor x y) z)
;; (binary-logand x y)
;; (binary-logior (binary-logior (binary-logand x y) (binary-logand x z)) (binary-logand y z))
(define get-nth-bit ((term pseudo-termp)
                     (n natp)
                     (needint booleanp))
  :otf-flg nil
  :hints ((and stable-under-simplificationp
               '(:in-theory (e/d (match-tree-obj-equals-subst-when-successful) ()))))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (e/d (match-tree-obj-equals-subst-when-successful) ())))
  :returns (mv (okp booleanp) (r bvf-p) (ivl symbol-listp))
  (cond ((and (atom term) (mbt (symbolp term)))
         (if needint
             (mv t (bvf-bv (bv-bit term n)) (list term))
           (mv t (bvf-bv (bv-bit term n)) nil)))
        ((quotep term)
         (if (integerp (unquote term))
             (mv t (if1 (bitn (unquote term) n) (bvf-bv (bv-v 1)) (bvf-bv (bv-v 0))) nil)
           (mv nil (bvf-bv (bv-v 0)) nil)))
        ((eq (car term) 'ash)
         (treematch-when term
           ((ash (:? v) (quote (:? sh)))
            :when (natp sh)
            (if (< n sh)
                (mv t (bvf-bv (bv-v 0)) nil)
              (get-nth-bit v (- n sh) t)))
           (& (mv nil (bvf-bv (bv-v 0)) nil))))
        ((eq (car term) 'setbits)
         (treematch-when term
            ((setbits (:? v1) (quote (:? w1)) (quote (:? e1)) (quote (:? s1)) (:? v2))
             :when (and (natp w1) (natp e1) (natp s1) (<= s1 e1) (< e1 w1))
             (if (< n s1)
                 (get-nth-bit v1 n nil)
               (if (<= n e1)
                   (get-nth-bit v2 (- n s1) nil)
                 (if (< n w1)
                     (get-nth-bit v1 n nil)
                   (mv t (bvf-bv (bv-v 0)) nil)))))
                         (& (mv nil (bvf-bv (bv-v 0)) nil))))
        ((eq (car term) 'setbitn)
         (treematch-when term
            ((setbitn (:? v1) (quote (:? w1)) (quote (:? e1)) (:? v2))
             :when (and (natp w1) (natp e1) (< e1 w1))
             (if (< n e1)
                 (get-nth-bit v1 n nil)
               (if (= n e1)
                   (get-nth-bit v2 0 nil)
                 (if (< n w1)
                     (get-nth-bit v1 n nil)
                   (mv t (bvf-bv (bv-v 0)) nil)))))
                         (& (mv nil (bvf-bv (bv-v 0)) nil))))
        ((eq (car term) 'bits)
         (treematch-when term
            ((bits (:? v1) (quote (:? e1)) (quote (:? s1)))
             :when (and (natp e1) (natp s1) (<= s1 e1))
             (if (<= n (- e1 s1))
                 (get-nth-bit v1 (+ n s1) nil)
               (mv t (bvf-bv (bv-v 0)) nil)))
                         (& (mv nil (bvf-bv (bv-v 0)) nil))))
        ((eq (car term) 'bitn)
         (treematch-when term
            ((bitn (:? v1) (quote (:? e1)))
             :when (natp e1)
             (if (= n 0)
                 (get-nth-bit v1 e1 nil)
               (mv t (bvf-bv (bv-v 0)) nil)))
                         (& (mv nil (bvf-bv (bv-v 0)) nil))))
        ((eq (car term) 'binary-logxor)
         (treematch-when term
            ((binary-logxor (binary-logxor (:? v1) (:? v2)) (:? v3))
             (b* (((mv ok1p v1 ivl1) (get-nth-bit v1 n t))
                  ((mv ok2p v2 ivl2) (get-nth-bit v2 n t))
                  ((mv ok3p v3 ivl3) (get-nth-bit v3 n t))
                  ((unless (and ok1p ok2p ok3p)) (mv nil (bvf-bv (bv-v 0)) nil)))
               (mv t (bvf-fas v1 v2 v3) (union$ ivl1 ivl2 ivl3 :test 'eq))))
                         ((binary-logxor (:? v1) (:? v2))
                          (b* (((mv ok1p v1 ivl1) (get-nth-bit v1 n t))
                               ((mv ok2p v2 ivl2) (get-nth-bit v2 n t))
                               ((unless (and ok1p ok2p)) (mv nil (bvf-bv (bv-v 0)) nil)))
                            (mv t (bvf-fas v1 v2 (bvf-bv (bv-v 0))) (union$ ivl1 ivl2 :test 'eq))))
                         (& (mv nil (bvf-bv (bv-v 0)) nil))))
        ((eq (car term) 'binary-logior)
         (treematch-when term
            ((binary-logior (binary-logior (binary-logand (:? v1) (:? v2))
                                           (binary-logand (:? v1) (:? v3)))
                            (binary-logand (:? v2) (:? v3)))
             (b* (((mv ok1p v1 ivl1) (get-nth-bit v1 n t))
                  ((mv ok2p v2 ivl2) (get-nth-bit v2 n t))
                  ((mv ok3p v3 ivl3) (get-nth-bit v3 n t))
                  ((unless (and ok1p ok2p ok3p)) (mv nil (bvf-bv (bv-v 0)) nil)))
               (mv t (bvf-fac v1 v2 v3) (union$ ivl1 ivl2 ivl3 :test 'eq))))
                         (& (mv nil (bvf-bv (bv-v 0)) nil))))
        ((eq (car term) 'binary-logand)
         (treematch-when term
            ((binary-logand (:? v1) (:? v2))
             (b* (((mv ok1p v1 ivl1) (get-nth-bit v1 n t))
                  ((mv ok2p v2 ivl2) (get-nth-bit v2 n t))
                  ((unless (and ok1p ok2p)) (mv nil (bvf-bv (bv-v 0)) nil)))
               (mv t (bvf-fac v1 v2 (bvf-bv (bv-v 0))) (union$ ivl1 ivl2 :test 'eq))))
                         (& (mv nil (bvf-bv (bv-v 0)) nil))))
        (t (mv nil (bvf-bv (bv-v 0)) nil))))

;; Interpretation of an integer variable list
(define interp-ivl ((ivl symbol-listp))
  :returns (r pseudo-termp :hyp :guard)
  (if (atom ivl)
      ''t
    `(if (integerp ,(car ivl)) ,(interp-ivl (cdr ivl)) 'nil)))

(local-defthm integerp-get-nth-bit
  (implies (and (mv-nth 0 (get-nth-bit term n t))
                (mev (interp-ivl (mv-nth 2 (get-nth-bit term n t))) al))
           (integerp (mev term al)))
  :hints (("Goal" :in-theory (e/d (get-nth-bit
                                   interp-ivl) ()))))

(local-defthm interp-ivl-member-equal
  (implies (and (mev (interp-ivl y) al)
                (member x y))
           (integerp (mev x al)))
  :hints (("Goal" :in-theory (e/d (interp-ivl) ()))))

(local-defthm interp-ivl-union-equal
  (iff (mev (interp-ivl (union-equal x y)) al)
       (and (mev (interp-ivl x) al)
            (mev (interp-ivl y) al)))
  :hints (("Goal" :in-theory (e/d (interp-ivl) ()))))

(local-defthm bitn-shift-up-1-alt
  (implies (and (integerp n) (integerp k))
           (equal (bitn (* (expt 2 k) x) n)
                  (bitn x (- n k))))
  :hints (("Goal" :in-theory (e/d (rtl::bitn-shift-up-alt) ()))))

(local-defthm get-nth-bit-ev-correct
  (implies (and (mv-nth 0 (get-nth-bit term n needint))
                (mev (interp-ivl (mv-nth 2 (get-nth-bit term n needint))) al)
                (natp n))
           (equal (mev (interp-bvf (mv-nth 1 (get-nth-bit term n needint))) al)
                  (bitn (mev term al) n)))
  :hints (("Goal" :in-theory (e/d (get-nth-bit
                                   interp-bvf
                                   interp-bv
                                   bitn-logand
                                   bitn-logior
                                   bitn-logxor
                                   match-tree-obj-equals-subst-and-open-when-successful
                                   match-tree-alist-opener-theory
                                   bitn-bits
                                   bitn-cat)
                                  ()))
          (and stable-under-simplificationp
           '(:use (:instance integerp-get-nth-bit
                   (term (cadr term))
                   (n (- n (cadr (caddr term)))))
             :in-theory (e/d (get-nth-bit
                              interp-bvf
                              interp-bv
                              bitn-logand
                              bitn-logior
                              bitn-logxor
                              match-tree-obj-equals-subst-and-open-when-successful
                              match-tree-alist-opener-theory
                              bitn-bits
                              bitn-cat)
                         (integerp-get-nth-bit))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm integerp-of-interp-bvfsl
  (integerp (mev (interp-bvfsl x) al))
  :hints (("Goal" :in-theory (e/d (interp-bvfsl
                                   interp-bvfs) ())))
  :rule-classes :type-prescription)

(local-defthm interp-bvfsl-of-append
  (equal (mev (interp-bvfsl (append x y)) al)
         (+ (mev (interp-bvfsl x) al) (mev (interp-bvfsl y) al)))
  :hints (("Goal" :in-theory (e/d (interp-bvfsl) ()))))

(local-defthm true-listp-of-mev-lst
  (true-listp (mev-lst x al))
  :hints (("Goal" :in-theory (e/d () ())
                  :induct (true-listp x))))

(local-defthm pseudo-term-substp-is-alistp
  (implies (pseudo-term-substp x)
           (alistp x))
  :hints (("Goal" :in-theory (e/d (pseudo-term-substp) ()))))

(local
 (define mev-ctx-alist ((ctx pseudo-term-substp)
                        (al alistp))
   :returns (r alistp)
   (pairlis$ (strip-cars ctx)
             (mev-lst (strip-cdrs ctx) al))))

(local
 (define mev-ctxl-alist ((ctxl context-p)
                         (al alistp))
   :returns (r alistp :hyp :guard)
   (if (atom ctxl)
       al
     (mev-ctx-alist (car ctxl) (mev-ctxl-alist (cdr ctxl) al)))))

(local-defthm mev-ctxl-alist-of-append-list
  (equal (mev-ctxl-alist (append ctxl1 ctxl2) al)
         (mev-ctxl-alist ctxl1 (mev-ctxl-alist ctxl2 al)))
  :hints (("Goal" :in-theory (e/d (mev-ctxl-alist) ()))))

;; The following name is used in sorting bvfsl's.
(define bv-name ((bv bv-p))
  :returns (r stringp)
  (case (bv-kind bv)
    (:v (if (eql (bv-v->v bv) 0) "0" "1"))
    (:bit (concatenate 'string "s-" (string (bv-bit->v bv))))))

(define order-3-bvf ((a-n stringp)
                     (b-n stringp)
                     (c-n stringp)
                     (a bvf-p)
                     (b bvf-p)
                     (c bvf-p))
  :returns (mv (ra-n stringp :hyp :guard) (rb-n stringp :hyp :guard) (rc-n stringp :hyp :guard)
               (ra bvf-p :hyp :guard) (rb bvf-p :hyp :guard) (rc bvf-p :hyp :guard))
  (if (string< a-n b-n)
      (if (string< b-n c-n)
          (mv a-n b-n c-n a b c)
        (if (string< a-n c-n)
            (mv a-n c-n b-n a c b)
          (mv c-n a-n b-n c a b)))
    (if (string< a-n c-n)
        (mv b-n a-n c-n b a c)
      (if (string< b-n c-n)
          (mv b-n c-n a-n b c a)
        (mv c-n b-n a-n c b a)))))

;; Returns a bvf (:fa* a b c) such that a < b < c.
(define normalize-bvf ((bvf bvf-p))
  :returns (mv (r bvf-p) (r-n stringp))
  :verify-guards :after-returns
  (if (mbt (bvf-p bvf))
      (case (bvf-kind bvf)
        (:bv (mv bvf (bv-name (bvf-bv->bv bvf))))
        (:fas (b* (((mv a a-n) (normalize-bvf (bvf-fas->a bvf)))
                   ((mv b b-n) (normalize-bvf (bvf-fas->b bvf)))
                   ((mv c c-n) (normalize-bvf (bvf-fas->c bvf)))
                   ((mv a-n b-n c-n a b c) (order-3-bvf a-n b-n c-n a b c)))
                (mv (bvf-fas a b c) (concatenate 'string "{" a-n "," b-n "," c-n ",sum}"))))
        (:fac (b* (((mv a a-n) (normalize-bvf (bvf-fac->a bvf)))
                   ((mv b b-n) (normalize-bvf (bvf-fac->b bvf)))
                   ((mv c c-n) (normalize-bvf (bvf-fac->c bvf)))
                   ((mv a-n b-n c-n a b c) (order-3-bvf a-n b-n c-n a b c)))
                (mv (bvf-fac a b c) (concatenate 'string "{" a-n "," b-n "," c-n ",carry}"))))
        (t (mv (bvf-bv (bv-v 0)) "")))
    (mv (bvf-bv (bv-v 0)) "")))

;; normalize-bvf does not have an effect on its interpretation
(local-defthm interp-bvf-of-normalize-bvf
  (implies (bvf-p bvf)
           (equal (mev (interp-bvf (mv-nth 0 (normalize-bvf bvf))) al)
                  (mev (interp-bvf bvf) al)))
  :hints (("Goal" :in-theory (e/d (normalize-bvf
                                   order-3-bvf
                                   interp-bvf) ()))))

(define normalize-bvfs ((bvfs bvfs-p))
  :returns (r bvfs-p)
  (bvfs (mv-nth 0 (mv-list 2 (normalize-bvf (bvfs->bvf bvfs)))) (bvfs->sh bvfs)))

(local-defthm interp-bvfs-of-normalize-bvfs
  (equal (mev (interp-bvfs (normalize-bvfs bvfs)) al)
         (mev (interp-bvfs bvfs) al))
  :hints (("Goal" :in-theory (e/d (normalize-bvfs interp-bvfs) ()))))

(define normalize-bvfsl ((bvfsl bvfsl-p))
  :returns (r bvfsl-p)
  (if (atom bvfsl)
      nil
    (cons (normalize-bvfs (car bvfsl))
          (normalize-bvfsl (cdr bvfsl)))))

(local-defthm interp-bvfsl-of-normalize-bvfsl
  (equal (mev (interp-bvfsl (normalize-bvfsl bvfsl)) al)
         (mev (interp-bvfsl bvfsl) al))
  :hints (("Goal" :in-theory (e/d (normalize-bvfsl interp-bvfsl) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Function to make a substitution into a bit-value. Note: it returns a list of
;; symbols that need to be an integer (based on syntactic checks) for this
;; substitution to be correct.
(define subst-ctx-bv ((ctx pseudo-term-substp)
                      (x bv-p))
  :returns (mv (okp booleanp) (r bvf-p) (ivl symbol-listp))
  (case (bv-kind x)
    (:v (mv t (bvf-bv x) nil))
    (:bit (b* (((bv-bit x) x)
             (pair (assoc x.v ctx))
             ((unless (and x.v pair)) (mv nil (bvf-bv x) nil))
             ((mv okp res ivl) (get-nth-bit (cdr pair) x.n nil))
             ((unless okp) (mv nil (bvf-bv x) nil)))
          (mv t (mv-nth 0 (mv-list 2 (normalize-bvf res))) ivl)))
    (t (mv nil (bvf-bv x) nil))))

(local-defthm mev-cdr-assoc-equal-lemma
  (equal (cdr (assoc-equal x (pairlis$ (strip-cars ctx) (mev-lst (strip-cdrs ctx) al))))
         (mev (cdr (assoc-equal x ctx)) al))
  :hints (("Goal" :in-theory (e/d () ()))))

;; Interpretation of a bit-value after making substitution is the same as it's
;; value under a different evaluator alist.
(local-defthm interp-subst-ctx-bv
  (implies (and (mv-nth 0 (subst-ctx-bv ctx bv))
                (mev (interp-ivl (mv-nth 2 (subst-ctx-bv ctx bv))) al)
                (bv-p bv))
           (equal (mev (interp-bvf (mv-nth 1 (subst-ctx-bv ctx bv))) al)
                  (mev (interp-bv bv) (mev-ctx-alist ctx al))))
  :hints (("Goal" :in-theory (e/d (interp-bv
                                   subst-ctx-bv
                                   mev-ctx-alist
                                   interp-bvf) ()))))

;; Interpretation of a bit-value-form
(define subst-ctx-bvf ((ctx pseudo-term-substp)
                       (x bvf-p))
  :returns (mv (okp booleanp) (r bvf-p) (ivl symbol-listp))
  :verify-guards :after-returns
  (if (mbt (bvf-p x))
      (case (bvf-kind x)
        (:bv (b* (((bvf-bv x) x))
               (subst-ctx-bv ctx x.bv)))
        (:fas (b* (((bvf-fas x) x)
                   ((mv oka a aivl) (subst-ctx-bvf ctx x.a))
                   ((mv okb b bivl) (subst-ctx-bvf ctx x.b))
                   ((mv okc c civl) (subst-ctx-bvf ctx x.c))
                   ((unless (and oka okb okc)) (mv nil (bvf-bv (bv-v 0)) nil)))
                (mv t (mv-nth 0 (mv-list 2 (normalize-bvf (bvf-fas a b c))))
                    (union$ aivl bivl civl :test 'eq))))
        (:fac (b* (((bvf-fac x) x)
                   ((mv oka a aivl) (subst-ctx-bvf ctx x.a))
                   ((mv okb b bivl) (subst-ctx-bvf ctx x.b))
                   ((mv okc c civl) (subst-ctx-bvf ctx x.c))
                   ((unless (and oka okb okc)) (mv nil (bvf-bv (bv-v 0)) nil)))
                (mv t (mv-nth 0 (mv-list 2 (normalize-bvf (bvf-fac a b c))))
                    (union$ aivl bivl civl :test 'eq))))
        (t (mv nil (bvf-bv (bv-v 0)) nil)))
    (mv nil (bvf-bv (bv-v 0)) nil)))

(local-defthm interp-subst-ctx-bvf
  (implies (and (mv-nth 0 (subst-ctx-bvf ctx bvf))
                (mev (interp-ivl (mv-nth 2 (subst-ctx-bvf ctx bvf))) al))
           (equal (mev (interp-bvf (mv-nth 1 (subst-ctx-bvf ctx bvf))) al)
                  (mev (interp-bvf bvf) (mev-ctx-alist ctx al))))
  :hints (("Goal" :in-theory (e/d (subst-ctx-bvf
                                   interp-bvf) ()))))

(define subst-ctx-bvfs ((ctx pseudo-term-substp)
                        (bvfs bvfs-p))
  :returns (mv (okp booleanp) (r bvfs-p) (ivl symbol-listp))
  (b* (((mv okp bvf ivl) (subst-ctx-bvf ctx (bvfs->bvf bvfs))))
    (if okp
        (mv t (bvfs bvf (bvfs->sh bvfs)) ivl)
      (mv nil (bvfs (bvf-bv (bv-v 0)) 0) nil))))

(local-defthm interp-subst-ctx-bvfs
  (implies (and (mv-nth 0 (subst-ctx-bvfs ctx bvfs))
                (mev (interp-ivl (mv-nth 2 (subst-ctx-bvfs ctx bvfs))) al))
           (equal (mev (interp-bvfs (mv-nth 1 (subst-ctx-bvfs ctx bvfs))) al)
                  (mev (interp-bvfs bvfs) (mev-ctx-alist ctx al))))
  :hints (("Goal" :in-theory (e/d (interp-bvfs
                                   subst-ctx-bvfs) ()))))

(define subst-ctx-bvfsl ((ctx pseudo-term-substp)
                         (bvfsl bvfsl-p))
  :returns (mv (okp booleanp) (r bvfsl-p) (ivl symbol-listp))
  :verify-guards :after-returns
  (if (consp bvfsl)
      (b* (((mv ok1 bvfs1 ivl1) (subst-ctx-bvfs ctx (car bvfsl)))
           ((unless ok1)
            (prog2$ (cw "Error subtituting BVFS: ~x0~%" (car bvfsl))
                    (mv nil nil nil)))
           ((mv okrest rest rivl) (subst-ctx-bvfsl ctx (cdr bvfsl)))
           ((unless okrest) (mv nil nil nil)))
        (mv t (cons bvfs1 rest) (union$ ivl1 rivl :test 'eq)))
    (mv t nil nil)))

(local-defthm interp-of-subst-ctx-bvfsl
  (implies (and (mv-nth 0 (subst-ctx-bvfsl ctx bvfsl))
                (mev (interp-ivl (mv-nth 2 (subst-ctx-bvfsl ctx bvfsl))) al))
           (equal (mev (interp-bvfsl (mv-nth 1 (subst-ctx-bvfsl ctx bvfsl))) al)
                  (mev (interp-bvfsl bvfsl) (mev-ctx-alist ctx al))))
  :hints (("Goal" :in-theory (e/d (subst-ctx-bvfsl
                                   interp-bvfsl) ()))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local-defthm type-strip-cars-cdrs-of-ctx
  (implies (pseudo-term-substp ctx)
           (and (symbol-listp (strip-cars ctx))
                (pseudo-term-listp (strip-cdrs ctx))))
  :hints (("Goal" :in-theory (e/d (pseudo-term-substp) ()))))

(local-defthm len-strip-cars-strip-cdr
  (equal (len (strip-cars x)) (len (strip-cdrs x)))
  :hints (("Goal" :in-theory (e/d () ()))))

(define bvf-name ((bvf bvf-p))
  :returns (r stringp)
  :verify-guards :after-returns
  (if (mbt (bvf-p bvf))
      (case (bvf-kind bvf)
        (:bv (bv-name (bvf-bv->bv bvf)))
        (:fas (concatenate 'string
                           "{"
                           (bvf-name (bvf-fas->a bvf)) ","
                           (bvf-name (bvf-fas->b bvf)) ","
                           (bvf-name (bvf-fas->c bvf)) ",sum}"))
        (:fac (concatenate 'string
                           "{"
                           (bvf-name (bvf-fac->a bvf)) ","
                           (bvf-name (bvf-fac->b bvf)) ","
                           (bvf-name (bvf-fac->c bvf)) ",carry}"))
        (t ""))
    ""))

(define bvf> ((bvf1 bvf-p)
              (bvf2 bvf-p))
  :returns (r booleanp)
  (if (string< (bvf-name bvf2) (bvf-name bvf1)) t nil))

;; total order on bvfs, which keeps the bvfs with the same shift-values
;; together.
(define bvfs> ((bvfs1 bvfs-p)
               (bvfs2 bvfs-p))
  :returns (r booleanp)
  (if (> (bvfs->sh bvfs1) (bvfs->sh bvfs2))
      t
    (if (= (bvfs->sh bvfs1) (bvfs->sh bvfs2))
        (bvf> (bvfs->bvf bvfs1) (bvfs->bvf bvfs2))
      nil)))

;; total order on bvfs which keeps the bvfs with the same names together.
(define bvfs2> ((bvfs1 bvfs-p)
                (bvfs2 bvfs-p))
  ;; Needed for merging runs of bits later
  :returns (r booleanp)
  (or (bvf> (bvfs->bvf bvfs1) (bvfs->bvf bvfs2))
      (and (not (bvf> (bvfs->bvf bvfs2) (bvfs->bvf bvfs1)))
           (> (bvfs->sh bvfs1) (bvfs->sh bvfs2)))))

(define merge-bvfsl ((x bvfsl-p)
                     (y bvfsl-p))
  :returns (r bvfsl-p :hyp :guard)
  :measure (+ (acl2-count x) (acl2-count y))
  (cond ((atom x) y)
        ((atom y) x)
        ((bvfs> (car x) (car y))
         (cons (car x) (merge-bvfsl (cdr x) y)))
        (t (cons (car y) (merge-bvfsl x (cdr y))))))

(define merge-bvfsl2 ((x bvfsl-p)
                     (y bvfsl-p))
  :returns (r bvfsl-p :hyp :guard)
  :measure (+ (acl2-count x) (acl2-count y))
  (cond ((atom x) y)
        ((atom y) x)
        ((bvfs2> (car x) (car y))
         (cons (car x) (merge-bvfsl2 (cdr x) y)))
        (t (cons (car y) (merge-bvfsl2 x (cdr y))))))

(local-defthm len-take-ub
  (implies (natp n) (<= (len (take n l)) n))
  :hints (("Goal" :in-theory (e/d () ())))
  :rule-classes :linear)

(local-defthm len-nth-cdr-ub
  (implies (and (natp n) (<= n (len l)))
           (equal (len (nthcdr n l)) (- (len l) n)))
  :hints (("Goal" :in-theory (e/d () ()))))

(encapsulate ()
  (local (arith-5-for-rtl))
  (define sort-bvfsl ((x bvfsl-p))
    :returns (r bvfsl-p :hyp :guard)
    :measure (len x)
    :verify-guards :after-returns
    (cond ((atom x) nil)
          ((atom (cdr x)) (list (car x)))
          (t (let ((half (floor (len x) 2)))
               (merge-bvfsl (sort-bvfsl (take half x))
                            (sort-bvfsl (nthcdr half x))))))))

(encapsulate ()
  (local (arith-5-for-rtl))
  (define sort-bvfsl2 ((x bvfsl-p))
    :returns (r bvfsl-p :hyp :guard)
    :measure (len x)
    :verify-guards :after-returns
    (cond ((atom x) nil)
          ((atom (cdr x)) (list (car x)))
          (t (let ((half (floor (len x) 2)))
               (merge-bvfsl2 (sort-bvfsl2 (take half x))
                             (sort-bvfsl2 (nthcdr half x))))))))

(local-defthm interp-bvfsl-of-cons
  (equal (mev (interp-bvfsl (cons x y)) al)
         (+ (mev (interp-bvfs x) al) (mev (interp-bvfsl y) al)))
  :hints (("Goal" :in-theory (e/d (interp-bvfsl) ()))))

(local-defthm interp-bvfsl-of-atom
  (implies (atom x)
           (equal (mev (interp-bvfsl x) al) 0))
  :hints (("Goal" :in-theory (e/d (interp-bvfsl) ()))))

(local-defthm interp-of-merge-bvfsl
  (equal (mev (interp-bvfsl (merge-bvfsl bvfsl1 bvfsl2)) al)
         (mev (interp-bvfsl (append bvfsl1 bvfsl2)) al))
  :hints (("Goal" :in-theory (e/d (merge-bvfsl) ())
                  :induct (merge-bvfsl bvfsl1 bvfsl2))))

(local-defthm interp-of-merge-bvfsl2
  (equal (mev (interp-bvfsl (merge-bvfsl2 bvfsl1 bvfsl2)) al)
         (mev (interp-bvfsl (append bvfsl1 bvfsl2)) al))
  :hints (("Goal" :in-theory (e/d (merge-bvfsl2) ())
                  :induct (merge-bvfsl2 bvfsl1 bvfsl2))))

(local-defthm append-take-nthcdr
  (implies (and (natp n) (<= n (len l))) (equal (append (take n l) (nthcdr n l)) l))
  :hints (("Goal" :in-theory (e/d () ()))))

(local
 (encapsulate ()
   (local (arith-5-for-rtl))
   (defthm floor<=x
     (implies (natp x)
              (and (<= (floor x 2) x)
                   (>= (floor x 2) 0)))
     :rule-classes :linear)))

;; Sorting bvfsl does not change its interpretation.
(local-defthm interp-of-sort-bvfsl
  (equal (mev (interp-bvfsl (sort-bvfsl bvfsl)) al)
         (mev (interp-bvfsl bvfsl) al))
  :hints (("Goal" :in-theory (e/d (sort-bvfsl) (interp-bvfsl-of-append
                                                floor)))
          ("Subgoal *1/3"
           :use ((:instance interp-bvfsl-of-append
                  (x (sort-bvfsl (take (floor (len bvfsl) 2) bvfsl)))
                  (y (sort-bvfsl (nthcdr (floor (len bvfsl) 2) bvfsl))))
                 (:instance interp-bvfsl-of-append
                  (x (take (floor (len bvfsl) 2) bvfsl))
                  (y (nthcdr (floor (len bvfsl) 2) bvfsl)))))))

(local-defthm interp-of-sort-bvfsl2
  (equal (mev (interp-bvfsl (sort-bvfsl2 bvfsl)) al)
         (mev (interp-bvfsl bvfsl) al))
  :hints (("Goal" :in-theory (e/d (sort-bvfsl2) (interp-bvfsl-of-append
                                                floor)))
          ("Subgoal *1/3"
           :use ((:instance interp-bvfsl-of-append
                  (x (sort-bvfsl2 (take (floor (len bvfsl) 2) bvfsl)))
                  (y (sort-bvfsl2 (nthcdr (floor (len bvfsl) 2) bvfsl))))
                 (:instance interp-bvfsl-of-append
                  (x (take (floor (len bvfsl) 2) bvfsl))
                  (y (nthcdr (floor (len bvfsl) 2) bvfsl)))))))

(define insert-sorted ((bvfs bvfs-p)
                       (bvfsl bvfsl-p))
  :returns (r bvfsl-p :hyp :guard)
  (if (atom bvfsl)
      (list bvfs)
    (if (bvfs> bvfs (car bvfsl))
        (cons bvfs bvfsl)
      (cons (car bvfsl) (insert-sorted bvfs (cdr bvfsl))))))

(local-defthm interp-of-insert-sorted
  (equal (mev (interp-bvfsl (insert-sorted bvfs bvfsl)) al)
         (+ (mev (interp-bvfs bvfs) al) (mev (interp-bvfsl bvfsl) al)))
  :hints (("Goal" :in-theory (e/d (insert-sorted interp-bvfsl) ()))))

;; Prune constant zero bit-values from bvfsl
(define prune-zero ((bvfsl bvfsl-p))
  :returns (r bvfsl-p :hyp :guard)
  (if (atom bvfsl)
      nil
    (b* ((bvf (bvfs->bvf (car bvfsl))))
      (if (and (eq (bvf-kind bvf) :bv)
               (equal (bvf-bv->bv bvf) (bv-v 0)))
          (prune-zero (cdr bvfsl))
        (cons (car bvfsl) (prune-zero (cdr bvfsl)))))))

(local-defthm interp-of-prune-zero
  (equal (mev (interp-bvfsl (prune-zero bvfsl)) al)
         (mev (interp-bvfsl bvfsl) al))
  :hints (("Goal" :in-theory (e/d (prune-zero
                                   interp-bvfsl
                                   interp-bvfs
                                   interp-bvf) ()))))

;; prune bvfs with shift larger that `w`.
(define prune-large-shift ((bvfsl bvfsl-p)
                           (w natp))
  :returns (r bvfsl-p :hyp :guard)
  (if (atom bvfsl)
      nil
    (if (< (bvfs->sh (car bvfsl)) w)
        (cons (car bvfsl) (prune-large-shift (cdr bvfsl) w))
      (prune-large-shift (cdr bvfsl) w))))

(local
 (encapsulate ()
   (local (arith-5-for-rtl))
   (defthm interp-of-prune-large-shift
     (implies (natp w)
              (equal (bits (mev (interp-bvfsl (prune-large-shift bvfsl w)) al) (1- w) 0)
                     (bits (mev (interp-bvfsl bvfsl) al) (1- w) 0)))
     :hints (("Goal" :in-theory (e/d (interp-bvfsl
                                      prune-large-shift
                                      interp-bvfs
                                      bits-plus-mult-2-meta) ()))
             ("Subgoal *1/2"
              :use ((:instance bits-bits-sum
                     (x (mev (interp-bvfsl (prune-large-shift (cdr bvfsl) w)) al))
                     (k (1- w))
                     (y (mev (interp-bvfs (car bvfsl)) al))
                     (i (1- w)) (j 0))))))))

;; Replace a (bvfs (:fas a b c) n) with (bvfs a n) (bvfs b n) (bvfs c n) when n
;; = (1- w). Assumes that bvfsl are sorted using bvfs>.
(define replace-sum-at-boundary ((bvfsl bvfsl-p)
                                (w natp))
  :returns (r bvfsl-p :hyp :guard)
  (if (or (atom bvfsl) (< (bvfs->sh (car bvfsl)) (1- w)))
      bvfsl
    (case (bvf-kind (bvfs->bvf (car bvfsl)))
      (:fas  (b* (((bvf-fas bvf) (bvfs->bvf (car bvfsl)))
                  (sh (bvfs->sh (car bvfsl)))
                  (a (bvfs bvf.a sh))
                  (b (bvfs bvf.b sh))
                  (c (bvfs bvf.c sh)))
               (insert-sorted a (insert-sorted b (insert-sorted c (replace-sum-at-boundary (cdr bvfsl) w))))))
      (t (cons (car bvfsl) (replace-sum-at-boundary (cdr bvfsl) w))))))

(local-defthm integerp-interp-bv
  (integerp (mev (interp-bv x) al))
  :hints (("Goal" :in-theory (e/d (interp-bv) ())))
  :rule-classes :type-prescription)

(local-defthm integerp-interp-bvf
  (integerp (mev (interp-bvf x) al))
  :hints (("Goal" :in-theory (e/d (interp-bvf) ())))
  :rule-classes :type-prescription)

(local
 (encapsulate ()
   (local (arith-5-for-rtl))
   (local-defthm logxor-rw
     (implies (and (integerp x) (integerp y) (integerp z))
              (equal (logxor x y z) (- (+ x y z) (* 2 (logior (logand x y) (logand y z) (logand z x))))))
     :hints (("Goal" :use (add-3))))

   (defthm interp-of-replace-sum-at-boundary
     (implies (natp w)
              (equal (bits (mev (interp-bvfsl (replace-sum-at-boundary bvfsl w)) al) (1- w) 0)
                     (bits (mev (interp-bvfsl bvfsl) al) (1- w) 0)))
     :hints (("Goal" :in-theory (e/d (interp-bvfsl
                                      replace-sum-at-boundary
                                      interp-bvfs
                                      bits-plus-mult-2-meta
                                      interp-bvf) ()))
             ("Subgoal *1/2" :cases ((< (bvfs->sh (car bvfsl)) w))
                             :use ((:instance bits-bits-sum
                                    (x (mev (interp-bvfsl (replace-sum-at-boundary (cdr bvfsl) w)) al))
                                    (k (1- w))
                                    (y (+ (* (expt 2 (bvfs->sh (car bvfsl)))
                                             (mev (interp-bvf (bvf-fas->a (bvfs->bvf (car bvfsl))))
                                                  al))
                                          (* (expt 2 (bvfs->sh (car bvfsl)))
                                             (mev (interp-bvf (bvf-fas->b (bvfs->bvf (car bvfsl))))
                                                  al))
                                          (* (expt 2 (bvfs->sh (car bvfsl)))
                                             (mev (interp-bvf (bvf-fas->c (bvfs->bvf (car bvfsl))))
                                                  al))))
                                    (i (1- w)) (j 0))
                                   (:instance bits-bits-sum
                                    (x (mev (interp-bvfsl (replace-sum-at-boundary (cdr bvfsl) w)) al))
                                    (k (1- w))
                                    (y (mev (interp-bvfs (car bvfsl)) al))
                                    (i (1- w)) (j 0))))))
   ))

;; Search and replace a (bvfs (:fas a b c) sh) with (bvfs a sh) (bvfs b sh) and
;; (bvfs c sh).
(define replace-sum ((bvfsl bvfsl-p)
                    (a bvf-p)
                    (b bvf-p)
                    (c bvf-p)
                    (sh natp))
  :returns (mv (matchedp booleanp) (r bvfsl-p :hyp :guard))
  (if (atom bvfsl)
      (mv nil bvfsl)
    (case (bvf-kind (bvfs->bvf (car bvfsl)))
      (:bv (b* (((mv matchedp rest) (replace-sum (cdr bvfsl) a b c sh)))
               (mv matchedp (cons (car bvfsl) rest))))
      (:fas (b* (((bvf-fas f) (bvfs->bvf (car bvfsl))))
              (if (and (equal f.a a)
                       (equal f.b b)
                       (equal f.c c)
                       (equal (bvfs->sh (car bvfsl)) sh))
                  (mv t (insert-sorted
                         (bvfs a sh)
                         (insert-sorted
                          (bvfs b sh)
                          (insert-sorted
                           (bvfs c sh)
                           (cdr bvfsl)))))
               (b* (((mv matchedp rest) (replace-sum (cdr bvfsl) a b c sh)))
                 (mv matchedp (cons (car bvfsl) rest))))))
      (:fac (b* (((mv matchedp rest) (replace-sum (cdr bvfsl) a b c sh)))
              (mv matchedp (cons (car bvfsl) rest))))
      (t (mv nil nil)))))

(local
 (encapsulate ()
   (local (arith-5-for-rtl))
   (local-defthm logxor-rw
     (implies (and (integerp x) (integerp y) (integerp z))
              (equal (logxor x y z) (- (+ x y z) (* 2 (logior (logand x y) (logand y z) (logand z x))))))
     :hints (("Goal" :use (add-3))))
   (defthm interp-of-replace-sum
     (and (implies (mv-nth 0 (replace-sum bvfsl a b c sh))
                   (equal (mev (interp-bvfsl (mv-nth 1 (replace-sum bvfsl a b c sh))) al)
                          (+ (mev (interp-bvfsl bvfsl) al)
                             (* (expt 2 (1+ sh))
                                (logior (logand (mev (interp-bvf a) al) (mev (interp-bvf b) al))
                                        (logand (mev (interp-bvf a) al) (mev (interp-bvf c) al))
                                        (logand (mev (interp-bvf b) al) (mev (interp-bvf c) al)))))))
          (implies (case-split (not (mv-nth 0 (replace-sum bvfsl a b c sh))))
                   (equal (mv-nth 1 (replace-sum bvfsl a b c sh)) bvfsl)))
     :hints (("Goal" :in-theory (e/d (replace-sum
                                      interp-bvfsl
                                      interp-bvfs)
                                     ())
                     :expand ((interp-bvf (bvfs->bvf (car bvfsl)))))))))

(define count-sums-bvf ((bvf bvf-p))
  :returns (r natp)
  :enabled t
  (if (bvf-p bvf)
      (case (bvf-kind bvf)
        (:fas (+ 1 (count-sums-bvf (bvf-fas->a bvf)) (count-sums-bvf (bvf-fas->b bvf)) (count-sums-bvf (bvf-fas->c bvf))))
        (:fac (+ (count-sums-bvf (bvf-fac->a bvf)) (count-sums-bvf (bvf-fac->b bvf)) (count-sums-bvf (bvf-fac->c bvf))))
        (t 0))
    0))

(define count-sums-bvfsl ((bvfsl bvfsl-p))
  :enabled t
  :returns (r natp)
  (if (atom bvfsl)
      0
    (+ (count-sums-bvf (bvfs->bvf (car bvfsl))) (count-sums-bvfsl (cdr bvfsl)))))

(local-defthm count-sums-bvfl-of-cdr-ub
  (<= (count-sums-bvfsl (cdr bvfsl)) (count-sums-bvfsl bvfsl))
  :rule-classes :linear)

(local-defthm count-sums-insert-sorted-lemma
  (equal (count-sums-bvfsl (insert-sorted x y))
         (+ (count-sums-bvf (bvfs->bvf x)) (count-sums-bvfsl y)))
  :hints (("Goal" :in-theory (e/d (insert-sorted) ()))))

(local-defthm count-sums-lower-when-replace-sums
  (b* (((mv matchedp res) (replace-sum bvfsl a b c sh)))
    (implies matchedp
             (< (count-sums-bvfsl res) (count-sums-bvfsl bvfsl))))
  :hints (("Goal" :in-theory (e/d (replace-sum) (interp-of-replace-sum))))
  :rule-classes :linear)

;; For every carry-form, search and replace the sum-form with list of 3 bvfs
;; (applying add-3 lemma)
(define match-elim ((bvfsl bvfsl-p))
  :returns (r bvfsl-p :hyp :guard)
  :measure (cons (cons 1 (1+ (count-sums-bvfsl bvfsl))) (acl2-count bvfsl))
  :hints (("Goal" :in-theory (e/d () (count-sums-bvfsl))
                  :do-not-induct t))
  :otf-flg nil
  (if (atom bvfsl)
      nil
    (case (bvf-kind (bvfs->bvf (car bvfsl)))
      (:bv (cons (car bvfsl) (match-elim (cdr bvfsl))))
      (:fas (cons (car bvfsl) (match-elim (cdr bvfsl))))
      (:fac (b* (((bvf-fac f) (bvfs->bvf (car bvfsl)))
                 (sh (bvfs->sh (car bvfsl)))
                 ((unless (> sh 0)) (cons (car bvfsl) (match-elim (cdr bvfsl))))
                 ((mv matchedp rest) (replace-sum (cdr bvfsl) f.a f.b f.c (1- sh)))
                 (rest (match-elim rest)))
              (if matchedp
                  rest
                (cons (car bvfsl) rest)))))))

(local
 (encapsulate ()
   (local (arith-5-for-rtl))
   (local-defthm logxor-rw
     (implies (and (integerp x) (integerp y) (integerp z))
              (equal (logxor x y z) (- (+ x y z) (* 2 (logior (logand x y) (logand y z) (logand z x))))))
     :hints (("Goal" :use (add-3))))
   (defthm interp-of-match-elim
     (equal (mev (interp-bvfsl (match-elim bvfsl)) al)
            (mev (interp-bvfsl bvfsl) al))
     :hints (("Goal" :in-theory (e/d (match-elim interp-bvfsl
                                      interp-bvfs
                                      interp-bvf) ()))))))

(local-defthm true-listp-union-equal
  (implies (and (true-listp x) (true-listp y))
           (true-listp (union-equal x y))))

(define ivl-term ((term pseudo-termp))
  :returns (mv (okp booleanp) (r symbol-listp))
  (cond ((and term (atom term) (mbt (symbolp term)))
         (mv t (list term)))
        ((quotep term)
         (if (integerp (unquote term))
             (mv t nil)
           (mv nil nil)))
        ((member-eq (car term) '(bits bitn setbitn setbits))
         (mv t nil))
        ((member-eq (car term) '(binary-logior binary-logand binary-logxor))
         (b* (((mv okl left) (ivl-term (cadr term)))
              ((mv okr right) (ivl-term (caddr term)))
              ((unless (and okl okr)) (mv nil nil)))
           (mv t (union$ left right :test 'eq))))
        (t
         (mbe :logic (mv nil nil)
              :exec
              (prog2$ (cw "Cannot demonstrate that ~x0 is an integer~%" term)
                      (mv nil nil))))))

(local-defthm mev-ivl-term-lemma
  (implies (and (mv-nth 0 (ivl-term term))
                (mev (interp-ivl (mv-nth 1 (ivl-term term))) al))
           (integerp (mev term al)))
  :hints (("Goal" :in-theory (e/d (ivl-term interp-ivl) ()))))

(define resolve-iv-ctx ((ctx pseudo-term-substp)
                        (iv symbolp))
  :returns (mv (okp booleanp) (r symbol-listp))
  (b* ((pair (assoc-eq iv ctx))
       ((unless (and iv pair)) (mv nil nil))
       ((mv okp ivl) (ivl-term (cdr pair)))
       ((unless okp) (mv nil nil)))
    (mv t ivl)))

(local-defthm mev-resolve-iv-ctx-lemma
  (implies (and (mv-nth 0 (resolve-iv-ctx ctx iv))
                (symbolp iv)
                (mev (interp-ivl (mv-nth 1 (resolve-iv-ctx ctx iv))) al))
           (integerp (cdr (assoc-equal iv (mev-ctx-alist ctx al)))))
  :hints (("Goal" :in-theory (e/d (interp-ivl
                                   resolve-iv-ctx
                                   mev-ctx-alist) ()))))

(define resolve-ivl-ctx ((ctx pseudo-term-substp)
                         (ivl symbol-listp))
  :returns (mv (okp booleanp) (r symbol-listp))
  (if (atom ivl)
      (mv t nil)
    (b* (((mv ok1 ivl1) (resolve-iv-ctx ctx (car ivl)))
         ((unless ok1) (mv nil nil))
         ((mv ok2 ivl2) (resolve-ivl-ctx ctx (cdr ivl)))
         ((unless ok2) (mv nil nil)))
      (mv t (union$ ivl1 ivl2 :test 'eq)))))

(local-defthm mev-resolve-ivl-ctx-lemma
  (implies (and (mv-nth 0 (resolve-ivl-ctx ctx ivl))
                (symbol-listp ivl)
                (mev (interp-ivl (mv-nth 1 (resolve-ivl-ctx ctx ivl))) al))
           (mev (interp-ivl ivl) (mev-ctx-alist ctx al)))
  :hints (("Goal" :in-theory (e/d (resolve-ivl-ctx
                                   interp-ivl) ())
                  :expand ((resolve-iv-ctx ctx nil)))))

;; The main sequence of operations applied every time a variable substitution
;; is applied.
(define cl-main ((ctx pseudo-term-substp)
                 (bvfsl bvfsl-p)
                 (ivl symbol-listp)
                 (w natp))
  :returns (mv (okp booleanp) (r bvfsl-p :hyp :guard) (rivl symbol-listp :hyp (symbol-listp ivl)))
  (b* ((bvfsl (sort-bvfsl bvfsl))
       (bvfsl (prune-large-shift bvfsl w))
       (bvfsl (prune-zero bvfsl))
       (bvfsl (replace-sum-at-boundary bvfsl w))
       (bvfsl (match-elim bvfsl))
       ((mv okp new-bvfsl ivl-new) (subst-ctx-bvfsl ctx bvfsl))
       ((unless okp)
        (prog2$ (cw "Subtitution failed!~%")
                (mv nil nil nil)))
       ((mv okp ivl-resolved) (resolve-ivl-ctx ctx ivl))
       ((unless okp)
        (prog2$ (cw "Resolving IVL failed!~%")
                (mv nil nil nil))))
    (mv t new-bvfsl (union$ ivl-new ivl-resolved :test 'eq))))

(local-defthm interp-cl-main-lemma
  (b* (((mv okp rbvfsl rivl) (cl-main ctx bvfsl ivl w)))
    (implies (and okp
                  (natp w)
                  (symbol-listp ivl)
                  (mev (interp-ivl rivl) al))
             (and (mev (interp-ivl ivl) (mev-ctx-alist ctx al))
                  (equal (bits (mev (interp-bvfsl rbvfsl) al) (1- w) 0)
                         (bits (mev (interp-bvfsl bvfsl) (mev-ctx-alist ctx al)) (1- w) 0)))))
  :hints (("Goal" :in-theory (e/d (cl-main) ())
                  :do-not-induct t)))

;; Main clause-process simplifier loop
(define cl-main-loop ((ctxl context-p)
                      (bvfsl bvfsl-p)
                      (ivl symbol-listp)
                      (w natp))
  :returns (mv (okp booleanp) (r bvfsl-p :hyp :guard) (rivl symbol-listp :hyp (symbol-listp ivl)))
  (prog2$ (cw "CTV-CP: Substitution depth: ~x0~%" (len ctxl))
          (if (atom ctxl)
              (mv t bvfsl ivl)
            (b* (((mv okp bvfsl-new ivl-new) (cl-main (car ctxl) bvfsl ivl w))
                 ((unless okp) (mv nil nil nil)))
              (cl-main-loop (cdr ctxl) bvfsl-new ivl-new w)))))

(local-defthm interp-cl-main-loop-lemma
  (implies (and (mv-nth 0 (cl-main-loop ctxl bvfsl ivl w))
                (symbol-listp ivl)
                (natp w)
                (mev (interp-ivl (mv-nth 2 (cl-main-loop ctxl bvfsl ivl w))) al))
           (and (mev (interp-ivl ivl) (mev-ctxl-alist ctxl al))
                (equal (bits (mev (interp-bvfsl (mv-nth 1 (cl-main-loop ctxl bvfsl ivl w))) al) (1- w) 0)
                       (bits (mev (interp-bvfsl bvfsl) (mev-ctxl-alist ctxl al)) (1- w) 0))))
  :hints (("Goal" :in-theory (e/d (cl-main-loop mev-ctxl-alist) ()))))

(local-defthm len-remove1
  (implies (member x y)
           (equal (len (remove1 x y)) (1- (len y)))))

(local-defthm symbol-list-p-of-remove1
  (implies (symbol-listp x)
           (symbol-listp (remove1 y x))))

(local-defthm context-p-implies-true-listp
  (implies (context-p x)
           (true-listp x)))

(local-defthm symbol-listp-implies-true-listp
  (implies (symbol-listp x)
           (true-listp x)))

(local-defthm match-tree-lemma-1
  (implies (and (MV-NTH 0
                        (MATCH-TREE '(BITS (:? T1) '(:? W) '0)
                                          TERM NIL))
                (pseudo-termp term))
           (PSEUDO-TERMP
            (CDR (ASSOC-EQUAL 'T1
                              (MATCH-TREE-ALIST '(BITS (:? T1) '(:? W) '0)
                                                      TERM NIL)))))
  :hints (("Goal" :in-theory (e/d (match-tree-obj-equals-subst-and-open-when-successful) ()))))

(defoption maybe-nat
                natp
                :pred maybe-natp)

;; Get the inner-most term while building the context and infering the width of
;; the expression.
(define build-ctx-and-get-inner-term ((term pseudo-termp)
                                      (fn-list symbol-listp)
                                      state)
  :measure (cons (cons 1 (1+ (len fn-list))) (acl2-count term))
  :hints (("Goal" :in-theory (e/d (match-tree-obj-equals-subst-and-open-when-successful) ())))
  :returns (mv (okp booleanp) (ctxl context-p :hyp :guard) (r pseudo-termp :hyp :guard) (w maybe-natp))
  :verify-guards :after-returns
  :guard-hints (("Goal" :in-theory (e/d (match-tree-obj-equals-subst-and-open-when-successful) ())))
  (treematch-when term
    ((bits (:? t1) (quote (:? w)) '0)
     :when (natp w)
     (b* (((mv okp ctxl term w2) (build-ctx-and-get-inner-term t1 fn-list state)))
       (if (or (not (natp w2)) (> w2 w))
           (mv okp ctxl term (1+ w))
         (mv okp ctxl term w2))))
    (&
     (if (and (consp term)
              (flambda-applicationp term)
              (mbt (and (equal (len (car term)) 3)
                        (eq (caar term) 'lambda)
                        (symbol-listp (cadr (car term)))
                        (pseudo-termp (caddr (car term)))
                        (pseudo-term-listp (cdr term))
                        (equal (len (cadr (car term)))
                               (len (cdr term))))))
         (b* ((lambda-form (ffn-symb term))
              (formals (lambda-formals lambda-form))
              ((when (member-eq nil formals)) (mv nil nil nil nil))
              (body (lambda-body lambda-form))
              (actuals (fargs term))
              (ctx (pairlis$ formals actuals))
              ((mv okp ctxl term w) (build-ctx-and-get-inner-term body fn-list state))
              ((unless okp) (mv nil nil nil nil)))
           (mv okp (append ctxl (list ctx)) term w))
       (if (and (consp term)
                (not (eq (car term) 'bits))
                (not (quotep term))
                (member-eq (car term) fn-list))
           (b* (((mv okp formals body) (fn-get-def (car term) state))
                (- (if (not okp) (cw "Failed to retrieve body of function ~x0!~%" (car term)) nil))
                ((unless (and okp
                              (mbt (not (member-eq nil formals)))
                              (pseudo-termp body)
                              (equal (len formals) (len (fargs term)))))
                 (mv nil nil nil nil))
                (fn-list (remove1 (car term) fn-list))
                (actuals (fargs term))
                (ctx (pairlis$ formals actuals))
                ((mv okp ctxl term w) (build-ctx-and-get-inner-term body fn-list state))
                ((unless okp) (mv nil nil nil nil)))
             (mv okp (append ctxl (list ctx)) term w))
         (mv t nil term nil))))))

(local
 (define ind-fn ((term pseudo-termp) fn-list al state)
   :measure (cons (cons 1 (1+ (len fn-list))) (acl2-count term))
   :verify-guards nil
   :irrelevant-formals-ok t
   :hints (("Goal" :in-theory (e/d (match-tree-obj-equals-subst-and-open-when-successful) ())))
  (treematch-when term
                  ((bits (:? t1) (quote (:? w)) '0)
                   :when (natp w)
      (ind-fn t1 fn-list al state))
    (& (if (and (consp term)
                (flambda-applicationp term)
                (equal (len (car term)) 3)
                (eq (caar term) 'lambda)
                (symbol-listp (cadr (car term)))
                (pseudo-termp (caddr (car term)))
                (pseudo-term-listp (cdr term))
                (equal (len (cadr (car term)))
                       (len (cdr term))))
           (b* ((lambda-form (ffn-symb term))
                (formals (lambda-formals lambda-form))
                (body (lambda-body lambda-form))
                (actuals (fargs term))
                (ctx (pairlis$ formals (mev-lst actuals al))))
             (ind-fn body fn-list ctx state))
         (if (and (consp term)
                  (not (quotep term))
                  (not (eq (car term) 'bits))
                  (member-eq (car term) fn-list))
             (b* (((mv ? formals body) (fn-get-def (car term) state))
                  (fn-list (remove1 (car term) fn-list))
                  (actuals (fargs term))
                  (ctx (pairlis$ formals (mev-lst actuals al))))
               (ind-fn body fn-list ctx state))
           nil))))))

(local-defthm mev-list-pairlis-ctx-alist
  (equal (mev-ctxl-alist (list (pairlis$ x y)) al)
         (pairlis$ x (mev-lst y al)))
  :hints (("Goal" :in-theory (e/d (mev-ctxl-alist
                                   mev-ctx-alist) ()))))

(local-defthm maybe-natp-non-nil
  (implies (and (maybe-natp x)
                x)
           (integerp x))
  :hints (("Goal" :in-theory (e/d () ())
                  :use (natp-when-maybe-natp))))

(local-defthm maybe-natp-non-nil-2
  (implies (and (maybe-natp x)
                x)
           (not (< x 0)))
  :hints (("Goal" :in-theory (e/d () ())
                  :use (natp-when-maybe-natp))))

(local-defthm maybe-natp-non-nil-3
  (implies (maybe-natp x)
           (iff (acl2-numberp x)
                (integerp x)))
  :hints (("Goal" :in-theory (e/d () ())
                  :use (natp-when-maybe-natp))))

(local-defthm mev-of-build-ctx-and-get-inner-term
  (b* (((mv okp ctxl rterm w)
        (build-ctx-and-get-inner-term term fn-list state)))
    (implies (and okp
                  (symbol-listp fn-list)
                  (mev-meta-extract-global-facts))
             (and (implies (natp w)
                           (equal (bits (mev rterm (mev-ctxl-alist ctxl al)) (1- w) 0)
                                  (mev term al)))
                  (implies (not w)
                           (equal (mev rterm (mev-ctxl-alist ctxl al))
                                  (mev term al))))))
  :hints (("Goal" :in-theory (e/d (mev-ctxl-alist
                                   match-tree-obj-equals-subst-and-open-when-successful
                                   match-tree-alist-opener-theory
                                   ind-fn)
                                  (mev-fn-get-def))
                  :expand ((build-ctx-and-get-inner-term term fn-list state))
                  :induct (ind-fn term fn-list al state))
          ("Subgoal *1/2"
           :use ((:instance mev-fn-get-def
                  (fn (car term))
                  (st state)
                  (state state)
                  (args (cdr term))
                  (a al))))
          ("Subgoal *1/4"
           :in-theory  (e/d (match-tree-obj-equals-subst-and-open-when-successful
                             match-tree-alist-opener-theory
                             ind-fn)
                            (bits-bits
                             mev-fn-get-def))
           :use ((:instance bits-bits
                  (x (mev (mv-nth 2 (build-ctx-and-get-inner-term (cadr term) fn-list state))
                      (mev-ctxl-alist (mv-nth 1 (build-ctx-and-get-inner-term (cadr term) fn-list state)) al)))
                  (i (+ -1 (mv-nth 3 (build-ctx-and-get-inner-term (cadr term) fn-list state))))
                  (j 0)
                  (k (cadr (caddr term)))
                  (l 0))))))

;; Convert a term into a bvfsl
(define shatter-bits ((term pseudo-termp)
                      (w natp))
  :returns (mv (okp booleanp) (r bvfsl-p) (rivl symbol-listp))
  :verify-guards :after-returns
  (if (zp w)
      (mv t nil nil)
    (b* (((mv okp bvf1 ivl1) (get-nth-bit term (1- w) t))
         ((unless okp) (mv nil nil nil))
         ((mv okp rbvfsl ivl2) (shatter-bits term (1- w)))
         ((unless okp) (mv nil nil nil))
         (bvfs (bvfs bvf1 (1- w))))
      (mv t (cons bvfs rbvfsl) (union$ ivl1 ivl2 :test 'eq)))))

(local
 (encapsulate ()
   (local (arith-5-for-rtl))
   (defthm shatter-bits-ev-correct
     (implies (and (mv-nth 0 (shatter-bits term w))
                   (mev (interp-ivl (mv-nth 2 (shatter-bits term w))) al)
                   (natp w))
              (and (implies (case-split (posp w)) (integerp (mev term al)))
                   (equal (mev (interp-bvfsl (mv-nth 1 (shatter-bits term w))) al)
                          (bits (mev term al) (1- w) 0))))
     :hints (("Goal" :in-theory (e/d (shatter-bits
                                      interp-bvfsl
                                      interp-bvfs) ())
                     :induct (shatter-bits term w))
             ("Subgoal *1/2" :use ((:instance bitn-plus-bits
                                    (x (mev term al)) (n (1- w)) (m 0))))))))

;; Convert a term which is a sum of other terms into a bvfsl
(define shatter-sum ((term pseudo-termp)
                     (w natp))
  :verify-guards :after-returns
  :returns (mv (okp booleanp) (r bvfsl-p) (rivl symbol-listp))
  (cond ((and (consp term) (eql (len term) 3)
              (eq (car term) 'binary-+))
         (b* (((mv okl lbvfsl livl) (shatter-sum (cadr term) w))
              ((unless okl) (mv nil nil nil))
              ((mv okr rbvfsl rivl) (shatter-sum (caddr term) w))
              ((unless okr) (mv nil nil nil)))
           (mv t (append lbvfsl rbvfsl) (union$ livl rivl :test 'eq))))
        (t (shatter-bits term w))))

(local-defthm shatter-sum-ev-correct
  (implies (and (mv-nth 0 (shatter-sum term w))
                (mev (interp-ivl (mv-nth 2 (shatter-sum term w))) al)
                (natp w))
           (and (implies (case-split (posp w)) (integerp (mev term al)))
                (equal (bits (mev (interp-bvfsl (mv-nth 1 (shatter-sum term w))) al) (1- w) 0)
                       (bits (mev term al) (1- w) 0))))
  :hints (("Goal" :in-theory (e/d (shatter-sum) ()))
          (and stable-under-simplificationp
               '(:use ((:instance bits-bits-sum
                        (x (mev (interp-bvfsl (mv-nth 1 (shatter-sum (cadr term) w)))
                            al))
                        (y (mev (interp-bvfsl (mv-nth 1 (shatter-sum (caddr term) w)))
                            al))
                        (k (1- w))
                        (i (1- w)) (j 0))
                       (:instance bits-bits-sum
                        (y (bits (mev (interp-bvfsl (mv-nth 1 (shatter-sum (cadr term) w)))
                                  al) (1- w) 0))
                        (x (mev (interp-bvfsl (mv-nth 1 (shatter-sum (caddr term) w)))
                            al))
                        (k (1- w))
                        (i (1- w)) (j 0))
                       (:instance bits-bits-sum
                        (x (mev (cadr term) al))
                        (y (mev (caddr term) al))
                        (k (1- w))
                        (i (1- w)) (j 0))
                       (:instance bits-bits-sum
                        (x (bits (mev (cadr term) al) (1- w) 0))
                        (y (mev (caddr term) al))
                        (k (1- w))
                        (i (1- w)) (j 0)))))))

(define parse-and-simp ((term pseudo-termp)
                        (fn-list symbol-listp)
                        state)
  :returns (mv (okp booleanp) (r bvfsl-p :hyp :guard) (rivl symbol-listp) (w natp))
  (b* (((mv okp ctxl rterm w) (build-ctx-and-get-inner-term term fn-list state))
       ((unless okp)
        (prog2$ (cw "CTV-CP: Failed to parse inner-most term~%")
                (mv nil nil nil 0)))
       ((unless w)
        (prog2$ (cw "CTV-CP: Failed to obtain width of inner-most term~%")
                (mv nil nil nil 0)))
       ((mv okp bvfsl ivl) (shatter-sum rterm w))
       ((unless okp)
        (prog2$ (cw "CTV-CP: Inner-most term uses unknown functions~%")
                (mv nil nil nil 0)))
       ((mv okp bvfsl ivl) (cl-main-loop ctxl bvfsl ivl w))
       ((unless okp)
        (prog2$ (cw "CTV-CP: Failed to run main simplifier loop")
                (mv nil nil nil 0))))
    (mv t bvfsl ivl w)))

(local-defthm parse-and-simp-ev-correct
  (implies (and (mv-nth 0 (parse-and-simp term fn-list state))
                (mev-meta-extract-global-facts)
                (symbol-listp fn-list)
                (mev (interp-ivl (mv-nth 2 (parse-and-simp term fn-list state))) al))
           (equal (bits (mev (interp-bvfsl (mv-nth 1 (parse-and-simp term fn-list state))) al)  (1- (mv-nth 3 (parse-and-simp term fn-list state))) 0)
                  (mev term al)))
  :hints (("Goal" :in-theory (e/d (parse-and-simp) ())
                  :do-not-induct t)))

(local-defthm remove1-still-bvfsl-p
  (implies (bvfsl-p x)
           (bvfsl-p (REMOVE1-EQUAL y x))))

;; Give two BVFSL's from LHS and RHS, cancel like terms:
(define cancel-bvfsl ((lbvfsl bvfsl-p)
                      (rbvfsl bvfsl-p)
                      (acc bvfsl-p))
  :returns (mv (l bvfsl-p :hyp :guard) (r bvfsl-p :hyp :guard))
  :verify-guards :after-returns
  (if (atom lbvfsl)
      (mv acc rbvfsl)
    (if (member-equal (car lbvfsl) rbvfsl)
        (cancel-bvfsl (cdr lbvfsl) (remove1-equal (car lbvfsl) rbvfsl) acc)
      (cancel-bvfsl (cdr lbvfsl) rbvfsl (cons (car lbvfsl) acc)))))

(local-defthm interp-bvfsl-of-remove1-equal
  (implies (member-equal x y)
           (equal (mev (interp-bvfsl (remove1-equal x y)) al)
                  (- (mev (interp-bvfsl y) al)
                     (mev (interp-bvfs x) al))))
  :hints (("Goal" :in-theory (e/d (interp-bvfsl) ()))))

(local-defthm interp-of-cancel-lemma
  (iff (equal (mev (interp-bvfsl (mv-nth 0 (cancel-bvfsl l r acc))) al)
              (mev (interp-bvfsl (mv-nth 1 (cancel-bvfsl l r acc))) al))
       (equal (+ (mev (interp-bvfsl l) al) (mev (interp-bvfsl acc) al))
              (mev (interp-bvfsl r) al)))
  :hints (("Goal" :in-theory (e/d (interp-bvfsl
                                   cancel-bvfsl) ()))))

;; To output a simplified equivalent expresssion, we need to merge a run of
;; bvfsl. Let's assume for now that the final simplified bvfsl do not contain
;; :fas or :fac form.

;; A bit-value-range-with-shift! Interpreted as (ash (bits v e s) sh).
(defprod bvrs
  ((v symbolp)
   (s natp)
   (e natp)
   (sh natp)))

(deflist bvrsl
  :elt-type bvrs
  :true-listp t)

;; Convert bvfsl to bvrsl
(define convert-to-bvr ((bvrsl bvrsl-p)
                        (bvfsl bvfsl-p))
  :returns (mv (r1 bvrsl-p :hyp (bvrsl-p bvrsl))
               (r2 bvfsl-p :hyp (bvfsl-p bvfsl)))
  (if (atom bvfsl)
      (mv bvrsl nil)
    (b* (((mv rbvrl rbvfsl) (convert-to-bvr bvrsl (cdr bvfsl))))
      (case (bvf-kind (bvfs->bvf (car bvfsl)))
        (:bv (b* (((bvfs x) (car bvfsl))
                    ((bvf-bv x.bvf) x.bvf))
                 (case (bv-kind x.bvf.bv)
                   (:bit (b* (((bv-bit x.bvf.bv) x.bvf.bv))
                         (mv (cons (bvrs x.bvf.bv.v x.bvf.bv.n x.bvf.bv.n x.sh)
                                   rbvrl)
                             rbvfsl)))
                   (t (mv rbvrl (cons (car bvfsl) rbvfsl))))))
        (t (mv rbvrl (cons (car bvfsl) rbvfsl)))))))

(define interp-bvrs ((bvrs bvrs-p))
  :returns (r pseudo-termp)
  (b* (((bvrs x) bvrs))
    `(ash (bits ,x.v ,(kwote x.e) ,(kwote x.s)) ,(kwote x.sh))))

(define interp-bvrsl ((bvrsl bvrsl-p))
  :returns (r pseudo-termp)
  (if (atom bvrsl)
      (kwote 0)
    `(binary-+ ,(interp-bvrs (car bvrsl)) ,(interp-bvrsl (cdr bvrsl)))))

(local-defthm convert-to-bvr-ev-correct
  (equal (+ (mev (interp-bvrsl (mv-nth 0 (convert-to-bvr bvrsl bvfsl))) al) (mev (interp-bvfsl (mv-nth 1 (convert-to-bvr bvrsl bvfsl))) al))
         (+ (mev (interp-bvrsl bvrsl) al) (mev (interp-bvfsl bvfsl) al)))
  :hints (("Goal" :in-theory (e/d (convert-to-bvr
                                   interp-bvfsl
                                   interp-bvrsl
                                   interp-bvrs
                                   interp-bvfs
                                   interp-bvf
                                   interp-bv) ()))))

(define merge-bvrs-low ((bvrs1 bvrs-p)
                        (bvrs2 bvrs-p))
  :returns (mv (mergedp booleanp) (r bvrs-p))
  (b* (((bvrs x1) bvrs1)
       ((bvrs x2) bvrs2))
    (if (and (eq x1.v x2.v)
             (eql x1.s (1+ x2.e))
             (>= x2.e x2.s)
             (>= x1.e x1.s)
             (eql x1.sh (+ x2.sh 1 (- x2.e x2.s))))
        (mv t (bvrs x1.v x2.s x1.e x2.sh))
      (mv nil (bvrs nil 0 0 0)))))

(local
 (encapsulate ()
   (local (arith-5-for-rtl))
   (local-defthm bits-nil-0
     (equal (bits nil n m) 0)
     :hints (("Goal" :in-theory (e/d (bits) ()))))

   (defthm merge-bvrs-correct
     (implies (mv-nth 0 (merge-bvrs-low x1 x2))
              (equal (mev (interp-bvrs (mv-nth 1 (merge-bvrs-low x1 x2))) al)
                     (+ (mev (interp-bvrs x1) al)
                        (mev (interp-bvrs x2) al))))
     :hints (("Goal" :in-theory (e/d (merge-bvrs-low
                                      interp-bvrs) ())
                     :use ((:instance bits-plus-bits
                            (x (CDR (ASSOC-EQUAL (BVRS->V X1) AL)))
                            (n (bvrs->e x1))
                            (m (bvrs->s x2))
                            (p (1+ (bvrs->e x2))))))))))

(define merge-seq ((bvrs bvrs-p)
                   (bvrsl bvrsl-p))
  :measure (acl2-count bvrsl)
  :returns (mv (r1 bvrs-p :hyp (bvrs-p bvrs)) (r2 bvrsl-p :hyp (bvrsl-p bvrsl)))
  (if (atom bvrsl)
      (mv bvrs nil)
    (b* (((mv mergedp merged-bvrs) (merge-bvrs-low bvrs (car bvrsl)))
         ((when mergedp) (merge-seq merged-bvrs (cdr bvrsl))))
      (mv bvrs bvrsl))))

(local-defthm merge-seq-ev-correct
  (equal (+ (mev (interp-bvrs (mv-nth 0 (merge-seq x1 x2))) al)
            (mev (interp-bvrsl (mv-nth 1 (merge-seq x1 x2))) al))
         (+ (mev (interp-bvrs x1) al)
            (mev (interp-bvrsl x2) al)))
  :hints (("Goal" :in-theory (e/d (merge-seq
                                   interp-bvrsl) ()))))

(local-defthm len-of-merge-seq-ub
  (<= (len (mv-nth 1 (merge-seq x y))) (len y))
  :hints (("Goal" :in-theory (e/d (merge-seq) ())))
  :rule-classes :linear)

(define merge-bvrsl ((bvrsl bvrsl-p))
  :measure (len bvrsl)
  :returns (r bvrsl-p :hyp :guard)
  (if (atom bvrsl)
      nil
    (b* (((mv first rest) (merge-seq (car bvrsl) (cdr bvrsl))))
      (cons first (merge-bvrsl rest)))))

(local-defthm merge-bvrsl-ev-correct
  (equal (mev (interp-bvrsl (merge-bvrsl brvsl)) al)
         (mev (interp-bvrsl brvsl) al))
  :hints (("Goal" :in-theory (e/d (merge-bvrsl
                                   interp-bvrsl) ()))))

(define compress-eq ((term (and (pseudo-termp term)
                                (consp term)
                                (eq (car term) 'equal)))
                     (fn-list symbol-listp)
                     state)
  :returns (mv (okp booleanp) (suff pseudo-termp))
  (prog2$ (cw "CTV-CP: Identified ~x0 as the main term for simplification~%" term)
  (b* ((lhs (cadr term))
       (rhs (caddr term))
       ((mv okl lbvfsl livl wl) (parse-and-simp lhs fn-list state))
       ((unless okl) (mv nil nil))
       ((mv okr rbvfsl rivl wr) (parse-and-simp rhs fn-list state))
       ((unless okr) (mv nil nil))
       ((unless (= wr wl)) (prog2$ (cw "LHS and RHS have different widths. TODO!~%")
                                   (mv nil nil)))
       ((mv lbvfsl rbvfsl) (cancel-bvfsl lbvfsl rbvfsl nil))
       (lbvfsl (sort-bvfsl2 lbvfsl))
       (rbvfsl (sort-bvfsl2 rbvfsl))
       ((mv lbvrsl lbvfsl) (convert-to-bvr nil lbvfsl))
       (lbvrsl (merge-bvrsl lbvrsl))
       ((mv rbvrsl rbvfsl) (convert-to-bvr nil rbvfsl))
       (rbvrsl (merge-bvrsl rbvrsl))
       (lhs `(binary-+ ,(interp-bvrsl lbvrsl) ,(interp-bvfsl lbvfsl)))
       (rhs `(binary-+ ,(interp-bvrsl rbvrsl) ,(interp-bvfsl rbvfsl))))
    (mv t `(if ,(interp-ivl (union$ livl rivl :test 'eq))
               (equal ,lhs ,rhs)
             'nil)))))

(define find-pos-eq-lit ((cl pseudo-term-listp))
  :returns (mv (r pseudo-termp :hyp :guard) (rcl pseudo-term-listp :hyp :guard))
  (if (atom cl)
      (mv nil cl)
    (if (and (consp (car cl))
             (eq (caar cl) 'equal))
        (mv (car cl) (cdr cl))
      (b* (((mv lit rcl) (find-pos-eq-lit (cdr cl))))
        (mv lit (cons (car cl) rcl))))))

(local-defthm find-pos-eq-lit-lemma
  (implies (mv-nth 0 (find-pos-eq-lit cl))
           (and (equal (car (mv-nth 0 (find-pos-eq-lit cl))) 'equal)
                (consp (mv-nth 0 (find-pos-eq-lit cl)))))
  :hints (("Goal" :in-theory (e/d (find-pos-eq-lit) ()))))

(define ctv-cp ((cl pseudo-term-listp)
                     fn-list
                     state)
  :otf-flg nil
  (if (not (symbol-listp fn-list))
      (mv t "CTV-CP: Expecting a list of functions" state)
    (if (atom cl)
        (mv nil (list cl) state)
      (b* (((mv lit rcl) (find-pos-eq-lit cl))
           ((unless lit)
            (prog2$ (cw "CTV-CP: Failed to find a literal to apply ctv-cp on.~%")
                    (mv nil (list cl) state)))
           ((mv okp suff) (compress-eq lit fn-list state))
           ((unless okp)
            (mv nil (list cl) state)))
        (mv nil (list (cons suff rcl)) state)))))

(local-defthm disjoin-mv-nth-1-find-pos-eq-lit
  (implies (syntaxp (and (not (equal (car cl) 'mv-nth)) (not (equal (car cl) 'cons))))
           (iff (mev (disjoin cl) al)
                (or (mev (disjoin (mv-nth 1 (find-pos-eq-lit cl))) al)
                    (mev (mv-nth 0 (find-pos-eq-lit cl)) al))))
  :hints (("Goal" :in-theory (e/d (find-pos-eq-lit) ()))))

(defthm correctness-of-ctv-cp
  (implies (and (pseudo-term-listp cl)
                (alistp al)
                (mev (conjoin-clauses (clauses-result (ctv-cp cl fn-list state))) al)
                (mev-meta-extract-global-facts))
           (mev (disjoin cl) al))
  :hints (("Goal" :in-theory (e/d (ctv-cp
                                   compress-eq)
                                  (parse-and-simp-ev-correct))
                  :use ((:instance parse-and-simp-ev-correct
                         (term (cadr (mv-nth 0 (find-pos-eq-lit cl)))))
                        (:instance parse-and-simp-ev-correct
                         (term (caddr (mv-nth 0 (find-pos-eq-lit cl))))))
                  :do-not-induct t))
  :rule-classes :clause-processor)

(defmacro def-ctv-thm (thm-name form &key (expand 'nil))
  `(acl2::defthm ,thm-name ,form
     :hints (("Goal" :in-theory '((ash)))
             (and stable-under-simplificationp
                  '(:clause-processor (ctv-cp clause ',expand state))))))

(defmacro def-ctv-thmd (thm-name form &key (expand 'nil))
  `(acl2::defthmd ,thm-name ,form
     :hints (("Goal" :in-theory '((ash)))
             (and stable-under-simplificationp
                  '(:clause-processor (ctv-cp clause ',expand state))))))

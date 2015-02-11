; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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

(in-package "AIGNET")
(include-book "add-ons/hash-stobjs" :dir :system)
(include-book "arrays")
(include-book "centaur/misc/2d-arr" :dir :system)
(include-book "centaur/misc/iter" :dir :system)
(include-book "centaur/misc/natarr" :dir :system)
(include-book "centaur/misc/nth-equiv" :dir :system)
(include-book "clause-processors/stobj-preservation" :dir :system)
(include-book "clause-processors/generalize" :dir :system)
(include-book "clause-processors/find-subterms" :dir :system)

(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (enable* acl2::arith-equiv-forwarding)))
(local (in-theory (disable set::double-containment)))
(local (in-theory (disable nth update-nth
                           acl2::nfix-when-not-natp
                           resize-list
                           acl2::resize-list-when-empty
                           acl2::make-list-ac-redef
                           set::double-containment
                           set::sets-are-true-lists
                           make-list-ac)))

(local (include-book "std/lists/nth" :dir :system))


(local (in-theory (disable true-listp-update-nth
                           acl2::nth-when-zp
                           acl2::nth-with-large-index)))

(local (defthmd equal-1-to-bitp
         (implies (and (not (equal x 0))
                       (bitp x))
                  (equal (equal x 1) t))
         :hints(("Goal" :in-theory (enable bitp)))))

;; sigh
(defmacro mksym (pkg &rest concats)
  `(intern-in-package-of-symbol
    (concatenate 'string . ,concats)
    ,pkg))

(defthmd redundant-update-nth
  (implies (and (< (nfix n) (len x))
                (equal v (nth n x)))
           (equal (update-nth n v x)
                  x))
  :hints(("Goal" :in-theory (enable nth update-nth))))

;; BOZO move somewhere else
(defrefinement nth-equiv bits-equiv :hints(("Goal" :in-theory (enable bits-equiv))))

(defmacro const-type () 0)
(defmacro gate-type () 1)
(defmacro in-type () 2)
(defmacro out-type () 3)

;; (defsection aignet-untranslate
;;   (defun untranslate-preproc-node-types (term wrld)
;;     (declare (ignore wrld))
;;     (case-match term
;;       (('equal ('node->type ('nth-node id ('nth ''6 aignet))) ('quote typenum))
;;        (case typenum
;;          (0 `(equal (id->type ,id ,aignet) (const-type)))
;;          (1 `(equal (id->type ,id ,aignet) (gate-type)))
;;          (2 `(equal (id->type ,id ,aignet) (in-type)))
;;          (3 `(equal (id->type ,id ,aignet) (out-type)))
;;          (otherwise term)))
;;       (& term)))

;;   (defmacro use-aignet-untrans ()
;;     '(local
;;       (table acl2::user-defined-functions-table 'acl2::untranslate-preprocess
;;              'untranslate-preproc-node-types))))

;; (use-aignet-untrans)

;; (in-theory (disable acl2::aignetp))



(defsection misc

  (defthm lookup-id-implies-aignet-idp
    (implies (consp (lookup-id id aignet))
             (aignet-idp id aignet))
    :hints(("Goal" :in-theory (enable aignet-idp lookup-id))))

  (defthm aignet-idp-of-node-count-of-extension
    (implies (aignet-extension-p aignet prev)
             (aignet-idp (node-count prev) aignet))
    :hints(("Goal" :in-theory (enable aignet-extension-p
                                      aignet-idp))))

  (defthm lookup-id-of-cons
    (equal (lookup-id id (cons node rest))
           (if (equal (nfix id) (+ 1 (node-count rest)))
               (cons node rest)
             (lookup-id id rest)))
    :hints(("Goal" :in-theory (enable lookup-id))))

  
  (defun equiv-search-type-alist (type-alist goaltype equiv lhs rhs unify-subst wrld)
    (declare (xargs :mode :program))
    (b*  (((when (endp type-alist))
           (mv nil nil))
          ((list* term type ?ttree) (car type-alist))
          ((unless
               (and (acl2::ts-subsetp type goaltype)
                    (consp term)
                    (symbolp (car term))
                    (member equiv
                            (fgetprop (car term) 'acl2::coarsenings
                                      nil wrld))))
           (equiv-search-type-alist (cdr type-alist) goaltype equiv lhs rhs unify-subst
                                    wrld))
          ((mv ans new-unify-subst)
           (acl2::one-way-unify1 lhs (cadr term) unify-subst))
          ((mv ans new-unify-subst)
           (if ans
               (acl2::one-way-unify1 rhs (caddr term) new-unify-subst)
             (mv nil nil)))
          ((when ans) (mv t new-unify-subst))
          ;; try (equiv rhs lhs)
          ((mv ans new-unify-subst)
           (acl2::one-way-unify1 lhs (caddr term) unify-subst))
          ((mv ans new-unify-subst)
           (if ans
               (acl2::one-way-unify1 rhs (cadr term) new-unify-subst)
             (mv nil nil)))
          ((when ans) (mv t new-unify-subst)))
      (equiv-search-type-alist (cdr type-alist) goaltype equiv lhs rhs unify-subst
                               wrld)))

  ;; Term has at least one variable not bound in unify-subst.  Search
  ;; type-alist for term matching (equiv1 lhs rhs) or (equiv1 rhs lhs)
  ;; and return the matching free variables.
  (defun match-equiv-or-refinement (equiv var binding-term mfc state)
    (declare (xargs :mode :program :stobjs state))
    (b* (; (*mfc* mfc)
         (unify-subst (acl2::mfc-unify-subst mfc))
         ((mv erp tbind)
          (acl2::translate-cmp binding-term t t nil 'match-equiv-or-refinement (w state)
                               (acl2::default-state-vars t)))
         ((when erp)
          (er hard? erp "~@0" tbind))
         (type-alist (acl2::mfc-type-alist mfc))
         ;; Does the var unify with the binding-term already?
         ((mv ok new-unify-subst)
          (acl2::one-way-unify1 tbind (cdr (assoc var unify-subst)) unify-subst))
         ((when ok)
          (butlast new-unify-subst (length unify-subst)))
         ((mv ok new-unify-subst)
          (equiv-search-type-alist type-alist acl2::*ts-non-nil* equiv var tbind unify-subst
                                   (w state)))
         ((unless ok) nil))
      (butlast new-unify-subst (length unify-subst))))


  (defun match-equiv-or-refinement-lst (equiv var terms mfc state)
    (declare (xargs :mode :program :stobjs state))
    (if (atom terms)
        nil
      (or (match-equiv-or-refinement equiv var (car terms) mfc state)
          (match-equiv-or-refinement-lst equiv var (cdr terms) mfc state))))
    

  (defthm lookup-id-of-node-count
    (equal (lookup-id (node-count x) x)
           x)
    :hints(("Goal" :in-theory (enable lookup-id))))

  (defthm lookup-id-of-node-count-bind
    (implies (and (bind-free (match-equiv-or-refinement-lst
                              'acl2::nat-equiv$inline 'id
                              '((node-count x)
                                (+ 1 (node-count (cdr x))))
                              mfc state)
                             (x))
                  (syntaxp (not (subtermp `(lookup-id ,id ,y) x)))
                  (nat-equiv id (node-count x))
                  (aignet-extension-p y x))
             (equal (lookup-id id y)
                    x))
    :hints(("Goal" :in-theory (e/d () (nat-equiv)))))

  (defthm node-count-of-lookup-id-when-consp
    (implies (consp (lookup-id id aignet))
             (equal (node-count (lookup-id id aignet))
                    id))
    :hints(("Goal" :in-theory (enable lookup-id))))

  (defthm posp-when-consp-of-lookup-id
    (implies (consp (lookup-id id aignet))
             (posp id))
    :hints(("Goal" :in-theory (enable lookup-id)))
    :rule-classes :forward-chaining)

  (defthm aignet-idp-of-0
    (aignet-idp 0 aignet)
    :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm aignet-litp-of-0-and-1
    (and (aignet-litp 0 aignet)
         (aignet-litp 1 aignet))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm aignet-litp-of-mk-lit-lit-id
    (equal (aignet-litp (mk-lit (lit-id lit) neg) aignet)
           (aignet-litp lit aignet))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defthm aignet-litp-of-mk-lit-0
    (aignet-litp (mk-lit 0 neg) aignet)
    :hints(("Goal" :in-theory (enable aignet-litp)))))
                    

(defsection ionum-uniqueness

  (in-theory (disable lookup-id-in-bounds))


  (defthm lookup-id-by-stype
    (implies (not (equal (stype (car (lookup-id id aignet)))
                         (const-stype)))
             (lookup-id id aignet)))

  (defthm stype-counts-unique
    (implies (and (equal type (stype (car (lookup-id id1 aignet))))
                  (equal type (stype (car (lookup-id id2 aignet))))
                  (not (equal type (const-stype))))
             (equal (equal (stype-count type (cdr (lookup-id id1 aignet)))
                           (stype-count type (cdr (lookup-id id2 aignet))))
                    (nat-equiv id1 id2)))
    :hints(("Goal" :in-theory (enable lookup-id
                                      stype-count
                                      aignet-idp)))
    :otf-flg t)

  (defthm stype-ids-unique
    (implies (and (< (nfix n1) (stype-count stype aignet))
                  (< (nfix n2) (stype-count stype aignet)))
             (equal (equal (node-count (lookup-stype n1 stype aignet))
                           (node-count (lookup-stype n2 stype aignet)))
                    (nat-equiv n1 n2)))
    :hints(("Goal" :in-theory (enable lookup-stype
                                      stype-count))))

  (defthm stype-ids-unique-cdr
    (implies (and (< (nfix n1) (stype-count stype aignet))
                  (< (nfix n2) (stype-count stype aignet)))
             (equal (equal (node-count (cdr (lookup-stype n1 stype aignet)))
                           (node-count (cdr (lookup-stype n2 stype aignet))))
                    (nat-equiv n1 n2)))
    :hints(("Goal" :in-theory (e/d (lookup-stype-in-bounds
                                    node-count)
                                   (stype-ids-unique))
            :use ((:instance stype-ids-unique)))))

  (defthm lookup-reg->nxsts-unique
    (implies (and (consp (lookup-reg->nxst n1 aignet))
                  (consp (lookup-reg->nxst n2 aignet)))
             (equal (equal (node-count (lookup-reg->nxst n1 aignet))
                           (node-count (lookup-reg->nxst n2 aignet)))
                    (nat-equiv n1 n2)))
    :hints(("Goal" :in-theory (enable lookup-reg->nxst))))
  

  (defthm lookup-stype-of-stype-count-match
    (implies (and (bind-free (match-equiv-or-refinement
                              'acl2::nat-equiv$inline 'count '(stype-count stype (cdr orig))
                              mfc state)
                             (orig))
                  (nat-equiv count (stype-count stype (cdr orig)))
                  (aignet-extension-p new orig)
                  (equal (stype (car orig)) (stype-fix stype))
                  (not (equal (stype-fix stype) (const-stype))))
             (equal (lookup-stype count stype new)
                    orig))
    :hints(("Goal" :in-theory (disable nat-equiv)))))


(defsection aignet-lit-listp

  (defun aignet-lit-listp (x aignet)
    (declare (xargs :stobjs aignet
                    :guard (lit-listp x)))
    (if (atom x)
        (eq x nil)
      (and (fanin-litp (car x) aignet)
           (aignet-lit-listp (cdr x) aignet)))))


(defsection aignet-extension-p
  :parents (aignet-logic)
  :short "Predicate that says that one aignet is the result of building some new
nodes onto another aignet"
  :long "<p>Aignet A is an extension of B if B is a suffix of A.  That is, A
consists of B along with maybe some additional nodes built on top of it; this
is a transitive, reflexive relation. This is a useful concept because every
aignet-modifying function that doesn't reinitialize the AIG produces an
extension of its input, and this relation implies many useful things.  The most
basic is that any ID of the original aignet is an ID of the new aignet, and the
node of that ID (and its entire suffix) is the same in both aignets.  This
implies, for example, that the evaluations of nodes existing in the first are
the same as their evaluations in the second.</p>

<p>Rewrite rules using aignet-extension-p are a little odd.  For example, suppose we
want a rewrite rule just based on the definition, e.g.,
<code>
 (implies (and (aignet-extension-p new-aignet orig-aignet)
               (aignet-idp id orig-aignet))
          (equal (nth-node id new-aignet)
                 (nth-node id orig-aignet)))
</code>
This isn't a very good rewrite rule because it has to match the free variable
orig-aignet.  However, we can make it much better with a bind-free strategy.
We'll check the syntax of new-aignet to see if it is a call of a
aignet-updating function.  Then, we'll use the aignet input of that function as the
binding for orig-aignet.</p>
"


  (defun simple-search-type-alist (term typ type-alist unify-subst)
    (declare (xargs :mode :program))
    (cond ((endp type-alist)
           (mv nil unify-subst))
          ((acl2::ts-subsetp (cadr (car type-alist)) typ)
           (mv-let (ans unify-subst)
             (acl2::one-way-unify1 term (car (car type-alist)) unify-subst)
             (if ans
                 (mv t unify-subst)
               ;; note: one-way-unify1 is a no-change-loser so unify-subst is
               ;; unchanged below
               (simple-search-type-alist term typ (cdr type-alist)
                                         unify-subst))))
          (t (simple-search-type-alist term typ (cdr type-alist) unify-subst))))


  ;; Additional possible strategic thing: keep aignet-modifying functions that
  ;; don't produce an extension in a table and don't bind their inputs.
  (defun find-prev-stobj-binding (new-term state)
    (declare (xargs :guard (pseudo-termp new-term)
                    :stobjs state
                    :mode :program))
    (b* (((mv valnum function args)
          (case-match new-term
            (('mv-nth ('quote valnum) (function . args) . &)
             (mv (and (symbolp function) valnum) function args))
            ((function . args)
             (mv (and (symbolp function) 0) function args))
            (& (mv nil nil nil))))
         ((unless valnum) (mv nil nil))
         ((when (or (eq function 'if)
                    (eq function 'return-last)))
          ;; Can't call stobjs-out on either of these
          (mv nil nil))
         ((when (and (eq function 'cons)
                     (int= valnum 0)))
          ;; special case for update-nth.
          (mv t (nth 1 args)))
         (w (w state))
         (stobjs-out (acl2::stobjs-out function w))
         (formals (acl2::formals function w))
         (stobj-out (nth valnum stobjs-out))
         ((unless stobj-out) (mv nil nil))
         (pos (position stobj-out formals))
         ((unless pos) (mv nil nil)))
      (mv t (nth pos args))))

  (defun iterate-prev-stobj-binding (n new-term state)
    (declare (xargs :guard (and (pseudo-termp new-term)
                                (natp n))
                    :stobjs state
                    :mode :program))
    (if (zp n)
        new-term
      (mv-let (ok next-term)
        (find-prev-stobj-binding new-term state)
        (if ok
            (iterate-prev-stobj-binding (1- n) next-term state)
          new-term))))

  (defun prev-stobj-binding (new-term prev-var iters mfc state)
    (declare (xargs :guard (and (pseudo-termp new-term)
                                (symbolp prev-var))
                    :stobjs state
                    :mode :program)
             (ignore mfc))
    (let ((prev-term (iterate-prev-stobj-binding iters new-term state)))
      (if (equal new-term prev-term)
          `((do-not-use-this-long-horrible-variable
             . do-not-use-this-long-horrible-variable))
        `((,prev-var . ,prev-term)))))

  (defmacro aignet-extension-binding (&key (new 'new)
                                           (orig 'orig)
                                           (iters '1))
    `(and (bind-free (prev-stobj-binding ,new ',orig ',iters mfc state))
          (aignet-extension-p ,new ,orig)
          (syntaxp (not (subtermp ,new ,orig)))))

  (defthm aignet-extension-p-transitive-rw
    (implies (and (aignet-extension-binding :new aignet3 :orig aignet2)
                  (aignet-extension-p aignet2 aignet1))
             (aignet-extension-p aignet3 aignet1))
    :hints(("Goal" :in-theory (enable aignet-extension-p-transitive))))

  ;; already has inverse
  (defthm aignet-extension-simplify-lookup-id
    (implies (and (aignet-extension-binding)
                  (aignet-idp id orig))
             (equal (lookup-id id new)
                    (lookup-id id orig))))

  (defthm aignet-extension-simplify-lookup-stype
    (implies (and (aignet-extension-binding)
                  (consp (lookup-stype n stype orig)))
             (equal (lookup-stype n stype new)
                    (lookup-stype n stype orig)))
    :hints(("Goal" :in-theory (enable lookup-stype
                                      aignet-extension-p))))

  (defthm aignet-extension-simplify-lookup-stype-when-counts-same
    (implies (and (aignet-extension-binding)
                  (equal (stype-count stype new)
                         (stype-count stype orig)))
             (equal (lookup-stype n stype new)
                    (lookup-stype n stype orig)))
    :hints(("Goal" :in-theory (enable aignet-extension-p
                                      lookup-stype))))

  (defthm aignet-extension-simplify-lookup-stype-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (consp (lookup-stype n stype orig)))
             (equal (lookup-stype n stype orig)
                    (lookup-stype n stype new))))

  (defthm aignet-extension-simplify-aignet-idp
    (implies (and (aignet-extension-binding)
                  (aignet-idp id orig))
             (aignet-idp id new)))

  (defthm aignet-extension-simplify-aignet-litp
    (implies (and (aignet-extension-binding)
                  (aignet-litp lit orig))
             (aignet-litp lit new)))

  (defthm aignet-extension-implies-aignet-lit-listp
    (implies (and (aignet-extension-binding)
                  (aignet-lit-listp lits orig))
             (aignet-lit-listp lits new)))

  (defthm aignet-extension-implies-node-count-gte
    (implies (aignet-extension-binding)
             (<= (node-count orig) (node-count new)))
    :rule-classes ((:linear :trigger-terms ((node-count new)))))

  (defthm aignet-extension-implies-stype-count-gte
    (implies (aignet-extension-binding)
             (<= (stype-count stype orig)
                 (stype-count stype new)))
    :rule-classes ((:linear :trigger-terms ((stype-count stype new)))))

  (defthmd aignet-extension-p-implies-consp
    (implies (and (aignet-extension-binding)
                  (consp orig))
             (consp new))
    :hints(("Goal" :in-theory (enable aignet-extension-p)))))

(defsection preservation-thms
  (acl2::def-stobj-preservation-macros
   :name aignet
   :default-stobjname aignet
   :templates aignet-preservation-templates
   :history aignet-preservation-history)

  (add-aignet-preservation-thm
   aignet-extension-p
   :body `(aignet-extension-p ,new-stobj ,orig-stobj)
   :hints `(,@expand/induct-hints))

  (add-aignet-preservation-thm
   aignet-nodes-ok
   :body `(implies (aignet-nodes-ok ,orig-stobj)
                   (aignet-nodes-ok ,new-stobj))
   :hints expand/induct-hints))


(local (defthm car-nonnil-forward-to-consp
         (implies (not (equal (car x) nil))
                  (consp x))
         :rule-classes ((:forward-chaining :trigger-terms ((car x))))))

(defsection semantics
  :parents (aignet-logic)
  :short "Combinational semantics of aignets"
  :long "<p>The combinational semantics of aignets is given by the function
ID-EVAL.  This takes an aignet, a node ID, and assignments to the primary
inputs and registers, and produces the value of that ID under those
assignments.</p>"
  (defstobj-clone aignet-invals bitarr :strsubst (("BIT" . "AIGNET-INVAL")))
  (defstobj-clone aignet-regvals bitarr :strsubst (("BIT" . "AIGNET-REGVAL")))

  ; (local (in-theory (enable gate-orderedp co-orderedp)))

  
  (local (in-theory (enable aignet-lit-fix-id-val-linear)))

  ;; ;;; BOZO: Move this into the absstobj definition?  i.e., have
  ;; ;; gate-id->fanin0
  ;; ;; gate-id->fanin1
  ;; ;; co-id->fanin
  ;; ;; do this implicitly?
  ;; (defmacro fanin-lit-fix (lit id aignet)
  ;;   `(mbe :logic (non-exec (aignet-lit-fix ,lit (cdr (lookup-id ,id ,aignet))))
  ;;         :exec ,lit))


  (mutual-recursion
   (defun lit-eval (lit aignet-invals aignet-regvals aignet)
     (declare (xargs :stobjs (aignet aignet-invals aignet-regvals)
                     :guard (and (litp lit)
                                 (fanin-litp lit aignet)
                                 (<= (num-ins aignet) (bits-length aignet-invals))
                                 (<= (num-regs aignet) (bits-length aignet-regvals)))
                     :measure (acl2::two-nats-measure (lit-id lit) 1)
                     :verify-guards nil))
     (b-xor (id-eval (lit-id lit) aignet-invals aignet-regvals aignet)
            (lit-neg lit)))

   (defun eval-and-of-lits (lit1 lit2 aignet-invals aignet-regvals aignet)
     (declare (xargs :stobjs (aignet aignet-invals aignet-regvals)
                     :guard (and (litp lit1) (fanin-litp lit1 aignet)
                                 (litp lit2) (fanin-litp lit2 aignet)
                                 (<= (num-ins aignet) (bits-length aignet-invals))
                                 (<= (num-regs aignet) (bits-length
                                                        aignet-regvals)))
                     :measure (acl2::two-nats-measure
                               (max (lit-id lit1)
                                    (lit-id lit2))
                               2)))
    (b-and (lit-eval lit1 aignet-invals aignet-regvals aignet)
           (lit-eval lit2 aignet-invals aignet-regvals aignet)))

   (defun id-eval (id aignet-invals aignet-regvals aignet)
     (declare (xargs :stobjs (aignet aignet-invals aignet-regvals)
                     :guard (and (natp id) (id-existsp id aignet)
                                 (<= (num-ins aignet) (bits-length aignet-invals))
                                 (<= (num-regs aignet) (bits-length aignet-regvals)))
                     :measure (acl2::two-nats-measure id 0)
                     :hints(("Goal" :in-theory (enable aignet-idp)))))
     (b* (((unless (mbt (id-existsp id aignet)))
           ;; out-of-bounds IDs are false
           0)
          (type (id->type id aignet)))
       (aignet-case
        type
        :gate (b* ((f0 (gate-id->fanin0 id aignet))
                   (f1 (gate-id->fanin1 id aignet)))
                (mbe :logic (eval-and-of-lits
                             f0 f1 aignet-invals aignet-regvals aignet)
                     :exec (b-and (b-xor (id-eval (lit-id f0)
                                                  aignet-invals aignet-regvals aignet)
                                         (lit-neg f0))
                                  (b-xor (id-eval (lit-id f1)
                                                  aignet-invals aignet-regvals
                                                  aignet)
                                         (lit-neg f1)))))
        :in    (if (int= (io-id->regp id aignet) 1)
                   (get-bit (io-id->ionum id aignet) aignet-regvals)
                 (get-bit (io-id->ionum id aignet) aignet-invals))
        :out (b* ((f (co-id->fanin id aignet)))
               (lit-eval f aignet-invals aignet-regvals aignet))
        :const 0))))

  (in-theory (disable id-eval lit-eval eval-and-of-lits))
  (local (in-theory (enable id-eval lit-eval eval-and-of-lits)))

  (defun-nx id-eval-ind (id aignet)
    (declare (xargs :measure (nfix id)
                    :hints(("Goal" :in-theory (enable aignet-idp)))))
    (b* (((unless (mbt (aignet-idp id aignet)))
          ;; out-of-bounds IDs are false
          0)
         (type (id->type id aignet)))
      (aignet-case
       type
       :gate (b* ((f0 (gate-id->fanin0 id aignet))
                   (f1 (gate-id->fanin1 id aignet)))
                (list
                 (id-eval-ind (lit-id f0) aignet)
                 (id-eval-ind (lit-id f1) aignet)))
       :in    nil
       :out (b* ((f (co-id->fanin id aignet)))
              (id-eval-ind (lit-id f) aignet))
       :const 0)))

  (defcong nat-equiv equal (id-eval id invals regvals aignet) 1
    :hints (("goal" :expand ((id-eval id invals regvals aignet)
                             (id-eval nat-equiv invals regvals aignet)))))

  (defcong bits-equiv equal (id-eval id invals regvals aignet) 2
    :hints (("goal" :induct (id-eval-ind id aignet)
             :expand ((:free (invals regvals)
                       (id-eval id invals regvals aignet))))))

  (defcong bits-equiv equal (id-eval id invals regvals aignet) 3
    :hints (("goal" :induct (id-eval-ind id aignet)
             :expand ((:free (invals regvals)
                       (id-eval id invals regvals aignet))))))

  (defcong list-equiv equal (id-eval id invals regvals aignet) 4
    :hints (("goal" :induct (id-eval-ind id aignet)
             :expand ((:free (aignet)
                       (id-eval id invals regvals aignet))))))

  (defcong bits-equiv equal (lit-eval lit invals regvals aignet) 2
    :hints (("goal"
             :expand ((:free (invals regvals)
                       (lit-eval lit invals regvals aignet))))))

  (defcong bits-equiv equal (lit-eval lit invals regvals aignet) 3
    :hints (("goal"
             :expand ((:free (invals regvals)
                       (lit-eval lit invals regvals aignet))))))

  (defcong lit-equiv equal (lit-eval lit invals regvals aignet) 1
    :hints (("goal" :expand ((lit-eval lit invals regvals aignet)
                             (lit-eval lit-equiv invals regvals
                                       aignet)))))

  (defcong list-equiv equal (lit-eval lit invals regvals aignet) 4
    :hints (("goal"
             :expand ((:free (aignet)
                       (lit-eval lit invals regvals aignet))))))

  (defcong bits-equiv equal
    (eval-and-of-lits lit1 lit2 invals regvals aignet) 3
    :hints (("goal"
             :expand ((:free (invals regvals)
                       (eval-and-of-lits lit1 lit2 invals regvals
                                         aignet))))))

  (defcong bits-equiv equal
    (eval-and-of-lits lit1 lit2 invals regvals aignet) 4
    :hints (("goal"
             :expand ((:free (invals regvals)
                       (eval-and-of-lits lit1 lit2 invals regvals
                                         aignet))))))

  (defcong lit-equiv equal
    (eval-and-of-lits lit1 lit2 invals regvals aignet) 1
    :hints (("goal"
             :expand ((:free (lit1)
                       (eval-and-of-lits lit1 lit2 invals regvals
                                         aignet))))))

  (defcong lit-equiv equal
    (eval-and-of-lits lit1 lit2 invals regvals aignet) 2
    :hints (("goal"
             :expand ((:free (lit2)
                       (eval-and-of-lits lit1 lit2 invals regvals
                                         aignet))))))

  (defcong list-equiv equal
    (eval-and-of-lits lit1 lit2 invals regvals aignet) 5
    :hints (("goal"
             :expand ((:free (aignet)
                       (eval-and-of-lits lit1 lit2 invals regvals
                                         aignet))))))


  (flag::make-flag lit/id-eval-flag lit-eval
                   :flag-mapping ((lit-eval . lit)
                                  (id-eval . id)
                                  (eval-and-of-lits . and))
                   :hints(("Goal" :in-theory (enable aignet-idp))))

  (defthm bitp-of-lit-eval
    (bitp (lit-eval lit invals regvals aignet))
    :hints (("goal" :expand (lit-eval lit invals regvals aignet))))

  (defthm bitp-of-id-eval
    (bitp (id-eval id invals regvals aignet))
    :hints (("goal" :expand (id-eval id invals regvals aignet))))

  (defthm bitp-of-eval-and
    (bitp (eval-and-of-lits lit1 lit2 invals regvals aignet))
    :hints (("goal" :expand (eval-and-of-lits lit1 lit2 invals
                                              regvals aignet))))


  (defthm-lit/id-eval-flag
    (defthm id-eval-preserved-by-extension
      (implies (and (aignet-extension-binding :orig aignet)
                    (aignet-idp id aignet))
               (equal (id-eval id invals regvals new)
                      (id-eval id invals regvals aignet)))
      :hints ((and stable-under-simplificationp
                   '(:expand ((:free (aignet) (id-eval id invals regvals aignet))))))
      :flag id)
    (defthm lit-eval-preserved-by-extension
      (implies (and (aignet-extension-binding :orig aignet)
                    (aignet-idp (lit-id lit) aignet))
               (equal (lit-eval lit invals regvals new)
                      (lit-eval lit invals regvals aignet)))
      :flag lit)
    (defthm eval-and-preserved-by-extension
      (implies (and (aignet-extension-binding :orig aignet)
                    (aignet-idp (lit-id lit1) aignet)
                    (aignet-idp (lit-id lit2) aignet))
               (equal (eval-and-of-lits lit1 lit2 invals regvals new)
                      (eval-and-of-lits lit1 lit2 invals regvals aignet)))
      :flag and))

  (defthm id-eval-preserved-by-extension-inverse
    (implies (and (aignet-extension-bind-inverse :orig aignet)
                  (aignet-idp id aignet))
             (equal (id-eval id invals regvals aignet)
                    (id-eval id invals regvals new)))
    :hints (("goal" :use id-eval-preserved-by-extension)))

  (defthm lit-eval-preserved-by-extension-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (aignet-idp (lit-id lit) orig))
             (equal (lit-eval lit invals regvals orig)
                    (lit-eval lit invals regvals new))))

  (defthm eval-and-preserved-by-extension-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (aignet-idp (lit-id lit1) orig)
                  (aignet-idp (lit-id lit2) orig))
             (equal (eval-and-of-lits lit1 lit2 invals regvals orig)
                    (eval-and-of-lits lit1 lit2 invals regvals new))))


  (defthm aignet-idp-of-co-node->fanin-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (id->type id aignet) (out-type))
                  (aignet-extension-p aignet2 (cdr (lookup-id id aignet))))
             (aignet-idp (lit-id (co-node->fanin (car (lookup-id id aignet))))
                         aignet2))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok lookup-id))))

  (defthm aignet-idp-of-gate-node->fanins-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (id->type id aignet) (gate-type))
                  (aignet-extension-p aignet2 (cdr (lookup-id id aignet))))
             (and (aignet-idp (lit-id (gate-node->fanin0 (car (lookup-id id aignet))))
                              aignet2)
                  (aignet-idp (lit-id (gate-node->fanin1 (car (lookup-id id aignet))))
                              aignet2)))
    :hints(("Goal" :in-theory (enable aignet-nodes-ok lookup-id))))

  (local (include-book "centaur/aignet/bit-lemmas" :dir :system))

  (defthm lit-eval-of-mk-lit-of-lit-id
    (equal (lit-eval (mk-lit (lit-id x) neg) invals regvals aignet)
           (b-xor (b-xor neg (lit-neg x))
                  (lit-eval x invals regvals aignet))))

  (local (defthm lit-eval-of-mk-lit-0
           (equal (lit-eval (mk-lit 0 neg) invals regvals aignet)
                  (bfix neg))))

  (defthm lit-eval-of-aignet-lit-fix
    (equal (lit-eval (aignet-lit-fix x aignet) invals regvals aignet)
           (lit-eval x invals regvals aignet))
    :hints(("Goal" :in-theory (e/d (aignet-lit-fix)
                                   (lit-eval))
            :induct (aignet-lit-fix x aignet)
            :expand ((lit-eval x invals regvals aignet)))))

  (defthm lit-eval-of-aignet-lit-fix-extension
    (implies (aignet-extension-p aignet2 aignet)
             (equal (lit-eval (aignet-lit-fix x aignet) invals regvals aignet2)
                    (lit-eval x invals regvals aignet))))

  (defthm id-eval-of-aignet-lit-fix
    (equal (id-eval (lit-id (aignet-lit-fix x aignet)) invals regvals aignet)
           (b-xor (b-xor (lit-neg x) (lit-neg (aignet-lit-fix x aignet)))
                  (id-eval (lit-id x) invals regvals aignet)))
    :hints (("goal" :use lit-eval-of-aignet-lit-fix
             :in-theory (e/d (lit-eval b-xor)
                             (lit-eval-of-aignet-lit-fix
                              lit-eval-of-aignet-lit-fix-extension
                              id-eval)))))

  (defthm eval-and-of-lits-of-aignet-lit-fix-1
    (equal (eval-and-of-lits (aignet-lit-fix x aignet) y invals regvals aignet)
           (eval-and-of-lits x y invals regvals aignet))
    :hints(("Goal" :in-theory (disable lit-eval))))

  (defthm eval-and-of-lits-of-aignet-lit-fix-1-extension
    (implies (and (aignet-extension-p aignet2 aignet)
                  (aignet-idp (lit-id y) aignet))
             (equal (eval-and-of-lits (aignet-lit-fix x aignet) y invals regvals aignet2)
                    (eval-and-of-lits x y invals regvals aignet))))

  (defthm eval-and-of-lits-of-aignet-lit-fix-2
    (equal (eval-and-of-lits y (aignet-lit-fix x aignet) invals regvals aignet)
           (eval-and-of-lits y x invals regvals aignet))
    :hints(("Goal" :in-theory (disable lit-eval))))

  (defthm eval-and-of-lits-of-aignet-lit-fix-2-extension
    (implies (and (aignet-extension-p aignet2 aignet)
                  (aignet-idp (lit-id y) aignet))
             (equal (eval-and-of-lits y (aignet-lit-fix x aignet) invals regvals aignet2)
                    (eval-and-of-lits y x invals regvals aignet))))

  (in-theory (disable id-eval-of-aignet-lit-fix
                      lit-eval-of-aignet-lit-fix
                      lit-eval-of-aignet-lit-fix-extension
                      eval-and-of-lits-of-aignet-lit-fix-1
                      eval-and-of-lits-of-aignet-lit-fix-1-extension
                      eval-and-of-lits-of-aignet-lit-fix-2
                      eval-and-of-lits-of-aignet-lit-fix-2-extension))


  (verify-guards lit-eval)

  (defun lit-eval-list (x aignet-invals aignet-regvals aignet)
    (declare (xargs :stobjs (aignet aignet-invals aignet-regvals)
                    :guard (and (lit-listp x)
                                (aignet-lit-listp x aignet)
                                (<= (num-ins aignet) (bits-length aignet-invals))
                                (<= (num-regs aignet) (bits-length aignet-regvals)))))
    (if (atom x)
        nil
      (cons (lit-eval (car x) aignet-invals aignet-regvals aignet)
            (lit-eval-list (cdr x) aignet-invals aignet-regvals aignet))))

  (defthm lit-eval-list-preserved-by-extension
    (implies (and (aignet-extension-binding)
                  (aignet-lit-listp lits orig))
             (equal (lit-eval-list lits aignet-invals aignet-regvals new)
                    (lit-eval-list lits aignet-invals aignet-regvals orig))))

  (defthm lit-eval-list-preserved-by-extension-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (aignet-lit-listp lits orig))
             (equal (lit-eval-list lits aignet-invals aignet-regvals orig)
                    (lit-eval-list lits aignet-invals aignet-regvals new))))


  (defthm id-eval-of-aignet-add-gate-new
    (b* ((new-id (+ 1 (node-count aignet)))
         (aignet1 (cons (gate-node f0 f1) aignet)))
      (equal (id-eval new-id invals regvals aignet1)
             (eval-and-of-lits f0 f1 invals regvals aignet)))
    :hints(("Goal" :expand ((:free (id aignet1)
                             (id-eval id invals regvals aignet1)))
            :do-not-induct t
            :in-theory (e/d (aignet-idp
                             eval-and-of-lits-of-aignet-lit-fix-1
                             eval-and-of-lits-of-aignet-lit-fix-2-extension)
                            (eval-and-of-lits)))))

  (defthm id-eval-of-0
    (equal (id-eval 0 invals regvals aignet) 0))

  (defthm lit-eval-of-0-and-1
    (and (equal (lit-eval 0 invals regvals aignet) 0)
         (equal (lit-eval 1 invals regvals aignet) 1))))

(defsection semantics-seq
  :parents (aignet-logic)
  :short "Sequential semantics of aignets"
  :long "<p>The sequential semantics of aignets is given by the function
LIT-EVAL-SEQ.  This takes an aignet, a time frame number, a literal, a 2D bit
array assigning values to the primary inputs on each frame, and an initial
assignment to the registers.  It produces the value of that literal under those
sequential assignments.</p>

<p>The following theorem describes @('lit-eval-seq') in terms of combinational evaluation:
 @(thm lit-eval-seq-in-terms-of-lit-eval)</p>

<p>Here, @('frame-regvals') is a function that creates a register value array
from the previous frame's sequential evaluations of the next-state nodes
corresponding to each register.  That is, to get the value of a literal at a
particular timeframe, first evaluate the register next-states at the previous
timeframe, then combinationally evaluate the literal with the resulting
register values and the current frame's input values.</p>"

  (local (in-theory (disable acl2::bfix-when-not-1
                             acl2::nfix-when-not-natp)))
  (local (in-theory (enable acl2::make-list-ac-redef)))
  (local (in-theory (disable acl2::make-list-ac-removal)))

  (acl2::def2darr frames
                  :prefix frames
                  :elt-type bit
                  :elt-typep bitp
                  :default-elt 0
                  :elt-fix acl2::bfix
                  :elt-guard (bitp x))

  (defstobj-clone initsts bitarr :strsubst (("BIT" . "INITSTS")))

  (local (in-theory (enable aignet-lit-fix-id-val-linear)))

  (mutual-recursion
   (defun lit-eval-seq (k lit frames initsts aignet)
     (declare (xargs :stobjs (aignet frames initsts)
                     :guard (and (litp lit) (fanin-litp lit aignet)
                                 (natp k)
                                 (< k (frames-nrows frames))
                                 (<= (num-ins aignet) (frames-ncols frames))
                                 (<= (num-regs aignet) (bits-length initsts)))
                     :measure (acl2::nat-list-measure
                               (list k (lit-id lit) 1))
                     :verify-guards nil))
     (b-xor (id-eval-seq k (lit-id lit) frames initsts aignet)
            (lit-neg lit)))

   (defun eval-and-of-lits-seq (k lit1 lit2 frames initsts aignet)
     (declare (xargs :stobjs (aignet frames initsts)
                     :guard (and (litp lit1) (fanin-litp lit1 aignet)
                                 (litp lit2) (fanin-litp lit2 aignet)
                                 (natp k)
                                 (< k (frames-nrows frames))
                                 (<= (num-ins aignet) (frames-ncols frames))
                                 (<= (num-regs aignet) (bits-length initsts)))
                     :measure (acl2::nat-list-measure
                               (list k
                                     (max (lit-id lit1)
                                          (lit-id lit2))
                                     2))
                     :verify-guards nil))
     (b-and (lit-eval-seq k lit1 frames initsts aignet)
            (lit-eval-seq k lit2 frames initsts aignet)))

   (defun id-eval-seq (k id frames initsts aignet)
     (declare (xargs :stobjs (aignet frames initsts)
                     :guard (and (natp id) (id-existsp id aignet)
                                 (natp k)
                                 (< k (frames-nrows frames))
                                 (<= (num-ins aignet) (frames-ncols frames))
                                 (<= (num-regs aignet) (bits-length initsts)))
                     :measure (acl2::nat-list-measure
                               (list k id 0))))
     (b* (((unless (mbt (id-existsp id aignet)))
           ;; out-of-bounds IDs are false
           0)
          (type (id->type id aignet)))
         (aignet-case
          type
          :gate (b* ((f0 (gate-id->fanin0 id aignet))
                     (f1 (gate-id->fanin1 id aignet)))
                    (mbe :logic (eval-and-of-lits-seq
                                 k f0 f1 frames initsts aignet)
                         :exec (b-and (b-xor (id-eval-seq k (lit-id f0)
                                                          frames
                                                          initsts aignet)
                                             (lit-neg f0))
                                      (b-xor (id-eval-seq k (lit-id f1)
                                                          frames
                                                          initsts aignet)
                                             (lit-neg f1)))))
          :in    (let ((ionum (io-id->ionum id aignet)))
                   (if (int= (io-id->regp id aignet) 1)
                       (if (zp k)
                           (get-bit ionum initsts)
                         (id-eval-seq (1- k)
                                      (reg-id->nxst id aignet)
                                      frames initsts aignet))
                     (frames-get2 k ionum frames)))
          :out (b* ((f (co-id->fanin id aignet)))
                   (lit-eval-seq
                    k f frames initsts aignet))
          :const 0))))

  (in-theory (disable id-eval-seq lit-eval-seq eval-and-of-lits-seq))
  (local (in-theory (enable id-eval-seq lit-eval-seq eval-and-of-lits-seq)))


  (defun-nx id-eval-seq-ind (k id aignet)
    (declare (xargs :measure (acl2::two-nats-measure k id)))
    (b* (((unless (mbt (aignet-idp id aignet)))
          ;; out-of-bounds IDs are false
          0)
         (type (id->type id aignet)))
        (aignet-case
         type
         :gate (b* ((f0 (gate-id->fanin0 id aignet))
                    (f1 (gate-id->fanin1 id aignet)))
                   (list
                    (id-eval-seq-ind
                     k (lit-id f0) aignet)
                    (id-eval-seq-ind
                     k (lit-id f1) aignet)))
         :in     (if (int= (io-id->regp id aignet) 1)
                     (if (zp k)
                         0
                       (id-eval-seq-ind
                        (1- k) (reg-id->nxst id aignet) aignet))
                   0)
         :out  (b* ((f (co-id->fanin id aignet)))
                   (id-eval-seq-ind
                    k (lit-id f) aignet))
         :const 0)))

  (defcong nat-equiv equal (id-eval-seq k id frames initvals aignet) 1
    :hints (("goal" :induct (id-eval-seq-ind k id aignet))))

  (defcong bits-equiv equal (id-eval-seq k id frames initvals aignet) 4
    :hints (("goal" :induct (id-eval-seq-ind k id aignet))))

  (defcong nat-equiv equal (id-eval-seq k id frames initvals aignet) 2
    :hints (("goal" :induct (id-eval-seq-ind k id aignet)
             :expand ((id-eval-seq k id frames initvals aignet)
                      (id-eval-seq k nat-equiv frames initvals aignet)))))

  (defcong list-equiv equal (id-eval-seq k id frames initvals aignet) 5
    :hints (("goal" :induct (id-eval-seq-ind k id aignet)
             :in-theory (disable id-eval-seq lit-eval-seq))
            (and stable-under-simplificationp
                 '(:expand ((:free (k aignet)
                                   (id-eval-seq k id frames initvals aignet))
                            (:free (lit aignet)
                                   (lit-eval-seq k lit frames initvals aignet)))))))

  (defcong nat-equiv equal (lit-eval-seq k lit frames initvals aignet) 1
    :hints (("goal" :expand ((lit-eval-seq k lit frames initvals aignet)))))
  (defcong bits-equiv equal (lit-eval-seq k lit frames initvals aignet) 4
    :hints (("goal" :expand ((lit-eval-seq k lit frames initvals aignet)))))
  (defcong lit-equiv equal (lit-eval-seq k lit frames initvals aignet) 2
    :hints (("goal" :expand ((lit-eval-seq k lit frames initvals aignet)))))
  (defcong list-equiv equal (lit-eval-seq k lit frames initvals aignet) 5
    :hints (("goal" :expand ((:free (aignet)
                                    (lit-eval-seq k lit frames initvals aignet))))))

  (defcong nat-equiv equal (eval-and-of-lits-seq k lit1 lit2 frames initvals aignet) 1
    :hints (("goal" :expand ((eval-and-of-lits-seq k lit1 lit2 frames initvals aignet)))))
  (defcong bits-equiv equal (eval-and-of-lits-seq k lit1 lit2 frames initvals aignet) 5
    :hints (("goal" :expand ((eval-and-of-lits-seq k lit1 lit2 frames initvals aignet)))))
  (defcong lit-equiv equal (eval-and-of-lits-seq k lit1 lit2 frames initvals aignet) 2
    :hints (("goal" :expand ((eval-and-of-lits-seq k lit1 lit2 frames initvals aignet)))))
  (defcong lit-equiv equal (eval-and-of-lits-seq k lit1 lit2 frames initvals aignet) 3
    :hints (("goal" :expand ((eval-and-of-lits-seq k lit1 lit2 frames initvals aignet)))))
  (defcong list-equiv equal (eval-and-of-lits-seq k lit1 lit2 frames initvals aignet) 6
    :hints (("goal" :expand ((:free (aignet)
                                    (eval-and-of-lits-seq k lit1 lit2 frames initvals aignet))))))


  (defthm bitp-of-lit-eval-seq
    (bitp (lit-eval-seq k lit frames initsts aignet))
    :hints (("goal" :expand (lit-eval-seq k lit frames initsts aignet))))

  (defthm bitp-of-eval-and-of-lits-seq
    (bitp (eval-and-of-lits-seq k lit1 lit2 frames initsts aignet))
    :hints (("goal" :expand (eval-and-of-lits-seq k lit1 lit2 frames initsts aignet))))

  (defthm bitp-of-id-eval-seq
    (bitp (id-eval-seq k id frames initsts aignet))
    :hints (("goal" :induct (id-eval-seq-ind k id aignet)
             :expand ((id-eval-seq k id frames initsts aignet)
                      (:free (id)
                       (id-eval-seq (+ -1 k) id frames initsts aignet))))))

  (verify-guards id-eval-seq)

  (def-list-constructor frame-regvals (k frames initsts aignet)
    (declare (xargs :stobjs (frames initsts aignet)
                    :guard (and (natp k)
                                (<= k (frames-nrows frames))
                                (<= (num-ins aignet)
                                    (frames-ncols frames))
                                (<= (num-regs aignet)
                                    (bits-length initsts)))))
    (if (zp k)
        (get-bit n initsts)
      (id-eval-seq (1- k)
                   (reg-id->nxst (regnum->id n aignet) aignet)
                   frames initsts aignet))
    :length (num-regs aignet))

  (defthmd id-eval-seq-in-terms-of-id-eval
    (equal (id-eval-seq k id frames initsts aignet)
           (id-eval id
                    (nth k (cdr frames))
                    (frame-regvals k frames initsts aignet)
                    aignet))
    :hints (("goal" :induct (id-eval-ind id aignet)
             :expand ((:free (k) (id-eval-seq k id frames initsts aignet))
                      (:free (invals regvals)
                             (id-eval id invals regvals aignet))
                      (:free (k lit)
                             (lit-eval-seq k lit invals regvals aignet)))
             :in-theory (e/d (lit-eval
                              eval-and-of-lits)
                             (id-eval-seq
                              id-eval)))))

  (defthmd lit-eval-seq-in-terms-of-lit-eval
    (equal (lit-eval-seq k lit frames initsts aignet)
           (lit-eval lit (nth k (cdr frames))
                     (frame-regvals k frames initsts aignet)
                     aignet))
    :hints(("Goal" :expand ((lit-eval-seq k lit frames initsts aignet))
            :in-theory (enable id-eval-seq-in-terms-of-id-eval
                               lit-eval))))


  
  (defthm lookup-reg->nxst-of-non-nxst-extension
    (implies (and (aignet-extension-binding)
                  (equal (stype-count :nxst new)
                         (stype-count :nxst orig))
                  (<= (nfix id) (node-count orig)))
             (equal (lookup-reg->nxst id new)
                    (lookup-reg->nxst id orig)))
    :hints(("Goal" :in-theory (enable aignet-extension-p
                                      lookup-reg->nxst))))

  (defthm id-eval-seq-of-non-reg/nxst-extension
    (implies (and (aignet-extension-binding)
                  (equal (stype-count :reg new)
                         (stype-count :reg orig))
                  (equal (stype-count :nxst new)
                         (stype-count :nxst orig))
                  (aignet-idp id orig))
             (equal (id-eval-seq k id frames initvals new)
                    (id-eval-seq k id frames initvals orig)))
    :hints (("goal" :induct (id-eval-seq-ind k id new)
             :expand ((id-eval-seq k id frames initvals new)
                      (id-eval-seq k id frames initvals orig)
                      (id-eval-seq 0 id frames initvals new)
                      (id-eval-seq 0 id frames initvals orig))
             :in-theory (enable lit-eval-seq eval-and-of-lits-seq))))

  (defthm lit-eval-seq-of-non-reg/nxst-extension
    (implies (and (aignet-extension-binding)
                  (equal (stype-count :reg new)
                         (stype-count :reg orig))
                  (equal (stype-count :nxst new)
                         (stype-count :nxst orig))
                  (aignet-litp lit orig))
             (equal (lit-eval-seq k lit frames initvals new)
                    (lit-eval-seq k lit frames initvals orig)))
    :hints (("goal" :expand ((:free (aignet)
                                    (lit-eval-seq k lit frames initvals aignet))))))

  (defthm frame-regvals-of-non-reg/nxst-extension
    (implies (and (aignet-extension-binding)
                  (equal (stype-count :reg new)
                         (stype-count :reg orig))
                  (equal (stype-count :nxst new)
                         (stype-count :nxst orig))
                  (< (nfix n) (num-regs orig)))
             (equal (frame-regvals k frames initvals new)
                    (frame-regvals k frames initvals orig)))
    :hints ((and stable-under-simplificationp
                 (acl2::equal-by-nths-hint))))

  (defthm frame-regvals-when-zp
    (implies (zp k)
             (bits-equiv (frame-regvals k frames initvals aignet)
                         (take (num-regs aignet) initvals)))
    :hints(("Goal" :in-theory (enable bits-equiv
                                      nth-of-frame-regvals-split)))))





(defsection comb-equiv
  :parents (aignet-logic)
  :short "Combinational equivalence of aignets"
  :long "<p>We consider two aignets to be combinationally equivalent if:
<ul>
<li>they have the same number of primary outputs</li>
<li>they have the same number of registers</li>
<li>corresponding outputs evaluate to the same value under the same input/register
assignment</li>
<li>next-states of corresponding registers evaluate to the same value under the
same input/register assignment.</li></ul>
</p>"

  (defun-sk comb-equiv (aignet aignet2)
    (forall (n invals regvals)
            (and (equal (equal (id-eval (node-count (lookup-stype n
                                                                  (po-stype)
                                                                  aignet))
                                        invals regvals aignet)
                               (id-eval (node-count (lookup-stype n
                                                                  (po-stype)
                                                                  aignet2))
                                        invals regvals aignet2))
                        t)
                 (equal (equal (id-eval (node-count
                                         (lookup-reg->nxst
                                          (node-count
                                           (lookup-stype n (reg-stype)
                                                         aignet))
                                          aignet))
                                        invals regvals aignet)
                               (id-eval (node-count
                                         (lookup-reg->nxst
                                          (node-count
                                           (lookup-stype n (reg-stype)
                                                         aignet2))
                                          aignet2))
                                        invals regvals aignet2))
                        t)))
    :rewrite :direct)

  (in-theory (disable comb-equiv comb-equiv-necc))

  (local (defthm refl
           (comb-equiv x x)
           :hints(("Goal" :in-theory (enable comb-equiv)))))

  (local
   (defthm symm
     (implies (comb-equiv aignet aignet2)
              (comb-equiv aignet2 aignet))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :use ((:instance comb-equiv-necc
                           (n (mv-nth 0 (comb-equiv-witness aignet2 aignet)))
                           (invals (mv-nth 1 (comb-equiv-witness aignet2 aignet)))
                           (regvals (mv-nth 2 (comb-equiv-witness aignet2
                                                                  aignet))))))))))

  (local
   (defthm trans-lemma
     (implies (and (comb-equiv aignet aignet2)
                   (comb-equiv aignet2 aignet3))
              (comb-equiv aignet aignet3))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :use ((:instance comb-equiv-necc
                           (n (mv-nth 0 (comb-equiv-witness aignet aignet3)))
                           (invals (mv-nth 1 (comb-equiv-witness aignet aignet3)))
                           (regvals (mv-nth 2 (comb-equiv-witness aignet aignet3))))
                          (:instance comb-equiv-necc
                           (aignet aignet2) (aignet2 aignet3)
                           (n (mv-nth 0 (comb-equiv-witness aignet aignet3)))
                           (invals (mv-nth 1 (comb-equiv-witness aignet aignet3)))
                           (regvals (mv-nth 2 (comb-equiv-witness aignet
                                                                  aignet3))))))))))

  (defequiv comb-equiv))



(defsection seq-equiv
  :parents (aignet-logic)
  :short "Sequential equivalence of aignets"
  :long "<p>We consider two aignets to be sequentially equivalent if:
<ul>
<li>they have the same number of primary outputs</li>
<li>corresponding outputs sequentially evaluate to the same value under the
same series of primary input assignments and the all-0 initial register assignment.
</li></ul>
</p>

<p>This is a weaker condition than combinational equivalence: combinational
equivalence implies sequential equivalence, but not vice versa.</p>

<p>This particular formulation of sequential equivalence assumes that
evaluations of both networks start in the all-0 state.  Why?  Sequential
equivalence should allow differences in the the state encoding of the two
circuits, so we can't just universally quantify the initial register
assignment.  We could take the initial register assignments as two additional
inputs, but then this wouldn't truly be an equivalence relation.  We could
existentially quantify over the initial register assignments, i.e.

<blockquote> there exist initial states for aignets A and B such that for all
input sequences, the outputs of A and B have the same values on each
frame</blockquote>

but this isn't really what we want either.  It might instead be something like:

<blockquote> for each initial state of aignet A, there exists an initial state
for aignet B such that for all input sequences, the outputs of A and B have the
same values on each frame</blockquote>

but this isn't even an equivalence relation!  Instead we're going to fix an
initial state for each aignet, choosing the all-0 state as a simple
convention.  One can fix an FSM with a different initial state to one
with the all-0 initial state using @(see aignet-copy-init).</p>
"

  ;; NOTE: This assumes the initial states of both aignets are all-zero.
  (defun-sk seq-equiv (aignet aignet2)
    (forall (k n inframes)
            (equal (equal (id-eval-seq k (node-count (lookup-stype n
                                                                   (po-stype)
                                                                   aignet))
                                       inframes nil aignet)
                          (id-eval-seq k (node-count (lookup-stype n
                                                                   (po-stype)
                                                                   aignet2))
                                       inframes nil aignet2))
                   t))
    :rewrite :direct)

  (in-theory (disable seq-equiv seq-equiv-necc))

  (local (defthm refl
           (seq-equiv x x)
           :hints(("Goal" :in-theory (enable seq-equiv)))))

  (local
   (defthm symm
     (implies (seq-equiv aignet aignet2)
              (seq-equiv aignet2 aignet))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :use ((:instance seq-equiv-necc
                           (k (mv-nth 0 (seq-equiv-witness aignet2 aignet)))
                           (n (mv-nth 1 (seq-equiv-witness aignet2 aignet)))
                           (inframes (mv-nth 2 (seq-equiv-witness aignet2 aignet))))))))))

  (local
   (defthm trans-lemma
     (implies (and (seq-equiv aignet aignet2)
                   (seq-equiv aignet2 aignet3))
              (seq-equiv aignet aignet3))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :use ((:instance seq-equiv-necc
                           (k (mv-nth 0 (seq-equiv-witness aignet aignet3)))
                           (n (mv-nth 1 (seq-equiv-witness aignet aignet3)))
                           (inframes (mv-nth 2 (seq-equiv-witness aignet aignet3))))
                          (:instance seq-equiv-necc
                           (aignet aignet2) (aignet2 aignet3)
                           (k (mv-nth 0 (seq-equiv-witness aignet aignet3)))
                           (n (mv-nth 1 (seq-equiv-witness aignet aignet3)))
                           (inframes (mv-nth 2 (seq-equiv-witness aignet aignet3))))))))))

  (defequiv seq-equiv)

  (local (defun count-down (k)
           (if (zp k)
               k
             (count-down (1- k)))))

  (defthm id-eval-of-take-num-regs
    (equal (id-eval id invals
                    (take (stype-count :reg aignet) regvals)
                    aignet)
           (id-eval id invals regvals aignet))
    :hints (("goal" :induct (id-eval-ind id aignet)
             :expand ((:free (invals regvals)
                       (id-eval id invals regvals aignet)))
             :in-theory (enable lit-eval eval-and-of-lits))
            (and stable-under-simplificationp
                 '(:in-theory (enable acl2::nth-with-large-index)))))

  (defthmd comb-equiv-implies-same-frame-regvals
    (implies (and (comb-equiv aignet aignet2)
                  (<= (num-regs aignet)
                      (num-regs aignet2)))
             (bits-equiv (frame-regvals k frames initsts aignet)
                         (take (num-regs aignet)
                               (frame-regvals k frames initsts aignet2))))
    :hints (("goal" :induct (count-down k))
            (and stable-under-simplificationp
                 `(:expand (,(car (last clause)))
                   :in-theory (enable nth-of-frame-regvals-split
                                      id-eval-seq-in-terms-of-id-eval
                                      comb-equiv-necc)))))

  (defthm comb-equiv-implies-seq-equiv
    (implies (comb-equiv aignet aignet2)
             (seq-equiv aignet aignet2))
    :hints(("Goal" :in-theory (enable seq-equiv comb-equiv-necc
                                      comb-equiv-implies-same-frame-regvals
                                      id-eval-seq-in-terms-of-id-eval)
            :cases ((<= (num-regs aignet)
                        (num-regs aignet2)))))))


(defsection seq-equiv-init
  :parents (aignet-logic)
  :short "Sequential equivalence of aignets on a particular initial state"
  :long "<p>See @(see seq-equiv).  This variant additionally takes the initial
state of each aignet as an argument, and requires that they always produce the
same outputs when run starting at that initial state.</p>"

  (defstobj-clone initsts2 bitarr :strsubst (("BIT" . "INITSTS2")))

  (defun-sk seq-equiv-init (aignet initsts aignet2 initsts2)
    (forall (k n inframes)
            (equal (equal (id-eval-seq k (node-count (lookup-stype n
                                                                   (po-stype)
                                                                   aignet))
                                       inframes initsts aignet)
                          (id-eval-seq k (node-count (lookup-stype n
                                                                   (po-stype)
                                                                   aignet2))
                                       inframes initsts2 aignet2))
                   t))
    :rewrite :direct)

  (in-theory (disable seq-equiv-init seq-equiv-init-necc))

  (local (defthm refl
           (seq-equiv-init x initsts x initsts)
           :hints(("Goal" :in-theory (enable seq-equiv-init)))))

  (local
   (defthm symm
     (implies (seq-equiv-init aignet initsts aignet2 initsts2)
              (seq-equiv-init aignet2 initsts2 aignet initsts))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :use ((:instance seq-equiv-init-necc
                           (k (mv-nth 0 (seq-equiv-init-witness
                                         aignet2 initsts2 aignet initsts)))
                           (n (mv-nth 1 (seq-equiv-init-witness
                                         aignet2 initsts2 aignet initsts)))
                           (inframes (mv-nth 2 (seq-equiv-init-witness
                                                aignet2 initsts2 aignet initsts))))))))))

  (local
   (defthm trans-lemma
     (implies (and (seq-equiv-init aignet initsts aignet2 initsts2)
                   (seq-equiv-init aignet2 initsts2 aignet3 initsts3))
              (seq-equiv-init aignet initsts aignet3 initsts3))
     :hints ((and stable-under-simplificationp
                  `(:expand (,(car (last clause)))
                    :use ((:instance seq-equiv-init-necc
                           (k (mv-nth 0 (seq-equiv-init-witness
                                         aignet initsts aignet3 initsts3)))
                           (n (mv-nth 1 (seq-equiv-init-witness
                                         aignet initsts aignet3 initsts3)))
                           (inframes (mv-nth 2 (seq-equiv-init-witness
                                                aignet initsts aignet3 initsts3))))
                          (:instance seq-equiv-init-necc
                           (aignet aignet2) (aignet2 aignet3)
                           (initsts initsts2) (initsts2 initsts3)
                           (k (mv-nth 0 (seq-equiv-init-witness
                                                aignet initsts aignet3 initsts3)))
                           (n (mv-nth 1 (seq-equiv-init-witness
                                                aignet initsts aignet3 initsts3)))
                           (inframes (mv-nth 2 (seq-equiv-init-witness
                                                aignet initsts aignet3
                                                initsts3))))))))))

  (defthm comb-equiv-implies-seq-equiv-init
    (implies (comb-equiv aignet aignet2)
             (seq-equiv-init aignet initvals aignet2 initvals))
    :hints(("Goal" :in-theory (enable seq-equiv-init comb-equiv-necc
                                      comb-equiv-implies-same-frame-regvals
                                      id-eval-seq-in-terms-of-id-eval)
            :cases ((<= (num-regs aignet) (num-regs aignet2)))))))



(defsection aignet-print
  (local (in-theory (disable len)))
  (defund aignet-print-lit (lit aignet)
    (declare (xargs :stobjs aignet
                    :guard (and (litp lit)
                                (fanin-litp lit aignet))))
    (b* ((id (lit-id lit))
         (type (id->type id aignet))
         ((when (int= type (const-type)))
          (if (int= (lit-neg lit) 1) "1" "0")))
      (acl2::msg "~s0~s1~x2"
                 (if (int= (lit-neg lit) 1) "~" "")
                 (if (int= type (in-type))
                     (if (int= (io-id->regp id aignet) 1) "r" "i")
                   "g")
                 (if (int= type (in-type))
                     (io-id->ionum id aignet)
                   id))))

  (defund aignet-print-gate (n aignet)
    (declare (Xargs :stobjs aignet
                    :guard (and (natp n)
                                (id-existsp n aignet)
                                (int= (id->type n aignet) (gate-type)))))
    (b* ((f0 (gate-id->fanin0 n aignet))
         (f1 (gate-id->fanin1 n aignet)))
      (acl2::msg "g~x0 = ~@1 & ~@2"
                 n
                 (aignet-print-lit f0 aignet)
                 (aignet-print-lit f1 aignet))))


  (local (set-default-hints nil))
  
  (defund aignet-print-gates (n aignet)
    (declare (Xargs :stobjs aignet
                    :guard (and (natp n)
                                (<= n (num-nodes aignet)))
                    :guard-hints (("goal" :in-theory (enable aignet-idp)))
                    :measure (nfix (- (nfix (num-nodes aignet)) (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-nodes aignet)) (nfix n)))
                     :exec (= (num-nodes aignet) n)))
          nil)
         ((unless (int= (id->type n aignet) (gate-type)))
          (aignet-print-gates (1+ (lnfix n)) aignet))
         (- (cw "~@0~%" (aignet-print-gate n aignet))))
      (aignet-print-gates (1+ (lnfix n)) aignet)))

  (defund aignet-print-outs (n aignet)
    (declare (Xargs :stobjs aignet
                    :guard (and (natp n)
                                (<= n (num-outs aignet)))
                    :guard-hints (("goal" :in-theory (e/d (lookup-stype-in-bounds))))
                    :measure (nfix (- (nfix (num-outs aignet)) (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-outs aignet)) (nfix n)))
                     :exec (= (num-outs aignet) n)))
          nil)
         (- (cw "o~x0 = ~@1~%" n (aignet-print-lit
                                  (co-id->fanin (outnum->id n aignet) aignet)
                                  aignet))))
      (aignet-print-outs (1+ (lnfix n)) aignet)))

  (defthm ctype-of-aignet-lit
    (implies (aignet-litp lit aignet)
             (not (equal (CTYPE
                          (STYPE
                           (CAR
                            (LOOKUP-ID
                             (LIT-ID lit)
                             AIGNET))))
                         :OUTPUT)))
    :hints(("Goal" :in-theory (enable aignet-litp))))

  (defund aignet-print-regs (n aignet)
    (declare (Xargs :stobjs aignet
                    :guard (and (natp n)
                                (<= n (num-regs aignet)))
                    :guard-hints (("goal" :in-theory (e/d (lookup-stype-in-bounds
                                                           aignet-litp))))
                    :measure (nfix (- (nfix (num-regs aignet)) (nfix n)))))
    (b* (((when (mbe :logic (zp (- (nfix (num-regs aignet)) (nfix n)))
                     :exec (= (num-regs aignet) n)))
          nil)
         (id (regnum->id n aignet))
         (ri (reg-id->nxst id aignet))
         ((when (int= ri 0))
          (aignet-print-regs (1+ (lnfix n)) aignet))
         (- (cw "r~x0 = ~@1~%" n
                (if (int= ri id)
                    (aignet-print-lit (mk-lit id 0) aignet)
                  (aignet-print-lit (co-id->fanin ri aignet) aignet)))))
      (aignet-print-regs (1+ (lnfix n)) aignet)))

  (defund aignet-print (aignet)
    (declare (xargs :stobjs aignet))
    (progn$ (aignet-print-gates 0 aignet)
            (aignet-print-outs 0 aignet)
            (aignet-print-regs 0 aignet))))

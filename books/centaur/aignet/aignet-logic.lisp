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
;; (include-book "centaur/aignet/idp" :dir :system)
(include-book "litp")
(include-book "std/util/defmvtypes" :dir :system)
(include-book "std/util/defprojection" :dir :system)
(include-book "std/util/deflist" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/lists/equiv" :dir :system)
(include-book "tools/defmacfun" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "std/misc/two-nats-measure" :dir :system)
(include-book "clause-processors/unify-subst" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))
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


(local (in-theory (disable true-listp-update-nth
                           acl2::nth-with-large-index)))

(defmacro const-type () 0)
(defmacro gate-type () 1)
(defmacro in-type () 2)
(defmacro out-type () 3)

(defmacro const-ctype () :const)
(defmacro gate-ctype () :gate)
(defmacro in-ctype () :input)
(defmacro out-ctype () :output)


(make-event
 `(defmacro pi-stype () :pi))

(make-event
 `(defmacro reg-stype () :reg))

(make-event
 `(defmacro po-stype () :po))

(make-event
 `(defmacro nxst-stype () :nxst))

(make-event
 `(defmacro gate-stype () :gate))

(make-event
 `(defmacro const-stype () :const))

(define stypep (x)
  (consp (member x (list (pi-stype)
                         (reg-stype)
                         (po-stype)
                         (nxst-stype)
                         (gate-stype)
                         (const-stype)))))

(define stype-fix (x)
  :returns (stype stypep)
  (if (stypep x)
      x
    (const-stype))
  ///
  (defthm stype-fix-when-stypep
    (implies (stypep x)
             (equal (stype-fix x) x))))

;; (defthm stype-fix-possibilities
;;   (or (equal (stype-fix x) (const-stype))
;;       (equal (stype-fix x) (gate-stype))
;;       (equal (stype-fix x) (pi-stype))
;;       (equal (stype-fix x) (reg-stype))
;;       (equal (stype-fix x) (po-stype))
;;       (equal (stype-fix x) (nxst-stype)))
;;   :hints(("Goal" :in-theory (enable stype-fix stypep)))
;;   :rule-classes ((:forward-chaining :trigger-terms
;;                   ((stype-fix x)))))



;; This is just (car x), but it fixes it to one of the above things.
(define stype (x)
  :returns (stype stypep)
  (stype-fix (and (consp x) (car x))))


(defthm stype-possibilities
  (or (equal (stype x) (const-stype))
      (equal (stype x) (gate-stype))
      (equal (stype x) (pi-stype))
      (equal (stype x) (po-stype))
      (equal (stype x) (reg-stype))
      (equal (stype x) (nxst-stype)))
  :hints(("Goal" :in-theory (enable stype stype-fix stypep)))
  :rule-classes ((:forward-chaining :trigger-terms
                  ((stype x)))))


(define stype-equiv (x y)
  :enabled t
  (equal (stype-fix x) (stype-fix y))
  ///
  (defequiv stype-equiv)
  (defcong stype-equiv equal (stype-fix x) 1)
  (defthm stype-fix-under-stype-equiv
    (stype-equiv (stype-fix x) x)))

(define ctypep (x)
  (member x (list (in-ctype)
                  (out-ctype)
                  (gate-ctype)
                  (const-ctype))))

(define ctype-fix (x)
  :returns (ctype ctypep)
  (if (ctypep x)
      x
    (const-ctype))
  ///
  (defthm ctype-fix-when-ctypep
    (implies (ctypep x)
             (equal (ctype-fix x) x))))

(define ctype-equiv (x y)
  :enabled t
  (equal (ctype-fix x) (ctype-fix y))
  ///
  (defequiv ctype-equiv)
  (defcong ctype-equiv equal (ctype-fix x) 1)
  (defthm ctype-fix-under-ctype-equiv
    (ctype-equiv (ctype-fix x) x)))

;; (defthm ctype-fix-possibilities
;;   (or (equal (ctype-fix x) (const-ctype))
;;       (equal (ctype-fix x) (gate-ctype))
;;       (equal (ctype-fix x) (in-ctype))
;;       (equal (ctype-fix x) (out-ctype)))
;;   :rule-classes ((:forward-chaining :trigger-terms
;;                   ((ctype-fix x))))
;;   :hints(("Goal" :in-theory (enable ctype-fix ctypep))))

(defconst *stype-ctype-map*
  `((,(const-stype) . ,(const-ctype))
    (,(gate-stype) . ,(gate-ctype))
    (,(nxst-stype) . ,(out-ctype))
    (,(reg-stype) . ,(in-ctype))
    (,(po-stype) . ,(out-ctype))
    (,(pi-stype) . ,(in-ctype))))

(define ctype ((x stypep))
  :returns (type ctypep)
  (let ((x (stype-fix x)))
    (cdr (assoc x *stype-ctype-map*)))
  :prepwork ((local (in-theory (enable stype-fix stypep))))
  ///
  (defthm ctype-possibilities
    (or (equal (ctype x) (const-ctype))
        (equal (ctype x) (gate-ctype))
        (equal (ctype x) (in-ctype))
        (equal (ctype x) (out-ctype)))
    :rule-classes ((:forward-chaining :trigger-terms
                    ((ctype x))))
    :hints(("Goal" :in-theory (enable ctype ctypep))))

  (defcong stype-equiv equal (ctype x) 1))

(defconst *ctype-code-map*
  `((,(in-ctype) . ,(in-type))
    (,(out-ctype) . ,(out-type))
    (,(gate-ctype) . ,(gate-type))
    (,(const-ctype) . ,(const-type))))


(define typecodep (x)
  (and (natp x) (< x 4)))

(define typecode-fix (x)
  (if (typecodep x) x 0)
  ///
  (local (in-theory (enable typecodep)))

  (defthm typecodep-of-typecode-fix
    (typecodep (typecode-fix x)))

  (defthm typecode-fix-when-typecodep
    (implies (typecodep x)
             (equal (typecode-fix x)
                    x))))


(define typecode ((x ctypep))
  :returns (code natp :rule-classes (:rewrite :type-prescription))
  :prepwork ((local (in-theory (enable ctype-fix ctypep))))
  (cdr (assoc (ctype-fix x) *ctype-code-map*))
  ///
  (defthm typecode-bound
    (< (typecode x) 4)
    :rule-classes :linear)

  (defthm typecodep-of-typecode
    (typecodep (typecode x))))

(define code->ctype ((x typecodep))
  :prepwork ((local (in-theory (enable typecode-fix typecodep))))
  :returns (ctype ctypep)
  (car (rassoc (typecode-fix x) *ctype-code-map*))
  ///
  (local (in-theory (enable typecode ctype-fix ctypep)))
  (defthm code->ctype-of-typecode
    (equal (code->ctype (typecode x))
           (ctype-fix x))
    :hints(("Goal" :in-theory (enable typecode))))

  (defthm typecode-of-code->ctype
    (equal (typecode (code->ctype x))
           (typecode-fix x)))

  (defthm normalize-typecode-equivalence
    (equal (equal (typecode x) code)
           (and (typecodep code)
                (equal (ctype-fix x) (code->ctype code))))))


(define regp ((x stypep))
  :returns (regp bitp)
  (if (member (stype-fix x) (list (reg-stype) (nxst-stype)))
      1
    0)
  ///
  (defcong stype-equiv equal (regp x) 1))



(defthm stype-not-const-implies-nonempty
  (implies (not (equal (stype (car x)) (const-stype)))
           (consp x))
  :rule-classes ((:forward-chaining :trigger-terms
                  ((stype (car x))))))

(defthm ctype-not-const-implies-nonempty
  (implies (not (equal (ctype (stype (car x))) (const-ctype)))
           (consp x))
  :rule-classes ((:forward-chaining :trigger-terms
                  ((ctype (stype (car x)))))))

(defthm regp-not-zero-implies-nonempty
  (implies (not (equal (regp (stype (car x))) 0))
           (consp x))
  :rule-classes ((:forward-chaining :trigger-terms
                  ((regp (stype (car x)))))))



(defthm stype-by-ctype
  (and (equal (equal (ctype (stype x)) (const-ctype))
              (equal (stype x) (const-stype)))
       (equal (equal (ctype (stype x)) (gate-ctype))
              (equal (stype x) (gate-stype)))
       (implies (equal (regp (stype x)) 1)
                (and (equal (equal (ctype (stype x)) (in-ctype))
                            (equal (stype x) (reg-stype)))
                     (equal (equal (ctype (stype x)) (out-ctype))
                            (equal (stype x) (nxst-stype)))))
       (implies (not (equal (regp (stype x)) 1))
                (and (equal (equal (ctype (stype x)) (in-ctype))
                            (equal (stype x) (pi-stype)))
                     (equal (equal (ctype (stype x)) (out-ctype))
                            (equal (stype x) (po-stype))))))
  :hints(("goal" :in-theory (enable stype ctype regp))))


(defthm stype-not-const-fwd
  (implies (not (equal (stype x) (const-stype)))
           (not (equal (ctype (stype x)) (const-ctype))))
  :rule-classes ((:forward-chaining :trigger-terms ((stype x)))))

(defthm stype-not-gate-fwd
  (implies (not (equal (stype x) (gate-stype)))
           (not (equal (ctype (stype x)) (gate-ctype))))
  :rule-classes ((:forward-chaining :trigger-terms ((stype x)))))

(defthm ctype-not-in-fwd
  (implies (not (equal (ctype (stype x)) (in-ctype)))
           (and (not (equal (stype x) (pi-stype)))
                (not (equal (stype x) (reg-stype)))))
  :rule-classes ((:forward-chaining :trigger-terms ((ctype (stype x))))))

(defthm ctype-not-out-fwd
  (implies (not (equal (ctype (stype x)) (out-ctype)))
           (and (not (equal (stype x) (po-stype)))
                (not (equal (stype x) (nxst-stype)))))
  :rule-classes ((:forward-chaining :trigger-terms ((ctype (stype x))))))






;; (defun const-node ()
;;   (declare (xargs :guard t))
;;   '(:const))
;; (defun const-node-p (node)
;;   (declare (xargs :guard t))
;;   (equal node (const-node)))


(make-event
 `(defun pi-node ()
    (declare (xargs :guard t))
    '(,(pi-stype))))

(defun pi-node-p (node)
  (declare (xargs :guard t))
  (equal node (pi-node)))

(make-event
 `(defun reg-node ()
    (declare (xargs :guard t))
    '(,(reg-stype))))
(defun reg-node-p (node)
  (declare (xargs :guard t))
  (equal node (reg-node)))

(define gate-node-p (node)
  (and (true-listp node)
       (equal (len node) 3)
       (equal (first node) (gate-stype))
       (litp (second node))
       (litp (third node)))
  ///
  (defthm stype-when-gate-node-p
    (implies (gate-node-p node)
             (equal (stype node)
                    (gate-stype)))
    :hints(("Goal" :in-theory (enable stype)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)
                   :forward-chaining)))

(define gate-node ((f0 litp) (f1 litp))
  :returns (gate gate-node-p :hints(("Goal" :in-theory (enable gate-node-p))))
  (list (gate-stype) (lit-fix f0) (lit-fix f1))
  ///
  (defthm stype-of-gate-node
    (equal (stype (gate-node f0 f1))
           (gate-stype))
    :hints(("Goal" :in-theory (enable stype)))))

(define gate-node->fanin0 ((gate gate-node-p))
  :prepwork ((local (in-theory (enable gate-node-p))))
  :returns (lit litp)
  (lit-fix (second gate))
  ///
  (defthm gate-node->fanin0-of-gate-node
    (equal (gate-node->fanin0 (gate-node f0 f1))
           (lit-fix f0))
    :hints(("Goal" :in-theory (enable gate-node)))))

(define gate-node->fanin1 ((gate gate-node-p))
  :prepwork ((local (in-theory (enable gate-node-p))))
  :returns (lit litp)
  (lit-fix (third gate))
  ///
  (defthm gate-node->fanin1-of-gate-node
    (equal (gate-node->fanin1 (gate-node f0 f1))
           (lit-fix f1))
    :hints(("Goal" :in-theory (enable gate-node)))))

(define po-node-p (node)
  (and (true-listp node)
       (equal (len node) 2)
       (equal (first node) (po-stype))
       (litp (second node)))
  ///
  (defthm stype-when-po-node-p
    (implies (po-node-p node)
             (equal (stype node)
                    (po-stype)))
    :hints(("Goal" :in-theory (enable stype)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)
                   :forward-chaining)))

(define po-node ((f litp))
  :returns (po po-node-p :hints(("Goal" :in-theory (enable po-node-p))))
  (list (po-stype) (lit-fix f))
  ///
  (defthm stype-of-po-node
    (equal (stype (po-node f))
           (po-stype))
    :hints(("Goal" :in-theory (enable stype)))))

(define po-node->fanin ((po po-node-p))
  :prepwork ((local (in-theory (enable po-node-p))))
  :returns (lit litp)
  (lit-fix (second po))
  ///
  (defthm po-node->fanin-of-po-node
    (equal (po-node->fanin (po-node f))
           (lit-fix f))
    :hints(("Goal" :in-theory (enable po-node)))))



(define nxst-node-p (node)
  (and (true-listp node)
       (equal (len node) 3)
       (equal (first node) (nxst-stype))
       (litp (second node))
       (natp (third node)))
  ///
  (defthm stype-when-nxst-node-p
    (implies (nxst-node-p node)
             (equal (stype node)
                    (nxst-stype)))
    :hints(("Goal" :in-theory (enable stype)))
    :rule-classes ((:rewrite :backchain-limit-lst 0)
                   :forward-chaining)))

(define nxst-node ((f litp) (reg natp))
  :returns (ri nxst-node-p :hints(("Goal" :in-theory (enable nxst-node-p))))
  (list (nxst-stype) (lit-fix f) (lnfix reg))
  ///
  (defthm stype-of-nxst-node
    (equal (stype (nxst-node f reg))
           (nxst-stype))
    :hints(("Goal" :in-theory (enable stype)))))

(define nxst-node->fanin ((ri nxst-node-p))
  :prepwork ((local (in-theory (enable nxst-node-p))))
  :returns (lit litp)
  (lit-fix (second ri))
  ///
  (defthm nxst-node->fanin-of-nxst-node
    (equal (nxst-node->fanin (nxst-node f reg))
           (lit-fix f))
    :hints(("Goal" :in-theory (enable nxst-node)))))

(define nxst-node->reg ((ri nxst-node-p))
  :prepwork ((local (in-theory (enable nxst-node-p))))
  :returns (id natp)
  (lnfix (third ri))
  ///
  (defthm nxst-node->reg-of-nxst-node
    (equal (nxst-node->reg (nxst-node f reg))
           (lnfix reg))
    :hints(("Goal" :in-theory (enable nxst-node)))))


(defun const-node-p (node)
  (declare (xargs :guard t))
  (eq node nil))


(define node-p (x)
  (or (pi-node-p x)
      (reg-node-p x)
      (gate-node-p x)
      (po-node-p x)
      (nxst-node-p x)
      (const-node-p x))
  ///
  (defthm stypes-when-node-p
    (implies (node-p node)
             (and (equal (pi-node-p node)
                         (equal (stype node) (pi-stype)))
                  (equal (reg-node-p node)
                         (equal (stype node) (reg-stype)))
                  (equal (gate-node-p node)
                         (equal (stype node) (gate-stype)))
                  (equal (nxst-node-p node)
                         (equal (stype node) (nxst-stype)))
                  (equal (po-node-p node)
                         (equal (stype node) (po-stype))))))

  (defthmd node-p-when-all-others-ruled-out
    (implies (not (member (stype node)
                          (list (pi-stype) (po-stype) (nxst-stype) (reg-stype) (gate-stype))))
             (equal (node-p node)
                    (const-node-p node))))

  (defthm node-p-of-gate-node
    (equal (node-p (gate-node f0 f1))
           t))

  (defthm node-p-of-po-node
    (equal (node-p (po-node f))
           t))

  (defthm node-p-of-nxst-node
    (equal (node-p (nxst-node f reg))
           t)))






(define node->type ((node node-p))
  :enabled t
  (typecode (ctype (stype node))))

(define io-node->regp ((node node-p))
  :enabled t
  (regp (stype node)))









(std::deflist node-listp (x)
              (node-p x)
              :true-listp t
              :elementp-of-nil t)

(define proper-node-p (x)
  (and (node-p x)
       (not (const-node-p x)))
  :enabled t)

(std::deflist proper-node-listp (x)
              (proper-node-p x)
              :true-listp t)

(defthmd proper-node-listp-implies-node-listp
  (implies (proper-node-listp x)
           (node-listp x))
  :hints(("Goal" :in-theory (enable proper-node-listp
                                    node-listp))))




(local
 (defthm induct-by-list-equiv
   t
   :rule-classes ((:induction
                   :pattern (list-equiv x y)
                   :scheme (acl2::fast-list-equiv x y)))))

(local (in-theory (enable (:induction acl2::fast-list-equiv))))

(define node-count (x)
  ;; This is just (len x).  But it's convenient (?) to have a different
  ;; function in order to know we're talking about aignets specifically.
  (if (atom x)
      0
    (+ 1 (node-count (cdr x))))
  ///
  (defthm node-count-of-cons
    (equal (node-count (cons a x))
           (+ 1 (node-count x))))
  (defthm node-count-of-atom
    (implies (not (consp x))
             (equal (node-count x) 0))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))
  (defthm node-count-equal-0
    (equal (equal (node-count x) 0)
           (not (consp x))))
  (defthm node-count-greater-than-0
    (equal (< 0 (node-count x))
           (consp x)))
  (defcong list-equiv equal (node-count x) 1))


(define stype-count (type x)
  (cond ((atom x) 0)
        ((equal (stype-fix type) (stype (car x)))
         (+ 1 (stype-count type (cdr x))))
        (t (stype-count type (cdr x))))
  ///
  (defcong stype-equiv equal (stype-count type x) 1)
  (defcong list-equiv equal (stype-count type x) 2)
  (defthm stype-count-of-cons
    (equal (stype-count type (cons a b))
           (if (equal (stype-fix type) (stype a))
               (+ 1 (stype-count type b))
             (stype-count type b))))
  (defthm stype-count-of-atom
    (implies (not (consp x))
             (equal (stype-count type x)
                    0))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm positive-stype-count-implies-consp
    (implies (< 0 (stype-count stype x))
             (and (consp x)
                  (posp (node-count x))))
    :hints(("Goal" :in-theory (enable stype-count node-count)))
    :rule-classes :forward-chaining))




(mutual-recursion
 (defun subtermp (x y)
   (declare (xargs :guard t))
   (or (equal x y)
       (and (consp y)
            (not (eq (car y) 'quote))
            (subtermp-list x (cdr y)))))
 (defun subtermp-list (x y)
   (declare (xargs :guard t))
   (if (atom y)
       nil
     (or (subtermp x (car y))
         (subtermp-list x (cdr y))))))


(defsection aignet-extension-bind-inverse
  ;; Table aignet-extension-bind-inverse, holding the various functions that look
  ;; up suffixes of the aignet -- such as lookup-id, lookup-stype,
  ;; lookup-reg->nxst.

  ;; Each entry is a key just bound to T, and the key is a term where the
  ;; variable NEW is in the position of the new aignet.
  (table aignet-lookup-fns
         nil
         '(((cdr new) . t)
           ((lookup-id n new) . t)
           ((lookup-reg->nxst n new) . t)
           ((lookup-stype n stype new) . t)) :clear)

  (defmacro add-aignet-lookup-fn (term)
    `(table aignet-lookup-fns ',term t))

  (defun aignet-extension-bind-scan-lookups (term var table)
    (Declare (Xargs :mode :program))
    (b* (((when (atom table)) nil)
         ((mv ok subst) (acl2::simple-one-way-unify
                         (caar table) term nil))
         ((unless ok)
          (aignet-extension-bind-scan-lookups term var (cdr table)))
         (new (cdr (assoc 'new subst))))
      `((,var . ,new))))


  (defun aignet-extension-bind-inverse-fn (x var mfc state)
    (declare (xargs :mode :program
                    :stobjs state)
             (ignorable mfc))
    (aignet-extension-bind-scan-lookups
     x var (table-alist 'aignet-lookup-fns (w state))))

  (defmacro aignet-extension-bind-inverse (&key (new 'new)
                                                (orig 'orig))
    `(and (bind-free (aignet-extension-bind-inverse-fn
                      ,orig ',new mfc state)
                     (,new))
          (aignet-extension-p ,new ,orig))))


(define aignet-extension-p (y x)
  (or (equal x y)
      (and (consp y)
           (aignet-extension-p (cdr y) x)))
  ///
  (defthm node-count-when-aignet-extension
    (implies (aignet-extension-p y x)
             (<= (node-count x) (node-count y)))
    :rule-classes ((:linear :trigger-terms ((node-count x)))))

  (defthm node-count-when-aignet-extension-bind-inverse
    (implies (aignet-extension-bind-inverse :orig x :new y)
             (<= (node-count x) (node-count y)))
    :rule-classes ((:linear :trigger-terms ((node-count x)))))

  (defthm stype-count-when-aignet-extension
    (implies (aignet-extension-p y x)
             (<= (stype-count k x) (stype-count k y)))
    :rule-classes ((:linear :trigger-terms ((stype-count k x)))))

  (defthm stype-count-when-aignet-extension-bind-inverse
    (implies (aignet-extension-bind-inverse :orig x :new y)
             (<= (stype-count k x) (stype-count k y)))
    :rule-classes ((:linear :trigger-terms ((stype-count k x)))))

  (defthm node-count-cdr-when-aignet-extension
    (implies (and (aignet-extension-p y x)
                  (or (consp x) (consp y)))
             (< (node-count (cdr x)) (node-count y)))
    :rule-classes ((:linear :trigger-terms
                    ((node-count (cdr x))))))

  (defthm node-count-cdr-when-aignet-extension-inverse
    (implies (and (aignet-extension-bind-inverse :orig x :new y)
                  (or (consp x) (consp y)))
             (< (node-count (cdr x)) (node-count y)))
    :rule-classes ((:linear :trigger-terms
                    ((node-count (cdr x))))))

  (defthm stype-count-cdr-when-aignet-extension-p
    (implies (and (aignet-extension-p y x)
                  (equal type (stype (car x)))
                  (or (not (equal (stype-fix type) (const-stype)))
                      (consp x)))
             (< (stype-count type (cdr x))
                (stype-count type y)))
    :rule-classes ((:linear :trigger-terms
                    ((stype-count type (cdr x))))))

  (defthm stype-count-cdr-when-aignet-extension-inverse
    (implies (and (aignet-extension-bind-inverse :orig x :new y)
                  (equal type (stype (car x)))
                  (or (not (equal (stype-fix type) (const-stype)))
                      (consp x)))
             (< (stype-count type (cdr x))
                (stype-count type y)))
    :rule-classes ((:linear :trigger-terms
                    ((stype-count type (cdr x))))))

  ;; (defcong list-equiv equal (aignet-extension-p y x) 1)
  ;; (defcong list-equiv equal (aignet-extension-p y x) 2)

  (defthmd aignet-extension-p-transitive
    (implies (and (aignet-extension-p x y)
                  (aignet-extension-p y z))
             (aignet-extension-p x z))
    :rule-classes ((:rewrite :match-free :all)))

  ;; (defthm node-count-aignet-extension-p-of-cdr
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y))
  ;;            (< (node-count x) (node-count y)))
  ;;   :hints (("goal" :induct (list-equiv x y))))
  ;; (defthm node-count-aignet-extension-p-of-cdr-not-equal
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y))
  ;;            (not (equal (node-count x) (node-count y))))
  ;;   :hints (("goal" :use node-count-aignet-extension-p-of-cdr
  ;;            :in-theory (disable node-count-aignet-extension-p-of-cdr))))
  ;; (defthm stype-count-aignet-extension-p-of-cdr
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y)
  ;;                 (equal (car y) k))
  ;;            (< (stype-count k x) (stype-count k y)))
  ;;   :hints (("goal" :induct (list-equiv x y))))
  ;; (defthm stype-count-aignet-extension-p-of-cdr-not-equal
  ;;   (implies (and (aignet-extension-p (cdr y) x)
  ;;                 (consp y)
  ;;                 (equal (car y) k))
  ;;            (not (equal (stype-count k x) (stype-count k y))))
  ;;   :hints (("goal" :use stype-count-aignet-extension-p-of-cdr
  ;;            :in-theory (disable stype-count-aignet-extension-p-of-cdr))))
  (defthm aignet-extension-p-self
    (aignet-extension-p x x))

  (defthm aignet-extension-p-cons
    (aignet-extension-p (cons x y) y))

  (defthm aignet-extension-p-cons-more
    (implies (aignet-extension-p y z)
             (aignet-extension-p (cons x y) z)))

  (defthm aignet-extension-p-cdr
    (implies (and (aignet-extension-p y z)
                  (consp z))
             (aignet-extension-p y (cdr z)))))







(define lookup-id ((id natp)
                     (aignet node-listp))
  :returns (suffix node-listp :hyp (node-listp aignet))
  (cond ((endp aignet) aignet)
        ((equal (node-count aignet) (lnfix id))
         aignet)
        (t (lookup-id id (cdr aignet))))
  ///
  (defcong nat-equiv equal (lookup-id id aignet) 1)
  (defthm node-count-of-lookup-id
    (implies (<= (nfix n) (node-count aignet))
             (equal (node-count (lookup-id n aignet))
                    (nfix n))))
  (defthm node-count-of-cdr-lookup-id
    (implies (consp (lookup-id n aignet))
             (equal (node-count (cdr (lookup-id n aignet)))
                    (+ -1 (nfix n)))))
  (defthm lookup-id-0
    (list-equiv (lookup-id 0 aignet) nil))
  (defthmd lookup-id-in-bounds
    (iff (consp (lookup-id n aignet))
         (and (< 0 (nfix n))
              (<= (nfix n) (node-count aignet)))))
  (defthm lookup-id-aignet-extension-p
    (aignet-extension-p aignet (lookup-id id aignet))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))
  (defcong list-equiv list-equiv (lookup-id id aignet) 2)
  ;; (defcong list-equiv iff (lookup-id id aignet) 2)
  (defthm lookup-id-in-extension
    (implies (and (aignet-extension-p new orig)
                  (<= (nfix id) (node-count orig)))
             (equal (lookup-id id new)
                    (lookup-id id orig)))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))
  (defthm lookup-id-in-extension-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (<= (nfix id) (node-count orig)))
             (equal (lookup-id id orig)
                    (lookup-id id new)))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))
  (defthm node-count-of-cdr-lookup-bound-by-id
    (implies (consp (lookup-id id aignet))
             (< (node-count (cdr (lookup-id id aignet)))
                (nfix id)))
    :rule-classes :linear)
  (defthm lookup-id-of-node-count-of-suffix
    (implies (and (aignet-extension-p y x)
                  (consp x))
             (equal (lookup-id (node-count x) y)
                    x))
    :hints(("Goal" :in-theory (enable lookup-id))))
  (defthm true-listp-lookup-id-of-node-listp
    (implies (node-listp aignet)
             (true-listp (lookup-id id aignet)))
    :rule-classes :type-prescription)
  (defthm lookup-id-of-nil
    (equal (lookup-id x nil) nil))
  ;; (defun check-not-known-natp (term mfc state)
  ;;   (declare (xargs :mode :program :stobjs state))
  ;;   (not (acl2::ts-subsetp (acl2::mfc-ts term mfc state)
  ;;                          acl2::*ts-non-negative-integer*)))
  (defthm lookup-id-consp-forward-to-id-bound-nfix
    (implies (and (consp (lookup-id id aignet))
                  ;; (syntaxp (check-not-known-natp term mfc state))
                  )
             (<= (nfix id) (node-count aignet)))
    :rule-classes :forward-chaining)
  (defthm lookup-id-consp-forward-to-id-bound
    (implies (and (consp (lookup-id id aignet))
                  (natp id))
             (<= id (node-count aignet)))
    :rule-classes :forward-chaining))


(define lookup-stype ((n natp)
                      (stype stypep)
                      (aignet node-listp))
  :returns (suffix node-listp :hyp (node-listp aignet))
  (cond ((endp aignet) aignet)
        ((and (equal (stype (car aignet)) (stype-fix stype))
              (equal (stype-count stype (cdr aignet)) (lnfix n)))
         aignet)
        (t (lookup-stype n stype (cdr aignet))))
  ///
  (defcong nat-equiv equal (lookup-stype n stype aignet) 1)
  (defcong stype-equiv equal (lookup-stype n stype aignet) 2
    :hints(("Goal" :in-theory (disable stype-equiv))))
  (defcong list-equiv list-equiv (lookup-stype n stype aignet) 3)
  (defthm stype-count-of-lookup-stype
    (implies (< (nfix n) (stype-count stype aignet))
             (equal (stype-count stype (cdr (lookup-stype n stype aignet)))
                    (nfix n))))
  (defthm car-of-lookup-stype
    (implies (< (nfix n) (stype-count stype aignet))
             (equal (stype (car (lookup-stype n stype aignet)))
                    (stype-fix stype))))
  (defthmd lookup-stype-in-bounds
    (iff (consp (lookup-stype n stype aignet))
         (< (nfix n) (stype-count stype aignet))))
  (defthm lookup-stype-aignet-extension-p
    (aignet-extension-p aignet (lookup-stype n stype aignet))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))

  (defthm lookup-stype-of-stype-count
    (implies (and (aignet-extension-p new orig)
                  (equal (stype (car orig)) (stype-fix stype))
                  (not (equal (stype-fix stype) (const-stype))))
             (equal (lookup-stype (stype-count stype (cdr orig))
                                  stype
                                  new)
                    orig))
    :hints(("Goal" :in-theory (enable aignet-extension-p
                                      lookup-stype
                                      stype-count)
            :induct t)
           (and stable-under-simplificationp
                '(:cases ((< (stype-count stype (cdr new))
                             (stype-count stype orig)))))))

  (defthm lookup-stype-in-extension
    (implies (and (aignet-extension-p new orig)
                  (consp (lookup-stype n stype orig)))
             (equal (lookup-stype n stype new)
                    (lookup-stype n stype orig)))
    :hints(("Goal" :in-theory (enable aignet-extension-p
                                      lookup-stype-in-bounds))))

  (defthm lookup-stype-in-extension-inverse
    (implies (and (aignet-extension-bind-inverse)
                  (consp (lookup-stype n stype orig)))
             (list-equiv (lookup-stype n stype orig)
                         (lookup-stype n stype new)))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))

  (defthm stype-of-lookup-stype
    (implies (consp (lookup-stype n stype aignet))
             (equal (stype (car (lookup-stype n stype aignet)))
                    (stype-fix stype)))))


;; NOTE this is different from the other lookups: it's by ID of the
;; corresponding RO node, not IO number.  I think the asymmetry is worth it
;; though.
(define lookup-reg->nxst ((reg-id natp)
                          (aignet node-listp))
  :returns (suffix node-listp :hyp (node-listp aignet))
  (cond ((endp aignet) aignet)
        ((and (equal (stype (car aignet)) (nxst-stype))
              (b* ((ro (nxst-node->reg (car aignet))))
                (and (nat-equiv reg-id ro)
                     (< ro (node-count aignet))
                     ;; this check ensures that if we look for the nxst of a
                     ;; nonexistent reg we won't find one
                     (equal (stype (car (lookup-id ro aignet)))
                            (reg-stype)))))
         aignet)
        ((and (equal (stype (car aignet)) (reg-stype))
              (nat-equiv (node-count aignet) reg-id))
         aignet)
        (t (lookup-reg->nxst reg-id (cdr aignet))))
  ///
  (defcong nat-equiv equal (lookup-reg->nxst reg-id aignet) 1)
  (defcong list-equiv list-equiv (lookup-reg->nxst reg-id aignet) 2)
  (defthm car-of-lookup-reg->nxst-when-nxst
    (implies (and (consp (lookup-reg->nxst reg-id aignet))
                  ;; (not (equal (stype (car (lookup-reg->nxst reg-id aignet)))
                  ;;             (reg-stype)))
                  (not (equal (node-count (lookup-reg->nxst reg-id aignet))
                              (nfix reg-id))))
             (and (equal (stype (car (lookup-reg->nxst reg-id aignet))) (nxst-stype))
                  (equal (nxst-node->reg (car (lookup-reg->nxst reg-id aignet)))
                         (nfix reg-id)))))

  ;; (defthm lookup-reg->nxst-count-when-reg
  ;;   (implies (equal (stype (car (lookup-reg->nxst reg-id aignet)))
  ;;                   (reg-stype))
  ;;            (equal (node-count (lookup-reg->nxst reg-id aignet))
  ;;                   (nfix reg-id))))

  (defthm aignet-extension-p-of-lookup-reg->nxst
    (aignet-extension-p aignet (lookup-reg->nxst reg-id aignet))
    :hints(("Goal" :in-theory (enable aignet-extension-p))))

  ;; (defthm stype-of-lookup-reg->nxst
  ;;   (implies (consp (lookup-reg->nxst n aignet))
  ;;            (equal (stype (car (lookup-reg->nxst n aignet)))
  ;;                   (nxst-stype))))

  (defthm node-count-of-lookup-reg->nxst
    (implies (consp (lookup-reg->nxst n aignet))
             (<= (nfix n) (node-count (lookup-reg->nxst n aignet))))
    :rule-classes :linear)

  (defthm lookup-reg->nxst-out-of-bounds
    (implies (< (node-count aignet) (nfix id))
             (not (consp (lookup-reg->nxst id aignet))))))







;; (defthm node-by-stype-types
;;   (implies (node-p node)
;;            (and (equal (equal (ctype (stype node)) (const-type))
;;                        (const-node-p node))
;;                 (equal (equal (ctype (stype node)) (gate-type))
;;                        (gate-node-p node))
;;                 (implies (equal (ctype (stype node)) (in-type))
;;                          (equal (equal (regp (stype node)) 1)
;;                                 (reg-node-p node)))
;;                 (implies (not (reg-node-p node))
;;                          (equal (equal (ctype (stype node)) (in-type))
;;                                 (pi-node-p node)))
;;                 (implies (equal (ctype (stype node)) (out-type))
;;                          (equal (equal (regp (stype node)) 1)
;;                                 (nxst-node-p node)))
;;                 (implies (not (nxst-node-p node))
;;                          (equal (equal (ctype (stype node)) (out-type))
;;                                 (po-node-p node)))))
;;   :hints(("Goal" :in-theory (enable node-p))))



(define co-node->fanin ((node node-p))
  :guard (equal (node->type node) (out-type))
  :returns (lit litp)
  (lit-fix (if (equal (io-node->regp node) 1)
               (nxst-node->fanin node)
             (po-node->fanin node)))
  :prepwork ((local (in-theory (e/d (node->type
                                     io-node->regp)
                                    ((force))))))
  ///
  (defthm co-node->fanin-of-po-node
    (equal (co-node->fanin (po-node f))
           (lit-fix f)))
  (defthm co-node->fanin-of-nxst-node
    (equal (co-node->fanin (nxst-node f n))
           (lit-fix f))))



(define aignet-litp ((lit litp)
                     (aignet node-listp))
  (and (<= (lit-id lit)
           (node-count aignet))
       (not (equal (node->type (car (lookup-id (lit-id lit) aignet)))
                   (out-type))))
  ///
  (defthm lit-id-bound-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (<= (lit-id lit) (node-count aignet)))
    :rule-classes ((:linear :trigger-terms ((lit-id lit)))))
  (local (defthm <=-when-<-+-1
           (implies (and (< x (+ 1 y))
                         (integerp x) (integerp y))
                    (<= x y))))
  (defthm aignet-litp-in-extension
    (implies (and (aignet-extension-p new orig)
                  (aignet-litp lit orig))
             (aignet-litp lit new)))
  (defcong lit-equiv equal (aignet-litp lit aignet) 1)
  (defcong list-equiv equal (aignet-litp lit aignet) 2))

(define aignet-idp ((id natp) aignet)
  (<= (lnfix id) (node-count aignet))
  ///
  (defthm bound-when-aignet-idp
    (implies (aignet-idp id aignet)
             (<= (nfix id) (node-count aignet))))
  (local (defthm <=-when-<-+-1
           (implies (and (< x (+ 1 y))
                         (integerp x) (integerp y))
                    (<= x y))))
  (defthm aignet-idp-in-extension
    (implies (and (aignet-extension-p aignet2 aignet)
                  (aignet-idp id aignet))
             (aignet-idp id aignet2)))
  (defcong nat-equiv equal (aignet-idp id aignet) 1)
  (defcong list-equiv equal (aignet-idp id aignet) 2)
  (defthm aignet-idp-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (aignet-idp (lit-id lit) aignet))
    :hints(("Goal" :in-theory (enable aignet-litp)))))


(defsection aignet-case
  (defmacro aignet-case (type &key const gate in out)
    `(case ,type
       (,(gate-type)      ,gate)
       (,(in-type)        ,in)
       (,(out-type)       ,out)
       (otherwise         ,const)))

  (defmacro aignet-seq-case (type regp &rest keys)
    ;; we can't use keyword args because "pi" can't be used as a formal
    (declare (xargs :guard (and (keyword-value-listp keys)
                                (not (and (assoc-keyword :ci keys)
                                          (or (assoc-keyword :pi keys)
                                              (assoc-keyword :reg keys))))
                                (not (and (assoc-keyword :co keys)
                                          (or (assoc-keyword :po keys)
                                              (assoc-keyword :nxst keys)))))))
    `(case ,type
       (,(gate-type) ,(cadr (assoc-keyword :gate keys)))
       (,(in-type)   ,(if (assoc-keyword :ci keys)
                          (cadr (assoc-keyword :ci keys))
                        `(if (int= 1 ,regp)
                             ,(cadr (assoc-keyword :reg keys))
                           ,(cadr (assoc-keyword :pi keys)))))
       (,(out-type)  ,(if (assoc-keyword :co keys)
                          (cadr (assoc-keyword :co keys))
                        `(if (int= 1 ,regp)
                             ,(cadr (assoc-keyword :nxst keys))
                           ,(cadr (assoc-keyword :po keys)))))
       (otherwise    ,(cadr (assoc-keyword :const keys))))))


(define aignet-nodes-ok ((aignet node-listp))
  (if (endp aignet)
      t
    (and (aignet-seq-case
          (node->type (car aignet))
          (io-node->regp (car aignet))
          :ci   t
          :po   (aignet-litp (co-node->fanin (car aignet))
                             (cdr aignet))
          :nxst   (and (aignet-litp (co-node->fanin (car aignet))
                                  (cdr aignet))
                     (aignet-idp (nxst-node->reg (car aignet))
                                 (cdr aignet)))
          :gate (let ((f0 (gate-node->fanin0 (car aignet)))
                      (f1 (gate-node->fanin1 (car aignet))))
                  (and (aignet-litp f0 (cdr aignet))
                       (aignet-litp f1 (cdr aignet)))))
         (aignet-nodes-ok (cdr aignet))))
  ///
  (defthm proper-node-list-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (node-listp aignet))
             (proper-node-listp aignet)))
  (defthm co-fanin-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet)))
                         (out-type)))
             (< (lit-id (co-node->fanin
                         (car (lookup-id id aignet))))
                (nfix id)))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)))
    :rule-classes (:rewrite
                   (:linear :trigger-terms
                    ((lit-id (co-node->fanin
                              (car (lookup-id id aignet))))))))
  (defthm nxst-reg-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet)))
                         (out-type))
                  (equal (io-node->regp (car (lookup-id id aignet)))
                         1))
             (< (nxst-node->reg (car (lookup-id id aignet)))
                (nfix id)))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (e/d (lookup-id aignet-idp)
                             ((force)))))
    :rule-classes (:rewrite
                   (:linear :trigger-terms
                    ((nxst-node->reg
                      (car (lookup-id id aignet)))))))
  (defthm nxst-reg-aignet-idp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet)))
                         (out-type))
                  (equal (io-node->regp (car (lookup-id id aignet)))
                         1))
             (aignet-idp (nxst-node->reg (car (lookup-id id aignet)))
                         (cdr (lookup-id id aignet))))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (e/d (lookup-id aignet-idp)
                             ((force))))))
  (defthm gate-fanin0-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet)))
                         (gate-type)))
             (< (lit-id (gate-node->fanin0
                         (car (lookup-id id aignet))))
                (nfix id)))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)))
    :rule-classes (:rewrite
                   (:linear :trigger-terms
                    ((lit-id (gate-node->fanin0
                              (car (lookup-id id aignet))))))))
  (defthm gate-fanin1-ordered-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet))) (gate-type)))
             (< (lit-id (gate-node->fanin1
                         (car (lookup-id id aignet))))
                (nfix id)))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)))
    :rule-classes (:rewrite
                   (:linear :trigger-terms
                    ((lit-id (gate-node->fanin1
                              (car (lookup-id id aignet))))))))
  (local (defthm aignet-litp-in-extension-bind
           (implies (and (aignet-litp lit orig)
                         (aignet-extension-p new orig))
                    (aignet-litp lit new))))
  (defthm co-fanin-aignet-litp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet))) (out-type))
                  (aignet-extension-p aignet2 (cdr (lookup-id id aignet))))
             (aignet-litp (co-node->fanin
                           (car (lookup-id id aignet)))
                          aignet2))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)
             :expand ((aignet-nodes-ok aignet)))))
  (defthm gate-fanin0-aignet-litp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet))) (gate-type))
                  (aignet-extension-p aignet2 (cdr (lookup-id id aignet))))
             (aignet-litp (gate-node->fanin0
                           (car (lookup-id id aignet)))
                          aignet2))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)
             :expand ((aignet-nodes-ok aignet)))))
  (defthm gate-fanin1-aignet-litp-when-aignet-nodes-ok
    (implies (and (aignet-nodes-ok aignet)
                  (equal (node->type (car (lookup-id id aignet))) (gate-type))
                  (aignet-extension-p aignet2 (cdr (lookup-id id aignet))))
             (aignet-litp (gate-node->fanin1
                           (car (lookup-id id aignet)))
                          aignet2))
    :hints (("goal" :induct (lookup-id id aignet)
             :in-theory (enable lookup-id)
             :expand ((aignet-nodes-ok aignet)))))
  (defcong list-equiv equal (aignet-nodes-ok x) 1
    :hints (("goal" :induct (list-equiv x acl2::x-equiv)
             :in-theory (disable (force)))))
  (defthm aignet-nodes-ok-of-extension
    (implies (and (aignet-extension-p y x)
                  (aignet-nodes-ok y))
             (aignet-nodes-ok x))
    :hints(("Goal" :in-theory (enable aignet-extension-p aignet-nodes-ok)
            :induct (aignet-nodes-ok y))))

  (defthm aignet-nodes-ok-of-suffix-inverse
    (implies (and (aignet-extension-bind-inverse :orig x :new y)
                  (aignet-nodes-ok y))
             (aignet-nodes-ok x))
    :hints(("Goal" :in-theory (enable aignet-extension-p aignet-nodes-ok)
            :induct (aignet-nodes-ok y)))))



;; (defthm reg-count-aignet-extension-p-by-node->type/regp
;;   (implies (and (aignet-extension-bind-inverse :orig x :new y)
;;                 (aignet-extension-p y x)
;;                 (equal (node->type (car x)) (in-type))
;;                 (equal (io-node->regp (car x)) 1))
;;            (< (reg-count (cdr x)) (reg-count y)))
;;   :hints(("Goal" :in-theory (enable node->type
;;                                     io-node->regp)))
;;   :rule-classes ((:linear :trigger-terms
;;                   ((reg-count (cdr x))))))

(local (defthm node-count-cdr-when-consp
         (implies (consp x)
                  (< (node-count (cdr x)) (node-count x)))
         :rule-classes :linear))


(define aignet-lit-fix ((x litp)
                        (aignet node-listp))
  :verify-guards nil
  :measure (node-count aignet)
  :hints ('(:in-theory (enable lookup-id-in-bounds)))
  :returns (fix)
  (b* ((id (lit-id x))
       (look (lookup-id id aignet))
       ((unless (consp look))
        (mk-lit 0 (lit-neg x)))
       ((cons node rest) look)
       ((when (eql (node->type node) (out-type)))
        (lit-negate-cond
         (aignet-lit-fix (co-node->fanin node) rest)
         (lit-neg x))))
    (lit-fix x))
  ///
  (defthm litp-of-aignet-lit-fix
    (litp (aignet-lit-fix x aignet)))
  (verify-guards aignet-lit-fix)

  (local (defthm lookup-id-in-extension-bind-inverse
           (implies (and (aignet-extension-bind-inverse :orig x :new y)
                         (< (nfix id) (node-count x)))
                    (equal (lookup-id id (cdr x))
                           (lookup-id id y)))
           :hints(("Goal" :in-theory (enable aignet-extension-p lookup-id)))))

  (local (defthm <=-minus-1-rewrite
           (implies (and (natp x) (natp y))
                    (equal (< (+ -1 y) x)
                           (not (< x y))))))

  (defthm aignet-lit-fix-id-val-linear
    (<= (lit-id (aignet-lit-fix lit aignet))
        (node-count aignet))
    :rule-classes :linear)

  (defthm aignet-litp-of-aignet-lit-fix
    (aignet-litp (aignet-lit-fix x aignet) aignet)
    :hints(("Goal"
            :induct (aignet-lit-fix x aignet))
           (and stable-under-simplificationp
                '(:in-theory (enable aignet-litp
                                     lookup-id-in-bounds)))))

  (defthm aignet-litp-of-aignet-lit-fix-extension
    (implies (aignet-extension-p new orig)
             (aignet-litp (aignet-lit-fix x orig) new)))

  (defthm aignet-lit-fix-when-aignet-litp
    (implies (aignet-litp lit aignet)
             (equal (aignet-lit-fix lit aignet)
                    (lit-fix lit)))
    :hints(("Goal" :in-theory (enable aignet-litp
                                      lookup-id-in-bounds
                                      aignet::equal-of-mk-lit))))

  (defcong lit-equiv equal (aignet-lit-fix lit aignet) 1)
  (local (defun-nx aignet-lit-fix-ind2a (x aignet aignet2)
           (declare (xargs :measure (node-count aignet)
                           :hints(("Goal" :in-theory (enable lookup-id-in-bounds)))))
           (b* ((id (lit-id x))
                (look (lookup-id id aignet))
                ((unless look)
                 (mk-lit 0 (lit-neg x)))
                ((cons node rest) look)
                (rest2 (cdr (lookup-id id aignet2)))
                ((when (eql (node->type node) (out-type)))
                 (aignet-lit-fix-ind2a (co-node->fanin node) rest rest2)))
             aignet2)))
  (defcong list-equiv equal (aignet-lit-fix lit aignet) 2
    :hints (("goal" :induct (aignet-lit-fix-ind2a lit aignet acl2::aignet-equiv)
             :expand ((:free (aignet)
                       (aignet-lit-fix lit aignet)))))))

(define aignet-id-fix ((x natp) aignet)
  :returns (id natp :rule-classes :type-prescription)
  (if (<= (lnfix x) (node-count aignet))
      (lnfix x)
    0)
  ///
  (defthm aignet-idp-of-aignet-id-fix
    (aignet-idp (aignet-id-fix x aignet) aignet)
    :hints(("Goal" :in-theory (enable aignet-idp))))
  (defthm aignet-id-fix-id-val-linear
    (<= (aignet-id-fix id aignet)
        (node-count aignet))
    :rule-classes :linear)
  (defthm aignet-id-fix-when-aignet-idp
    (implies (aignet-idp id aignet)
             (equal (aignet-id-fix id aignet)
                    (nfix id)))
    :hints(("Goal" :in-theory (enable aignet-idp)))))



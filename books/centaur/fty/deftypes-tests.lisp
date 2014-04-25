; FTY type support library
; Copyright (C) 2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Sol Swords <sswords@centtech.com>

(in-package "FTY")

(include-book "deftypes")

(include-book "std/lists/acl2-count" :dir :system)

(logic)

(in-theory (disable acl2-count))

(defsection varp
  (define varp (x)
    (and (symbolp x)
         (not (eq x nil))))

  (local (in-theory (enable varp)))

  (define var-fix (x)
    :returns (xx varp)
    (if (and (symbolp x) x) x 'x)
    ///
    (defthm varp-of-var-fix
      (implies (varp x)
               (equal (var-fix x) x)))

    (deffixtype var :pred varp :fix var-fix :equiv var-equiv :define t)))

(local (defthm len-equal-val
         (implies (syntaxp (quotep val))
                  (equal (equal (len x) val)
                         (if (zp val)
                             (and (equal 0 val)
                                  (atom x))
                           (and (consp x)
                                (equal (len (cdr x)) (1- val))))))))
(local (in-theory (disable len)))

(defflexsum var-tree
  :short "A tree of variables."
  (:leaf
   :cond (atom w)
   :fields ((val :acc-body w :type varp))
   :ctor-body val)
  (:triple
   :cond t
   :require (and (true-listp w) (eql (len w) 3))
   :fields ((left :acc-body (car w) :type var-tree)
            (mid :acc-body (cadr w) :type var-tree)
            (right :acc-body (caddr w) :type var-tree))
   :ctor-body (list left mid right))
  :xvar w)

(deflist varlist :elt-type varp :xvar q)


(defsection fnsym-p
  (define fnsym-p (x)
    (and (symbolp x)
         x (not (eq x 'quote)))
    ///
    (defthm not-quote-when-fnsym-p
      (implies (fnsym-p x)
               (not (equal x 'quote)))
      :rule-classes :forward-chaining)

    (defthm fnsym-compound-recognizer
      (implies (fnsym-p x)
               (and (symbolp x) x))
      :rule-classes :compound-recognizer))

  (local (in-theory (enable fnsym-p)))

  (define fnsym-fix (x)
    :returns (xx fnsym-p)
    (if (fnsym-p x) x 'some-fnsym)
    ///
    (defthm fnsym-p-of-fnsym-fix
      (implies (fnsym-p x)
               (equal (fnsym-fix x) X)))

    (deffixtype fnsym :pred fnsym-p :fix fnsym-fix :equiv fnsym-equiv :define t)))


(deftypes pterm
  :prepwork ((local (defthm len-equal-val
                      (implies (syntaxp (quotep val))
                               (equal (equal (len x) val)
                                      (if (zp val)
                                          (and (equal 0 val)
                                               (atom x))
                                        (and (consp x)
                                             (equal (len (cdr x)) (1- val))))))))
             (local (in-theory (disable len)))
             ;; (local (in-theory (enable var-fix varp fnsym-fix fnsym-p)))
             )
  (defflexsum pterm
    (:null
     :cond (not y)
     :ctor-body nil)
    (:var 
     :cond (atom y)
     :fields ((name :acc-body y :type varp))
     :ctor-body name)
    (:quote
     :cond (eq (car y) 'quote)
     :require (and (consp (cdr y))
                   (not (cddr y)))
     :fields ((val :acc-body (cadr y)))
     :ctor-body (list 'quote val))
    (:call
     :fields ((fn :acc-body (car y) :type pfunc-p)
              (args :acc-body (cdr y) :type ptermlist-p))
     :ctor-body (cons fn args))
    :xvar y)
  (defflexsum pfunc
    ;; :kind nil
    (:sym
     :cond (atom z)
     :fields ((fnname :acc-body z :type fnsym-p))
     :ctor-body fnname)
    (:lambda
     :require (and (eq (car z) 'lambda)
                   (true-listp z)
                   (eql (len z) 3))
     :fields ((formals :acc-body (cadr z) :type varlist-p)
              (body :acc-body (caddr z) :type pterm-p))
     :ctor-body (list 'lambda formals body))
    :xvar z)

  (deflist ptermlist :elt-type pterm-p :xvar acl2-asg::x))

(deflist fnsymlist :elt-type fnsym)

(deffixtype nat :fix nfix :pred natp :equiv nat-equiv :define t)

(with-output :off (prove event observation)
  :summary (acl2::form)
  :gag-mode t
  (defflexsum fnsym-tree
    :parents (var-tree)
    :short "A tree of function symbols."
    (:leaf
     :cond (atom w)
     :fields ((val :acc-body w :type fnsym))
     :ctor-body val)
    (:triple
     :cond t
     :require (and (true-listp w) (eql (len w) 4))
     :fields ((left :acc-body (car w) :type fnsym-tree)
              (mid :acc-body (cadr w) :type fnsym-tree)
              (right :acc-body (caddr w) :type fnsym-tree)
              (idx :acc-body (cadddr w) :type nat))
     :ctor-body (list left mid right idx))
    :xvar w))

  

;; testing no-count
(with-output :off (prove event observation)
  :summary (acl2::form)
  :gag-mode t
  (deftypes pterm1
    :prepwork ((local (defthm len-equal-val
                        (implies (syntaxp (quotep val))
                                 (equal (equal (len x) val)
                                        (if (zp val)
                                            (and (equal 0 val)
                                                 (atom x))
                                          (and (consp x)
                                               (equal (len (cdr x)) (1- val))))))))
               (local (in-theory (disable len)))
               ;; (local (in-theory (enable var-fix varp fnsym-fix fnsym-p)))
               )
    (defflexsum pterm1
      (:null
       :cond (not y)
       :ctor-body nil)
      (:var 
       :cond (atom y)
       :fields ((name :acc-body y :type varp))
       :ctor-body name)
      (:quote
       :cond (eq (car y) 'quote)
       :require (and (consp (cdr y))
                     (not (cddr y)))
       :fields ((val :acc-body (cadr y)))
       :ctor-body (list 'quote val))
      (:call
       :fields ((fn :acc-body (car y) :type pfunc1-p)
                (args :acc-body (cdr y) :type pterm1list-p))
       :ctor-body (cons fn args))
      :xvar y)
    (defflexsum pfunc1
      ;; :kind nil
      (:sym
       :cond (atom z)
       :fields ((fnname :acc-body z :type fnsym-p))
       :ctor-body fnname)
      (:lambda
       :require (and (eq (car z) 'lambda)
                     (true-listp z)
                     (eql (len z) 3))
       :fields ((formals :acc-body (cadr z) :type varlist-p)
                (body :acc-body (caddr z) :type pterm1-p))
       :ctor-body (list 'lambda formals body))
      :xvar z
      :count nil)

    (deflist pterm1list :elt-type pterm1-p :xvar acl2-asg::x)))

(with-output :off (prove event observation)
  :summary (acl2::form)
  :gag-mode t
  (deftypes pterm2
    :prepwork ((local (defthm len-equal-val
                        (implies (syntaxp (quotep val))
                                 (equal (equal (len x) val)
                                        (if (zp val)
                                            (and (equal 0 val)
                                                 (atom x))
                                          (and (consp x)
                                               (equal (len (cdr x)) (1- val))))))))
               (local (in-theory (disable len)))
               ;; (local (in-theory (enable var-fix varp fnsym-fix fnsym-p)))
               )
    (defflexsum pterm2
      (:null
       :cond (not y)
       :ctor-body nil)
      (:var 
       :cond (atom y)
       :fields ((name :acc-body y :type varp))
       :ctor-body name)
      (:quote
       :cond (eq (car y) 'quote)
       :require (and (consp (cdr y))
                     (not (cddr y)))
       :fields ((val :acc-body (cadr y)))
       :ctor-body (list 'quote val))
      (:call
       :fields ((fn :acc-body (car y) :type pfunc2-p)
                (args :acc-body (cdr y) :type pterm2list-p))
       :ctor-body (cons fn args))
      :xvar y)
    (defflexsum pfunc2
      ;; :kind nil
      (:sym
       :cond (atom z)
       :fields ((fnname :acc-body z :type fnsym-p))
       :ctor-body fnname)
      (:lambda
       :require (and (eq (car z) 'lambda)
                     (true-listp z)
                     (eql (len z) 3))
       :fields ((formals :acc-body (cadr z) :type varlist-p)
                (body :acc-body (caddr z) :type pterm2-p))
       :ctor-body (list 'lambda formals body))
      :xvar z)

    (deflist pterm2list :elt-type pterm2-p :xvar acl2-asg::x :count nil)))


;; non-recursive SOP
(defflexsum silly
  (:num :cond (integerp x)
   :fields ((val :type natp :acc-body x))
   :ctor-body val)
  (:pair
   :require (consp x)
   :fields ((fn :type fnsym :acc-body (car x))
            (var :type fnsym :acc-body (cdr x)))
   :ctor-body (cons fn var)))

(define symbol-fix (x)
  :returns (xx symbolp)
  (if (symbolp x) x 'foo)
  ///
  (defthm symbol-fix-when-symbolp
    (implies (symbolp x)
             (equal (symbol-fix x) x))))

(deffixtype symbol :pred symbolp :fix symbol-fix :equiv symbol-equiv :define t)

(deffixtype integer :pred integerp :fix ifix :equiv int-equiv :define t)

(deftypes intterm
  (defflexsum intterm
    (:num :cond (atom x)
     :fields ((val :type integerp :acc-body x))
     :ctor-body val)
    (:call
     :fields ((fn :type symbol :acc-body (car x))
              (args :type inttermlist :acc-body (cdr x)))
     :ctor-body (cons fn args)))
  (deflist inttermlist
    :elt-type intterm))

(defflexsum arithterm
  (:num :cond (atom x)
   :fields ((val :type integerp :acc-body x))
   :ctor-body val)
  (:plus
   :cond (eq (car x) '+)
   :require (and (true-listp x) (eql (len x) 3))
   :fields ((left :type arithterm :acc-body (cadr x))
            (right :type arithterm :acc-body (caddr x)))
   :ctor-body (list '+ left right))
  (:minus
   :require (and (eq (car x) '-)
                 (true-listp x)
                 (eql (len x) 2))
   :fields ((arg :type arithterm :acc-body (cadr x)))
   :ctor-body (list '- arg)))

(define arithterm-eval ((x arithterm-p))
  :returns (xval integerp :rule-classes :type-prescription)
  :measure (arithterm-count x)
  (case (arithterm-kind x)
    (:num (arithterm-num->val x))
    (:plus (+ (arithterm-eval (arithterm-plus->left x))
              (arithterm-eval (arithterm-plus->right x))))
    (t (- (arithterm-eval (arithterm-minus->arg x)))))
  ///
  (deffixequiv arithterm-eval))

(define arithterm-double ((x arithterm-p))
  :verify-guards nil ;; requires return type theorem first
  :returns (xx arithterm-p)
  :measure (arithterm-count x)
  (arithterm-case x
    :num (arithterm-num (* 2 x.val))
    :plus (arithterm-plus (arithterm-double x.left)
                          (arithterm-double x.right))
    :minus (arithterm-minus (arithterm-double x.arg)))
  ///
  (verify-guards arithterm-double)

  (deffixequiv arithterm-double)

  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (defthm arithterm-double-correct
    (equal (arithterm-eval (arithterm-double x))
           (* 2 (arithterm-eval x)))
    :hints(("Goal" :in-theory (enable arithterm-eval)))))
   
   

(deffixtype nat :pred natp :fix nfix :equiv nat-equiv :define t)
(deffixtype int :pred integerp :fix ifix :equiv int-equiv :define t)

;; This has only one product type, and it basically acts like a product
(defflexsum foo
  :kind nil
  (:foo
   :require (and (true-listp x)
                 (eql (len x) 3))
   :fields ((nat :type nat :acc-body (car x))
            (int :type int :acc-body (cadr x))
            (var :type var :acc-body (caddr x)))
   :type-name foo
   :ctor-body (list nat int var)))

(include-book "std/misc/two-nats-measure" :dir :system)

(deftypes faba
  ;; this is a product type
  (defflexsum fa
    :kind nil
    :measure (two-nats-measure (acl2-count x) 1)
    (:fa
     :require (and (true-listp x)
                   (eql (len x) 3))
     :fields ((nat :type nat :acc-body (car x))
              (int :type int :acc-body (cadr x))
              (ba :type ba :acc-body (caddr x)))
     :type-name fa
     :ctor-body (list nat int ba)))

  (deflist ba :elt-type fa :measure (two-nats-measure (acl2-count x) 0)))
     
(deftagsum xtree
  (:leaf ((val natp)))
  (:pair ((left xtree-p) (right xtree-p)))
  (:unary ((fn symbol) (arg xtree)))
  :layout :alist)

(deftagsum ytree
  (:leaf ((val natp)))
  (:pair ((left ytree-p) (right ytree-p)))
  (:unary ((fn symbol) (arg ytree)))
  :layout :tree)

(deftagsum ztree
  (:leaf ((val natp)))
  (:pair ((left ztree-p) (right ztree-p)))
  (:unary ((fn symbol) (arg ztree)))
  :layout :list)


(deftypes atree
  (deftagsum atree
    (:leaf ((val natp)))
    (:pair ((left atree-p) (right atree-p)))
    (:unary ((fn symbol) (arg atreelist-p))))

  (deflist atreelist :elt-type atree))

(deftypes btree
  (deftagsum btree
    (:pair ((left btree-p) (right btree-p)))
    (:unary ((fn symbol) (arg btreelist-p)))
    :base-case-override :unary
    :measure (two-nats-measure (acl2-count x) 1))
  (deflist btreelist-p :elt-type btree
    :measure (two-nats-measure (acl2-count x) 0)))


(deftagsum ctree
  (:ctree ((fn symbol) (arg nat)))
  :count nil)

(defprod 3ple
  ((first nat)
   (second int)
   (third symbol))
  :layout :tree)

(defprod 3ple-b
  ((first nat)
   (second int)
   (third symbol))
  :layout :list)

(defprod 3ple-c
  ((first nat)
   (second int)
   (third symbol))
  :layout :alist)

(defprod 3ple-d
  ((first nat)
   (second int)
   (third symbol))
  :tag :d
  :layout :alist)

(defprod 3ple-e
  ((first nat)
   (second int)
   (third symbol))
  :tag :e
  :layout :list)

(defprod 3ple-f
  ((first nat)
   (second int)
   (third symbol))
  :tag :f
  :layout :tree)


(deftypes 4uple
  (defprod 4uple
    ((first nat)
     (second int)
     (third symbol)
     (fourth 4uplelist))
    :measure (two-nats-measure (acl2-count x) 1))
  (deflist 4uplelist :elt-type 4uple :measure
    (two-nats-measure (acl2-count x) 0)))


(include-book "std/util/deflist" :dir :system)

(std::deflist 4uplelist-p (x)
  (4uple-p x)
  :elementp-of-nil nil
  :already-definedp t)


(deflist 4uplelist2 :elt-type 4uple :true-listp t)

(std::deflist 4uplelist2-p (x)
  (4uple-p x)
  :true-listp t
  :elementp-of-nil nil
  :already-definedp t)

(include-book "std/util/defprojection" :dir :system)

(std::defprojection 4uplelist2-fix (x)
  (4uple-fix x)
  :guard (4uplelist-p x)
  :already-definedp t)


;; make sure b* binders are working
(define 3ple->list ((x 3ple-f-p))
  (b* (((3ple-f y) x))
    (list y.first y.second)))




(defflexsum foo2
  :kind nil
  (:foo
   :require (and (true-listp x)
                 (eql (len x) 3))
   :fields ((nat :type nat :acc-body (car x) :acc-name foo2n)
            (int :type int :acc-body (cadr x) :acc-name foo2i)
            (var :type var :acc-body (caddr x) :acc-name foo2v))
   :type-name foo2
   :ctor-body (list nat int var)))

(define foo2->list ((f foo2-p))
  (b* (((foo2 x) f))
    (list x.nat x.int x.var)))



(defalist sym-nat-alist :key-type symbol :val-type nat)
(defalist sym-nat-alist2 :key-type symbol :val-type nat :true-listp t)


(deftypes recalist
  (deftagsum alterm
    (:v ((val natp)))
    (:t ((fn symbolp)
         (al recalist)))
    :layout :list)
  (defalist recalist :key-type int :val-type alterm))


(include-book "std/util/defalist" :dir :system)

(std::defalist recalist-p (x) :key (integerp x) :val (alterm-p x) :already-definedp t)




(deftypes recalist2
  (deftagsum alterm2
    (:v ((val natp)))
    (:t ((fn symbolp)
         (al recalist2)))
    :layout :list)
  (defalist recalist2 :key-type alterm2 :val-type int :true-listp t))

(std::defalist recalist2-p (x) :key (alterm2-p x) :val (integerp x)
  :true-listp t :already-definedp t)



(deftagsum arithtm
  (:num ((val integerp :rule-classes :type-prescription)))
  (:plus ((left arithtm-p)
          (right arithtm-p)))
  (:minus ((arg arithtm-p))))

(define arithtm-eval ((x arithtm-p))
  :returns (val integerp :rule-classes :type-prescription)
  :measure (arithtm-count x)
  :verify-guards nil
  (case (arithtm-kind x)
    (:num (arithtm-num->val x))
    (:plus (+ (arithtm-eval (arithtm-plus->left x))
              (arithtm-eval (arithtm-plus->right x))))
    (:minus (- (arithtm-eval (arithtm-minus->arg x)))))
  ///
  (verify-guards arithtm-eval))


(define arithtm-double ((x arithtm-p))
  :returns (xx arithtm-p)
  :measure (arithtm-count x)
  :verify-guards nil
  (arithtm-case x
    :num (arithtm-num (* 2 x.val))
    :plus (arithtm-plus (arithtm-double x.left)
                        (arithtm-double x.right))
    :minus (arithtm-minus (arithtm-double x.arg)))
  ;; (case (arithtm-kind x)
  ;;   (:num (arithtm-num (* 2 (arithtm-num->val x))))
  ;;   (:plus (arithtm-plus (arithtm-double (arithtm-plus->left x))
  ;;                          (arithtm-double (arithtm-plus->right x))))
  ;;   (:minus (arithtm-minus (arithtm-double (arithtm-minus->arg x)))))
  ///
  (verify-guards arithtm-double)

  (local (include-book "arithmetic/top-with-meta" :dir :system))

  (defthm arithtm-eval-of-double
    (equal (arithtm-eval (arithtm-double x))
           (* 2 (arithtm-eval x)))
    :hints(("Goal" :in-theory (enable arithtm-eval)))))

(deflist arithtmlist :elt-type arithtm)

(define arithtmlist-double ((x arithtmlist-p))
  :returns (xx arithtmlist-p)
  (if (atom x)
      nil
    (cons (arithtm-case (x (car x))
            :num (arithtm-num (* 2 x.val))
            :plus (arithtm-plus (arithtm-double x.left)
                                (arithtm-double x.right))
            :minus (arithtm-minus (arithtm-double x.arg)))
          (arithtmlist-double (cdr x)))))

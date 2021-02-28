; FTY type support library
; Copyright (C) 2014 Centaur Technology
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

(in-package "FTY")
(include-book "../deftypes")
(include-book "../basetypes")
(include-book "std/lists/acl2-count" :dir :system)
(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/util/tests/utils" :dir :system)

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
    (defthm var-fix-when-varp
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

(defsection list-with-hint
  ;; bozo consider incorporating into std/util/cons and using for remaking
  ;; :list style structures

  (defun list-with-hint-macro (orig lst)
    (if (consp lst)
        `(cons-with-hint ,(car lst)
                         ,(list-with-hint-macro `(cdr ,orig) (cdr lst))
                         ,orig)
      nil))

  (defmacro list-with-hint (orig &rest args)
    (list-with-hint-macro orig args))

  (local (defthm list-with-hint-tests
           (and (equal (list-with-hint orig) nil)
                (equal (list-with-hint orig a) (list a))
                (equal (list-with-hint orig a b) (list a b))
                (equal (list-with-hint orig a b c) (list a b c)))
           :rule-classes nil)))

(defflexsum var-tree
  :short "A tree of variables."
  (:leaf
   :cond (atom w)
   :fields ((val :acc-body w :type varp))
   :ctor-body val)
  (:triple
   :cond t
   :shape (and (true-listp w) (eql (len w) 3))
   :fields ((left :acc-body (car w) :type var-tree)
            (mid :acc-body (cadr w) :type var-tree)
            (right :acc-body (caddr w) :type var-tree))
   :ctor-body (list left mid right)
   :remake-body (list-with-hint w left mid right))
  :xvar w)

(std::assert-logic-mode remake-var-tree-triple)
(std::assert-guard-verified remake-var-tree-triple)

(assert!
 (b* (((var-tree-triple orig)
       (make-var-tree-triple :left (make-var-tree-leaf :val 'myleft)
                             :right (make-var-tree-leaf :val 'myright)
                             :mid (make-var-tree-leaf :val 'mymid)))
      ((var-tree-triple new)
       (change-var-tree-triple orig :left (make-var-tree-leaf :val 'yourleft))))
   (and (equal orig.right new.right)
        (equal orig.mid new.mid)
        (equal orig.left (make-var-tree-leaf :val 'myleft))
        (equal new.left (make-var-tree-leaf :val 'yourleft)))))

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
    (defthm fnsym-fix-when-fnsym-p
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
     :shape (and (consp (cdr y))
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
     :shape (and (eq (car z) 'lambda)
                   (true-listp z)
                   (eql (len z) 3))
     :fields ((formals :acc-body (cadr z) :type varlist-p)
              (body :acc-body (caddr z) :type pterm-p))
     :ctor-body (list 'lambda formals body))
    :xvar z)

  (deflist ptermlist :elt-type pterm-p))

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
     :shape (and (true-listp w) (eql (len w) 4))
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
       :shape (and (consp (cdr y))
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
       :shape (and (eq (car z) 'lambda)
                     (true-listp z)
                     (eql (len z) 3))
       :fields ((formals :acc-body (cadr z) :type varlist-p)
                (body :acc-body (caddr z) :type pterm1-p))
       :ctor-body (list 'lambda formals body))
      :xvar z
      :count nil)

    (deflist pterm1list :elt-type pterm1-p)))

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
       :shape (and (consp (cdr y))
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
       :shape (and (eq (car z) 'lambda)
                     (true-listp z)
                     (eql (len z) 3))
       :fields ((formals :acc-body (cadr z) :type varlist-p)
                (body :acc-body (caddr z) :type pterm2-p))
       :ctor-body (list 'lambda formals body))
      :xvar z)

    (deflist pterm2list :elt-type pterm2-p :count nil)))


;; non-recursive SOP
(defflexsum silly
  (:num :cond (integerp x)
   :fields ((val :type natp :acc-body x))
   :ctor-body val)
  (:pair
   :shape (consp x)
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
   :shape (and (true-listp x) (eql (len x) 3))
   :fields ((left :type arithterm :acc-body (cadr x))
            (right :type arithterm :acc-body (caddr x)))
   :ctor-body (list '+ left right))
  (:minus
   :shape (and (eq (car x) '-)
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
    (:num (arithterm-num (* 2 x.val)))
    (:plus (arithterm-plus (arithterm-double x.left)
                           (arithterm-double x.right)))
    (:minus (arithterm-minus (arithterm-double x.arg))))
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
   :shape (and (true-listp x)
                 (eql (len x) 3))
   :fields ((nat :type nat :acc-body (car x))
            (int :type int :acc-body (cadr x))
            (var :type var :acc-body (caddr x)))
   :type-name foo
   :ctor-body (list nat int var)))

(deftypes faba
  ;; this is a product type
  (defflexsum fa
    :kind nil
    :measure (two-nats-measure (acl2-count x) 1)
    (:fa
     :shape (and (true-listp x)
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

(std::assert-guard-verified remake-ytree-leaf)
(std::assert-guard-verified remake-ytree-pair)

#||
;; Making sure the change macro is invoking the remake function.
;; BOZO how can we write a test that will fail if this doesn't happen?

(trace$ remake-ytree-pair)

(defun my-test (x)
  (declare (xargs :guard (natp x)))
  (b* ((ytree (make-ytree-pair :left (make-ytree-leaf :val 5)
                               :right (make-ytree-leaf :val 6))))
    (change-ytree-pair ytree :left (make-ytree-leaf :val x))))

(my-test 5) ;; should show trace output

(untrace$)

(define memtest-ytree ((n natp) (left ytree-p) (ytree ytree-p))
  :guard (ytree-case ytree :pair)
  (if (zp n)
      ytree
    (memtest-ytree (- n 1)
                   left
                   (change-ytree-pair ytree :left left))))

(define memtest-xtree ((n natp) (left xtree-p) (xtree xtree-p))
  :guard (xtree-case xtree :pair)
  (if (zp n)
      xtree
    (memtest-xtree (- n 1)
                   left
                   (change-xtree-pair xtree :left left))))

(time$
 ;; On CCL this allocates 80 KB.
 (b* ((left (make-xtree-leaf :val 5))
      (right (make-xtree-leaf :val 6))
      (base (make-xtree-pair :left left :right right)))
   (memtest-xtree 1000 left base)))

(time$
 ;; This should allocate (almost) nothing.  496 bytes as of this writing in CCL.
 (b* ((left (make-ytree-leaf :val 5))
      (right (make-ytree-leaf :val 6))
      (base (make-ytree-pair :left left :right right)))
   (memtest-ytree 1000 left base)))

||#

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
  :extra-binder-names (first-two (list . 3ple-to-list))
  :layout :tree)

(std::assert-guard-verified remake-3ple)


(define 3ple->first-two ((x 3ple-p))
  (b* (((3ple x)))
    (cons x.first x.second)))

(define 3ple-to-list ((x 3ple-p))
  (b* (((3ple x)))
    (list x.first x.second x.third x.first-two)))

(define 3ple-test ((x 3ple-p))
  (b* (((3ple x)))
    (list x.list x.first-two x.third))
  ///
  (assert! (equal (3ple-test (make-3ple :first 1 :second 2 :third 'three))
                  '((1 2 three (1 . 2)) (1 . 2) three))))

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
    :tag :four
    :measure (two-nats-measure (acl2-count x) 1))
  (deflist 4uplelist :elt-type 4uple :measure
    (two-nats-measure (acl2-count x) 0)
    :elementp-of-nil nil))






(include-book "std/util/deflist" :dir :system)

(std::deflist 4uplelist-p (x)
  (4uple-p x)
  :elementp-of-nil nil
  :already-definedp t)


(deflist 4uplelist2 :elt-type 4uple :true-listp t :elementp-of-nil nil)

(std::deflist 4uplelist2-p (x)
  (4uple-p x)
  :true-listp t
  :elementp-of-nil nil
  :already-definedp t)

;; (include-book "std/util/defprojection" :dir :system)

;; (std::defprojection 4uplelist2-fix (x)
;;   (4uple-fix x)
;;   :guard (4uplelist-p x)
;;   :already-definedp t)


;; make sure b* binders are working
(define 3ple->list ((x 3ple-f-p))
  (b* (((3ple-f y) x))
    (list y.first y.second)))




(defflexsum foo2
  :kind nil
  (:foo
   :shape (and (true-listp x)
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

(defmap sym-nat-alist3 :key-type symbol :val-type nat)
(defalist sym-nat-alist4 :key-type symbol :val-type nat :true-listp t
  :strategy :drop-keys)


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

(deftypes recalist3
  (deftagsum alterm3
    (:v ((val natp)))
    (:t ((fn symbolp)
         (al recalist3)))
    :layout :list)
  (defmap recalist3 :key-type alterm3 :val-type alterm3))



(deftagsum arithtm
  (:num ((val integerp :rule-classes :type-prescription)))
  (:plus ((left arithtm-p)
          (right arithtm-p))
   :extra-binder-names ((val . arithtm-eval)))
  (:minus ((arg arithtm-p))
   :extra-binder-names ((val . arithtm-eval))))

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

(define arithtm-info ((x arithtm-p))
  (arithtm-case x
    :plus (list :plus x.val)
    :minus (list :minus x.val)
    :num (list :num x.val))
  ///
  (make-event
   (and (equal (arithtm-info (make-arithtm-plus :left (make-arithtm-num :val 1)
                                                :right (make-arithtm-num :val 2)))
               '(:plus 3))
        '(value-triple :ok))))

(deflist arithtmlist :elt-type arithtm)

(define arithtmlist-double ((x arithtmlist-p))
  :returns (xx arithtmlist-p)
  (if (atom x)
      nil
    (cons (b* ((x (car x)))
            (arithtm-case x
              :num (arithtm-num (* 2 x.val))
              :plus (arithtm-plus (arithtm-double x.left)
                                  (arithtm-double x.right))
              :minus (arithtm-minus (arithtm-double x.arg))))
          (arithtmlist-double (cdr x)))))


(define arithtm-op-p ((x arithtm-p))
  (arithtm-case x
    :num nil
    :otherwise t))

(define arithtm-op-p2 ((x arithtm-p))
  (arithtm-case x
    (:num nil)
    (& t)))

(define arithtm-op-p3 ((x arithtm-p))
  (arithtm-case x
    (:num nil)
    (:plus t)
    (& t)))


(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (in-theory (disable unsigned-byte-p)))

(defprod sizednum
  ((size natp)
   (bits natp
         :reqfix (acl2::loghead size bits)))
  :require (unsigned-byte-p size bits))

(defprod sizednum2
  ((size natp)
   (bits :reqfix (acl2::loghead size bits)))
  :require (unsigned-byte-p size bits))




(include-book "std/lists/take" :dir :system)


(deftypes pterm3
  :prepwork ((local (defthm len-equal-val
                      (implies (syntaxp (quotep val))
                               (equal (equal (len x) val)
                                      (if (zp val)
                                          (and (equal 0 val)
                                               (atom x))
                                        (and (consp x)
                                             (equal (len (cdr x)) (1- val))))))))
             ;; (local (defthm equal-of-cons
             ;;          (equal (equal (cons a b) c)
             ;;                 (and (consp c)
             ;;                      (equal a (car c))
             ;;                      (equal b (cdr c))))))
             (local (in-theory (disable len)))
             ;; (local (in-theory (enable var-fix varp fnsym-fix fnsym-p)))
             )
  (defflexsum pterm3
    (:null
     :cond (not y)
     :ctor-body nil)
    (:var
     :cond (atom y)
     :fields ((name :acc-body y :type varp))
     :ctor-body name)
    (:quote
     :cond (eq (car y) 'quote)
     :shape (and (consp (cdr y))
                   (not (cddr y)))
     :fields ((val :acc-body (cadr y)))
     :ctor-body (list 'quote val))
    (:fncall
     :cond (atom (car y))
     :fields ((fn :acc-body (car y) :type fnsym-p)
              (args :acc-body (cdr y) :type pterm3list-p))
     :ctor-body (cons fn args))
    (:lambdacall
     :shape (and (eq (caar y) 'lambda)
                 (true-listp (car y))
                 (eql (len (car y)) 3))
     :fields ((formals :acc-body (cadar y) :type varlist-p)
              (body :acc-body (caddar y) :type pterm3-p)
              (args :acc-body (cdr y) :type pterm3list-p
                    :reqfix (take (len formals) args)))
     :require (eql (len formals) (len args))
     :ctor-body (cons (list 'lambda formals body) args))


    :post-pred-events (;; (defthm pterm3list-p-of-take
                       ;;   (implies (pterm3list-p x)
                       ;;            (pterm3list-p (take n x))))
                       ;; (defthm pterm3list-p-implies-true-listp
                       ;;   (implies (pterm3list-p x)
                       ;;            (true-listp x))
                       ;;   :rule-classes :forward-chaining)
                       )

    :xvar y)
  ;; (defflexsum pfunc
  ;;   ;; :kind nil
  ;;   (:sym
  ;;    :cond (atom z)
  ;;    :fields ((fnname :acc-body z :type fnsym-p))
  ;;    :ctor-body fnname)
  ;;   (:lambda
  ;;    :shape (and (eq (car z) 'lambda)
  ;;                  (true-listp z)
  ;;                  (eql (len z) 3))
  ;;    :fields ((formals :acc-body (cadr z) :type varlist-p)
  ;;             (body :acc-body (caddr z) :type pterm-p))
  ;;    :ctor-body (list 'lambda formals body))
  ;;   :xvar z)

  (deflist pterm3list :elt-type pterm3-p
    :elementp-of-nil t
    :true-listp t))


(define pterm4-take ((n natp) x)
  :guard (eql (len x) n)
  (mbe :logic (let ((n (nfix n)))
                (if (equal (len x) n)
                    x
                  (if (< (len x) n)
                      (append x (replicate (- n (len x)) ''nil))
                    (take n x))))
       :exec x)
  ///
  (defthm len-of-pterm4-take
    (equal (len (pterm4-take n x))
           (nfix n)))
  (defthm pterm4-take-when-len
    (implies (equal (len x) (nfix n))
             (equal (pterm4-take n x) x))))



(deftypes pterm4
  :prepwork ((local (defthm len-equal-val
                      (implies (syntaxp (quotep val))
                               (equal (equal (len x) val)
                                      (if (zp val)
                                          (and (equal 0 val)
                                               (atom x))
                                        (and (consp x)
                                             (equal (len (cdr x)) (1- val))))))))
             ;; (local (defthm equal-of-cons
             ;;          (equal (equal (cons a b) c)
             ;;                 (and (consp c)
             ;;                      (equal a (car c))
             ;;                      (equal b (cdr c))))))
             (local (in-theory (disable len)))
             ;; (local (in-theory (enable var-fix varp fnsym-fix fnsym-p)))
             )
  (defflexsum pterm4
    (:var
     :cond (atom y)
     :fields ((name :acc-body y :type varp))
     :ctor-body name)
    (:quote
     :cond (eq (car y) 'quote)
     :shape (and (consp (cdr y))
                 (not (cddr y)))
     :fields ((val :acc-body (cadr y)))
     :ctor-body (list 'quote val))
    (:fncall
     :cond (atom (car y))
     :fields ((fn :acc-body (car y) :type fnsym-p)
              (args :acc-body (cdr y) :type pterm4list-p))
     :ctor-body (cons fn args))
    (:lambdacall
     :shape (and (eq (caar y) 'lambda)
                 (true-listp (car y))
                 (eql (len (car y)) 4))
     :fields ((formals :acc-body (cadar y) :type varlist-p)
              (body :acc-body (caddar y) :type pterm4-p)
              (atts :acc-body (car (cdddar y)) :type pterm4-atts)
              (args :acc-body (cdr y) :type pterm4list-p
                    :reqfix (pterm4-take (len formals) args)))
     :require (eql (len formals) (len args))
     :ctor-body (cons (list 'lambda formals body atts) args))

    :xvar y
    :measure (two-nats-measure (acl2-count y) 1))

  (defflexsum maybe-pterm4
    :kind nil
    (:null :cond (not x)
     :ctor-body nil)
    (:term :cond t
     :fields ((val :acc-body x :type pterm4))
     :ctor-body val)
    :measure (two-nats-measure (acl2-count x) 3))

  (defalist pterm4-atts :key-type stringp :val-type maybe-pterm4
    :measure (two-nats-measure (acl2-count x) 0))
  ;; (defflexsum pfunc
  ;;   ;; :kind nil
  ;;   (:sym
  ;;    :cond (atom z)
  ;;    :fields ((fnname :acc-body z :type fnsym-p))
  ;;    :ctor-body fnname)
  ;;   (:lambda
  ;;    :shape (and (eq (car z) 'lambda)
  ;;                  (true-listp z)
  ;;                  (eql (len z) 3))
  ;;    :fields ((formals :acc-body (cadr z) :type varlist-p)
  ;;             (body :acc-body (caddr z) :type pterm-p))
  ;;    :ctor-body (list 'lambda formals body))
  ;;   :xvar z)

  (deflist pterm4list :elt-type pterm4-p
    :true-listp t
    :elementp-of-nil nil
    :measure (two-nats-measure (acl2-count x) 0) )



  :post-pred-events (;; (defthm pterm4list-p-of-append
                     ;;   (implies (and (pterm4list-p x)
                     ;;                 (pterm4list-p y))
                     ;;            (pterm4list-p (append x y)))
                     ;;   :hints(("Goal" :in-theory (enable pterm4list-p))))
                     ;; (defthm pterm4list-p-of-take
                     ;;   (implies (and (pterm4list-p x)
                     ;;                 (< (nfix n) (len x)))
                     ;;            (pterm4list-p (take n x)))
                     ;;   :hints(("Goal" :in-theory (enable pterm4list-p len))))
                     ;; (defthm pterm4list-p-of-replicate
                     ;;   (implies (pterm4-p x)
                     ;;            (pterm4list-p (replicate n x)))
                     ;;   :hints(("Goal" :in-theory (enable pterm4list-p
                     ;;                                     replicate))))
                     (defthm pterm4list-p-of-pterm4-take
                       (implies (pterm4list-p x)
                                (pterm4list-p (pterm4-take n x)))
                       :hints(("Goal" :in-theory (enable pterm4-take))))
                     ;; (defthm pterm4list-p-implies-true-listp
                     ;;   (implies (pterm4list-p x)
                     ;;            (true-listp x))
                     ;;   :rule-classes :forward-chaining)
                     ))





(define pterm5-take ((n natp) x)
  :guard (eql (len x) n)
  (mbe :logic (let ((n (nfix n)))
                (if (equal (len x) n)
                    x
                  (if (< (len x) n)
                      (append x (replicate (- n (len x)) '(:quote . nil)))
                    (take n x))))
       :exec x)
  ///
  (defthm len-of-pterm5-take
    (equal (len (pterm5-take n x))
           (nfix n)))
  (defthm pterm5-take-when-len
    (implies (equal (len x) (nfix n))
             (equal (pterm5-take n x) x))))



(deftypes pterm5
  :prepwork ((local (defthm len-equal-val
                      (implies (syntaxp (quotep val))
                               (equal (equal (len x) val)
                                      (if (zp val)
                                          (and (equal 0 val)
                                               (atom x))
                                        (and (consp x)
                                             (equal (len (cdr x)) (1- val))))))))
             ;; (local (defthm equal-of-cons
             ;;          (equal (equal (cons a b) c)
             ;;                 (and (consp c)
             ;;                      (equal a (car c))
             ;;                      (equal b (cdr c))))))
             (local (in-theory (disable len)))
             ;; (local (in-theory (enable var-fix varp fnsym-fix fnsym-p)))
             )
  (deftagsum pterm5
    :layout :tree
    (:var  ((name varp)))
    (:quote (val))
    (:fncall ((fn fnsym)
              (args pterm4list)))
    (:lambdacall ((formals varlist)
                  (body pterm5)
                  (atts pterm5-atts)
                  (args pterm5list
                        :reqfix (pterm5-take (len formals) args)))
     :require (eql (len formals) (len args)))

    :xvar y
    :measure (two-nats-measure (acl2-count y) 1))

  (defflexsum maybe-pterm5
    :kind nil
    (:null :cond (not x)
     :ctor-body nil)
    (:term :cond t
     :fields ((val :acc-body x :type pterm5))
     :ctor-body val)
    :measure (two-nats-measure (acl2-count x) 3))

  (defmap pterm5-atts :key-type stringp :val-type maybe-pterm5
    :measure (two-nats-measure (acl2-count x) 0))
  ;; (defflexsum pfunc
  ;;   ;; :kind nil
  ;;   (:sym
  ;;    :cond (atom z)
  ;;    :fields ((fnname :acc-body z :type fnsym-p))
  ;;    :ctor-body fnname)
  ;;   (:lambda
  ;;    :shape (and (eq (car z) 'lambda)
  ;;                  (true-listp z)
  ;;                  (eql (len z) 3))
  ;;    :fields ((formals :acc-body (cadr z) :type varlist-p)
  ;;             (body :acc-body (caddr z) :type pterm-p))
  ;;    :ctor-body (list 'lambda formals body))
  ;;   :xvar z)

  (deflist pterm5list :elt-type pterm5-p
    :true-listp t
    :elementp-of-nil nil
    :measure (two-nats-measure (acl2-count x) 0) )



  :post-pred-events (
                     (defthm pterm5list-p-of-pterm5-take
                       (implies (pterm5list-p x)
                                (pterm5list-p (pterm5-take n x)))
                       :hints(("Goal" :in-theory (enable pterm5-take))))))

(define cons-fix ((x consp))
  :returns (xx consp :rule-classes :type-prescription)
  (mbe :logic (cons (car x) (cdr x))
       :exec x)
  ///
  (defthm cons-fix-when-consp
    (implies (consp x)
             (equal (cons-fix x) x)))

  (deffixtype cons :pred consp :fix cons-fix :equiv cons-equiv :define t :forward t))

(local (in-theory (disable double-containment
                           default-car default-cdr)))

(defprod flarn
  ((a natp)
   (b consp :rule-classes :type-prescription)
   (c cons)
   (d))
  :layout :tree)


(deftagsum jaredtree
  (:leaf
   :short "The leaf of a jared tree."
   :long "<p>Green in the autumn, orange in the summer.</p>"
   ((val natp "Kind of a like a @(see posp), but can also be <b>zero</b>!")))
  (:pair
   :short "Two jared trees glued together."
   :long "<p>Protip: use wood glue.</p>"
   ((left jaredtree-p    "The hand that makes an <i>L</i> shape.")
    (right jaredtree-p   "The other hand, it makes a backwards L shape.")))
  (:unary ((fn symbol    "Name of a function being called.")
           (arg jaredtree)))
  :layout :tree
  :parents (top)
  :short "A very goofy structure."
  :long "<p>Don't let your cat get stuck in one of these!</p>")


;; ;; ;; temporary

;; (include-book "xdoc/save" :dir :system)
;; ;; (include-book "std/strings/pretty" :dir :system)

;; (xdoc::save "./manual" :redef-okp t)

;; (local (include-book "xdoc/save" :dir :system))
;; (local (make-event
;;         (b* (((mv ? all-xdoc-topics state) (xdoc::all-xdoc-topics state))
;;              (redef-report (xdoc::redef-errors (set::mergesort all-xdoc-topics)))
;;              (- (or (not redef-report)
;;                     (cw "Redefined topics report: ~x0.~%" redef-report)))
;;              (- (or (not redef-report)
;;                     (er hard? 'save
;;                         "Some XDOC topics have multiple definitions.  The above ~
;;                        report may help you to fix these errors.  Or, you can ~
;;                        just call XDOC::SAVE with :REDEF-OKP T to bypass this ~
;;                        error (and use the most recent version of each topic.)"))))
;;           (value '(value-triple :invisible)))))

(deflist acl2::string-list :pred acl2::string-listp :elt-type string)

(deflist nat-list :pred acl2::nat-listp :elt-type natp)
(deflist integer-list :pred acl2::integer-listp :elt-type integerp)
(deflist symbol-list :pred acl2::symbol-listp :elt-type symbolp)
(deflist rational-list :pred acl2::rational-listp :elt-type rationalp)
(defalist symbol-alist :pred acl2::symbol-alistp :key-type symbolp)
(defmap symbol-alist2 :pred acl2::symbol-alistp :key-type symbolp)

(defun natlistp (x)
  (declare (xargs :guard t))
  (if (consp x)
      (and (natp (car x)) (natlistp (cdr x)))
    t))

(deflist natlist :pred natlistp :elt-type natp)

(defalist timer-alist :pred timer-alistp :key-type symbolp :val-type rational-listp)


(defoption maybe-jaredtree jaredtree)

(deftypes faz
  (deftagsum faz
    (:list ((q mfazlist)))
    (:base ((n natp :rule-classes :type-prescription)))
    :measure (two-nats-measure (acl2-count x) 0))
  (defoption maybe-faz faz
    :measure (two-nats-measure (acl2-count x) 1))
  (deflist mfazlist :elt-type maybe-faz
    :measure (two-nats-measure (acl2-count x) 0)))




(deftranssum anyple
  (3ple-d 3ple-e 3ple-f))

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


(deftranssum nested-transsum-1
  ;; 4uple is nested inside a deftypes (of the same name)
  (3ple-d 4uple))

(deftypes outer-name
  (defprod inner-name
    :measure (two-nats-measure (acl2-count x) 1)
    :tag :inner
    ((fn   integerp)
     (args inner-namelist)))
  (deflist inner-namelist
    :measure (two-nats-measure (acl2-count x) 0)
    :elt-type inner-name))

(deftypes outer-name2
  (deftagsum inner-name2
    :measure (two-nats-measure (acl2-count x) 1)
    (:inner ((fn   integerp)
             (args inner-name2list)))
    (:outer ((fn symbolp))))
  (deflist inner-name2list
    :measure (two-nats-measure (acl2-count x) 2)
    :elt-type inner-name2
    :non-emptyp t))

(deftypes outer-name3
  (deftagsum inner-name3
    :measure (two-nats-measure (acl2-count x) 1)
    (:inner ((fn   integerp)
             (args inner-name3list)))
    (:outer ((fn symbolp))))
  (deflist inner-name3list
    :measure (two-nats-measure (acl2-count x) 2)
    :elt-type inner-name3
    :non-emptyp t
    :true-listp t))


(deftranssum nested-transsum-2
  (3ple-d inner-name)
  ///
  (local (defthm crock
           (implies (or (3ple-d-p x)
                        (inner-name-p x))
                    (nested-transsum-2-p x)))))


;; BOZO This doesn't work because we'd need to somewhat rearchitect the parsing
;; of deftypes forms to accomodate analyzing the other types in the mutual-recursion to find
;; their possible tags so that they can be used in the transsum.
;; (deftypes argle
;;   (defprod argle
;;     ((aaa anyple2)
;;      (bbb anyple))
;;     :tag :argle)
;;   (deftranssum anyple2
;;     (3ple-d 3ple-e 3ple-f argle)))


(deftypes funnyterm
  (deftagsum funnyterm
    (:var ((name symbolp :rule-classes :type-prescription)))
    (:quote ((val)))
    (:call ((fn symbol)
            (args funnyterm-list)))
    (:let ((bindings funnyalist)
           (body funnyterm))))
  (deflist funnyterm-list :elt-type funnyterm)
  (defalist funnyalist :key-type symbol :val-type funnyterm :unique-keys t))


(deftypes funny2term
  (deftagsum funny2term
    (:var ((name symbolp :rule-classes :type-prescription)))
    (:quote ((val)))
    (:call ((fn symbol)
            (args funny2term-list)))
    (:let ((bindings funny2alist)
           (body funny2term))))
  (deflist funny2term-list :elt-type funny2term)
  (defmap funny2alist :key-type symbol :val-type funny2term :unique-keys t))

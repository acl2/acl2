; Centaur BED Library
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
; Original authors: Jared Davis <jared@centtech.com>

(in-package "BED")
(include-book "eval")
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (in-theory (enable arith-equiv-forwarding)))

(define bed-mk1
  :parents (bed)
  :short "Low-level functions for constructing BEDs.")

(local (xdoc::set-default-parents bed-mk1))

(define bed-match-var
  :short "Pattern match a variable ITE node."
  ((x "The BED to pattern match against."))
  :returns (mv (okp "Whether or not we matched a variable.")
               (var "On success, the variable we matched.")
               (left "On success, the true branch for this variable.")
               (right "On success, the false branch for this variable."))
  (if (and (consp x)
           (not (integerp (cdr x))))
      (mv t
          (car x)
          (car$ (cdr x))
          (cdr$ (cdr x)))
    (mv nil nil nil nil))
  ///
  (defthm bed-match-var-correct
    (b* (((mv okp var left right) (bed-match-var x)))
      (implies okp
               (equal (bed-eval x env)
                      (if (bed-env-lookup var env)
                          (bed-eval left env)
                        (bed-eval right env)))))))


(define mk-var-raw ((var  "Variable that controls the decision.")
                    (left     "True branch (a bed).")
                    (right    "False branch (a bed)."))
  :returns bed
  :short "Raw constructor for a variable ITE node."
  :inline t
  (hons var (hons left right))
  ///
  (defthm bed-eval-of-mk-var-raw
    (equal (bed-eval (mk-var-raw var left right) env)
           (if (bed-env-lookup var env)
               (bed-eval left env)
             (bed-eval right env)))
    :hints(("Goal" :in-theory (enable bed-eval)))))

(define mk-op-raw ((op bed-op-p "Operator being applied to these operands.")
                   (left  "First argument to the operator (a bed).")
                   (right "Second argument to the operator (a bed)."))
  :returns bed
  :short "Raw construct for an binary operator node."
  :inline t
  (hons (hons left right)
        (mbe :logic (bed-op-fix op) :exec op))
  ///
  (local (in-theory (enable bed-eval)))
  (defthm bed-eval-of-mk-op-raw
    (equal (bed-eval (mk-op-raw op left right) env)
           (bed-op-eval op
                        (bed-eval left env)
                        (bed-eval right env)))))

(define mk-const-prop
  ((op    bed-op-p "Operator being applied to these operands.")
   (left  atom     "First argument to the operator (a terminal bed).")
   (right atom     "Second argument to the operator (a terminal bed)."))
  :returns bed
  (if (mbt (and (atom left)
                (atom right)))
      (eql 1 (bed-op-eval op
                          (bool->bit left)
                          (bool->bit right)))
    (mk-op-raw op left right))
  ///
  (local (in-theory (enable bed-eval)))
  (defthm bed-eval-of-mk-const-prop
    (equal (bed-eval (mk-const-prop op left right) env)
           (bed-eval (mk-op-raw op left right) env))))


(define mk-not ((x "Node to negate (a bed)"))
  :returns bed
  :short "Construct a reduced BED for @('not(x)')."
  :long "<p>We do just a few straightforward reductions.</p>

<p>If we don't make a reduction, we use @('not2(t, x)') as our usual way of
writing @('not(x)').  This particular choice always keeps the arguments in
@(see bed-order), since @('t') is the smallest bed in this order.</p>"
  (b* (((when (atom x))
        (not x))
       ((cons a b) x)
       ((unless (integerp b))
        ;; Push the NOT through a variable, into its branches
        (mk-var-raw a
                    (mk-not (car$ b))
                    (mk-not (cdr$ b))))
       (op (bed-op-fix b))
       (left  (car$ a))
       (right (cdr$ a))
       ((when (eql op (bed-op-true)))  nil)
       ((when (eql op (bed-op-false))) t)
       ((when (eql op (bed-op-not1)))  left)
       ((when (eql op (bed-op-not2)))  right)
       ((when (eql op (bed-op-arg1)))  (mk-not left))
       ((when (eql op (bed-op-arg2)))  (mk-not right))
       ((when (eql op (bed-op-orc1)))  (mk-op-raw (bed-op-andc2) left right))
       ((when (eql op (bed-op-orc2)))  (mk-op-raw (bed-op-andc1) left right))
       ((when (eql op (bed-op-andc1))) (mk-op-raw (bed-op-orc2) left right))
       ((when (eql op (bed-op-andc2))) (mk-op-raw (bed-op-orc1) left right))
       ((when (eql op (bed-op-eqv)))   (mk-op-raw (bed-op-xor) left right))
       ((when (eql op (bed-op-xor)))   (mk-op-raw (bed-op-eqv) left right))
       ((when (eql op (bed-op-nand)))  (mk-op-raw (bed-op-and) left right))
       ((when (eql op (bed-op-and)))   (mk-op-raw (bed-op-nand) left right))
       ((when (eql op (bed-op-nor)))   (mk-op-raw (bed-op-ior) left right))
       ((when (eql op (bed-op-ior)))   (mk-op-raw (bed-op-nor) left right)))
    (mk-op-raw (bed-op-not2) t x))
  ///
  (local (in-theory (enable b-and b-not b-ior)))
  (defthm bed-eval-of-mk-not
    (equal (bed-eval (mk-not x) env)
           (b-not (bed-eval x env)))))

(define mk-op-true-x
  ((op    bed-op-p "The operator being applied.")
   (right          "Second argument to the operator (a bed)."))
  :returns bed
  :short "Construct a reduced BED for @('op(true, right)')."
  (b* ((op (bed-op-fix$ op))

       ((when (eql op (bed-op-true))) t) ;; true(true,b) == true
       ((when (eql op (bed-op-ior)))  t) ;; or(true,b) == true
       ((when (eql op (bed-op-orc2))) t) ;; orc2(true, b) == true
       ((when (eql op (bed-op-arg1))) t) ;; arg1(true, b) == true

       ((when (eql op (bed-op-orc1))) right) ;; orc1(true, b) == b
       ((when (eql op (bed-op-arg2))) right) ;; arg2(true, b) == b
       ((when (eql op (bed-op-eqv)))  right) ;; eqv(true, b) == b
       ((when (eql op (bed-op-and)))  right) ;; and(true, b) == b

       ((when (eql op (bed-op-nand)))  (mk-not right)) ;; nand(true, b) == not(b)
       ((when (eql op (bed-op-xor)))   (mk-not right)) ;; xor(true, b) == not(b)
       ((when (eql op (bed-op-not2)))  (mk-not right)) ;; not2(true, b) == not(b)
       ((when (eql op (bed-op-andc2))) (mk-not right)) ;; andc2(true, b) == not(b)

       ((when (eql op (bed-op-not1)))  nil)  ;; not1(true, b) == false
       ((when (eql op (bed-op-andc1))) nil)  ;; andc1(true, b) == false
       ((when (eql op (bed-op-nor)))   nil)  ;; nor(true, b) == false
       ((when (eql op (bed-op-false))) nil)) ;; false(true, b) == false

    ;; Some unknown operator, don't reduce
    (mk-op-raw op t right))
  ///
  (defthm bed-eval-of-mk-op-true-x
    (equal (bed-eval (mk-op-true-x op right) env)
           (bed-eval (mk-op-raw op t right) env))))

(define mk-op-false-x
  ((op    bed-op-p "The operator being applied.")
   (right          "Second argument to the operator (a bed)."))
  :returns bed
  :short "Construct a reduced BED for @('op(false, right)')."
  (b* ((op (bed-op-fix$ op))

       ((when (eql op (bed-op-true))) t)               ;; true(false,b) == true
       ((when (eql op (bed-op-ior)))  right)           ;; or(false,b) == b
       ((when (eql op (bed-op-orc2))) (mk-not right))  ;; orc2(false, b) == not(b)
       ((when (eql op (bed-op-arg1))) nil)             ;; arg1(false, b) == false

       ((when (eql op (bed-op-orc1))) t)               ;; orc1(false, b) == true
       ((when (eql op (bed-op-arg2))) right)           ;; arg2(false, b) == b
       ((when (eql op (bed-op-eqv)))  (mk-not right))  ;; eqv(false, b) == not(b)
       ((when (eql op (bed-op-and)))  nil)             ;; and(false, b) == false

       ((when (eql op (bed-op-nand)))  t)              ;; nand(false, b) == true
       ((when (eql op (bed-op-xor)))   right)          ;; xor(false, b) == b
       ((when (eql op (bed-op-not2)))  (mk-not right)) ;; not2(false, b) == not(b)
       ((when (eql op (bed-op-andc2))) nil)            ;; andc2(false, b) == false

       ((when (eql op (bed-op-not1)))  t)              ;; not1(false, b) == true
       ((when (eql op (bed-op-andc1))) right)          ;; andc1(false, b) == b
       ((when (eql op (bed-op-nor)))   (mk-not right)) ;; nor(false, b) == not(b)
       ((when (eql op (bed-op-false))) nil))           ;; false(false, b) == false

    ;; Some unknown operator, don't reduce
    (mk-op-raw op nil right))
  ///
  (defthm bed-eval-of-mk-op-false-x
    (equal (bed-eval (mk-op-false-x op right) env)
           (bed-eval (mk-op-raw op nil right) env))))

(define mk-op-x-true
  ((op   bed-op-p "The operator being applied.")
   (left          "First argument to the operator (a bed)."))
  :returns bed
  :short "Construct a reduced BED for @('op(left, true)')."
  (b* ((op (bed-op-fix$ op))

       ((when (eql op (bed-op-true))) t)    ;; true(left,true) == true
       ((when (eql op (bed-op-ior)))  t)    ;; or(left, true) == true
       ((when (eql op (bed-op-orc2))) left) ;; orc2(left, true) == left
       ((when (eql op (bed-op-arg1))) left) ;; arg1(left, true) == left

       ((when (eql op (bed-op-orc1))) t)    ;; orc1(left, true) == true
       ((when (eql op (bed-op-arg2))) t)    ;; arg2(left, true) == true
       ((when (eql op (bed-op-eqv)))  left) ;; eqv(left, true) == left
       ((when (eql op (bed-op-and)))  left) ;; and(left, true) == left

       ((when (eql op (bed-op-nand)))  (mk-not left)) ;; nand(left, true) == not(left)
       ((when (eql op (bed-op-xor)))   (mk-not left)) ;; xor(left, true) == not(left)
       ((when (eql op (bed-op-not2)))  nil)           ;; not2(left, true) == false
       ((when (eql op (bed-op-andc2))) nil)           ;; andc2(left, true) == false

       ((when (eql op (bed-op-not1)))  (mk-not left)) ;; not1(left, true) == not(left)
       ((when (eql op (bed-op-andc1))) (mk-not left)) ;; andc1(left, true) == not(left)
       ((when (eql op (bed-op-nor)))   nil)           ;; nor(left, true) == false
       ((when (eql op (bed-op-false))) nil))          ;; false(left, true) == false

    ;; Some unknown operator, don't reduce
    (mk-op-raw op left t))
  ///
  (defthm bed-eval-of-mk-op-x-true
    (equal (bed-eval (mk-op-x-true op left) env)
           (bed-eval (mk-op-raw op left t) env))))

(define mk-op-x-false
  ((op   bed-op-p "The operator being applied.")
   (left          "First argument to the operator (a bed)."))
  :returns bed
  :short "Construct a reduced BED for @('op(left, false)')."
  (b* ((op (bed-op-fix$ op))

       ((when (eql op (bed-op-true))) t)    ;; true(left, false) == true
       ((when (eql op (bed-op-ior)))  left) ;; or(left, false) == left
       ((when (eql op (bed-op-orc2))) t)    ;; orc2(left, false) == true
       ((when (eql op (bed-op-arg1))) left) ;; arg1(left, false) == left

       ((when (eql op (bed-op-orc1))) (mk-not left)) ;; orc1(left, false) == not(left)
       ((when (eql op (bed-op-arg2))) nil)           ;; arg2(left, false) == false
       ((when (eql op (bed-op-eqv)))  (mk-not left)) ;; eqv(left, false) == not(left)
       ((when (eql op (bed-op-and)))  nil)           ;; and(left, false) == false

       ((when (eql op (bed-op-nand)))  t)    ;; nand(left, false) == true
       ((when (eql op (bed-op-xor)))   left) ;; xor(left, false) == left
       ((when (eql op (bed-op-not2)))  t)    ;; not2(left, false) == true
       ((when (eql op (bed-op-andc2))) left) ;; andc2(left, false) == left

       ((when (eql op (bed-op-not1)))  (mk-not left)) ;; not1(left, false) == not(left)
       ((when (eql op (bed-op-andc1))) nil)           ;; andc1(left, false) == false
       ((when (eql op (bed-op-nor)))   (mk-not left)) ;; nor(left, false) == not(left)
       ((when (eql op (bed-op-false))) nil))          ;; false(left, false) == false

    ;; Some unknown operator, don't reduce
    (mk-op-raw op left nil))
  ///
  (defthm bed-eval-of-mk-op-x-false
    (equal (bed-eval (mk-op-x-false op left) env)
           (bed-eval (mk-op-raw op left nil) env))))

(define mk-op-x-x
  ((op   bed-op-p "The operator being applied.")
   (arg           "First and second argument to the operator (a bed)."))
  :returns bed
  :short "Construct a reduced BED for @('op(arg, arg)')."
  (b* ((op (bed-op-fix$ op))

       ((when (eql op (bed-op-true))) t)   ;; true(arg, arg) == true
       ((when (eql op (bed-op-ior)))  arg) ;; or(arg, arg) == arg
       ((when (eql op (bed-op-orc2))) t)   ;; orc2(arg, arg) == true
       ((when (eql op (bed-op-arg1))) arg) ;; arg1(arg, arg) == arg

       ((when (eql op (bed-op-orc1))) t)   ;; orc1(arg, arg) == true
       ((when (eql op (bed-op-arg2))) arg) ;; arg2(arg, arg) == arg
       ((when (eql op (bed-op-eqv)))  t)   ;; eqv(arg, arg) == true
       ((when (eql op (bed-op-and)))  arg) ;; and(arg, arg) == arg

       ((when (eql op (bed-op-nand)))  (mk-not arg)) ;; nand(arg, arg) == not(arg)
       ((when (eql op (bed-op-xor)))   nil)          ;; xor(arg, arg) == false
       ((when (eql op (bed-op-not2)))  (mk-not arg)) ;; not2(arg, arg) == not(arg)
       ((when (eql op (bed-op-andc2))) nil)          ;; andc2(arg, arg) == false

       ((when (eql op (bed-op-not1)))  (mk-not arg)) ;; not1(arg, arg) == not(arg)
       ((when (eql op (bed-op-andc1))) nil)          ;; andc1(arg, arg) == false
       ((when (eql op (bed-op-nor)))   (mk-not arg)) ;; nor(arg, arg) == not(arg)
       ((when (eql op (bed-op-false))) nil))         ;; false(arg, arg) == false

    ;; Some unknown operator, don't reduce
    (mk-op-raw op arg arg))
  ///
  (defthm bed-eval-of-mk-op-x-x
    (equal (bed-eval (mk-op-x-x op arg) env)
           (bed-eval (mk-op-raw op arg arg) env))))

(define bed-order
  ((a     "The first node to consider")
   (b     "The second node to consider")
   (order "Table mapping nodes to ranks."))
  :returns (mv (okp   "Is @('a <= b') per this order?")
               (order "Possibly updated order table."))
  :parents (bed-mk1)
  :short "Ordering mechanism for canonicalizing symmetric operators."

  :long "<p>One of the main drawbacks of using a Hons-based representation is
that there isn't a convenient way to ask whether one node comes \"earlier\"
than another.  In a DAG-based representation you could just compare the indices
of the nodes.  But our DAG, being extralogical, is inaccessible and can't be
used in this heuristic way.</p>

<p>Well, we still want to be able to reorder the children of, e.g., AND nodes,
since keeping things in a particular order will encourage structure sharing and
help us to notice opportunities for additional reductions such as @('A & A -->
A').  So, we impose an order on the nodes using an explicit table.</p>

<p>We want to keep the reasoning impact of this table to a minimum.
Accordingly, we don't require any guards on it.  The general idea is that the
order table maps nodes to numbers.  These numbers are assigned in an arbitrary
way as we happen to encounter nodes.  That is, if @('a') or @('b') hasn't yet
been assigned an index, we will go ahead and assign it one here.</p>

<p>The nature of @(see hons-acons) means that the @(see car) of @('order') will
be the most recently assigned node.  So, it's easy to assign sequential indices
without having to maintain some separate free counter.</p>"

  (b* (((when (or (atom a) (atom b)))
        (cond ((and (atom a) (atom b))
               ;; Could go crazy and use something like alphorder here, but it
               ;; should be basically fine to assume A and B are Boolean.  I
               ;; want to consider T to be smaller than anything else so that
               ;; for instance (VAR T NIL) is properly ordered.  So, atoms are
               ;; ordered as long as A or ~B.
               (mv (or a (not b)) order))
              ((atom a)
               ;; Any atom will be smaller than any cons.  So, we're proper.
               (mv t order))
              (t
               ;; A is a Cons and B is an Atom, so we're out of order.
               (mv nil order))))
       ;; Else, interesting case
       (alook (hons-get a order))
       (blook (hons-get b order))
       ((when (and alook blook))
        (mv (<= (ifix (cdr alook)) (ifix (cdr blook)))
            order))
       (free (ifix (and (consp order)
                        (consp (car order))
                        (cdar order))))
       ((mv aidx order free)
        (b* (((when alook)
              (mv (ifix (cdr alook)) order free))
             (free (+ 1 free))
             (order (hons-acons a free order)))
          (mv free order free)))
       ((mv bidx order)
        (b* (((when blook)
              (mv (ifix (cdr blook)) order))
             (free (+ 1 free))
             (order (hons-acons b free order)))
          (mv free order))))
    (mv (<= aidx bidx) order)))

(define mk-op-reorder
  ((op    bed-op-p "Operator being applied.")
   (left  "First argument to the operator (a bed).")
   (right "Second argument to the operator (a bed).")
   (order "The ordering for @(see bed-order)."))
  :returns (mv (bed   "A bed for op(left, right).")
               (order "The (perhaps extended) order."))
  :short "Construct a reduced BED using @(see bed-order)."
  :long "<p>We expect that by now, we've already dealt with:</p>

<ul>
<li>Trivial operators: @('true'), @('false'), @('arg1'), and @('arg2')</li>
<li>Constant propagation</li>
<li>Identical arguments</li>
</ul>

<p>And we've decided that we're really going to construct op(left, right).  We
now want to take symmetry into account.  That is, we can merge @('and(a,b)')
and @('and(b,a)') into some canonical version.</p>

<p>Something subtle is, what do we want to do with symmetry w.r.t. the negation
operators like @('andc1').  Suppose that @('a < b') in the @(see bed-order).  I
think there are perhaps two good options:</p>

<ol>

<li>Prefer fewer operators.  We could, e.g., reduce @('andc1') and @('andc2')
toward @('andc1(a,b)') or @('andc1(b,a)'), so that we never use an @('andc2')
operator.</li>

<li>Prefer fewer permutations.  We could, e.g., reduce @('andc1') and
@('andc2') toward @('andc1(a,b)') or @('andc1(a,b)'), so that we never have the
arguments out of order.</li>

</ol>

<p>I think that to start, I want to try out the latter option.  It seems like
it might have some slight advantages w.r.t. structure sharing, and I guess the
whole point of BEDs is to embrace having a lot of operators.</p>"

  (b* ((op (bed-op-fix$ op))

       ;; Silly operators for which we don't need any reordering.
       ((when (eql op (bed-op-true)))  (mv t order))
       ((when (eql op (bed-op-false))) (mv nil order))
       ((when (eql op (bed-op-arg1)))  (mv left order))
       ((when (eql op (bed-op-arg2)))  (mv right order))

       ;; Special handling for NOT.  See the comments in mk-not.  It's aware of
       ;; the order and does the right thing.
       ((when (eql op (bed-op-not2)))  (mv (mk-not right) order))
       ((when (eql op (bed-op-not1)))  (mv (mk-not left) order))

       ;; For anything else, we're going to consider the order
       ((mv okp order) (bed-order left right order))

       ;; Truly symmetric operators
       ((when (or (eql op (bed-op-and))
                  (eql op (bed-op-ior))
                  (eql op (bed-op-eqv))
                  (eql op (bed-op-nand))
                  (eql op (bed-op-nor))
                  (eql op (bed-op-xor))))
        (mv (if okp
                (mk-op-raw op left right)
              (mk-op-raw op right left))
            order))

       ;; Complementing operators; convert into alternate versions if the
       ;; arguments are mis-ordered.
       ((when (eql op (bed-op-orc1)))
        (mv (if okp
                (mk-op-raw op left right)
              (mk-op-raw (bed-op-orc2) right left))
            order))
       ((when (eql op (bed-op-andc1)))
        (mv (if okp
                (mk-op-raw op left right)
              (mk-op-raw (bed-op-andc2) right left))
            order))
       ((when (eql op (bed-op-orc2)))
        (mv (if okp
                (mk-op-raw op left right)
              (mk-op-raw (bed-op-orc1) right left))
            order))
       ((when (eql op (bed-op-andc2)))
        (mv (if okp
                (mk-op-raw op left right)
              (mk-op-raw (bed-op-andc1) right left))
            order)))

    ;; Some unknown operator, don't reduce
    (mv (mk-op-raw op left right) order))
  ///
  (defthm bed-eval-of-mk-op-reorder
    (b* (((mv bed &) (mk-op-reorder op left right order)))
      (equal (bed-eval bed env)
             (bed-eval (mk-op-raw op left right) env)))))


(define mk-op1
  ((op    bed-op-p)
   (left  "First argument to the operator (a bed)")
   (right "Second argument to the operator (a bed)")
   (order "The ordering for @(see bed-order)."))
  :returns (mv (bed   "A bed for op(left, right).")
               (order "The (perhaps extended) order."))
  :short "Operator node constructor with basic reductions."
  (b* ((op (bed-op-fix$ op))

       ;; Trivial functions
       ((when (eql op (bed-op-true)))  (mv t order))
       ((when (eql op (bed-op-false))) (mv nil order))
       ((when (eql op (bed-op-arg1)))  (mv left order))
       ((when (eql op (bed-op-arg2)))  (mv right order))

       ;; Constant propagation
       ((when (or (atom left) (atom right)))
        (mv (cond ((and (atom left) (atom right))
                   (mk-const-prop op left right))
                  ((atom left)
                   (if left
                       (mk-op-true-x op right)
                     (mk-op-false-x op right)))
                  (t
                   (if right
                       (mk-op-x-true op left)
                     (mk-op-x-false op left))))
            order))

       ;; Same arguments
       ((when (hons-equal left right))
        (mv (mk-op-x-x op left) order)))

    (mk-op-reorder op left right order))
  ///
  (defthm bed-eval-of-mk-op1
    (b* (((mv bed &) (mk-op1 op left right order)))
      (equal (bed-eval bed env)
             (bed-op-eval op
                          (bed-eval left env)
                          (bed-eval right env))))))

(define mk-var1
  ((var   )
   (left  "True branch for this variable ITE node")
   (right "False branch for this variable ITE node"))
  :returns (bed "A bed for var(left, right)")
  :short "Variable node constructor with basic reductions."
  ;; We don't go too crazy here.
  (b* (((when (hons-equal left right))
        left)
       ((mv lvarp lvar la ?lb) (bed-match-var left))
       ((mv rvarp rvar ?ra rb) (bed-match-var right))
       (left (if (and lvarp (equal lvar var))
                 la
               left))
       (right (if (and rvarp (equal rvar var))
                  rb
                right)))
    (mk-var-raw var left right))
  ///
  (defthm bed-eval-of-mk-var1
    (equal (bed-eval (mk-var1 var left right) env)
           (if (bed-env-lookup var env)
               (bed-eval left env)
             (bed-eval right env)))))


; SVEX - Symbolic, Vector-Level Hardware Description Library
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

(in-package "SV")
(include-book "std/util/defines" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "tools/flag" :dir :system)
(include-book "centaur/misc/universal-equiv" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(include-book "tools/easy-simplify" :dir :system)
(include-book "std/lists/repeat" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(local (include-book "std/lists/acl2-count" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/append" :dir :system))

(defxdoc svex-package
  :parents (acl2::hardware-verification)
  :short "A hardware verification package based on a bit-vector expression language."
  :long "<p>SVEX stands for Symbolic Vector EXpression.</p>

<p>@(see Svex) is, narrowly, an expression language of bitvectors.  More
broadly, it is a framework for representing and reasoning about hardware
modules.  Its goal is to allow a Verilog design to be translated into a
finite-state machine representation with well-defined semantics and full
observability of all parts of the original design.  It is somewhat like @(see
esim) in its goals; for a comparison, see @(see svex-esim-comparison).</p>

<h3>Basic Tutorial</h3>

<p>For basic usage of svex for datapath verification (in the style of esim
@(see symbolic-test-vectors), see @(see svex-tutorial).</p>

<h5>SVEX Expressions and @(see 4vec) Values</h5>

<p>The SVEX expression language simply consists of s-expressions with functions
applied to variables or constants.  The functions are predefined;
there are no lambdas or user-defined primitives.</p>

<p>The values on which these functions operate are @(see 4vec) objects, which
can be thought of as signed integers whose bits may take any of the four values
1, 0, X, or Z.</p>

<p>The expressions of the language are @(see svex) objects.  This is a sum of
products type with the following kinds/fields:</p>

<ul>
<li>kind @(':quote') has field @('val'), a @(see 4vec)</li>
<li>kind @(':var') has field @('name'), an @(see svar)</li>
<li>kind @(':call') has fields @('fn'), a @(see fnsym), and @('args'), an svexlist.</li>
</ul>


<h5>LHS Expressions</h5>

<p>An @(see LHS) expression is a special format representing a concatenation of
finite segments of wires (variables).  An LHS expression may be
straightforwardly converted to an svex, and a particular subset of svex
expressions may be converted to LHS expressions.</p>

<h5>SVEX Modules</h5>

<p>Svex has an associated module format; see @(see svmods) and @(see design).
Verilog designs can be converted into this format using @(see
vl::vl-design->svex-design).  Each module contains:</p>

<ul>
<li>a list of wire names and dimensions (width, lower bit index, and range direction)</li>
<li>a list of submodule instances (instance name and submodule name)</li>
<li>a list of assignments (pairings of LHS expressions and svex right-hand-sides)</li>

<li>a list of aliases (pairings of LHS expressions), representing port
connections and any other constructs that cause a single wire to have more than
one name</li>
</ul>

<h5>FSM Conversion</h5>

<p>A hardware design may be expressed hierarchically as an svex @(see design),
but for reasoning usually it is best to have a finite-state machine
representation; that is, a set of states with update functions and a set of
outputs with value functions, each in terms of inputs and previous states.  See
@(see svex-compilation) for a description of the process of obtaining an FSM
representation from a hierarchical one.</p>

<h5>Rewriting and Masks</h5>

<p>The svex library contains a rewriting routine, @(see svex-rewrite), that
applies a series of rules in order to simplify expressions.  The rewriter is
unconditional and memoized so that it runs in time linear in the size of the
expression set.  The rewrite rules are somewhat conservative in that they are
careful to avoid transformations that might increase the total number of nodes.
The rewriter uses a table of bitmasks that signify which bits of each
subexpression are used; for example, if we have a concatenation
@({
  (concat 4 a b)
 })
but the mask for this subexpression is, say, 5 -- which has no bits set past
the lowest 4 -- then this expression may be rewritten to just @('a').</p>

<h5>Composition and Apparent Loops</h5>

<p>Most of the time, expressions may be composed together into full update
functions by recursively traversing them down to the variables and replacing
the variables the update functions produced by recurring on their assigned
expressions.  However, because our variables represent multi-bit vectors,
sometimes a variable appears to depend on itself.  We then must stop this
process early and leave an unresolved non-input variable in the update
functions; otherwise the process would not terminate.  However, we can get rid
of these self-looping variables in the cases where there is no dependency of
any bit of the variable on itself, only dependencies among different bits.  In
this case, we can use the care-masks introduced in the previous section to
determine how many times we need to unroll the expression in order to eliminate
the apparent self-dependency.</p>

<h5>Symbolic Execution and Translation to AIGs</h5>

<p>See @(see svex-symbolic-evaluation).  The book \"symbolic.lisp\" provides a
connection to GL that allows symbolic evaluations of SVEXes to be done by
translating the svexes into AIGs and composing those AIGs with the symbolic
representations of the variable bindings.</p>

<h5>Decomposition Proofs</h5>

<p>See @(see svex-decomp).  The book \"decomp.lisp\" provides automation for
proving that a composition of several slices of a circuit are equivalent to a
whole circuit.</p>

")

(defxdoc symbolic-test-vector
  :parents (svex-package)
  :short "An object describing a finite run of a hardware model."
  :long "
<p>Originally, symbolic test vectors (STVs) were conceived as an aid to
concretely and symbolically simulating E/@(see esim) modules.  Now, a similar
library exists for <see topic='@(url svex-package)'>@(csym svex)</see> which is
nearly a drop-in replacement for @(see esim) STVs.  See @(see
acl2::symbolic-test-vectors) for description of the original esim-based
library, and @(see svex-stvs) for a description of the differences in the new
svex version.</p>")

(defxdoc svex-esim-comparison
  :parents (svex-package)
  :short "Similarities and differences between the <see topic='@(url
svex-package)'>@(csym svex)</see> and @(csee esim) packages"
  :long " <p>Svex and esim largely share the same goal: to provide a
representation for (RTL) hardware designs that can be automatically derived
from Verilog/SystemVerilog and can be concretely or symbolically simulated.
Historically, esim is a successor to the E language of Hunt &amp; Boyer, which is
in turn descended from DE2 (Hunt &amp; Reeber) and DUAL-EVAL (Hunt &amp; Brock).</p>

<p>Below we discuss some of the differences between Svex and Esim, and their
motivations.</p>

<h3>Vector-level expression language</h3>

<p>The expression language used by esim is @(see 4v), in which each expression
just represents a single bit (though like in Verilog, it may take 4 values, 1,
0, X, or Z).  In the svex language, each expression represents a (4-valued) bit
vector, somewhat similar to a bignum representation.  (In fact, the values
taken by svex expressions are represented by @(see 4vec) structures, each of
which is essentially a pair of integers.)</p>

<p>The motivation for this change was to make it easier to translate large
Verilog/SystemVerilog models with reasonable performance.  In esim,
bit-blasting every expression has been a major performance bottleneck.  A
vector-level expression language also may lends itself to more specialized
reasoning strategies than just bit-blasting, although bit-blasting is also
supported by svex (see @(see svex-symbolic-evaluation)).</p>

<h3>Expression-level module representations</h3>

<p>In the esim module representation, each module is either a primitive (which
has an explicit representation of outputs/next-states in terms of
inputs/previous-states) or simply a bundle of submodules.  This means that to
translate a typical Verilog module containing assignments as well as
submodules, the assignments first needed to be broken down and represented as a
series of submodules themselves, in the @(see split) and @(see occform)
transformations.  In svex, we eliminate this process by directly representing
assignments of expressions to wires in the modules; this removes the need for
these two steps.</p>

<h3>Flattening</h3>

<p>One advantage of esim is that the semantics of a module hierarchy are
relatively straightforward and well-defined: each module has its output and
next-state functions in terms of its inputs and previous states, and the
functions for a parent module are computed by taking a fixpoint of the
compositions of the functions of all submodules.</p>

<p>In svex, rather than expressing the semantics in terms of a module
hierarchy, only the expression language has a real concrete interpretation.  To
obtain the meaning of a module hierarchy, we first flatten it and resolve
aliasing between wires, obtaining a flattened set of assignments and state
updates.  We then compose these together to obtain update functions for each
wire and state element in terms of primary inputs and previous states.</p>

<p>While arguably some meaning is lost here -- the flattening and
alias-normalization transforms are sufficiently complicated that we can't argue
that the module hierarchy has a well-defined semantics -- an important
advantage is that this process offers a much simpler way to deal with Verilog
constructs that violate the module hierarchy, such writes to hierarchical
identifiers.  This sort of construct can't be accommodated in esim without
drastically modifying its simple, elegant hierarchical semantics.
Additionally, esim support for bidirectionally-driven wires relies on a
complicated, unverified transformation to the module hierarchy, necessary to
ensure a fundamental assumption that every wire has only one driving module.
With flattening, a wire that is bidirectionally driven reduces to one that is
just multiply driven, and it is relatively easy to resolve any multiply-driven
wires after flattening and before composition.</p>

<h3>SystemVerilog support</h3>

<p>The flattening/alias-normalization/composition flow for deriving an FSM
representation from a module hierarchy has proven to be very convenient for
expressing new SystemVerilog features such as compound data structures.  For
this reason, some SystemVerilog support is now present in svex and more is
planned, whereas no further features are planned for esim development.</p>")


(defxdoc svex.lisp :parents (svex))
(local (xdoc::set-default-parents svex.lisp))

(defsection 4vec
  :parents (svex-package)
  :short "A 4-valued bit vector representation, used by the SVEX package."
  :long "<p>A 4vec represents a vector of 4-valued bits.  Each bit can be 1, 0,
X, or Z.  The concrete representation is either an integer (for special cases
where every bit is 1 or 0) or a pair of integers, upper and lower.  Each
4-valued bit is determined by the corresponding positions in the two integers.
If two corresponding bits are equal, then the resulting bit is that value (1 or
0).  If the upper bit is 1 and the lower 0, then the resulting value is X, and
if the upper bit is 0 and the lower 1, then the resulting value is Z.</p>

<p>Examples:</p>
<table>
<tr><th>Representation</th><th>Meaning (LSB first)</th></tr>
<tr><td>6</td>        <td>0,1,1,0,0,0,...</td></tr>
<tr><td>-13</td>      <td>1,1,0,0,1,1,...</td></tr>
<tr><td>(6 . -13)</td><td>Z,1,X,0,Z,Z,...</td></tr>
</table>"
  (define 4vec-p (x)
    (or (integerp x)
        (and (consp x)
             (integerp (car x))
             (integerp (cdr x))
             (not (equal (car x) (cdr x))))))

  (local (in-theory (enable 4vec-p)))

  (define 4vec ((upper integerp)
                (lower integerp))
    :parents nil
    :returns (x 4vec-p)
    (b* ((upper (lifix upper))
         (lower (lifix lower)))
      (if (eql upper lower)
          upper
        (cons upper lower))))

  (local (in-theory (enable 4vec)))

  (defconst *4vec-x* (4vec -1 0))
  (defconst *4vec-z* (4vec 0 -1))
  (defmacro 4vec-x () `',*4vec-x*)
  (defmacro 4vec-z () `',*4vec-z*)

  (defconst *4vec-1x* (4vec 1 0))
  (defconst *4vec-1z* (4vec 0 1))
  (defmacro 4vec-1x () `',*4vec-1x*)
  (defmacro 4vec-1z () `',*4vec-1z*)

  (define 4vec-fix ((x 4vec-p))
    :parents (4vec)
    :short "Fix an arbitrary object to a 4vec-p.  Guard assumes already 4vec-p."
    :inline t
    :prepwork ((local (in-theory (disable (force)))))
    :returns (newx 4vec-p)
    (mbe :logic (if (consp x)
                    (4vec (ifix (car x))
                          (ifix (cdr x)))
                  (if (integerp x)
                      x
                    (4vec-x)))
         ;; (4vec (ifix (4vec->upper x))
         ;;       (ifix (4vec->lower x)))
         :exec x)
    ///
    (defthm 4vec-fix-of-4vec
      (implies (4vec-p x)
               (equal (4vec-fix x) x)))

    (fty::deffixtype 4vec :pred 4vec-p :fix 4vec-fix :equiv 4vec-equiv :define t :forward t))

  (local (in-theory (enable 4vec-fix)))

  (define 4vec->upper ((x 4vec-p))
    :returns (upper integerp
                    :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (consp x)
                    (ifix (car x))
                  (if (integerp x)
                      x
                    -1))
         :exec (if (integerp x)
                   x
                 (car x)))
    ///
    (defthm 4vec->upper-of-4vec
      (equal (4vec->upper (4vec upper lower))
             (ifix upper)))

    (defthm 4vec->upper-of-4vec-fix
      (equal (4vec->upper (4vec-fix x))
             (4vec->upper x))))

  (define 4vec->lower ((x 4vec-p))
    :returns (lower integerp :rule-classes (:rewrite :type-prescription))
    (mbe :logic (if (consp x)
                    (ifix (cdr x))
                  (if (integerp x)
                      x
                    0))
         :exec (if (integerp x)
                   x
                 (cdr x)))
    ///
    (defthm 4vec->lower-of-4vec
      (equal (4vec->lower (4vec upper lower))
             (ifix lower)))

    (defthm 4vec->lower-of-4vec-fix
      (equal (4vec->lower (4vec-fix x))
             (4vec->lower x))))

  (local (in-theory (enable 4vec->upper 4vec->lower)))

  (defthm 4vec-of-fields
    (4vec-equiv (4vec (4vec->upper x) (4vec->lower x))
                x)
    :hints(("Goal" :in-theory (enable 4vec-fix 4vec-equiv))))

  (defthmd 4vec-fix-is-4vec-of-fields
    (equal (4vec-fix x)
           (4vec (4vec->upper x) (4vec->lower x)))
    :hints(("Goal" :in-theory (enable 4vec-fix))))

  (defthm 4vec-elim
    (implies (4vec-p x)
             (equal (4vec (4vec->upper x) (4vec->lower x))
                    x))
    :rule-classes :elim)

  (def-b*-binder 4vec
    :body
    (std::da-patbind-fn '4vec '((upper . 4vec->upper)
                                (lower . 4vec->lower))
                        args acl2::forms acl2::rest-expr))

  (defthm 4vec-equal
    (equal (equal (4vec upper lower) x)
           (and (4vec-p x)
                (equal (4vec->upper x) (ifix upper))
                (equal (4vec->lower x) (ifix lower))))
    :hints(("Goal" :in-theory (e/d (4vec-fix)))))


  (local (in-theory (enable 4vec-equiv)))

  (defcong 4vec-equiv equal (4vec->upper x) 1)
  (defcong 4vec-equiv equal (4vec->lower x) 1))


(define 2vec-p ((x 4vec-p))
  :parents (2vec)
  :inline t
  :enabled t
  :guard-hints (("goal" :in-theory (e/d (4vec-p 4vec->upper 4vec->lower 4vec-fix))))
  (mbe :logic (equal (4vec->upper x)
                     (4vec->lower x))
       :exec (integerp x))
  ///
  (defthm 4vec->lower-when-2vec-p
    (implies (2vec-p x)
             (equal (4vec->lower x)
                    (4vec->upper x))))

  (fty::deffixequiv 2vec-p))

(define 2vec ((x integerp))
  :parents (4vec)
  :short "A 2vec is a 4vec that has no X or Z bits."
  :long "<p>@('2vec') constructs a 2vec from an integer; @('2vec-p') recognizes
a 2vec; @('2vec->val') gets the integer value out of a 2vec.</p>"
  :inline t
  :guard-hints (("goal" :in-theory (enable 4vec)))
  (mbe :logic (4vec x x)
       :exec x)
  ///
  (defthm 4vec-p-of-2vec
    (4vec-p (2vec x)))

  (defthm 4vec->upper-of-2vec
    (equal (4vec->upper (2vec x))
           (ifix x)))

  (defthm 4vec->lower-of-2vec
    (equal (4vec->lower (2vec x))
           (ifix x)))

  (defthm equal-of-2vec
    (equal (equal (2vec x) y)
           (and (4vec-p y)
                (equal (4vec->upper y) (ifix x))
                (equal (4vec->lower y) (ifix x)))))

  (fty::deffixequiv 2vec))

(define 2vec->val ((x (and (4vec-p x) (2vec-p x))))
  :parents (2vec)
  :short "Extract the upper/lower value (both the same) from a 2vec."
  :inline t
  :enabled t
  :guard-hints (("goal" :in-theory (enable 4vec->upper 4vec->lower 4vec-p)))
  (mbe :logic (4vec->upper x)
       :exec x))


(defflexsum svar
  :parents (svex)
  :kind nil
  (:svar :type-name svar
   :cond t
   :shape (if (atom x)
              (or (stringp x)
                  (and (symbolp x)
                       (not (booleanp x))))
            (and (eq (car x) :var)
                 (consp (cdr x))
                 (not (and (or (stringp (cadr x))
                               (and (symbolp (cadr x))
                                    (not (booleanp (cadr x)))))
                           (eql (cddr x) 0)))))
   :fields
   ((name :acc-body (if (atom x) x (cadr x)))
    (delay :type natp :acc-body (if (atom x) 0 (cddr x))
           :default 0))
   :ctor-body (if (and (or (stringp name)
                           (and (symbolp name)
                                (not (booleanp name))))
                       (eql delay 0))
                  name
                (hons :var (hons name delay)))))



(define fnsym-p (x)
  (and (symbolp x)
       (not (eq x 'quote))
       (not (keywordp x)))
  ///
  (defthm fnsym-p-compound-recognizer
    (implies (fnsym-p x)
             (symbolp x))
    :rule-classes :compound-recognizer))

(define fnsym-fix (x)
  :returns (x fnsym-p)
  (if (fnsym-p x) x 'id)
  ///
  (defthm fnsym-fix-when-fnsym-p
    (implies (fnsym-p x)
             (equal (fnsym-fix x) x)))

  (fty::deffixtype fnsym :pred fnsym-p :fix fnsym-fix :equiv fnsym-equiv :define t :forward t))


(fty::deftypes svex
  :parents (svex-package)
  :prepwork ((local (defthm 4vec-not-svar-p
                      (implies (svar-p x)
                               (not (4vec-p x)))
                      :hints(("Goal" :in-theory (enable 4vec-p svar-p)))))
             (local (defthm cons-fnsym-not-svar-p
                      (implies (not (eq x :var))
                               (not (svar-p (cons x y))))
                      :hints(("Goal" :in-theory (enable fnsym-p svar-p))))))
  (fty::defflexsum svex
    (:var
     :cond (svar-p x)
     :fields ((name :acc-body x :type svar-p))
     :ctor-body name)
    (:quote
     :cond (or (atom x)
               (eq (car x) 'quote))
     :shape (or (atom x) (and (consp (cdr x))
                              (consp (cadr x))
                              (not (cddr x))))
     :fields ((val :acc-body (if (atom x) x (cadr x))
                   :type 4vec))
     :ctor-body (if (atom val) val (hons 'quote (hons val nil))))
    (:call
     :cond t
     :fields ((fn :acc-body (car x) :type fnsym)
              (args :acc-body (cdr x) :type svexlist))
     :ctor-body (hons fn args)))
  (fty::deflist svexlist :elt-type svex :true-listp t))

(memoize 'svex-p :condition '(consp x))

(defconst *svex-z* (svex-quote (4vec-z)))
(defconst *svex-x* (svex-quote (4vec-x)))
(defconst *svex-1z* (svex-quote (4vec-1z)))
(defconst *svex-1x* (svex-quote (4vec-1x)))

(defmacro svex-z () `',*svex-z*)
(defmacro svex-x () `',*svex-x*)
(defmacro svex-1z () `',*svex-1z*)
(defmacro svex-1x () `',*svex-1x*)

(defthm len-of-svexlist-fix
  (equal (len (svexlist-fix x))
         (len x)))

(defthm svex-count-of-car-weak
  (<= (svex-count (car args))
      (svexlist-count args))
  :hints (("goal" :cases ((consp args))))
  :rule-classes :linear)

(defthm svexlist-count-of-cdr-weak
  (<= (svexlist-count (cdr args))
      (svexlist-count args))
  :hints (("goal" :cases ((consp args))))
  :rule-classes :linear)



(define svex-nth ((n natp) (x svexlist-p))
  :enabled t
  :guard-debug t
  (mbe :logic (svex-fix (nth n x))
       :exec (if (< n (len x))
                 (nth n x)
               (svex-quote (4vec-x)))))

(define svex-update-nth ((n natp) (v svex-p) (x svexlist-p))
  :enabled t
  :prepwork ((local (in-theory (e/d (update-nth replicate svexlist-fix)
                                    (acl2::equal-of-append-repeat))))
             (local (include-book "arithmetic/top-with-meta" :dir :system)))
  (mbe :logic (svexlist-fix (update-nth n v x))
       :exec (if (<= n (len x))
                 (update-nth n v x)
               (append x
                       (replicate (- n (len x)) (svex-quote (4vec-x)))
                       (list v)))))


(fty::defalist svex-alist :key-type svar :val-type svex :true-listp t)



(define svex-acons ((var svar-p) (v svex-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p))))
  :returns (aa svex-alist-p)
  (mbe :logic (cons (cons (svar-fix var)
                          (svex-fix v))
                    (svex-alist-fix a))
       :exec (cons (cons var v) a))
  ///
  (fty::deffixequiv svex-acons))

(define svex-lookup ((var svar-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p))))
  :returns (v (iff (svex-p v) v))
  (mbe :logic (cdr (hons-assoc-equal (svar-fix var) (svex-alist-fix a)))
       :exec (cdr (assoc-equal var a)))
  ///
  (fty::deffixequiv svex-lookup)

  (defthm svex-lookup-of-nil
    (equal (svex-lookup v nil) nil))

  (defthm svex-lookup-of-svex-acons
    (equal (svex-lookup var1 (svex-acons var2 x a))
           (if (equal (svar-fix var1) (svar-fix var2))
               (svex-fix x)
             (svex-lookup var1 a)))
    :hints(("Goal" :in-theory (enable svex-acons)))))

(define svex-fastlookup ((var svar-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-fix svex-alist-p
                                       svex-lookup))))
  :enabled t
  (mbe :logic (svex-lookup var a)
       :exec (cdr (hons-get var a))))

(define svex-fastacons ((var svar-p) (v svex-p) (a svex-alist-p))
  :prepwork ((local (in-theory (enable svex-acons))))
  :enabled t
  (mbe :logic (svex-acons var v a)
       :exec (hons-acons var v a)))

(fty::deflist svarlist :elt-type svar :true-listp t :elementp-of-nil nil)

(define svex-alist-keys ((x svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :returns (keys svarlist-p)
  (if (atom x)
      nil
    (if (consp (car x))
        (cons (mbe :logic (svar-fix (caar x)) :exec (caar x))
              (svex-alist-keys (cdr x)))
      (svex-alist-keys (cdr x))))
  ///
  (fty::deffixequiv svex-alist-keys
    :hints (("goal" :expand ((svex-alist-fix x)))))

  (defthm member-svex-alist-keys
    (iff (member k (svex-alist-keys x))
         (and (svar-p k)
              (svex-lookup k x)))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defthm svex-alist-keys-of-svex-acons
    (equal (svex-alist-keys (svex-acons k v x))
           (cons (svar-fix k) (svex-alist-keys x)))
    :hints(("Goal" :in-theory (enable svex-acons)))))

(define svex-alist-vals ((x svex-alist-p))
  :prepwork ((local (in-theory (enable svex-alist-p))))
  :returns (vals svexlist-p)
  (if (atom x)
      nil
    (if (consp (car x))
        (cons (mbe :logic (svex-fix (cdar x)) :exec (cdar x))
              (svex-alist-vals (cdr x)))
      (svex-alist-vals (cdr x))))
  ///
  (fty::deffixequiv svex-alist-vals
    :hints (("goal" :expand ((svex-alist-fix x)))))

  (defthm member-svex-alist-vals-when-svex-lookup
    (implies (svex-lookup k x)
             (member (svex-lookup k x)
                     (svex-alist-vals x)))
    :hints(("Goal" :in-theory (enable svex-lookup svex-alist-fix))))

  (defthm svex-alist-vals-of-svex-acons
    (equal (svex-alist-vals (svex-acons k v x))
           (cons (svex-fix v) (svex-alist-vals x)))
    :hints(("Goal" :in-theory (enable svex-acons))))

  (defthm len-of-svex-alist-vals
    (equal (len (svex-alist-vals x))
           (len (svex-alist-keys x)))
    :hints(("Goal" :in-theory (enable svex-alist-keys)))))



(defalist svar-alist :key-type svar)

(defalist svar-map :key-type svar :val-type svar)


; Centaur AIG Library
; Copyright (C) 2008-2011 Centaur Technology
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
;
; July 2011, Jared added some documentation and merged in the
; faig-op-commutativity theorems.

(in-package "ACL2")
(include-book "faig-base")

(defxdoc faig-constructors
  :parents (faig)
  :short "Low-level functions for constructing @(see faig)s."

  :long "<p>These functions construct new FAIGs from existing ones.  They
typically @(see hons)ing up some new onset and offset @(see aig)s by using the
using @(see aig-constructors) like @(see aig-and) and @(see aig-not), and then
@(see cons) those new onset/offset AIGs together to form a new FAIG.</p>

<p>Most of these functions are geared toward modeling hardware.  For instance,
@(see f-aig-and) is intended to produce a new FAIG that captures the
four-valued logic semantics of an AND gate.</p>

<box><p>Note: the details about how X and Z are handled by these functions are
often subtle and this documentation doesn't really explain <i>why</i> these
functions work the way they do.  <b>However</b>, for most functions here there
are corresponding @(see 4v-operations), and the documentation there typically
<i>does</i> explaining the X/Z behavior.</p></box>


<h3>Three-valued (T-) vs. Four-valued (F-) constructors</h3>

<p>There is an important optimization you can make when modeling hardware gates
as FAIGs.  In particular, it is often possible to construct more
efficient (smaller) FAIGs to represent the gate's output when you know that the
gate's inputs cannot evaluate to Z.</p>

<p>In CMOS designs, this property&mdash;never evaluating to Z&mdash;holds for
the outputs of most logic gates.  Accordingly, it's true for most <i>inputs</i>
to other gates.  For example, suppose you are trying to model a circuit like
this:</p>

@({
        |\\  b
     ---| >o---+
        |/     |       ____
               +------|    \\
        |\             | and )---
     ---| >o----------|____/   o
        |/    a
})

<p>Here, we know that wires @('a') and @('b') can never have the value Z,
because they are produced by NOT gates.  Accordingly, when we want to create
the FAIG corresponding to @('o'), we can use an optimized, less-general
implementation of the <i>and</i> gate, where we assume that our inputs are
non-Z.</p>

<p>Of course, some logic gates (e.g., tri-state buffers) <i>can</i> produce Z
valued outputs, so occasionally these sorts of optimizations aren't possible.
Because of this, we typically have two versions of each FAIG constructor:</p>

<ul>

<li>@('t-aig-*') functions make the assumption that their inputs are can never
evaluate to Z.  These are generally more efficient, and will produce smaller
AIGs that are easier to analyze with SAT solvers.</li>

<li>@('f-aig-*') functions do not make this assumption.  This makes them more
general purpose and able to operate on any FAIG inputs, at the cost of larger
AIGs.</li>

</ul>

<h3>Rulesets</h3>

<p>For historic reasons these functions are left enabled.  There are two
useful @(see rulesets) you can use to disable them:</p>

<ul>
<li>@('f-aig-defs') has all of the @('f-') constructors.</li>
<li>@('t-aig-defs') has all of the @('t-') constructors.</li>
</ul>")


; Macro to prove the FAIG constructors commute over FAIG-EVAL.

(defun pfoc-faig-eval-args (args)
  (if (atom args)
      nil
    (cons (list 'faig-eval (car args) 'env)
          (pfoc-faig-eval-args (cdr args)))))

(defun pfoc-arg-casesplit-list (args)
  (if (atom args)
      nil
    (list* `(and stable-under-simplificationp
                 '(:cases ((aig-eval (car ,(car args)) env))))
           `(and stable-under-simplificationp
                 '(:cases ((aig-eval (cdr ,(car args)) env))))
           (pfoc-arg-casesplit-list (cdr args)))))

(defmacro prove-faig-op-commutes (op args)
  `(defthm ,(intern-in-package-of-symbol
             (concatenate 'string "FAIG-EVAL-OF-" (symbol-name op))
             op)
     (equal (faig-eval (,op . ,args) env)
            (,op . ,(pfoc-faig-eval-args args)))
     :hints ,(pfoc-arg-casesplit-list args)))

(define f-aig-unfloat (a)
  :parents (faig-constructors)
  :short "@(call f-aig-unfloat) converts floating (Z) values to unknown (X)
values."
  :long "<p>See @(see 4v-unfloat); this is the analogous function for
FAIGs.</p>"
  :enabled t
  (b* (((faig a1 a0) a))
    (cons (aig-not (aig-and a0 (aig-not a1)))
          (aig-not (aig-and a1 (aig-not a0)))))
  ///
  (prove-faig-op-commutes f-aig-unfloat (a))

  (defcong faig-fix-equiv equal (f-aig-unfloat a) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define t-aig-not (a)
  :parents (faig-constructors)
  :short "@(call t-aig-not) negates the FAIG @('a'), assuming that it cannot
evaluate to Z."
  :inline t
  :enabled t
  (b* (((faig a1 a0) a))
    (cons a0 a1))
  ///
  (prove-faig-op-commutes t-aig-not (a))

  (defcong faig-fix-equiv equal (t-aig-not a) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-not (a)
  :parents (faig-constructors)
  :short "@(call f-aig-not) negates the FAIG @('a')."
  :enabled t
  (b* (((faig a1 a0) a))
    (cons (aig-not (aig-and a1 (aig-not a0)))
          (aig-not (aig-and a0 (aig-not a1)))))
  ///
  (prove-faig-op-commutes f-aig-not (a))

  (defcong faig-fix-equiv equal (f-aig-not a) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define t-aig-xdet (a)
  :parents (faig-constructors)
  :short "@(call t-aig-xdet) constructs an FAIG for @(see 4v-xdet), assuming
that the argument @('a') cannot evaluate to Z."
  :inline t
  :enabled t
  (b* (((faig a1 a0) a))
    ;; Want 0 if it's boolean, or X if it's not.
    ;; Offset must always be 1.
    ;; Onset is: (and a1 a0)
    (cons (aig-and a1 a0) t))
  ///
  (prove-faig-op-commutes t-aig-xdet (a))

  (defcong faig-fix-equiv equal (t-aig-xdet a) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))


(define f-aig-xdet (a)
  :parents (faig-constructors)
  :short "@(call f-aig-xdet) constructs an FAIG for @(see 4v-xdet)."
  :inline t
  :enabled t
  (b* (((faig a1 a0) a))
    ;; Want 0 if it's boolean, or X if it's not.
    ;; Offset must always be 1.
    ;; Onset is: (iff a1 a0)
    (cons (aig-iff a1 a0) t))
  ///
  (prove-faig-op-commutes f-aig-xdet (a))

  (defcong faig-fix-equiv equal (f-aig-xdet a) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))


(define t-aig-and (a b)
  :parents (faig-constructors)
  :short "@(call t-aig-and) <i>and</i>s together the FAIGs @('a') and @('b'),
assuming they cannot evaluate to Z."
  :enabled t
  (b* (((faig a1 a0) a)
       ((faig b1 b0) b))
    (cons (aig-and a1 b1)
          (aig-or  a0 b0)))
  ///
  (prove-faig-op-commutes t-aig-and (a b))

  (defcong faig-fix-equiv equal (t-aig-and a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (t-aig-and a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-and (a b)
  :parents (faig-constructors)
  :short "@(call f-aig-and) <i>and</i>s together the FAIGs @('a') and @('b')."
  :enabled t
  (b* ((a (f-aig-unfloat a))
       (b (f-aig-unfloat b)))
    (t-aig-and a b))
  ///
  (prove-faig-op-commutes f-aig-and (a b))

  (defcong faig-fix-equiv equal (f-aig-and a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-and a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))


(define t-aig-or (a b)
  :parents (faig-constructors)
  :short "@(call t-aig-or) <i>or</i>s together the FAIGs @('a') and @('b'),
assuming they cannot evaluate to Z."
  :enabled t
  (b* (((faig a1 a0) a)
       ((faig b1 b0) b))
    (cons (aig-or  a1 b1)
          (aig-and a0 b0)))
  ///
  (prove-faig-op-commutes t-aig-or (a b))

  (defcong faig-fix-equiv equal (t-aig-or a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (t-aig-or a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-or (a b)
  :parents (faig-constructors)
  :short "@(call f-aig-or) <i>or</i>s together the FAIGs @('a') and @('b')."
  :enabled t
  (b* ((a (f-aig-unfloat a))
       (b (f-aig-unfloat b)))
    (t-aig-or a b))
  ///
  (prove-faig-op-commutes f-aig-or (a b))

  (defcong faig-fix-equiv equal (f-aig-or a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-or a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))


(define t-aig-xor (a b)
  :parents (faig-constructors)
  :short "@(call t-aig-xor) <i>xor</i>s together the FAIGs @('a') and @('b'),
assuming they cannot evaluate to Z."
  :enabled t
  (t-aig-or (t-aig-and a (t-aig-not b))
            (t-aig-and (t-aig-not a) b))
  ///
  (prove-faig-op-commutes t-aig-xor (a b))

  (defcong faig-fix-equiv equal (t-aig-xor a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (t-aig-xor a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-xor (a b)
  :parents (faig-constructors)
  :short "@(call f-aig-xor) <i>xor</i>s together the FAIGs @('a') and @('b')."
  :enabled t
  (b* ((a (f-aig-unfloat a))
       (b (f-aig-unfloat b)))
    (t-aig-xor a b))
  ///
  (prove-faig-op-commutes f-aig-xor (a b))

  (defcong faig-fix-equiv equal (f-aig-xor a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-xor a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))


(define t-aig-iff (a b)
  :parents (faig-constructors)
  :short "@(call t-aig-iff) <i>iff</i>s together the FAIGs @('a') and @('b'),
assuming they cannot evaluate to Z."
  :enabled t
  (t-aig-or (t-aig-and a b)
            (t-aig-and (t-aig-not a) (t-aig-not b)))
  ///
  (prove-faig-op-commutes t-aig-iff (a b))

  (defcong faig-fix-equiv equal (t-aig-iff a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (t-aig-iff a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-iff (a b)
  :parents (faig-constructors)
  :short "@(call f-aig-iff) <i>iff</i>s together the FAIGs @('a') and @('b')."
  :enabled t
  (b* ((a (f-aig-unfloat a))
       (b (f-aig-unfloat b)))
    (t-aig-iff a b))
  ///
  (prove-faig-op-commutes f-aig-iff (a b))

  (defcong faig-fix-equiv equal (f-aig-iff a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-iff a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))


(define t-aig-ite (c a b)
  :parents (faig-constructors)
  :short "@(call t-aig-ite) constructs a (less conservative) FAIG representing
@('(if c a b)'), assuming these input FAIGs cannot evaluate to Z."
  :long "<p>This is a less-conservative version of @(see t-aig-ite*) that emits
@('a') in the case that @('c') is unknown but @('a = b').  See @(see 4v-ite)
for discussion related to this issue.</p>"
  :enabled t
  (b* (((faig a1 a0) a)
       ((faig b1 b0) b)
       ((faig c1 c0) c))
    (cons (aig-or (aig-and c1 a1) (aig-and c0 b1))
          (aig-or (aig-and c1 a0) (aig-and c0 b0))))
  ///
  (prove-faig-op-commutes t-aig-ite (c a b))

  (defcong faig-fix-equiv equal (t-aig-ite c a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (t-aig-ite c a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (t-aig-ite c a b) 3
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-ite (c a b)
  :parents (faig-constructors)
  :short "@(call f-aig-ite) constructs a (less conservative) FAIG representing
@('(if c a b)')."
  :long "<p>This is a less-conservative version of @(see f-aig-ite*) that emits
@('a') in the case that @('c') is unknown but @('a = b').  See @(see 4v-ite)
for discussion related to this issue.</p>"
  :enabled t
  (b* ((c (f-aig-unfloat c))
       (a (f-aig-unfloat a))
       (b (f-aig-unfloat b)))
    (t-aig-ite c a b))
  ///
  (prove-faig-op-commutes f-aig-ite (c a b))

  (defcong faig-fix-equiv equal (f-aig-ite c a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-ite c a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-ite c a b) 3
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))


(define t-aig-ite* (c a b)
  :parents (faig-constructors)
  :short "@(call t-aig-ite*) constructs a (more conservative) FAIG representing
@('(if c a b)'), assuming these input FAIGs cannot evaluate to Z."
  :long "<p>This is a more-conservative version of @(see t-aig-ite) that emits
@('X') in the case that @('c') is unknown, even when @('a = b').  See @(see
4v-ite) for discussion related to this issue.</p>"
  :enabled t
  (b* (((faig a1 a0) a)
       ((faig b1 b0) b)
       ((faig c1 c0) c)
       (x (aig-and c1 c0)))
    (cons (aig-or x (aig-or (aig-and c1 a1) (aig-and c0 b1)))
          (aig-or x (aig-or (aig-and c1 a0) (aig-and c0 b0)))))
  ///
  (prove-faig-op-commutes t-aig-ite* (c a b))
  (defcong faig-fix-equiv equal (t-aig-ite* c a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (t-aig-ite* c a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (t-aig-ite* c a b) 3
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-ite* (c a b)
  :parents (faig-constructors)
  :short "@(call f-aig-ite*) constructs a (more conservative) FAIG representing
@('(if c a b)'), assuming these input FAIGs cannot evaluate to Z."
  :long "<p>This is a more-conservative version of @(see f-aig-ite) that emits
@('X') in the case that @('c') is unknown, even when @('a = b').  See @(see
4v-ite) for discussion related to this issue.</p>"
  :enabled t
  (b* ((c (f-aig-unfloat c))
       (a (f-aig-unfloat a))
       (b (f-aig-unfloat b)))
    (t-aig-ite* c a b))
  ///
  (prove-faig-op-commutes f-aig-ite* (c a b))

  (defcong faig-fix-equiv equal (f-aig-ite* c a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-ite* c a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-ite* c a b) 3
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-zif (c a b)
  :parents (faig-constructors)
  :short "@(call f-aig-zif) constructs an FAIG representing a kind of pass gate
style mux."
  :long "<p>This mainly exists to support @(see 4v-zif) in sexpr-to-faig
conversion.</p>"
  :enabled t
  (b* ((c (f-aig-unfloat c)))
    (t-aig-ite* c a b))
  ///
  (prove-faig-op-commutes f-aig-zif (c a b))

  (defcong faig-fix-equiv equal (f-aig-zif c a b) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-zif c a b) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-zif c a b) 3
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-res (x y)
  :parents (faig-constructors)
  :short "@(call f-aig-res) constructs a FAIG that represents the result of
connecting two (independently driven) wires together."
  :long "<p>See @(see 4v-res) to understand what this is doing.  This is just
the @(see faig) equivalent.</p>"
  :enabled t
  (b* (((faig x1 x0) x)
       ((faig y1 y0) y))
    (cons (aig-or x1 y1) (aig-or x0 y0)))
  ///
  (prove-faig-op-commutes f-aig-res (a b))

  (defcong faig-fix-equiv equal (f-aig-res x y) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (f-aig-res x y) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))


;; Theorem: no F-AIG-UNFLOAT needed around the answer of f-aig-ite.
;; (thm
;;      (and
;;       (iff (aig-eval (car (f-aig-unfloat (t-aig-ite (f-aig-unfloat c)
;;                                                 (f-aig-unfloat a)
;;                                                 (f-aig-unfloat b))))
;;                      al)
;;            (aig-eval (car (t-aig-ite (f-aig-unfloat c)
;;                                      (f-aig-unfloat a)
;;                                      (f-aig-unfloat b)))
;;                      al))
;;       (iff (aig-eval (cdr (f-aig-unfloat (t-aig-ite (f-aig-unfloat c)
;;                                                 (f-aig-unfloat a)
;;                                                 (f-aig-unfloat b))))
;;                      al)
;;            (aig-eval (cdr (t-aig-ite (f-aig-unfloat c)
;;                                      (f-aig-unfloat a)
;;                                      (f-aig-unfloat b)))
;;                      al))))

(define t-aig-tristate (c a)
  :parents (faig-constructors)
  :short "@(call t-aig-tristate) constructs an FAIG representing a tri-state
buffer whose inputs are known to be non-X."
  :long "<p>See also @(see 4v-tristate).</p>

<p>Onset of output:</p>
@({
    (not (or (and (not c.on) c.off)
             (and c.on (not c.off) (not a.on) a.off)))
})

<p>Offset of output:</p>
@({
    (not (or (and (not c.on) c.off)
         (and c.on (not c.off) a.off (not a.on))))
})"
  (b* (((faig a1 a0) a)
       ((faig c1 c0) c)
       (float (aig-and (aig-not c1) c0))
       (set   (aig-and c1 (aig-not c0)))
       (on    (aig-and (aig-not a0) a1))
       (off   (aig-and (aig-not a1) a0)))
    (cons (aig-and (aig-not float) (aig-not (aig-and set off)))
          (aig-and (aig-not float) (aig-not (aig-and set on)))))
  ///
  (prove-faig-op-commutes t-aig-tristate (c a))

  (defcong faig-fix-equiv equal (t-aig-tristate c a) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix))))
  (defcong faig-fix-equiv equal (t-aig-tristate c a) 2
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))

(define f-aig-pullup (a)
  :parents (faig-constructors)
  :short "@(call f-aig-pullup) constructs an FAIG representing a pullup
resistor."
  (b* (((faig a1 a0) a)
       (a-not-aig-floating (aig-or a1 a0))
       (a-floating (aig-not a-not-aig-floating)))
    (cons (aig-or a-floating a1) a0))
  ///
  (prove-faig-op-commutes f-aig-pullup (a))

  (defcong faig-fix-equiv equal (f-aig-pullup a) 1
    :hints(("Goal" :in-theory (enable faig-fix-equiv faig-fix)))))


(def-ruleset f-aig-defs
  '(f-aig-unfloat
    f-aig-not
    f-aig-xdet
    f-aig-and
    f-aig-or
    f-aig-xor
    f-aig-iff
    f-aig-res
    f-aig-ite
    f-aig-ite*
    f-aig-zif
    t-aig-tristate
    f-aig-pullup))

(def-ruleset t-aig-defs
  '(t-aig-and
    t-aig-iff
    t-aig-ite
    t-aig-ite*
    t-aig-not
    t-aig-xdet
    t-aig-or
    t-aig-xor))


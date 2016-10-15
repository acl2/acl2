; SATLINK - Link from ACL2 to SAT Solvers
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
;                   Sol Swords <sswords@centtech.com>

; varp.lisp -- Definition of CNF Variables

(in-package "SATLINK")
(include-book "std/util/define" :dir :system)
(include-book "std/basic/defs" :dir :system)
(include-book "std/basic/arith-equivs" :dir :system)
(set-tau-auto-mode nil)

(define varp (x)
  :parents (cnf)
  :short "Representation of a Boolean variable."

  :long "<p>Think of a <b>VARIABLE</b> as an abstract data type that represents
a Boolean variable.  A variable has an <i>index</i> that can be used to
distinguish it from other variables.  The interface for working with variables
is simply:</p>

<dl>
<dt>@(call varp) &rarr; @('bool')</dt>
<dd>Recognize valid identifiers.</dd>

<dt>@(call make-var) &rarr; @('id')</dt>
<dd>Construct an identifier with the given given a natural number index.</dd>

<dt>@(call var->index) &rarr; @('index')</dt>
<dd>Get the index from an identifier.</dd>
</dl>

<p>In the implementation, variables are nothing more than natural numbers.
That is, @(see varp) is just @(see natp), while @(see make-var) and @(see
var->index) are logically just @(see nfix) and in the execution are the
identity.</p>

<p>Why, then, bother with a variable type at all?  We use (for efficiency)
integer encodings of related data types like variables and literals. Treating
these as separate types helps us avoid confusing them for one another when we
write programs.</p>

<p>A very nice presentation of this idea is found in <a
href='http://blog.ezyang.com/2010/08/type-kata-newtypes/'>Type Kata:
Distinguishing different data with the same underlying representation</a>, a
blog post by Edward Z. Yang.</p>"

  (natp x)

  ;; Not :type-prescription, ACL2 infers that automatically
  :returns (bool booleanp :rule-classes :tau-system))

(local (in-theory (enable varp)))


(define make-var ((index natp))
  :parents (varp)
  :short "Construct an identifier with the given index."
  (lnfix index)

  :inline t
  ;; Not :type-prescription, ACL2 infers that automatically
  :returns (id varp :rule-classes (:rewrite :tau-system)))


(define var->index ((id varp))
  :parents (varp)
  :short "Get the index from an identifier."
  (lnfix id)

  :inline t
  ;; Not :type-prescription, ACL2 infers that automatically
  :returns (index natp :rule-classes (:rewrite :tau-system)))



(local (in-theory (enable make-var var->index)))

(define var-equiv ((x varp) (y varp))
  :parents (varp)
  :short "Basic equivalence relation for identifiers."
  :enabled t

  (int= (var->index x) (var->index y))

  ///

  (defequiv var-equiv)
  (defcong var-equiv equal (var->index x) 1)
  (defcong nat-equiv equal (make-var x) 1))



(define var-fix ((x varp))
  :parents (varp)
  :short "Basic fixing function for identifiers."

  (make-var (var->index x))

  :inline t
  :returns (x-fix varp)
  ///

  (defcong var-equiv equal (var-fix x) 1)

  (defthm var-fix-of-id
    (implies (varp x)
             (equal (var-fix x) x)))

  (defthm var-equiv-of-var-fix
    (var-equiv (var-fix id) id)))

(local (in-theory (enable var-fix)))



(defsection varp-reasoning
  :parents (varp)
  :short "Basic rules for reasoning about identifiers."

  (defthm var->index-of-make-var
    (equal (var->index (make-var x))
           (nfix x)))

  (defthm var-equiv-of-make-var-of-var->index
    (var-equiv (make-var (var->index id)) id))

  (defthm equal-of-make-var-hyp
    (implies (syntaxp (acl2::rewriting-negative-literal-fn
                       `(equal (make-var$inline ,x) ,y)
                       mfc state))
             (equal (equal (make-var x) y)
                    (and (varp y)
                         (equal (nfix x) (var->index y))))))

  (defthm equal-of-var-fix-hyp
    (implies (syntaxp (acl2::rewriting-negative-literal-fn
                       `(equal (var-fix$inline ,x) ,y)
                       mfc state))
             (equal (equal (var-fix x) y)
                    (and (varp y)
                         (equal (var->index x) (var->index y))))))

  (defthm equal-of-make-var-backchain
    (implies (and (varp y)
                  (equal (nfix x) (var->index y)))
             (equal (equal (make-var x) y) t)))

  (defthm equal-of-var-fix-backchain
    (implies (and (varp y)
                  (equal (var->index x) (var->index y)))
             (equal (equal (var-fix x) y) t)))

  (defthm equal-var->index-forward-make-var-equiv
    (implies (and (equal (var->index x) y)
                  (syntaxp (not (and (consp y)
                                     (or (eq (car y) 'var->index)
                                         (eq (car y) 'nfix))))))
             (var-equiv x (make-var y)))
    :rule-classes :forward-chaining)

  (defthm equal-var->index-nfix-forward-make-var-equiv
    (implies (equal (var->index x) (nfix y))
             (var-equiv x (make-var y)))
    :rule-classes :forward-chaining)

  (defthm equal-var->index-forward-make-var-equiv-both
    (implies (equal (var->index x) (var->index y))
             (var-equiv x y))
    :rule-classes :forward-chaining)

  (defthm make-var-of-var->index
    (equal (make-var (var->index x))
           (var-fix x))))


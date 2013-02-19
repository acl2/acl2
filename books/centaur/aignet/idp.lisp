; AIGNET - And-Inverter Graph Networks
; Copyright (C) 2013 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "AIGNET")
(include-book "cutil/define" :dir :system)
(include-book "centaur/misc/arith-equivs" :dir :system)
(set-tau-auto-mode nil)

(define idp (x)
  :parents (aignet)
  :short "Representation of a Boolean variable."

  :long "<p>Think of an <b>IDENTIFIER</b> as an abstract data type that
represents a Boolean variable.  An identifier has an <i>index</i> that can be
used to distinguish it from other identifiers.  The interface for working with
identifiers is simply:</p>

<dl>
<dt>@(call idp) &rarr; @('bool')</dt>
<dd>Recognize valid identifiers.</dd>

<dt>@(call to-id) &rarr; @('id')</dt>
<dd>Construct an identifier with the given given a natural number index.</dd>

<dt>@(call id-val) &rarr; @('index')</dt>
<dd>Get the index from an identifier.</dd>
</dl>

<p>In the implementation, identifiers are nothing more than natural numbers.
That is, @(see idp) is just @(see natp), while @(see to-id) and @(see id-val)
are logically just @(see nfix) and in the execution are the identity.</p>

<p>Why, then, bother with an identifier type at all?  Throughout AIGNET we
use (for efficiency) integer encodings of lots of related data types, e.g.,
identifiers, literals, nodes, and so on.  Treating these as separate types
helps us avoid confusing them for one another when we write programs.</p>

<p>A very nice presentation of this idea is found in <a
href='http://blog.ezyang.com/2010/08/type-kata-newtypes/'>Type Kata:
Distinguishing different data with the same underlying representation</a>, a
blog post by Edward Z. Yang.</p>"

  (natp x)

  ;; Not :type-prescription, ACL2 infers that automatically
  :returns (bool booleanp :rule-classes :tau-system)

  ///

  (defthm idp-type
    ;; BOZO why this rule?  If we're going to have something like this,
    ;; shouldn't we strengthen it to an EQUAL compound-recognizer instead?  Do
    ;; we really ever want to know that an IDP is a NATP, instead of calling
    ;; ID-VAL on it?
    (implies (idp x)
             (natp x))
    :rule-classes (:tau-system :compound-recognizer)))


(local (in-theory (enable idp)))


(define to-id ((index natp))
  :parents (idp)
  :short "Construct an identifier with the given index."
  (lnfix index)

  :inline t
  ;; Not :type-prescription, ACL2 infers that automatically
  :returns (id idp :rule-classes (:rewrite :tau-system)))


(define id-val ((id idp))
  :parents (idp)
  :short "Get the index from an identifier."
  (lnfix id)

  :inline t
  ;; Not :type-prescription, ACL2 infers that automatically
  :returns (index natp :rule-classes (:rewrite :tau-system)))



(local (in-theory (enable to-id id-val)))

(define id-equiv ((x idp) (y idp))
  :parents (idp)
  :short "Basic equivalence relation for identifiers."
  :enabled t

  (int= (id-val x) (id-val y))

  ///

  (defequiv id-equiv)
  (defcong id-equiv equal (id-val x) 1)
  (defcong nat-equiv equal (to-id x) 1))



(define id-fix ((x idp))
  :parents (idp)
  :short "Basic fixing function for identifiers."

  (to-id (id-val x))

  :inline t
  :returns (x-fix idp)
  ///

  (defcong id-equiv equal (id-fix x) 1)

  (defthm id-fix-of-id
    (implies (idp x)
             (equal (id-fix x) x)))

  (defthm id-equiv-of-id-fix
    (id-equiv (id-fix id) id)))

(local (in-theory (enable id-fix)))



(defsection idp-reasoning
  :parents (idp)
  :short "Basic rules for reasoning about identifiers."

  (defthm id-val-of-to-id
    (equal (id-val (to-id x))
           (nfix x)))

  (defthm id-equiv-of-to-id-of-id-val
    (id-equiv (to-id (id-val id)) id))

  (defthm equal-of-to-id-hyp
    (implies (syntaxp (acl2::rewriting-negative-literal-fn
                       `(equal (to-id$inline ,x) ,y)
                       mfc state))
             (equal (equal (to-id x) y)
                    (and (idp y)
                         (equal (nfix x) (id-val y))))))

  (defthm equal-of-id-fix-hyp
    (implies (syntaxp (acl2::rewriting-negative-literal-fn
                       `(equal (id-fix$inline ,x) ,y)
                       mfc state))
             (equal (equal (id-fix x) y)
                    (and (idp y)
                         (equal (id-val x) (id-val y))))))

  (defthm equal-of-to-id-backchain
    (implies (and (idp y)
                  (equal (nfix x) (id-val y)))
             (equal (equal (to-id x) y) t)))

  (defthm equal-of-id-fix-backchain
    (implies (and (idp y)
                  (equal (id-val x) (id-val y)))
             (equal (equal (id-fix x) y) t)))

  (defthm equal-id-val-forward-to-id-equiv
    (implies (and (equal (id-val x) y)
                  (syntaxp (not (and (consp y)
                                     (or (eq (car y) 'id-val)
                                         (eq (car y) 'nfix))))))
             (id-equiv x (to-id y)))
    :rule-classes :forward-chaining)

  (defthm equal-id-val-nfix-forward-to-id-equiv
    (implies (equal (id-val x) (nfix y))
             (id-equiv x (to-id y)))
    :rule-classes :forward-chaining)

  (defthm equal-id-val-forward-to-id-equiv-both
    (implies (equal (id-val x) (id-val y))
             (id-equiv x y))
    :rule-classes :forward-chaining)

  (defthm to-id-of-id-val
    (equal (to-id (id-val x))
           (id-fix x))))

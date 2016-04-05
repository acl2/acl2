; Std/basic - Basic definitions
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")
(include-book "ihs/basic-definitions" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "tools/rulesets" :dir :system)

(defsection arith-equivs
  :parents (arithmetic std/basic)
  :short "Definitions for congruence reasoning about integers/naturals/bits."

  :long "<p>Note: to use this book at full strength, do:</p>

@({
    (include-book \"std/basic/arith-equivs\" :dir :system)
    (local (in-theory (enable* arith-equiv-forwarding)))
})

<p>You can also load just the definitions and bare-minimum theorems using</p>

@({
    (include-book \"std/basic/arith-equiv-defs\" :dir :system)
})")


; Commented out April, 2016 by Matt K., now that a better compound recognizer
; of the same name is part of ACL2.
;;; (defthm bitp-compound-recognizer
;;;   ;; Questionable given the bitp-forward rule.  But I think we may still want
;;;   ;; this.
;;;   (implies (bitp x)
;;;            (natp x))
;;;   :rule-classes :compound-recognizer)

;; (defthm bitp-when-under-2
;;   ;; questionable to bring arithmetic into it
;;   (implies (< x 2)
;;            (equal (bitp x)
;;                   (natp x))))

;; (defthm bitp-when-over-1
;;   (implies (< 1 x)
;;            (not (bitp x))))

(defsection int-equiv
  :parents (arith-equivs)
  :short "Equivalence under @(see ifix), i.e., integer equivalence."

  ;; this is now done in fty/basetypes.lisp
  ;; (defun int-equiv (a b)
  ;;   (declare (xargs :guard t))
  ;;   (equal (ifix a) (ifix b)))

  ;; (defequiv int-equiv)

  ;; (defthm ifix-under-int-equiv
  ;;   (int-equiv (ifix a) a))

  ;; (defcong int-equiv equal (ifix a) 1)

  ;; We leave int-equiv enabled since generally it's most useful as a congruence target.
  (in-theory (enable int-equiv))

  (defcong int-equiv equal (zip a) 1))


(defsection nat-equiv
  :parents (arith-equivs)
  :short "Equivalence under @(see nfix), i.e., natural number equivalence."

  ;; this is now done in fty/basetypes.lisp
  ;; (defun nat-equiv (a b)
  ;;   (declare (xargs :guard t))
  ;;   (equal (nfix a) (nfix b)))

  ;; (defequiv nat-equiv)
  ;; (defthm nfix-under-nat-equiv
  ;;   (nat-equiv (nfix a) a))

  ;; (defcong nat-equiv equal (nfix a) 1)

  ;; We leave nat-equiv enabled since generally it's most useful as a congruence target.
  (in-theory (enable nat-equiv))

  (defrefinement int-equiv nat-equiv
    :hints(("Goal" :in-theory (enable int-equiv))))

  (defcong nat-equiv equal (zp a)  1))


(defsection bit-equiv
  :parents (arith-equivs)
  :short "Equivalence under @(see bfix), i.e., bit equivalence."

  ;; [Jared] this is now done in basetypes
  ;; (fty::deffixtype bit :pred bitp :fix bfix :equiv bit-equiv :define t)

  ;; [Jared] bozo maybe move all of this to basetypes?

  ;; We leave bit-equiv enabled since generally it's most useful as a congruence target.
  (in-theory (enable bit-equiv))
  (defrefinement nat-equiv bit-equiv)
  (defcong bit-equiv equal (zbp a) 1))


(defsection bool->bit
  :parents (arith-equivs)
  :short "Coerce a Boolean into a @(see bitp)."

  (defund-inline bool->bit (x)
    (declare (xargs :guard t))
    (if x 1 0)))

(defsection bit->bool
  :parents (arith-equivs)
  :short "Coerce a bit into a Boolean."
  :long "<p>This is just @('(equal 1 x)').  However, using a function for this
allows us to use congruences and to control case-splitting.  For example, if we
have
@({
  (equal (equal 1 (foo x))
         (equal 1 (bar y)))
})
this will case split into:
@({
  (if (equal 1 (foo x))
      (equal 1 (bar y))
    (not (equal 1 (bar y))))
})
whereas
@({
 (equal (bit->bool (foo x)) (bit->bool (bar y)))
})
will not.</p>

<p>Because a bunch of libraries were written under the assumption that
@('(equal 1 x)') was the way to tell if a bit was true or false, we leave this
enabled by default.</p>"

  (defun-inline bit->bool (x)
    (declare (xargs :guard t))
    (equal 1 x))

  (defcong bit-equiv equal (bit->bool a) 1))




(defsection negp
  :parents (arith-equivs)
  :short "Recognizer for negative integers."

  (defund negp (x)
    (declare (xargs :guard t))
    (and (integerp x)
         (< x 0)))

  (defthm negp-compound-recognizer
    (equal (negp x)
           (and (integerp x)
                (< x 0)))
    :hints(("Goal" :in-theory (enable negp)))
    :rule-classes :compound-recognizer))




; ACL2 Version 8.5 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2023, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

(in-package "ACL2")

; See also float-b.lisp, as discussed in the comment that concludes this file.

; Essay on Support for Floating-point (double-float, df) Operations in ACL2

; Much of what we have to say about dfs is in :DOC df.  This Essay assumes
; familiarity with that :DOC topic and adds implementation-level remarks, more
; of which may be added in the future.

; Note: A tags-search for "[^a-z]df[^a-oq-z]" outside doc.lisp will hit "df"
; occurrences relevant to support for floating-point operations.

; A key to evaluation with dfs is that *1* functions never take or return
; Common Lisp floats.  This complicates ec-call a bit for raw Lisp calls when
; dfs are involved, but that is solved by requiring a :dfs argument in any such
; ec-call expression.

; The introduction of dfs after Version_8.5 affected translation for execution,
; by enforcing stobj-like syntactic restrictions when expressions may involve
; df inputs and outputs.  This is particularly tricky for mv, let, and mv-let
; expressions.

; First consider a call of translate11 on (mv expr1 ... exprk).  If the
; stobjs-out argument of translate11 is a list (mv x1 ... xk), then translation
; presents no difficulty; just translate expri with stobjs-out (xi).  But when
; stobjs-out is a symbol for that translate11 call, we have a challenge.
; Before the addition of dfs, this case was simple: each expri that is a stobj
; name would translate to itself (and that is still the case), and every other
; expri would translate with stobjs-out (nil).  But now, some of the non-stobj
; expri should be translated with stobjs-out (:DF).  Which ones?

; In that case, we guess which expressions should be treated as dfs (i.e.,
; translated with stobjs-out = (:DF)) using function compute-stobj-flags-df?
; (and its subroutine returns-df?).  That attempt to guess may occasionally
; fail, for example when the expression is a recursive call of a function F
; currently being defined and translation is with stobjs-out = F.  In that case
; the special value :df? is put into the stobjs-out list being constructed.
; That list of nil, :df, :df?, and stobj values is passed to
; translate11-lst/stobjs-out, which returns not only the usual three
; error/list/bindings results but also (in the non-error case) the stobjs-out
; for which translation is successful.  Then translate-bind assigns that
; returned stobjs-out to F in the returned bindings.

; Next consider translation of (let ((v1 expr1) ... (vk exprk)) <body>).  Here
; the problem is similar to translation of (mv expr1 ... exprk): which expri
; should be treated as dfs, i.e., translated with stobjs-out = (:DF)?  The
; solution is similar to the one for mv expressions.  For let, we use function
; compute-stobj-flags-df?-doublets (which too calls returns-df?) to guess which
; expri are dfs, but again, some guesses may fail.  So as for mv, in this case
; translate11-lst/stobjs-out is called on the list (expr1 ... exprk), which
; returns not only the usual three error/list/bindings results but also the
; stobjs-out for which translation is successful (in the non-error case).  That
; returned stobjs-out is used, together with double-float type declarations of
; the let form (not shown above), in determining which vi are known-dfs for
; translation of <body>.

; Finally, consider translation for execution of (mv-let (v1 ... vk) <expr>
; <body>).  Before there were dfs, we could construct a suitable stobjs-out for
; translating <body> even before translating <expr>: that stobjs-out is (s1
; ... sk), where si is vi if vi is a stobj name, and otherwise si is nil.  But
; now, when vi is not a stobj name then si might be either nil or :DF.  To
; determine which, translate11-mv-let calls translate11-collecting-known-dfs,
; which returns a suitable known-dfs for translation of <body>.  See
; translate11-mv-let for details.

#-acl2-loop-only
(declaim (inline
           binary-df*
           binary-df+
           binary-df-log
           binary-df/
           df-abs-fn
           df-acos-fn
           df-acosh-fn
           df-asin-fn
           df-asinh-fn
           df-atan-fn
           df-atanh-fn
           df-cos-fn
           df-cosh-fn
           df-exp-fn
           df-expt-fn
           df-pi
           df-rationalize
           df-string
           df-sin-fn
           df-sinh-fn
           df-sqrt-fn
           df-tan-fn
           df-tanh-fn
           dfp
           from-df
;          to-df ; macro in raw Lisp
           unary-df-
           unary-df/
           unary-df-log
           df<-fn
           df=-fn
           df/=-fn
           df0
           df1
           df-minus-1
           ))

(encapsulate () (logic)

; We use a surrounding encapsulate for logic mode, rather than of putting
; (logic) inside the partial-encapsulate, to support redundancy in pass 2.

(partial-encapsulate
 (((constrained-to-df *) => * :formals (x) :guard (rationalp x)))
 nil

; We describe here the implicit axioms of this partial-encapsulate as well as a
; local witness function, WDF, that satisfies those axioms and the explicit
; axioms below.  We introduce WDF abstractly, not in code, to be the required
; local witness for a partial-encapsulate that satisfies both the explicit and
; implicit axioms of the partial-encapsulate.  Throughout this discussion we
; imagine a fixed Lisp implementation.

; We consider computations C(x,y) that compute (rational (float x 0.0D0)) = y.
; Such C(x,y) is "actually performed" if that computation is actually performed
; by our fixed Lisp implementation, possibly in the past, possibly in the
; future.  Note that C(0,0) is actually performed, by a sanity check in
; acl2.lisp.

; Informally, we want to define WDF to specify not only the computations C(x,y)
; that are actually performed but also to "close" when computing on -x or on y.
; We make that idea precise by defining when a computation C(x,y) -- that is,
; computing (rational (float x 0.0D0)) for rational x to yield y -- is
; considered to be a "WDF computation": namely, if at least one of the
; following criteria are met.

; [WDF1]  C(x,y) is actually performed.

; [WDF2]  C(-x,z) is actually performed for some z.

; [WDF3]  C(x,y) when y = x {capturing computations where x is representable}

; Note that since (float x 0.0D0) has finite range and the function, rational,
; is injective on double-floats, there are only finitely many WDF computations,
; in spite of [WDF3].

; We now define WDF with a giant case statement that maps x to y for every WDF
; computation C(x,y) and maps everything else to 0.  Note that the argument
; just above shows that WDF is idempotent: the only remaining step is to check
; that (WDF (WDF r)) = (WDF r) for r not equal to any such x, but in that case
; we have (WDF (WDF r)) = (WDF 0) = 0 = (WDF r).

; The implicit axioms of this partial-encapsulate consist of all formulas
; (equal (constrained-to-df x) y) for WDF computations C(x,y).

; Comments in the theorems below argue that those theorems are satisfied by
; the witness, WDF.

; Since to-df is defined logically to be constrained-to-df, we also need to
; know that computations performed by the under-the-hood raw Lisp code for
; to-df are justified by the axioms.  More precisely, if (to-df r) evaluates to
; s, it must be the case that (equal (to-df r) s) is a theorem.  But that
; equality is in fact one of the implicit axioms of the partial-encapsulate, by
; the raw Lisp definition of to-df and by [WDF1] above.

(local (defun constrained-to-df (x)

; This is not the true witness for the partial encapsulate, which is WDF as
; defined in comments above.

         (declare (ignore x))
         0))

(defthm rationalp-constrained-to-df

; The local witness WDF defined above always returns a rational.

  (rationalp (constrained-to-df x))
  :rule-classes :type-prescription)

(defthm constrained-to-df-idempotent

; Let's call the following identity, quoting
; http://www.lispworks.com/documentation/HyperSpec/Body/f_ration.htm, the
; "float-rational identity".

;  It is always the case that
;
;  (float (rational x) x) ==  x

; Now we can show that this axiom holds for the witness, WDF, to
; constrained-to-df.  If (WDF x) = 0 then (WDF (WDF x)) = (WDF 0), which is 0
; since as noted above, C(0,0) is actually performed in a sanity check in
; acl2.lisp.  So suppose (WDF x) is not 0, in which case x is one of the values
; handled by the giant case statement defining WDF.  Then:

; (WDF (WDF x))
; = {by definition of WDF}
; (rational (float (rational (float x 0.0D0)) 0.0D0))
; = {since the second argument of float only specifies the type}
; (rational (float (rational (float x 0.0D0)) (float x 0.0D0)))
; = {by the float-rational identity applied to (float x 0.0D0) for x}
; (rational (float x 0.0D0))
; = {by definition of WDF}
; x

  (equal (constrained-to-df (constrained-to-df x))
         (constrained-to-df x)))

(defthm to-df-minus

; The HyperSpec section on "System Class FLOAT"
; (http://www.lispworks.com/documentation/HyperSpec/Body/t_float.htm) is not as
; helpful as it might be; in particular, "integer between b^p-1 and b^p-1"
; doesn't make any sense (maybe a minus sign is missing).  But we take that
; section to say that we can view a float in the usual way (especially when
; IEEE 754 is respected, which we may assume since we insist on the presence of
; feature :ieee-floating-point at build time).  So we take the HyperSpec to say
; that a double-float may be written either as 0.0 or as s*f*2^e where s is +1
; or -1, f is a positive integer, and e is an integer.

; [Aside: We use base 2 above.  That isn't explicitly specified in the
; HyperSpec section on "System Class FLOAT".  However, section "Basic and
; interchange formats" in the IEEE 754 spec
; (https://en.wikipedia.org/wiki/IEEE_754#CITEREFIEEE_7542019) has a table
; showing that the radix is 2 for double-precision.  We give this a little test
; in acl2.lisp by checking that (float-radix 1.0D0) = 2.]

; Now we show that WDF, as defined above, satisfies this defthm.  The
; hypothesis for WDF, (and (rationalp x) (equal (WDF x) x)), implies that x is
; a rational for whicch the following holds in Lisp.

; [1]  (rational (float x 0.0D0)) = x.

; To show that the conclusion holds for WDF, it suffices to show the following,
; since by clause [WDF2] in the definition of WDF, (WDF (- x)) = (rational
; (float (- x) 0.0D0)).

; [*]  (rational (float (- x) 0.0D0)) = (- x).

; To show [*], we use our interpretation above of the HyperSpec to choose s,
; f, and e as above so that (float x 0.0D0), whose rational value is x by [1],
; is realized as s*f*2^e.  So x = s*f*2^e, which we can state as follows.

; [2]  x is represented as s*f*2^e.

; Here is an immediate consequence of [2] by simple math.

; [3]  -x is represented as (-s)*f*2^e.

; The function (float number prototype) is specified by the HyperSpec
; (http://www.lispworks.com/documentation/HyperSpec/Body/f_float.htm) as
; follows.

;   If a prototype is supplied, a float is returned that is mathematically
;   equal to number but has the same format as prototype.

; That is clearly nonsense if the given number is not representable!  For
; example, the sentence displayed just above implies that the common value of
; the two float expressions just below is equal to both 11184811/33554432 and
; 1/3, which would imply the absurd conclusion that these two rationals are
; equal.

; ? (= (float 11184811/33554432 0.0f0) (float 1/3 0.0f0))
; T
; ?

; But if the HyperSpec sentence above means anything, it should hold for
; representable numbers, which we can state as follows.

; [4]  If a rational x is represented by the double-float s*f*2^e, then
;      (rational (float x 0.0D0)) is equal to x.

; Then [*] follows immediately from [3] by applying [4] to -x.

  (implies (and (rationalp x)
                (equal (constrained-to-df x) x)) ; basically, (dfp x)
           (equal (constrained-to-df (- x))
                  (- x))))

(defthm constrained-to-df-default

; WDF, as defined above, clearly satisfies this property.

  (implies (not (rationalp x))
           (equal (constrained-to-df x) 0)))

(defthm constrained-to-df-0

; As noted above, this is justified by a check in acl2.lisp, so we might as
; well make this constraint explicit.

  (equal (constrained-to-df 0) 0))
)
)

#+acl2-loop-only
(defun to-df (x)
  (declare (xargs :guard (rationalp x)
                  :mode :logic))
  (constrained-to-df x))

(defthm rationalp-to-df
  (rationalp (to-df x))
  :rule-classes :type-prescription)
(defthm to-df-idempotent
  (equal (to-df (to-df x))
         (to-df x)))
(defthm to-df-default
  (implies (not (rationalp x))
           (equal (to-df x) 0)))

(defun dfp (x)

; We need the #-acl2-loop-only case below.  For example, without it, then after
; we evaluatate (defun f (x) (declare (type double-float x)) (dfp x)) we'll see
; that (f (to-df 3)) evaluates (wrongly) to nil.  See the comment in
; translate11-call-1 about allowing dfp to be applied to a :df; that's why we
; need the #-acl2-loop-only case below.

  (declare (xargs :guard t :mode :logic))
  #+acl2-loop-only
  (and (rationalp x)
       (= (to-df x) x))
  #-acl2-loop-only
  (if (rationalp x)
      (= (rational (to-df x)) x)
    (typep x 'double-float)))

(defun from-df (x)
  (declare (xargs :guard (dfp x) :mode :logic))
  #+acl2-loop-only
  x

; When executing in raw Lisp, we need to ensure that we return an ordinary
; object here, not a double-float.  As usual with ACL2 functions, we are free
; to assume that the guard holds.

  #-acl2-loop-only
  (rational x))

(defun to-dfp (x)
  (declare (xargs :guard (rationalp x) :mode :logic))
  (from-df (to-df x)))

(defthm dfp-to-df
  (dfp (to-df x)))

(defthm dfp-implies-rationalp
  (implies (dfp x)
           (rationalp x))
  :rule-classes :compound-recognizer)

(defthm dfp-implies-to-df-is-identity

; This theorem is trivial, but worth stating, in analogy to
; to-df-of-df-rationalize.  Both are justified by the CL HyperSpec:
; http://www.lispworks.com/documentation/HyperSpec/Body/f_ration.htm

  (implies (dfp x)
           (equal (to-df x) x))
  :rule-classes (:forward-chaining :rewrite))

(in-theory (disable dfp to-df))

(encapsulate () (logic)

; We use a surrounding encapsulate for logic mode, rather than of putting
; (logic) inside the partial-encapsulate, to support redundancy in pass 2.

(partial-encapsulate
 (((df-round *) => * :formals (x) :guard (rationalp x)))
 nil

; In brief: The function df-round is intended to be the rounding function used
; by Common Lisp to satisfy the IEEE 754 spec, which says that floating-point
; operations are performed by rounding the exact mathematical result.  We now
; elaborate.

; The Common Lisp HyperSpec says
; (http://www.lispworks.com/documentation/lw71/CLHS/Body/v_featur.htm) of the
; :ieee-floating-point feature:

;    If present, indicates that the implementation purports to conform to the
;    requirements of IEEE Standard for Binary Floating-Point Arithmetic.

; Thus, we check in acl2.lisp that :ieee-floating-point is in *features*.  The
; IEEE 754 spec is summarized thus in https://en.wikipedia.org/wiki/IEEE_754):

;    Unless specified otherwise, the floating-point result of an operation is
;    determined by applying the rounding function on the infinitely precise
;    (mathematical) result. Such an operation is said to be correctly
;    rounded. This requirement is called correct rounding.[19]

; In the IEEE 754-2019 spec (see
; https://doi.org/10.1109%2FIEEESTD.2019.8766229) we find the following.

; Section 2.1.

;    correct rounding: This standard’s method of converting an infinitely
;    precise result to a floating-point number, as determined by the applicable
;    rounding direction. A floating-point number so obtained is said to be
;    correctly rounded.

; Section 5.1:

;    Unless otherwise specified, each of the computational operations specified
;    by this standard that returns a numeric result shall be performed as if it
;    first produced an intermediate result correct to infinite precision and
;    with unbounded range, and then rounded that intermediate result, if
;    necessary, to fit in the destination's format (see Clause 4 and Clause 7).

; With the comments above in mind, we now address the fact that we are in a
; partial-encapsulate, so we need to discuss the implicit axioms and the
; intended (implicit) local witness.  Note that although the explicit local
; witness and explicit axioms below suffice for ACL2 to admit this
; partial-encapsulate, they do not meet the logical burden imposed by
; partial-encapsulate.  For that, we need to describe the implicit axioms as
; well; moreover, these should suffice to justify results obtained when
; evaluating calls of df-round.  Note also that although ACL2 does not evaluate
; df-round directly, it evaluates df-round indirectly when applying df+ or any
; other rational df function.  For example, (df+ x y) is defined to be
; (df-round (+ x y)), but we have:

;    ACL2 !>(df+ (to-df 1/3) (to-df 2/3))
;    #d1.0
;    ACL2 !>

; Let WRND be our (implicit) local witness for df.  We want to base WRND on the
; rounding function used by the host Lisp.  In the future we might tie down
; WRND so that it rounds to nearest even; in that case we might replace this
; partial-encapsulate. with a suitable defun and theorems.  We could do this
; because the IEEE Spec (2019 version) defines RoundTiesToEven as one would
; expect, in Section 4.3.1, and Section 4.3.3 says the following.

;    The roundTiesToEven rounding-direction attribute shall be the default
;    rounding direction for results in binary formats.

; This seems to suggest that any Common Lisp implementation with
; :ieee-floating-point in *features* should use roundTiesToEven.

; However, we are not yet quite convinced by the argument above, nor are we
; ready to formalize round-to-even.  So for now, we take a different approach
; to defining WRND, as follows.

; The comments in the partial-encapsulate for constrained-to-df explain how a
; local witness is obtained by using a big case statement based on Lisp
; computations.  We define WRND that way too, though this time the computations
; are roundings in support of the application of df+ or any other rational df
; function.  For example, evaluation of (df/ #d1.0 #d3.0) leads Common Lisp to
; round the rational 1/3 to a df (at least, conceptually, as per the IEEE
; spec), displayed as #d0.3333333333333333; so our local witness maps 1/3 to
; (the rational number) #d0.3333333333333333.  The implicit axioms include
; (equal (df-round 1/3) #d0.3333333333333333) and all other such equalities.
; Moreover, we consider all roundings of (+ 0.0 x) where x is a double-float --
; there are only finitely many -- and note that since that sum is surely x,
; therefore x rounds to itself (see [WRND2] below).  So to summmarize, our
; intended (and implicit) local witness for df-round, WRND, is defined as
; follows.

; [WRND1]  For any rational df operation performed in the given Lisp
;          implementation (past or future) completed by rounding rational r to
;          double-float x:
;          (WRND r) = (rational x).

; [WRND2]  Let r = (rational x) for a double-float x; then
;          (WRND r) = r.

; [WRND3]  If r is not covered by [WRND1] or [WRND2], then
;          (WRND r) = 0.

(local (defun df-round (x)
         (if (dfp x)
             x
           0)))

(defthm rationalp-df-round

; This rule is important, since it supports the use of linear arithmetic for
; df+ and other rational df operations.

  (rationalp (df-round x))
  :rule-classes :type-prescription)

(defthm dfp-df-round

; Clearly (rationalp (WRND r)) follows by definition of WRND.  So by definition
; of dfp, it remains to prove that (equal (to-df (WRND r)) (WRND r)) holds for
; all r.  If (WRND r) = 0, then this is immediate by constrained-to-df-0.
; Otherwise, cases [WRND1] and [WRND2] of the definition of WRND tell us that
; if (WRND r) = s for some s that is (rational x) for some double-float x.  The
; float-rational identity (see constrained-to-df-idempotent) tells us that
; (float (rational x) 0.0D0) = x; Applying rational to both sides and using s =
; (rational x), we have (rational (float s 0.0D0)) = s.  So by [WDF3], we can
; prove (equal (to-df s)) s); that is, (equal (to-df (WRND r)) (WRND r)).

  (dfp (df-round r)))

(defthm df-round-is-identity-for-dfp

; Assume (dfp r), i.e., (rationalp r) and (equal (to-df r) r).  Then by the
; implicit constraints on constrained-to-df generated by the definition of WDF
; (see constrained-to-df), (rational (float r 0.0D0)) = r.  That (WRND r) = r
; follows immediately from [WRND2].

  (implies (dfp r)
           (equal (df-round r)
                  r)))

)
)

(defthm df-round-idempotent

; This follows from df-round-is-identity-for-dfp together with dfp-df-round.

  (equal (df-round (df-round x))
         (df-round x)))

(encapsulate () (logic)

; We do it this way (instead of putting (logic) inside the
; partial-encapsulate), to support redundancy in pass 2.

(partial-encapsulate
 (((constrained-df-rationalize *)  => * :formals (x) :guard (dfp x)))
 (constrained-to-df)

(local (defun constrained-df-rationalize (x)
         (if (dfp x) x 0)))

(defthm rationalp-constrained-df-rationalize
  (rationalp (constrained-df-rationalize x))
  :rule-classes :type-prescription)

(defthm to-df-of-constrained-df-rationalize
; This theorem is justified by the "Notes" in the CL HyperSpec topic:
; http://www.lispworks.com/documentation/HyperSpec/Body/f_ration.htm
  (implies (dfp x)
           (equal (to-df (constrained-df-rationalize x))
                  x)))
)
)

#+acl2-loop-only
(defun binary-df+ (x y)
; This function is defined in raw Lisp in float-raw.lisp, and it is given a
; suitable signature by the call of install-df-basic-primitives below.
  (declare (xargs :mode :logic
                  :guard (and (dfp x)
                              (dfp y))))
  (df-round (+ x y)))

#+acl2-loop-only
(defun unary-df- (x)
; This function is defined in raw Lisp in float-raw.lisp, and it is given a
; suitable signature by the call of install-df-basic-primitives below.
  (declare (xargs :mode :logic
                  :guard (dfp x)))
  (df-round (- x)))

(defthm dfp-minus
  (implies (dfp x)
	   (dfp (- x)))
  :hints (("Goal" :in-theory (enable dfp to-df))))

#+acl2-loop-only
(defun unary-df/ (x)
; This function is defined in raw Lisp in float-raw.lisp, and it is given a
; suitable signature by the call of install-df-basic-primitives below.
  (declare (xargs :mode :logic
                  :guard (and (dfp x)
                              (not (= x 0)))))
  (df-round (/ x)))

#+acl2-loop-only
(defun binary-df* (x y)
; This function is defined in raw Lisp in float-raw.lisp, and it is given a
; suitable signature by the call of install-df-basic-primitives below.
  (declare (xargs :mode :logic
                  :guard (and (dfp x)
                              (dfp y))))
  (df-round (* x y)))

#+acl2-loop-only
(defun binary-df/ (x y)
; This function is defined in raw Lisp in float-raw.lisp, and it is given a
; suitable signature by the call of install-df-basic-primitives below.
  (declare (xargs :mode :logic
                  :guard (and (dfp x)
                              (dfp y)

; It's a wart that the next conjunct uses = rather than df=.  But it's one that
; we believe we can get away with.  If not, then may well be feasible to defer
; the definition of binary-df/ until after df= is introduced.

                              (not (= y 0)))))
  (df-round (/ x y)))

(defconst *df-basic-primitives*

; These functions take or return a :DF.  We overcome potential boot-strapping
; issues with the form (install-df-basic-primitives state) below.  Note that
; the constant *df-primitives* (which is explained in a comment in its defconst
; form) consists of dfp, *df-basic-primitives*, and the function symbols
; introduced by df-function-sigs.

  '((from-df (:df) (nil))
    (to-df (nil) (:df))
    (df-string (:df) (nil))
    (binary-df+ (:df :df) (:df))
    (binary-df* (:df :df) (:df))
    (binary-df/ (:df :df) (:df))
    (unary-df- (:df) (:df))
    (unary-df/ (:df) (:df))))

(defun install-df-basic-primitives-1 (alist wrld)

; At the top level, alist is *df-basic-primitives*.

  (declare (xargs :mode :program))
  (cond ((endp alist) wrld)
        (t (install-df-basic-primitives-1
            (cdr alist)
            (let* ((tuple (car alist))
                   (fn (car tuple))
                   (stobjs-in (cadr tuple))
                   (stobjs-out (caddr tuple)))
              (putprop fn 'stobjs-in stobjs-in
                       (putprop fn 'stobjs-out stobjs-out
                                wrld)))))))

; This development is continued in float-b.lisp, which is processed during the
; boot-strap after set-w is defined in history-management.lisp.  We would
; process the two files as a single file after history-management.lisp, except
; that we need dfp to be defined in remove-guard-holders1.

; Copyright (C) 2023, ForrestHunt, Inc.
; Written by Matt Kaufmann and J Moore
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; Demos of ACL2 support for floating-point operations

;;; TABLE OF CONTENTS
;;; -----------------
;;; "Floats" as rationals
;;; Overflow and underflow
;;; An assertion macro
;;; Df-rationalize and rize
;;; More on dfp & to-df (recognizer & generator for representables)
;;; Fun with pi
;;; No support for complex floats
;;; Examples with defined functions
;;; Examples focused on ec-call
;;; We can't prove much
;;; Df stobj fields
;;; Arrays of double-floats
;;; DO loop$ expressions
;;; FOR loop$ expressions
;;; Stobj-let (nested stobjs)
;;; Using apply$ with dfs, including efficiency issues
;;; Encapsulate and signatures
;;; Memoization
;;; Miscellany
;;; Check consistency with values produced in raw Lisp

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; "Floats" as rationals
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; With the added support for floating point numbers in ACL2, a number i.j is
; interpreted as a double-float (double-precision floating-point number) in raw
; Lisp.  (Technical note: That's because the Common Lisp
; *read-default-float-format* has been set to 'double-float.)

; Logically, ACL2 numbers are all rationals or complex rationals, not floats.
; But it's important to note that in ACL2, raw Lisp evaluation will operate on
; actual double-floats.

; We use the #d prefix (or #D) on a double-float input, F -- that is, we write
; #dF, e.g., #d3.1 -- to indicate the rational value of that double-float,
; which we call a "representable rational" since it is represented by the
; floating-point number indicated by F.  Note that the "d" in "#d" is to
; suggest "double-float" and "decimal", which refers to the notation, not the
; value -- again, the value is the rational number corresponding to the
; double-float following "#d" or "#D".  That double-float has an optional "D"
; or "E" exponent marker (these are equivalent here).  But a "DO" or "E0"
; suffix is required after "#dx" and after "#dx." if x is an integer.

#d3.5 ; 7/2
#d3.1 ; an ugly rational, since 31/10 is not representable

(assert-event
; Each argument is read as the same rational: 3.5 represents the
; rational, 7/2, and #d3.5 means "the rational that is represented by
; 3.5".
 (equal #d3.5 7/2))
(assert-event
; 31/10 is not representable, but every #d number that is read without
; error is representable -- hence the equality below is false.
 (not (equal #d3.1 31/10)))

#d34E0 ; 34 (E0 is required here)

;;; For reason as yet unknown, the following, #d34, seems to cause some input
;;; to be missing during the read of the "Temp lisp file" forms shown in
;;; floating-point-book.cert.out, resulting in an error such as "Global
;;; variables, such as P-RESET-PREHISTORY, are not allowed.".

; #d34 ; Lisp error: 34 is not read as a float, but #d expects a float.

#d123.45E5 ; rational
#d123.45D5 ; same rational as preceding
#d1E50 ; a bigger rational than preceding
(assert-event (equal #d1d50 #d1.0E50)) ; Both are the same rational.
; The following are not quite equal because the latter is not representable.
(assert-event (not (equal #d1d50 (expt 10 50))))

3.1 ; Lisp error -- missing #d prefix

; Floating-point operations in ACL2 operate on representable rationals that are
; considered to be of :df (double-float) type, much as stobj inputs have stobj
; type.  The number returned by any floating-point operation is a representable
; rational that is considered to have :df type, much as stobj-returning
; functions return a value having stobj type.  Below are listed some key
; functions, each with a description that is followed by examples.  Note that
; the result of a :df-returning operation such as to-df is printed using #d
; notation.

; - Dfp is the recognizer for representable rationals.
(dfp 1/4) ; T since 1/4 is representable
(dfp #d0.25) ; T, just as with the preceding, since #d0.25 is read as 1/4
(dfp 1/3) ; NIL since 1/3 is not representable
(dfp 'abc) ; NIL since ABC is not even rational

; - To-df maps a rational number to a close-by representable rational of type
;   :df.  It's implemented in Common Lisp as follows:
;   (to-df x) = (float x 0.0D0).

(to-df 1/4) ; 1/4 is representable; :df returned is #d0.25
(to-df 1/3) ; 1/3 is not representable; we get #d0.3333333333333333

; - From-df maps a :df to its value as a representable rational.
(from-df (to-df #d0.25)) ; 1/4
(from-df (to-df 1/4)) ; 1/4 (same input as the preceding)
(from-df (to-df 1/3)) ; an ugly rational

; Syntax error: the constant 1/4 is not a :df.  However, (from-df 1/4)
; logically equals 1/4, as shown in the thm below.
(from-df 1/4)

(from-df #d0.25) ; same error as preceding, since #d0.25 is read as 1/4

(thm (equal (from-df 1/4) 1/4))

; - To-dfp maps rationals to representable rationals by the composition:
;   (to-dfp x) = (from-df (to-df x)).
(to-dfp 1/4) ; 1/4, since 1/4 is representable
(to-dfp 1/3) ; ugly rational since 1/3 is not representable

; Here are a few more examples.

; First, let's look at a difference in output between calls of to-df and
; to-dfp.  The results are logically equal, but to-df returns a :DF while
; to-dfp returns an ordinary object.  Further comments are below.

; The next form returns a :df, displayed as #d3.1:
(to-df 31/10)

; The next form returns an ugly rational equal to #d3.1:
(to-dfp 31/10)

; We can see the difference in output "types" by looking at the
; signatures of to-df and to-dfp, as follows.  (This also shows the
; guards and output "Type" formulas.)

:args to-df
:args to-dfp

; The phenomenon we see above, of different output for logically equal
; results, is familiar to users using STATE and other stobjs.  Suppose
; we introduce the single-threaded object my-st with one field named
; fld, i.e., (defstobj my-st fld).  Then this is a theorem:

; (thm (equal (and (my-stp my-st) (equal (fld my-st) 'abc))
;             (equal my-st '(abc))))

; [Note: to prove it we need a lemma, and this one suffices:
; (defthm non-nil-true-listp-has-nonzero-len
;   (implies (and (true-listp x) x) (< 0 (len x)))
;   :rule-classes :linear)]

; That is, if my-st is a my-stp and its fld contains ABC then my-st is equal to
; '(ABC).

; But the following sequence of evaluations shows that when we configure the
; live my-st to have fld ABC it prints as <my-st>, not as (ABC), even
; though we (and the theorem prover) know that such a my-st is equal to
; (ABC).

; ACL2 !>(update-fld 'abc my-st)
; <my-st>
; ACL2 !>(and (my-stp my-st) (equal (fld my-st) 'abc))
; T
; ACL2 !>my-st
; <my-st>
; ACL2 !>'(abc)
; (ABC)

; So this live my-st and '(abc) are equal in the session above, but they are
; displayed differently by ACL2 when printed at the top-level.  ACL2 users
; are used to this and now we see this same behavior when using :df objects.
; You'll get used to it.

(assert-event
; Here we see the ugly rational representing the double-float, 3.1.
 (equal #d3.1
        6980579422424269/2251799813685248))
(assert-event ; To-dfp is the identity on representable rationals.
 (equal #d3.1
        (to-dfp #d3.1)))
(assert-event ; 31/10 is not representable, so it is modified by to-dfp
 (not (equal (to-dfp 31/10) 31/10)))

; Recall that the result of a :df-returning operation such as
; to-df is printed using #d notation.  The exponent notation using
; "E" is used when the number is sufficiently large or small in
; magnitude, as per the Common lisp HyperSpec Section 22.3.3.2
; (http://www.lispworks.com/documentation/HyperSpec/Body/22_ccb.htm).

(to-df #d3.1) ; #d3.1 is representable, so to-df preserves value
(to-df 31/10) ; same as preceding, even though 31/10 is not representable
(assert-event (df= (to-df #d3.1) (to-df 31/10)))
(to-df 3100000) ; printed in CCL without E as #d3100000.0
(to-df 31000000) ; printed in CCL with E
(to-df #d1E-3) ; printed in CCL without E
(to-df #d1E-4) ; printed in CCL with E
(to-df 1E-3) ; Lisp error: Lisp sees 1E-3 as a float, so need #d prefix
(assert-event
; Integers are representable rationals, unless they are too big (see
; next section).
 (dfp 3100000))

; Value and value-triple print correctly, by printing a space (by default)
; before the value to indicate that a triple (mv nil _ state) is returned.
; However, value-triple prints the value without using #d notation; think of
; value-triple as returning the logical value without pretending to return a
; double-float (as value does) -- the difference is that (value x) expands to
; (mv nil x state) while (value-triple x) performs a less direct sort of
; evaluation.  Also, note the use of :stobjs-out with value-triple.
(value (to-df 1/4)) ; [space]#d0.25
(value-triple (to-df 1/4)) ; error (needs :stobjs-out argument, as below)
(value-triple (to-df 1/4) :stobjs-out '(:df)) ; [space]1/4
(value-triple (to-df 1/4) :stobjs-out :auto) ; [space]1/4

; Here are examples using the :df operation, df+.  Note that df+
; and other built in "df" operations are actually macros, which
; convert rational constant inputs to have :df type.  Also note
; that, as shown above for to-df, a result of type :df is
; printed using #d notation.

(df+ #d0.5 #d.5) ; #d1.0
(df+ 1/2 1/2) ; same as preceding
(df+ (to-df 1/2) (to-df 1/2)) ; same as preceding
(df+ (to-df #d0.5) (to-df #d.5)) ; same as preceding
(df+ #d.1 #d.2 #d.3) ; df+ is a macro that can take any number of args
(df+ #d.1 (df+ #d.2 #d.3)) ; same as preceding
(df+ (df+ #d.1 #d.2) #d.3) ; DIFFERENT; associativity fails!

; The difference in results for the two examples just above can be summarized
; as follows.
(assert-event
 (not (df= (df+ #d.1 (df+ #d.2 #d.3))
           (df+ (df+ #d.1 #d.2) #d.3))))

(df+ 1/4 1/3) ; error: 1/3 is non-representable constant arg of df+

; The following two examples illustrate that df+ is actually a macro
; that converts each representable rational argument to a df.
; Arguments that are not rational are left alone.  (The example just
; above shows that an error occurs if some argument is a
; non-representable rational, like 1/3.)

; ok
(trans '(df+ 1/4 1/2))

; error (x is not a :df)
(trans '(df+ 1/4 x))

; ok
(trans '(df+ 1/4 (to-df x)))

; Such conversion using to-df is important so that raw-Lisp
; evaluation of df+ calls actually operates on double-floats.  This is
; a somewhat complex implementation issue, not explained further here
; -- just please take away the idea that floating-point numbers are
; not ACL2 objects but things are set up so that "df" operations, such
; as df+, are optimized to do floating-point operations in raw Lisp.

(defmacro identity-macro (x) x)

; syntax error (no conversion of 1/4)
(df+ (identity-macro 1/4) 1/2)

; ok
(df+ (identity-macro (to-df 1/4)) 1/2)

; Our next goal is to assert a failure of associativity discussed
; above, but this time using LET-bindings.  However, first we'll shown
; two ill-formed attempts to do that, as a means to explain why the
; successful example is written the way it is.

; Here is our first attempt to use LET-bindings to show a violation of
; associativity.  It fails because df+ expects its arguments to be of
; type :df -- except that, as illustrated above, numbers are
; converted to type :df by wrapping them in a call of to-df.
; (Also any argument that is a defined constant symbol or a quoted
; rational gets a to-df wrapper.)  No such wrapping occurs for
; variables, however; so in particular, (df+ x y) macroexpands to
; (binary-df+ x y), which is ill-formed because its arguments are
; ordinary objects rather than of :df type.
(let ((x #d.1)
      (y #d.2)
      (z #d.3))
  (not (equal (df+ (df+ x y) z)
              (df+ x (df+ y z)))))

; It doesn't help to declare the let-bound variables to be double-float,
; because #d.1 is really a rational.
(let ((x #d.1)
      (y #d.2)
      (z #d.3))
  (declare (type double-float x y z))
  (not (equal (df+ (df+ x y) z)
              (df+ x (df+ y z)))))

; Here is our second attempt to use LET-bindings to show a violation
; of associativity.  It fixes the problem from the preceding input by
; applying to-df in each binding, so that each bound variable is
; seen to have :df type.  But it still causes an error, because
; equal expects arguments that represent ordinary objects, yet here
; the arguments of equal are of type :df because they are produced
; by df+.
(let ((x (to-df #d.1))
      (y (to-df #d.2))
      (z (to-df #d.3)))
  (not (equal (df+ (df+ x y) z)
              (df+ x (df+ y z))))) ; error

(assert-event
; Here we finally succeed in our assertion of the failure of
; associativity, fixing the problems illustrated by the two preceding
; attempts.  We fix the first of those two attempts by applying to-df
; in the bindings, as explained just above.  We fix the second
; attempt, accommodating the fact that equal accepts only ordinary
; arguments, not :dfs, by applying from-df to each argument of equal.
; From-df is logically the identity function, but maps a :df (whose
; value is a representable rational) to an ordinary object (that
; rational).
 (let ((x (to-df #d.1))
       (y (to-df #d.2))
       (z (to-df #d.3)))
   (not (equal (from-df (df+ (df+ x y) z))
               (from-df (df+ x (df+ y z)))))))

; But here's a better way: replace equal by df=.
(assert-event
 (let ((x (to-df #d.1))
       (y (to-df #d.2))
       (z (to-df #d.3)))
   (not (df= (df+ (df+ x y) z)
             (df+ x (df+ y z))))))

(assert-event
; Here is another alternative, though arguably uglier, for making a
; syntactically correct version of the assertion.
 (let ((x #d.1)
       (y #d.2)
       (z #d.3))
   (not (equal (from-df (df+ (df+ (to-df x) (to-df y))
                             (to-df z)))
               (from-df (df+ (to-df x)
                             (df+ (to-df y) (to-df z))))))))

(thm
; Here we prove the preceding failure of associativity.  We can omit
; the from-df and to-df calls, because syntax checking for
; :dfs is relaxed in theorems just as it is relaxed for stobjs.

; Note that, at least initially, the ONLY things that can be proved
; about floating point expressions are (a) things proved by
; evaluation, as in this case, (b) things (like substitutivity) that
; can be proved about any function (even a constrained function), and
; (c) type theorems, e.g., that df+ yields a dfp.  As the need arises
; we may add explicit constraints that allow more properties of
; floating-point operations to be proved -- but not associativity of
; df+!

 (let ((x #d.1) (y #d.2) (z #d.3))
   (not (equal (df+ (df+ x y) z)
               (df+ x (df+ y z))))))

(df+ #d.1 #d.2 #d.3) ; df+ can take 0 or more arguments

; Here's the left-associated version of the right-associated expression above,
; as shown previously above, isn't equal to it.

(df+ (df+ #d.1 #d.2) #d.3)

(trans
; Here we see macroexpansion of a df+ call on more than two arguments.
; Hopefully we won't see ugly rationals too much since unlike :trans,
; evaluation results will generally print :dfs in #d notation, as
; shown above.
 '(df+ #d.1 #d.2 #d.3))

(assert-event ; every #d number is representable
 (and (dfp #d.1) (dfp #d.2) (dfp #d.3) (dfp #d3.1)))
(defmacro dfp* (&rest rst)
  `(and ,@(pairlis-x1 'dfp (pairlis$ rst nil))))
(assert-event ; same as preceding: dfp* is conjunction of iterated dfp
 (dfp* #d.1 #d.2 #d.3 #d3.1))
(thm ; FAILS to prove
; This must fail to prove, given the df+ example falsifying
; associativity of df+ presented earlier above.  Of course, even valid
; properties of floating-point operations are generally unprovable by
; ACL2, at least initially, as noted earlier above.
 (implies (dfp* x y z)
          (equal (df+ (df+ x y) z)
                 (df+ x (df+ y z)))))

(assert-event
; Some review.  To-dfp maps a rational to a (nearby) representable
; rational.  The predicate dfp recognizes representable rationals.  We
; use to-dfp instead of the logically equivalent to-df below to
; avoid a syntax violation: both arguments of a call of equal must be
; ordinary objects, which is what to-dfp returns, but to-df returns
; a :df.
 (let ((r (to-dfp 1/3)))
   (and (dfp r)
        (equal r 6004799503160661/18014398509481984))))

(thm ; ok to use to-df, as :df syntax checks are off in theorems
 (let ((r1 (to-df 1/3))
       (r2 (to-dfp 1/3)))
   (and (dfp* r1 r2)
        (equal r1 r2)
        (equal r1 6004799503160661/18014398509481984))))

; error: syntax violation since equal does not take a :df
(assert-event
 (equal (to-df 1/2) 1/2))

(assert-event ; ok (fixes preceding syntax error)
 (equal (from-df (to-df 1/2)) 1/2))
(assert-event ; equivalent to the preceding input
 (equal (to-dfp 1/2) 1/2))
(thm ; OK: Syntactic handling of :df types is relaxed for theorems.
 (equal (to-df 1/2) 1/2))

; Much like stobj recognizers, dfp may be applied either to ordinary
; objects or to :dfs, as shown in the following two examples.
(assert-event
; dfp applied to :df
 (dfp (to-df 1/3)))
(assert-event
; dfp applied to ordinary object
 (dfp (to-dfp 1/3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Overflow and underflow
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Overflow and underflow are possible.  Note that we can get errors;
; we don't try to guard against them.  There is precedent; there is
; nothing wrong logically with (natp (ash 1 100000000000000)), but
; this can cause an error for ACL2 (as observed with CCL, SBCL, and
; GCL builds).

#d1E310 ; Lisp error (overflow)

#d1E-500 ; 0 (underflow)
(to-df #d1E-500) ; #d0.0 (underflow)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; An assertion macro
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro a-e (x &key hints)

; This macro, used below, checks that x is non-nil both by direct
; evaluation and with proof.

  `(with-output :off :all :gag-mode nil
     (progn (assert-event ,x)
            (thm ,x ,@(and hints `(:hints ,hints)))
            (value-triple :success))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Df-rationalize and rize
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Values of df expressions can be unpleasant to read when printed as rationals.
; Df-rationalize and rize can make those unpleasant rationals prettier.

(defconst *df{1/3}*
; This is a representable rational obtained by coercing 1/3 to a
; floating-point number.
  (to-dfp 1/3))

*df{1/3}* ; ugly rational

(dfp *df{1/3}*) ; T because to-dfp returns a representable rational


:pe from-df ; From-df is logically the identity.
:pe to-dfp ; To-dfp and to-df are logically equivalent.

(to-df 1/3) ; :df version of (to-dfp 1/3), i.e., of *df{1/3}*
(thm (equal *df{1/3}* (to-df 1/3)))
(equal *df{1/3}* #d0.3333333333333333) ; consistent with results above
       
; Df-rationalize maps a :df to a "nice" rational that approximates
; that df.
(to-df 1/3) ; again, :df that approximates 1/3
(from-df (to-df 1/3)) ; ugly representable rational
(to-dfp 1/3) ; same as preceding
(thm (equal (to-df 1/3) ; Rational representation is on next line.
            6004799503160661/18014398509481984))

; We have seen above that the rational value of (to-df 1/3) is
; 6004799503160661/18014398509481984.  Here we use df-rationalize to
; map that ugly rational to 1/3.
(df-rationalize
 (to-df 1/3)) ; result is 1/3

; Rize applies df-rationalize after converting to a nearby df.
:pe rize
(rize 1/3) ; 1/3; equivalent to (df-rationalize (to-df 1/3)) above

*df{1/3}* ; again, ugly rational
(rize
; Yields 1/3; much less ugly than the rational value of *df{1/3}*!
; Note that the result, 1/3, is not representable.  Both
; df-rationalize and rize can produce non-representable rationals.
 *df{1/3}*)

(a-e
; At least in this case, rize behaves well, mapping a representable
; rational to a rational approximated by that rational (i.e., mapping
; back to the given rational using to-dfp).  This is a general
; phenomenon; see the CL HyperSpec
; (http://www.lispworks.com/documentation/HyperSpec/Body/f_ration.htm),
; which says: "(float (rationalize x) x) == x".
 (equal (to-dfp (rize *df{1/3}*))
        *df{1/3}*))

:pe to-dfp-of-rize ; explains preceding result; may go into a book

(a-e ; some summary observations
 (and (not (dfp 1/3)) ; 1/3 is not representable
      (dfp *df{1/3}*) ; *df{1/3}* is representable (output of to-dfp)
      (not (equal 1/3 *df{1/3}*))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; More on dfp & to-df (recognizer & generator for representables)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

:pe dfp ; recognizes rationals representable as double-float
:pe dfp-to-df ; to-df returns representable rational

(a-e (equal (dfp 1/4) t)) ; 1/4 is representable
(a-e (equal (dfp 1/3) nil)) ; 1/3 is not representable
(a-e ; to-df maps a rational to one that's representable
 (equal (dfp (to-df 1/3)) t))
(thm (equal (to-df 'abc) 0)) ; default guard-violating behavior

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Fun with pi
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Since every ACL2 number is a rational (or complex rational), *df-pi*
; is too -- it's not a Lisp float.  In fact no ACL2 constant (defined
; by defconst) can be of type :df.  That explains why *df-pi* is
; defined by applying from-df to the term (df-pi), where df-pi returns
; a :df.

:pe *df-pi* ; (defconst *df-pi* (from-df (df-pi)))

(defconst *2pi*
; See also df-2pi.  This is a rational approximation to 2*df-pi.  Note
; that *df-pi* is already defined as a rational approximation to pi.
; Both *df-pi* and *2pi* are ordinary objects, not dfs; defconst
; always creates an ordinary object.
  (* 2 *df-pi*))

; Signature shows return of :DF in the following.
(defun-inline df-2pi ()
; See also *2pi*.  Here, however, we return a :df (which is a
; double-float in raw Lisp) rather than an ordinary object.  Note that
; since (df-pi) is representable, multiplying it by 2 produces a
; representable rational as well (since that multiplication keeps the
; mantissa and simply doubles the small exponent).
  (df* 2 (df-pi)))
:pe df-2pi
:args df-2pi$inline

(a-e
; This holds since *df-pi* = (df-pi) and (df-2pi) is just the exact
; product by 2 of (df-pi), as noted above.
 (equal *2pi* (from-df (df-2pi))))

; Let's look at the logically equal values of *2pi* and (df-2pi).
; These differ only in their "types": the former is an ordinary value,
; while the latter is a :df, i.e., the signature of df-2pi is
; ((df-2pi) => :DF).
*2pi* ; 884279719003555/140737488355328
(df-2pi) ; #d6.283185307179586

(rize
; Here is a less precise, somewhat more readable rational
; approximation (but still kind of ugly: 411557987/65501488), using
; the function rize, which is based on the Common Lisp function
; rationalize that maps a float to a less "large" rational that still
; maps to that float.  Unlike df-rationalize (the ACL2 version of
; rationalize), rize takes an ordinary object as input rather than a
; :df.
 *2pi*)

; Those rationals both map to the same double-float.
(a-e (equal (to-dfp *2pi*) (to-dfp (rize *2pi*))))

(to-df *2pi*) ; #d6.283185307179586

(assert-event
; For any rational x (e.g., *2pi*), (rize x) produces a rational that,
; while often not representable, does map to the same float as x (as
; noted earlier above with :pe to-dfp-of-rize).  We use to-dfp instead
; of to-df because the output of to-df is a :df, not suitable
; as an argument to EQUAL.
 (equal (to-dfp (rize *2pi*)) *2pi*))

(thm
; As above, except that in theorems we can use :df values freely,
; thanks to the same relaxation of syntax checking as for stobjs.
 (equal (to-df (rize *2pi*)) *2pi*))

(df-sin (df-2pi)) ; very near 0, but not 0 (floating-point sin is not exact)
(df-rationalize (df-sin (df-2pi))) ; prettier version
(dfp (df-sin (df-2pi))) ; rational from df-sin is always representable

; For the following, note that df-sin is a macro that converts a representable
; rational constant argument to the corresponding :df.  The intention is that
; df-sin (as with other df-xx operators) can be used like a function without
; understanding the roles of df-sin-fn (in general, df-xx-fn) and to-df?.
(df-sin *2pi*)
:pe df-sin

; ok; returns a :df
(trans '(to-df *2pi*))

(a-e
; We next want to define pi/6.  We could use rational division just as
; we used rational multiplication (by 2) for 2*pi, but here we see
; that the result wouldn't be representable.
 (not (dfp (/ *df-pi* 6))))

(a-e
; Fortunately, when converting after rational division, we get the
; same representable rational as when we use double-float division.
; One might think that such an equality always holds, and probably
; it does [implementor note: requires more thought]; for example, try
; experiments like the following in raw Lisp and see T as the result.
;   (loop for i from 1 to 10000000000 by 2371
;         always
;         (equal (to-dfp (/ *df-pi* i))
;                (from-df (df/ *df-pi* (to-df i)))))
 (equal (to-dfp (/ *df-pi* 6)) ; converting after rational division
        (from-df (df/ *df-pi* 6))))

(defconst *pi/6*
  (to-dfp (/ *df-pi* 6)))

(df-sin *pi/6*) ; very close to 1/2, but not exactly
(df-rationalize (df-sin *pi/6*)) ; sadly, still not 1/2; but close
(assert-event ; But in fact, (df-sin *pi/6*) is very close to 1/2.
 (let ((x (df-rationalize (df-sin *pi/6*))))
   (equal (denominator x)
          (1+ (* 2 (numerator x))))))

(df-sqrt 2) ; #d1.4142135623730951
(df* (df-sqrt 2) (df-sqrt 2)) ; #d2.0000000000000004
(a-e ; Look how close to 2 we got with the preceding result!
 (equal (- (from-df (df* (df-sqrt 2) (df-sqrt 2)))
           (/ 2251799813685248))
        2))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; No support for complex floats
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(to-df #c(0 1)) ; guard violation (expects a rational)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Examples with defined functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;## Example 1: signature (F1-FN :DF) => :DF

;The signature shows a return of :DF in the following.
(defun f0 (x)
; Note that a double-float type declaration is treated like :stobjs in
; how it contributes to the input signature.  A double-float type
; declaration for x generates a guard of (dfp x).  Recall that a type
; declaration causes guard verification by default; here, we defeat
; guard verification by using :verify-guards nil (we'll verify guards
; later below).  IMPORTANT: In raw Lisp, the df- call below will be
; made on a true double-float.  This fact evidences support for
; efficient execution.
  (declare (xargs :verify-guards nil)
           (type double-float x))
  (df- x))
:args f0

; error: need a :df input
(f0 3)

; same error as just above, since #d3.0 is read as 3
(f0 #d3.0)

; ok
(f0 (to-df 3))

; There is a handy way to allow rational automatically declare arguments to be
; double-floats while allowing rational, dfp inputs: use defun-df.  WARNING:
; The defun-df shortcut is only appropriate when all formals are :DFs and the
; output is a :DF, and it (deliberately) hides the need to pass :DF arguments
; to :DF operations, for example by converting 3 to (to-df 3) as noted in the
; use of :trans* below.

(defun-df f1 (x)
  (declare (xargs :verify-guards nil))
  (df- x))
(f1 3)
(f1 (to-df 3))

; Here we see how in (f1 3), 3 is automatically converted to a :DF.
:trans* t (f1 3)

; The following causes an error: x is not a constant, so to-df is needed, not
; merely to-df?.
(trans '(f1 x))

(trans '(f1 (to-df x))) ; ok

; Let's see that numbers are converted efficiently to dfs in raw Lisp.
; (Note that to-df is inlined, so (to-df 3) should be evaluated at
; compile time.)
(set-raw-mode-on!)
(values (macroexpand '(f1 3)))
(set-raw-mode nil)

(assert-event
; This is a syntax error since f1 returns a :df, yet equal expects
; ordinary objects as arguments.  This would be like using equal on a
; stobj.
 (equal (f1 3) -3))

(df= (f1 3) -3) ; OK since the macro df= converts -3 to the value of (to-df -3)
(thm (equal (f1 3) -3)) ; ok (thm relaxes thm syntax checks)
(assert-event (equal (from-df (f1 3)) -3))

; Now verify guards and then try the three tests above again.

; Clean error: Can't use macro-alias in verify-guards.
(verify-guards f1)

; ok:
(verify-guards+ f1)

(thm (equal (f1 3) -3))

(assert-event (equal (from-df (f1 3)) -3))

;## Example 2: signature (F2-FN :DF) => *

; The next Generated defun has a double-float type declaration
; and has signature (F2-FN :DF) => *.
(defun-df f2 (x)
; This is like f1, except that it returns an ordinary object (a
; rational).
  (declare (xargs :verify-guards nil))
  (from-df (df- x)))

:pe f2

:args f2-fn

(a-e
; [Implementor note, but needs thought: I think this is guaranteed by
; the IEEE spec, since 3 is representable and hence df- operates
; exactly on it.]
 (equal (f2 3) -3))
(a-e (equal (f2 #d3.0) #d-3.0)) ; equivalent to preceding

; Now verify guards and then try the two tests above again.
(verify-guards f2-fn)

(a-e (equal (f2 3) -3))

(a-e (equal (f2 #d3.0) #d-3.0))

;## Example 3: signature (F3 *) => :DF

; The signature shows return a of :DF in the following.
(defun f3 (x)
; This time the guard is (rationalp x), so this function takes a
; rational, not a :df.  But it returns a :df.
  (declare (xargs :guard (rationalp x)))
  (df- (to-df x)))
:args f3

(f3 30000000) ; #d-3.0E+7

(thm (equal (f3 30000000) -30000000))

;## Example 4: signature (F4 *) => *

(defun f4 (x)
; As above, but we return an ordinary rational, not a :df.
  (declare (xargs :guard (rationalp x)))
  (from-df (df- (to-df x))))

(a-e (equal (f4 3) -3))

;## Example 5: Using df+ and df* on more than two arguments,
;              where function parameters are rational.

(defun f5 (x y z)

; This definition represents a trivial version of what may become a
; common computing paradigm.  One passes in rationals at the top
; level, perhaps satisfying dfp; these are then converted to dfs so
; that all computations can be done efficiently with floating-point
; arithmetic; and finally (perhaps), the result is converted back to a
; rational number.

  (declare (xargs :guard (dfp* x y z) :verify-guards nil))
  (from-df (let ((x (to-df x))
                 (y (to-df y))
                 (z (to-df z)))
             (df* (df+ x y z)
                  #d2.0
                  5))))

(a-e ; Note that inputs are rationals and output is rational.
 (equal (f5 #d0.25 #d0.50 #d0.75)
        15))
(verify-guards+ f5)
(a-e ; Still OK after guard verification
 (equal (f5 #d0.25 #d0.50 #d0.75)
        15))

;## Example 6: Type errors

; The following is an error because the guard conjunct (rationalp x) is
; generated from (type rational x), yet x is a :df from the double-float type
; declaration.

(defun bad (x)
  (declare (type double-float x)
           (type rational x))
  x)

;;; The rest of this section discussions the use of THE and type-declarations.

; We have seen declarations (type double-float ...) at the top level of
; definitions.  Here we explore their use in let-bindings, along with (the
; double-float ...) expressions.

; The following definition fails because ACL2 guesses, from the binding of y to
; (g (cdr x)), that g returns an ordinary value, not a :DF.  (That guess is
; wrong, and at some point ACL2 might be improved to avoid this error.)  Below
; we should several ways around this problem.
(defun g (x)
  (if (consp x)
      (let ((y (g (cdr x))))
        (df+ (to-df (car x)) y))
    (df0)))

; One solution is to declare y to be of double-float type, which tells ACL2
; that y should be treated as a :DF.
(defun g0 (x)
  (if (consp x)
      (let ((y (g0 (cdr x))))
        (declare (type double-float y))
        (df+ (to-df (car x)) y))
    (df0)))

; An alternate solution is to use a THE form on the expression to which y is
; bound.
(defun g1 (x)
  (if (consp x)
      (let ((y (the double-float (g1 (cdr x)))))
        (df+ (to-df (car x)) y))
    (df0)))

; Yet another solution is simply to switch the two branches of the IF call.
; This causes ACL2 to deduce that g2 returns a :DF before translating the LET
; subexpression.
(defun g2 (x)
  (if (atom x)
      (df0)
    (let ((y (g2 (cdr x))))
      (df+ (to-df (car x)) y))))

; Each of g0, g1, and g2 returns a df:
(assert-event (and (equal (stobjs-out 'g0 (w state)) '(:df))
                   (equal (stobjs-out 'g1 (w state)) '(:df))
                   (equal (stobjs-out 'g2 (w state)) '(:df))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Examples focused on ec-call
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; See the comments in ACL2 source function ec-call1-raw-dfs if
; you are interested in the implementation challenge presented by
; ec-call.

; The following causes an error simply because df- is a macro.
(defun f6 (x)
  (declare (xargs :guard (rationalp x)))
  (ec-call (df- (to-df x))))

; The following causes an error because when a :df is returned, a :dfs
; argument to ec-call is required.
(defun f6 (x)
  (declare (xargs :guard (rationalp x)))
  (ec-call (unary-df- (to-df x))))

; The following fails because the :dfs argument should be '(t).
(defun f6 (x)
  (declare (xargs :guard (rationalp x)))
  (ec-call (unary-df- (to-df x))
           :dfs '(nil)))

; The following fails because the :dfs argument must be quoted.
(defun f6 (x)
  (declare (xargs :guard (rationalp x)))
  (ec-call (unary-df- (to-df x))
           :dfs (t)))

; The following fails because the :dfs argument specifies the wrong
; number of outputs.
(defun f6 (x)
  (declare (xargs :guard (rationalp x)))
  (ec-call (unary-df- (to-df x))
           :dfs '(t nil)))

; The following succeeds.
(defun f6 (x)
  (declare (xargs :guard (rationalp x)))
  (ec-call (unary-df- (to-df x))
           :dfs '(t)))

; Try running in the top-level loop.

(f6 7/2)

; The following is quite subtle, and should be ignored by those who do
; not use raw-mode.  As explained at the top of this section, the use
; of ec-call with :dfs is intended to cause the return of actual
; double-floats in raw Lisp.  That is what we illustrate here.

(set-raw-mode-on!)
(f6 7/2) ; -3.5, a double-float
(set-raw-mode nil)

; This is like f6, but without guard verification.
(defun f6-ideal (x)
  (declare (xargs :guard (rationalp x) :verify-guards nil))
  (ec-call (unary-df- (to-df x))
           :dfs '(t)))

(f6-ideal 7/2)

; This is like f6, but with :program mode.
(defun f6-prog (x)
  (declare (xargs :guard (rationalp x) :mode :program))
  (ec-call (unary-df- (to-df x))
           :dfs '(t)))

(f6-prog 7/2)

; Let's call all three of those in a :program mode function and see if
; that works as expected.

(defun f7 (x)
  (declare (xargs :mode :program))
  (mv (f6 x) (f6-ideal x) (f6-prog x)))

; We expect each of the three functions -- f6, f6-ideal, and f6-prog
; -- to return a :DF, because of their use of the :dfs argument of
; ec-call.  So f7 should produce an mv of three :DF values.

(f7 7/2) ; an mv of three :DF values, (#d-3.5 #d-3.5 #d-3.5)

; Let's get a bit crazy.

(defun f8 (x)
  (declare (xargs :mode :program))
  (ec-call (f7 x)
           :dfs '(t t t)))

(f8 7/2) ; as for f7: mv of three :DF values, (#d-3.5 #d-3.5 #d-3.5)

; As for f7, the following is a bit subtle.  In short, the raw-Lisp
; version of f8 returns three double-float values.
(set-raw-mode-on!)
(f8 7/2) ; an mv of three double-float values, (-3.5 -3.5 -3.5)
(set-raw-mode nil)

(defun f9 (x)
  (declare (xargs :mode :program
                  :guard (rationalp x)))
  (mv-let (a b c)
    (f8 x)
    (df+ a b c)))

(f9 7/2)

(verify-termination f6-prog)
(verify-termination f7)
(verify-termination f8)

(verify-termination f9
  (declare (xargs :verify-guards nil)))

(f9 7/2)

; Error: Need to quote the :dfs argument.
(defun f8-logic (x)
  (declare (xargs :guard (rationalp x)))
  (ec-call (f7 x)
           :dfs (t t t)))

(defun f8-logic (x)
  (declare (xargs :guard (rationalp x)))
  (ec-call (f7 x)
           :dfs '(t t t)))

(f8-logic 7/2)

(defun f9-logic (x)
  (declare (xargs :guard (rationalp x)))
  (mv-let (a b c)
    (f8-logic x)
    (df+ a b c)))

(f9-logic 7/2)

(set-guard-checking nil)

(f7 7/2)
(f8 7/2)
(f9 7/2)
(f8-logic 7/2)
(f9-logic 7/2)

(set-guard-checking :all)

(f7 7/2)
(f8 7/2)
(f9 7/2)
(f8-logic 7/2)
(f9-logic 7/2)

(set-guard-checking :none)

(f7 7/2)
(f8 7/2)
(f9 7/2)
(f8-logic 7/2)
(f9-logic 7/2)

(set-guard-checking t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; We can't prove much
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We can prove things about floating-point numbers, but rather little about
; computations with them.

; Here are some simple theorems.

(thm (dfp (to-df x)))
(thm (equal (dfp x)
            (and (rationalp x)
                 (equal (to-df x) x))))
(thm (dfp (df+ x y z)))
(thm (dfp (df- x)))
(thm (dfp (df/ x y)))

; These fail -- there are no completion axioms analogous to axioms like
; completion-of-+.  There probably could be, but given the single-threadedness
; tracking and likely ubiquity of dfp assumptions, and the chance that we'd be
; able to prove something like (equal (binary-df+ 4 1/3) 4) since 1/3 doesn't
; satisfy dfp, it seems best to leave well enough alone here.
(thm (equal (df+ 'apple 3) 0))

; In the following, the checkpoint contains the term (* 0 X), which is perhaps
; surprising.  But it comes from (/ x 0), which essentially translates to (* x
; (/ 0)), which turns into (* 0 x).
(thm (equal (df/ x 0) 0))

; Here's a pair of nice theorems, justified by the CL HyperSpec
; (http://www.lispworks.com/documentation/HyperSpec/Body/f_ration.htm).

(thm (implies (dfp x)
              (equal (to-df (from-df x))
                     x)))

(thm (implies (dfp x)
              (equal (to-df (df-rationalize x))
                     x)))

(thm ; succeeds
 (implies (dfp* x y) ; (and (dfp x) (dfp y))
          (equal (df+ x y) (df+ y x))))

(thm
; FAILS!  We showed a counterexample earlier (and noted earlier above
; that even valid properties about floating-point operations will not
; be provable by ACL2, at least initially).
 (implies (dfp* x y z)
          (equal (df+ x y z) (df+ (df+ x y) z))))

(thm ; succeeds
 (implies (and (dfp x)
               (not (equal x 0)))
          (equal (df/ x x) 1)))

(assert-event (not (equal (df-rationalize (df/ 1 3))
                          (from-df (df/ 1 3)))))

(thm ; succeeds (see assert-event just above)
 (let ((x (from-df (df/ 1 3))))
   (not (implies (rationalp x)
                 (equal x (df-rationalize (to-df x)))))))

(thm
; FAILS: The preceding thm provides a counterexample.
 (implies (rationalp x)
          (equal x (df-rationalize (to-df x)))))

(thm ; succeeds (as for df-rationalize)
 (let ((x (from-df (df/ 1 3))))
   (not (implies (rationalp x)
                 (equal x (rize (to-dfp x)))))))

(thm
; FAILS: The preceding thm provides a counterexample.
 (implies (rationalp x)
          (equal x (rize (to-dfp x)))))

(thm
; Here we prove trichotomy for double-floats.
; The CL HyperSpec says (at
; http://www.lispworks.com/documentation/HyperSpec/Body/f_eq_sle.htm)
; that numbers are compared according to their values.  The value of a
; floating-point number is the corresponding rational number, so since df< and
; df= are logically just < and = (respectively), we get trichotomy.
 (implies (dfp* x y)
          (or (df< x y)
              (df< y x)
              (df= x y))))

; The THM below fails to prove, which is a good thing given the following two
; examples.
(df+ #d.1 #d.2 #d.3) ; #d0.6 in CCL
(df+ #d.3 #d.2 #d.1) ; #d0.6000000000000001 in CCL
(thm ; Fails to prove, as noted above.
 (equal (df+ x y z) (df+ z y x)))

; Let's look at the checkpoint from the THM just above.  Note that
; checkpoint-list, below, returns a list of checkpoints.  Here there is a
; single checkpoint,, which is a single literal, an equality..

(include-book "kestrel/utilities/checkpoints" :dir :system)

(assert-event
 (equal (checkpoint-list t state)
        '(((EQUAL (DF-ROUND (BINARY-+ X (DF-ROUND (BINARY-+ Y Z))))
                  (DF-ROUND (BINARY-+ Z (DF-ROUND (BINARY-+ X Y)))))))))

#|
(EQUAL (DF-ROUND (+ X (DF-ROUND (+ Y Z))))
       (DF-ROUND (+ Z (DF-ROUND (+ X Y)))))
|#

; Finally, here are some simple theorems that prove automatically about
; rational operations on dfs.

(thm (df= (df+ x 'bad) (df+ x 0)))
(thm (implies (dfp x)
              (df= (df+ x 'bad) x)))
(thm (implies (dfp x) (df= (df+ x (df- x)) 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Df stobj and hash-table fields
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj st1
  (accum :type double-float :initially 0))

(assert-event (df= (accum st1) 0))

(update-accum (to-df 3) st1)

(assert-event (df= (accum st1) 3))

(defstobj st2
  (ht :type (hash-table eql 70 double-float) :initially 0))

(defun f10 (key st2)
  (declare (xargs :stobjs st2
                  :guard (eqlablep key)))
  (ht-get key st2))

(assert-event (df= (f10 'a st2) 0))

(ht-put 'b (to-df 1/3) st2)

(assert-event (df= (f10 'a st2) 0))

(assert-event (df= (f10 'b st2) (to-df 1/3)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Arrays of double-floats
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj st3
; Here is an array of double-floats.  The implementation will, as
; usual, take into account the array element type (here, double-float)
; when reading or writing the array, by generating suitable type
; declarations.
; NOTE: It may be that code runs faster (but using more space) if the raw Lisp
; array is declared to have elements of type t instead of type double-float.
; Such a change might be considered in the future.
  (ar :type (array double-float (8)) :initially 0))

(defun load-ar (i max lst st3)
; Update the ar field of st3 with the values in lst, starting at position i.
  (declare (xargs :stobjs st3
                  :guard (and (rational-listp lst)
                              (natp i)
                              (= (+ i (length lst)) (ar-length st3))
                              (integerp max)
                              (<= i max)
                              (<= max (ar-length st3)))
                  :measure (nfix (- (ar-length st3) i))))
  (if (mbt (and (natp i) (integerp max) (<= i max)
                (<= max (ar-length st3))
                (rational-listp lst)))
      (if (< i max)
          (let ((st3 (update-ari i (to-df (car lst)) st3)))
            (load-ar (1+ i) max (cdr lst) st3))
        st3)
    st3))

(load-ar 0 8 (list 3 0 *df-pi* 3/4 -2/3 5 -6 7) st3)

(assert-event (and (= (from-df (ari 2 st3)) *df-pi*)
                   (= (from-df (ari 6 st3)) -6)
                   (df= (ari 6 st3) -6)
                   (df< (ari 0 st3) 5)))

(thm (let ((st3 (load-ar 0 8 (list 3 0 *df-pi* 3/4 -2/3 5 -6 7) st3)))
       (and (= (from-df (ari 2 st3)) *df-pi*)
            (= (from-df (ari 6 st3)) -6)
            (df= (ari 6 st3) -6)
            (df< (ari 0 st3) 5)))
     :hints (("Goal" :expand (:free (i max lst st3)
                                    (load-ar i max lst st3)))))

(defthm dfp-nth-arp
; a useful lemma
  (implies (and (arp ar)
                (natp i)
                (< i (len ar)))
           (dfp (nth i ar))))

; We can read dfs and update with dfs.
(defun scalar-multiply-ar (i mult st3)
  (declare (xargs :stobjs st3
                  :guard (and (natp i) (<= i 8)))
           (type double-float mult))
  (cond ((zp i) st3)
        (t (let* ((i (1- i))
                  (old (ari i st3))
                  (st3 (update-ari i (df* mult old) st3)))
             (declare (type double-float old))
             (scalar-multiply-ar i mult st3)))))

(defun scalar-multiply-ar-example (st3)
   (declare (xargs :stobjs st3))
   (scalar-multiply-ar 4 (to-df 4) st3))

(load-ar 0 8 (list 3 0 *df-pi* 3/4 -2/3 5 -6 7) st3)

(scalar-multiply-ar-example st3)

(assert-event (and (= (from-df (ari 2 st3)) (* 4 *df-pi*))
                   (= (from-df (ari 6 st3)) -6)
                   (df= (ari 6 st3) -6)
                   (df< (ari 0 st3) 20)))

(load-ar 0 8 (list 3 0 *df-pi* 3/4 -2/3 5 -6 7) st3)

(scalar-multiply-ar 8 (to-df 4) st3)

(assert-event (and (= (from-df (ari 2 st3)) (* 4 *df-pi*))
                   (= (from-df (ari 6 st3)) -24)
                   (df= (ari 6 st3) (to-df -24))
                   (df< (ari 0 st3) (to-df 20))))

; The following caused an error at one time (technical note: because
; *1* functions didn't handle coerce inputs to dfs in the
; invariant-risk case, which is now done near the end of the
; definition of oneify).

(defstobj st-b-x
  (b :type (array double-float (10))
     :initially #d0.0)
  (x :type (array double-float (10))
     :initially #d0.0))

(defun st-b-x-fn (i st-b-x)
  (declare (xargs :stobjs (st-b-x)
                  :mode :program)
           (type (unsigned-byte 30) i))
  (let* ((b (df1))
         (st-b-x (update-xi i (df- b (df1)) st-b-x)))
    st-b-x))

(st-b-x-fn 2 st-b-x)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; DO loop$ expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The first example below is similar to the one above, except that it modifies
; the stobj array using a DO loop$ expression.

(include-book "projects/apply/top" :dir :system)

(defwarrant update-ari)

(defthm arp-update-nth
  (implies (and (arp ar)
                (natp i)
                (< i (len ar))
                (dfp val))
           (arp (update-nth i val ar))))

(defun load-ar-loop (lst st3)
  (declare (xargs :stobjs st3
                  :guard (and (rational-listp lst)
                              (<= (length lst) (ar-length st3)))))
  (loop$ with i = 0
         with tmp = lst
         do
         :values (st3)
         :measure (len tmp)
         :guard (and (rational-listp tmp)
                     (st3p st3)
                     (natp i)
                     (<= (+ i (len tmp))
                         (ar-length st3)))
         (if (atom tmp)
             (return st3)
           (progn (setq st3 (update-ari i (to-df (car tmp)) st3))
                  (setq tmp (cdr tmp))
                  (setq i (1+ i))))))

(load-ar-loop (list 10 11 12 13 14 15 16 17) st3)

(assert-event (and (= (from-df (ari 2 st3)) 12)
                   (= (from-df (ari 6 st3)) 16)
                   (df= (ari 6 st3) 16)
                   (df< (ari 0 st3) 11)))

; The next two examples use dfs that are not extracted from stobj arrays.

(defun f11 (lst)
  (declare (xargs :guard (rational-listp lst)))
  (loop$ with temp = lst
         with  ans of-type double-float = (to-df 0)
         do
         :values (:df)
         :guard (rational-listp temp)
         (cond ((endp temp) (return ans))
               (t (progn (setq ans (df+ (to-df (car temp)) ans))
                         (setq temp (cdr temp)))))))

(assert-event (df= (f11 '(3 1/2 4)) #d7.5))

(defun f12 (lst)
  (declare (xargs :guard t :verify-guards nil))
  (loop$ with temp = lst
         with  ans of-type double-float = (to-df 0)
         do
         :values (:df nil)
         (cond ((atom temp) (return (mv ans temp)))
               (t (progn (setq ans (df+ (to-df (rfix (car temp))) ans))
                         (setq temp (cdr temp)))))))

(assert-event (mv-let (x y)
                (f12 '(3 1/2 4 . a))
                (and (df= x #d7.5)
                     (eq y 'a))))

(thm (mv-let (x y)
       (f12 '(3 1/2 4 . a))
       (and (df= x #d7.5)
            (eq y 'a))))

(verify-guards f12)

(assert-event (mv-let (x y)
                (f12 '(3 1/2 4 . a))
                (and (df= x #d7.5)
                     (eq y 'a))))

(thm (mv-let (x y)
       (f12 '(3 1/2 4 . a))
       (and (df= x #d7.5)
            (eq y 'a))))

; Test printing of measure error.

(defstobj st4 (fld4 :type double-float :initially 0))

(defwarrant fld4)

(defun measure-not-decreasing (st4)
  (declare (xargs :stobjs (st4)
                  :verify-guards nil))
  (loop$ with x = 5
         with ac of-type double-float = (to-df 0)
         do
         :measure (acl2-count x)
         :values (:df)
         (if (zp x)
             (return ac)
             (setq ac (df+ ac (fld4 st4))))))

; Error: Notice printing of the stobj.
(measure-not-decreasing st4)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; FOR loop$ expressions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; The following is illegal, because it is illegal to use a df variable (in this
; case, w) in a FOR loop$ expression.  Use DO loop$ expressions instead in such
; cases, as illustrated in the preceding section.
(let ((w (to-df 7)))
  (loop$ for v from 1 to 3
         sum (from-df (df+ w (to-df v)))))

; The following is legal, because the loop$ variable v, which is not a df
; variable, shadows the let-bound df variable v.
(assert-event (equal (let ((v (to-df 7)))
                       (cons (loop$ for v from 1 to 3 sum v) ; v bound here
                             (from-df v) ; v is a let-bound df variable
                             ))
                     '(6 . 7)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Stobj-let (nested stobjs)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defstobj st5
  (st4a :type st4))

(defun set-fld4 (x st5)
  (declare (xargs :stobjs st5))
  (declare (type double-float x))
  (stobj-let
   ((st4 (st4a st5) update-st4a)) ; bindings, including updater(s)
   (st4)                          ; producer variables
   (update-fld4 x st4)            ; producer
   st5)                           ; consumer
  )

(defun get-fld4 (st5)
  (declare (xargs :stobjs st5))
  (stobj-let
   ((st4 (st4a st5))) ; bindings
   (val)              ; producer variables
   (fld4 st4)         ; producer
   val)               ; consumer
  )

(assert-event
 (df= (get-fld4 st5)
      #d0.0))

(set-fld4 (to-df 7) st5)

(assert-event
 (df= (get-fld4 st5)
      #d7.0))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Using apply$ with dfs, including efficiency issues
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; We see in examples below that apply$ works with df arguments.  This may seem
; surprising.  After all, there is a similar prohibition on stobj arguments
; because a stobj cannot be put into a list; wouldn't such a prohibition
; similarly pertain to df arguments, since they too cannot be put into a list?

; However, ACL2 evaluation of apply$ calls takes place by calling *1*
; functions, and these tolerate ordinary rational inputs where dfs are
; expected.  So apply$ accepts rational arguments where dfs are expected,
; provided they satisfy dfp.

; But see the next section for efficiency issues for using apply$ with dfs.

; Recall our first example:

; This is redundant.
(defun f0 (x)
  (declare (xargs :verify-guards nil)
           (type double-float x))
  (df- x))

; This too is redundant (already included above).
(include-book "projects/apply/top" :dir :system)

; "Teach" apply$ about f0:
(defwarrant f0)

; Succeeds, since 1/4 satisfies the guard for f0, (dfp x).
(assert-event (equal (apply$ 'f0 (list 1/4))
                     -1/4))

; Same as above, since the #d quantities are just rationals:
(assert-event (equal (apply$ 'f0 (list #d0.25))
                     #d-0.25))

; Error: guard violation, since (dfp 1/3) is false.
(apply$ 'f0 (list 1/3))

; Error: Attempt to execute df-round, since df- is just df-round of -.
(with-guard-checking nil (apply$ 'f0 (list 1/3)))

; Now we just repeat the examples above after guard-verifying f0.  These go
; just as the ones above.

(verify-guards f0)

; Succeeds:
(assert-event (equal (apply$ 'f0 (list 1/4))
                     -1/4))

; Succeeds as above
(assert-event (equal (apply$ 'f0 (list #d0.25))
                     #d-0.25))

; Error: guard violation as above.
(apply$ 'f0 (list 1/3))

; Error: Attempt to execute df-round as above.
(with-guard-checking nil (apply$ 'f0 (list 1/3)))

; Note that tracing works as expected: *1* functions traffic in rationals, and
; this raw Lisp function traffics in floats.

(er-progn (set-trace-co (standard-co state) state)
; Avoid printing filesystem-specific channel name:
          (value nil))
(trace$ f0)

(f0 (to-df 3))

(apply$ 'f0 (list 3))

; Lambdas are OK too:
(apply$ '(lambda (y) (f0 y)) (list 3))

; But the following causes an error.  We can tolerate that because it's not
; generally great to use apply$ on lambdas that involve dfs; see the next
; section.
(apply$ (lambda$ (y) (f0 y)) (list 3))

(untrace$ f0)

;;; Efficiency issues when using apply$ with dfs

; One gets raw Lisp performance when calling guard-verified functions on df
; arguments, including calls in DO loop$ expressions.  However, there is some
; loss of efficiency when using apply$ directly on df arguments.

; Redundant here:
(include-book "projects/apply/top" :dir :system)

; Recall the following (which is redundant here):
(defun$ f0 (x)
  (declare (type double-float x))
  (df- x))

(defun$ apply$-quote-f0 ()
  (declare (xargs :guard t))
  (apply$ 'f0 (list 3)))

(trace$ f0)

; Notice that *1*f0 is called.
(apply$-quote-f0)

(defun loop$-apply$-quote-f0 ()
  (declare (xargs :guard t))
  (loop$ for i from 1 to 3 collect
         (apply$-quote-f0)))

; The new compiled lambda object has status :GOOD, but we won't check that here
; since print-cl-cache uses cw and hence doesn't send output to
; floating-point-log.out.
; (print-cl-cache)

; Notice that *1*f0 is called.
(loop$-apply$-quote-f0)

; But a DO loop$ expression in guard-verified code does not similarly invoke
; the *1* function.

(defun do-loop$-on-f0 ()
  (declare (xargs :guard t))
  (loop$ with ans of-type double-float = (to-df 2)
         with i of-type (integer 0 *) = 3
         do
         :values (:df)
         (cond ((zp i) (return ans))
               (t (progn (setq i (1- i))
                         (setq ans (df* (f0 ans) ans)))))))

(do-loop$-on-f0)

; Finally, notice that the issue with *1* functions is relevant when using
; lambdas as well.

(defun$ apply$-f0-in-lambda ()
  (declare (xargs :guard t))
  (apply$ '(lambda (y)
             (declare (xargs :guard (dfp y) :split-types t)
                      (type double-float y))
             (f0 y))
          (list 3)))

; Notice *1*f0 being called:
(apply$-f0-in-lambda)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Encapsulate and signatures
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Here we illustrate the use of :df values in signatures.

(encapsulate
  (((f13 :df) => *))
  (local (defun f13 (x)
           (declare (type double-float x))
           (from-df x)))
  (defthm dfp-f13
    (implies (dfp x)
             (dfp (f13 x)))))

(encapsulate
  (((f14 :df) => :df))
  (local (defun f14 (x)
           (declare (type double-float x))
           (df- x)))
  (defthm dfp-f14
    (implies (dfp x)
             (dfp (f14 x)))))

(encapsulate
  (((f15 *) => :df))
  (local (defun f15 (x)
           (declare (ignore x))
           (to-df 0)))
  (defthm dfp-f15
    (dfp (f15 x))))

(encapsulate
  (((f16 *) => :df :formals (x) :guard (rationalp x)))
  (local (defun f16 (x)
           (declare (ignore x))
           (to-df 0))))

; Next we test defstub (which expands to encapsulate).

(defstub f17 (*) => :df)
(args 'f17)

(defstub f18 (:df) => :df)
(args 'f18)

(defstub f19 (:df) => (mv :df :df))
(args 'f19)

(defstub f20 (:df) => *)
(args 'f20)

(defstub f21 (:df st1 * :df) => (mv * * st1 :df))
(args 'f21)

(defstub f22 (x) t :dfs (x)) ; old-style
(args 'f22)

; Error: Formal cannot be both a stobj and a df.
(defstub bad (x st1) t :stobjs st1 :dfs (x st1))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Memoization
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Memoization works fine with dfs; the subtleties when memoizing with stobjs
; don't apply to dfs.

(defun f23a ()
  (declare (xargs :guard t))
  t)

(defun f23 (x y)
  (declare (type double-float x y))
  (prog2$ (f23a)
          (df+ x y)))

(trace$ f23a)

(memoize 'f23)

(f23 (to-df 3) (to-df 4)) ; shows traced f23a call
(f23 (to-df 3) (to-df 4)) ; no traced f23a call
(f23 (to-df 3) (to-df 4)) ; no traced f23a call

(unmemoize 'f23)

(memoize 'f23
         :condition '(df< x y))

(f23 (to-df 3) (to-df 4)) ; shows traced f23a call
(f23 (to-df 3) (to-df 4)) ; no traced f23a call
(f23 (to-df 3) (to-df 4)) ; no traced f23a call

(f23 (to-df 4) (to-df 3)) ; shows traced f23a call
(f23 (to-df 4) (to-df 3)) ; still shows traced f23a call

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Miscellany
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;; Defun-sk

; The following defun-sk is accepted.
(defun-sk f24 (x)
  (declare (xargs :dfs (x)))
  (exists (y) (df< x (to-df y))))

; The following defun-sk is accepted, even though y represents an ordinary
; object, because by default the defun-sk function is non-executable.
(defun-sk f25 (x)
  (declare (xargs :dfs (x)))
  (exists (y) (df< x y)))

; The following fails, unlike the event immediately above, because we have
; specified that the introduced function be executable and y represents an
; ordinary object but is passed to df<.
(defun-sk f25-bad (x)
  (declare (xargs :dfs (x) :non-executable nil))
  (exists (y) (df< x y)))

; But by adding back to-df we get an acceptable event.
(defun-sk f24-executable (x)
  (declare (xargs :dfs (x) :non-executable nil))
  (exists (y) (df< x (to-df y))))

;;; Memoize-partial works fine with dfs.

; The following two examples (each consisting of a defun followed by a
; memoize-partial) are adapted from an example in :DOC memoize-partial.  Each
; computes with dfs.  The first, collatz-1-limit and collatz-1, has integer
; return values.  The second, collatz-2-limit and collatz-2, has df return
; values.  ACL2 has been carefully programmed so that collatz-2 returns a df --
; hence, a rational -- at the top level, not a Lisp double-float.

; Collatz-1

(defun collatz-1-limit (n limit)
  (declare (xargs :guard (natp limit)
                  :measure (acl2-count limit))
           (type double-float n))
  (if (zp limit)
      (prog2$ (er hard? 'collatz-1-limit
                  "Limit exceeded!")
              0)
    (let ((limit (1- limit)))
      (if (df= n 1)
          0
        (1+ (collatz-1-limit (if (let ((k (df-rationalize n)))
                                 (and (integerp k)
                                      (evenp k)))
                               (df/ n 2)
                             (df+ 1 (df* 3 n)))
                           limit))))))

(memoize-partial collatz-1)

(collatz-1 (to-df 6)) ; prints as 8, not #d8.0 and not 8.0
(assert-event (= (collatz-1 (to-df 6)) 8))
(assert-event (= (collatz-1 (to-df 10)) 6))
(assert-event (= (collatz-1 (to-df 100)) 25))

; Collatz-2

(defun collatz-2-limit (n limit)
  (declare (xargs :guard (natp limit)
                  :measure (acl2-count limit))
           (type double-float n))
  (if (zp limit)
      (prog2$ (er hard? 'collatz-2-limit
                  "Limit exceeded!")
              (df0))
    (let ((limit (1- limit)))
      (if (df= n 1)
          (df0)
        (df+ 1 (collatz-2-limit (if (let ((k (df-rationalize n)))
                                 (and (integerp k)
                                      (evenp k)))
                               (df/ n 2)
                             (df+ 1 (df* 3 n)))
                           limit))))))

(memoize-partial collatz-2)

(collatz-2 (to-df 6)) ; prints as #d8.0, not 8.0
(assert-event (df= (collatz-2 (to-df 6)) 8))
(assert-event (df= (collatz-2 (to-df 10)) 6))
(assert-event (df= (collatz-2 (to-df 100)) 25))

;;; Defexec

(defexec f26 (x y)
  (declare (xargs :guard (natp x) :dfs (y))
; To support :dfs, ACL2 was modified to copy the :dfs from :guard to
; :exec-xargs.  Without that change, the exec-xargs would need to include :dfs
; explicitly below.
           (exec-xargs :default-value (to-df 1)))
  (mbe :logic (if (zp x)
                  y
                (df* (to-df x) (f26 (- x 1) y)))
       :exec  (if (= x 0)
                  y
                (df* (to-df x) (f26 (- x 1) y)))))

(assert-event (df= (f26 3 (to-df 7))
                   42))

;;; Tricky syntactic issues

; When ACL2 translates the body of f27-bad below, then when encountering the
; mv-let form, the output signature is guessed for the call (f27-bad (cdr x)).
; That fails, because at that point there is no clue about what the function
; returns, so translation occurs under the assumption that f27-bad does not
; return a df.  The defun for f27 is the same except that y is declared to have
; type double-float, and that hint allows ACL2 to deduce that f27 has output
; signature (mv :DF *).  Since f27-bad has no such declaration, in that case it
; is assumed that f27 returns (mv * *), and translation fails since (df0)
; returns a df, which is not compatible with the return type of (mv * *) that
; was deduced when translating the mv-let expression.

; Fails (see comment above)
(defun f27-bad (x)
  (if (consp x)
      (mv-let (y z)
        (f27-bad (cdr x))
        (mv y z))
    (mv (df0) x)))

; Succeeds (see comment above)
(defun f27 (x)
  (if (consp x)
      (mv-let (y z)
        (f27 (cdr x))
        (declare (type double-float y))
        (mv y z))
    (mv (df0) x)))

; And here's a version of f27 that doesn't need the type declaration, because
; the true branch of the IF provides the output signature for f27 that is used
; when translating the recursive call.
(defun f27-easy (x)
  (if (not (consp x))
      (mv (df0) x)
    (mv-let (y z)
      (f27-easy (cdr x))
      (mv y z))))

; Here is another set of examples illustrating delicate points about deducing
; which return values are dfs.

; The following fails much as f27-bad fails.  Here, the recursive call is
; assumed to return a non-df, so (df+ y z) is supposed to return a non-df since
; it is returning a value for f28-bad.
(defun f28-bad (x)
  (if (consp x)
      (mv-let (y z)
        (mv (to-df (car x))
            (f28-bad (cdr x)))
        (df+ y z))
    (df1)))

; The following succeeds because the mv expression is deduced to have output
; signature (mv :DF :DF), where the latter :DF comes courtesy of the
; double-float type declaration on z.
(defun f28 (x)
  (if (consp x)
      (mv-let (y z)
        (mv (to-df (car x))
            (f28 (cdr x)))
        (declare (type double-float z))
        (df+ y z))
    (df1)))

; This is similar to the preceding, but with a harmless double-float type
; declaration for y.
(defun f28-alt (x)
  (if (consp x)
      (mv-let (y z)
        (mv (to-df (car x))
            (f28-alt (cdr x)))
        (declare (type double-float y z))
        (df+ y z))
    (df1)))

; The following defun fails, as it should, because y should not have been
; declared of type double-float, since y is (car x) and car returns an ordinary
; object, not a df.
(defun f29 (x)
  (if (consp x)
      (mv-let (y z)
        (mv (car x)
            (f29 (cdr x)))
        (declare (type double-float y z))
        (df+ (to-df y) z))
    (df1)))

; The next set of examples are in the same spirit of the preceding ones, but
; this type they involve mutual-recursion.  The errors are similar to ones seen
; above.

; Error: The first mv in f30-bad1 guesses that f31-bad1 returns a non-df, which
; is at odds with the return of (mv (df0) (df1)).
(mutual-recursion

 (defun f30-bad1 (x)
   (if (consp x)
       (mv (to-df (car x)) (f31-bad1 (cdr x)))
     (mv (df0) (df1))))

 (defun f31-bad1 (x)
   (if (consp x)
       (mv-let (u v)
         (f30-bad1 (cdr x))
         (df+ (to-df (car x)) (df+ u v)))
     (df1)))
)

; Still an error; switching defun forms might sometimes help, but not here.
(mutual-recursion

 (defun f31-bad2 (x)
   (if (consp x)
       (mv-let (u v)
         (f30-bad2 (cdr x))
         (df+ (to-df (car x)) (df+ u v)))
     (df1)))

 (defun f30-bad2 (x)
   (if (consp x)
       (mv (to-df (car x)) (f31-bad2 (cdr x)))
     (mv (df0) (df1))))
)

; OK: Problem solved by switching IF branches.
(mutual-recursion

 (defun f30-good1 (x)
   (if (not (consp x))
       (mv (df0) (df1))
     (mv (to-df (car x)) (f31-good1 (cdr x)))))

 (defun f31-good1 (x)
   (if (consp x)
       (mv-let (u v)
         (f30-good1 (cdr x))
         (df+ (to-df (car x)) (df+ u v)))
     (df1)))
)

; OK: Problem solved by using THE.
(mutual-recursion

 (defun f30-good2 (x)
   (if (consp x)
       (mv (to-df (car x)) (the double-float (f31-good2 (cdr x))))
     (mv (df0) (df1))))

 (defun f31-good2 (x)
   (if (consp x)
       (mv-let (u v)
         (f30-good2 (cdr x))
         (df+ (to-df (car x)) (df+ u v)))
     (df1)))
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; Check consistency with values produced in raw Lisp
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This section has tests to check that ACL2 evaluation with dfs agrees with
; ccorresponding Common Lisp evaluation on double-floats.

(defttag :floating-point)

(defmacro raw-check (form &optional (raw-form 'nil raw-form-p))
  `(ld '((set-raw-mode nil)
         (er-let* ((stobjs-out/val
                    (trans-eval ',form 'raw-check state nil)))
           (assign raw-check-xxx (cdr stobjs-out/val)))
         (set-raw-mode t)
         (let ((raw-check-yyy ,(if raw-form-p raw-form form)))
           (if (if (typep raw-check-yyy 'real)
                   (= (@ raw-check-xxx) raw-check-yyy)
                 (equal (@ raw-check-xxx) raw-check-yyy))
               (pprogn (princ$ "Raw-check success" (standard-co state) state)
                       (newline (standard-co state) state))
             (fms "Raw-check failed for~|~x0~@1~|"
                  (list (cons #\0 ',form)
                        (cons #\1 ,(if raw-form-p
                                       `(msg "~|and raw form~|~x0"
                                             ',raw-form)
                                     "")))
                  (standard-co state) state nil)))
         (set-raw-mode nil)
         (value :q))
       :ld-verbose nil
       :ld-prompt nil
       :ld-pre-eval-print nil
       :ld-post-eval-print nil))

; Should succeed quietly:
(raw-check (equal 3 3))
(raw-check (equal 3 3) (= 3 3))

; The following two should fail with a "Raw-check failed for" message.
; These are included simply to check that raw-check can indeed report
; failures.
(raw-check (with-guard-checking nil (eq '(a) '(a))))
(raw-check (with-guard-checking nil (eq '(a) '(a)))
           (eq '(a) '(a)))

; The rest below should all succeed quietly:

(raw-check (df+ #d1.23))
(raw-check (df+ #d1.23)
           (+ (eval (read-from-string "1.23"))))
(raw-check (df+ 3 4)
           (eval (read-from-string "7.0")))
(raw-check (df+ 9/16 1/4 #d3.1))
(raw-check (df+ (to-df 1/3) 1/4))
(raw-check (df/ (to-df 1/3) 1/4))
(raw-check (dfp 'abc))
(raw-check (dfp 'abc)
           nil)
(raw-check (from-df (to-df 1/4)))
(raw-check (from-df (to-df 1/3)))
(raw-check (to-df 31/10))
(raw-check (to-dfp 31/10))
(raw-check ; 31/10 is not representable, so it is modified by to-dfp
 (not (equal (to-dfp 31/10) 31/10)))

; associativity fails:
(raw-check (not (df= (df+ #d.1 (df+ #d.2 #d.3))
                     (df+ (df+ #d.1 #d.2) #d.3))))
(raw-check (let ((x (to-df #d.1))
                 (y (to-df #d.2))
                 (z (to-df #d.3)))
             (not (df= (df+ (df+ x y) z)
                       (df+ x (df+ y z))))))

(raw-check (df+ (identity-macro 1/4) 1/2)
           (eval (read-from-string "0.75")))
(raw-check (df-rationalize (to-df 1/3)))
(raw-check (df-rationalize (to-df 1/3))
           (rationalize (to-df 1/3)))
(raw-check (rize 1/3)
           (rationalize (float 1/3 (eval (read-from-string "0.0")))))
(raw-check (rize *df-pi*))
(raw-check (rize *df-pi*)
           (rationalize pi))
; These both succeed since f1 was defined by defun-df.
(raw-check (f1 3))

(raw-check (f1 (to-df 3)))

(defttag nil)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

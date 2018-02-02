(in-package "ACL2")

#|

 defpun-exec.lisp
 ~~~~~~~~~~~~~~~~

Author: Sandip Ray
Email: sandip@cs.utexas.edu
Date of last revision: June 20, 2003.

Objective:
---------

The goal of this book is to create a macro that will produce partial functions
with efficient executable counterparts. This is achieved in ACL2 v2-8 through
the use of the :defexec and :mbe utility.

History:
--------

Let us look at the problem in a slightly greater detail. Assume you are given a
function name foo, and a logical body (hereafter called lbody). When a function
(defun foo (x) body) is defined in ACL2, it corresponds to extending the logic
with the axiom (foo x) = body. Assume now that body calls foo, recursively. In
that case, to ensure the soundness of the added axiom, it is imperative to show
that the function terminates. Otherwise it is easy to get unsoundness in the
logic by defining (foo x) as follows:

(defun foo (x) (if (zp x) 0 (1+ (foo x))))

Note that the equation, if used to extend the logic with an axiom, will quickly
produce nil. Informally, the problem is that no function satisfies this
definintional equation.

Now, the termination requirement specifies that you need to show that there is
a measure (m x) which is an ordinal, and decreases along every recursive call,
over a well-founded set. Then it is simple to show that the cotrresponding
axiom is sound in the following sense: There is at least one function that
satisfies this definitional equation.

Now, suppose you want to define a "partial function". Such a function will not
be specified for every input, and for example, will possibly not terminate for
every input. Manolios and Moore show in [1] that you can introduce a partial
function in ACL2 by showing that there exists at least one (total) function
that satisfies its defining equation. In particular, you can show that you can
introduce every partial function that is tail-recursive.

That has significance for example in modeling computing systems such as the
JVM. Consider the following equation that "runs" a machine until it halts.

(run s) = (if (halting s) s (run (step s)))

Of course the program might not halt at all but still it is sound to add the
equation. The approach is shown using a special macro defpun, and you would
write:

(defpun run (s) (if (halting s) s (run (step s))))

This is a macro that expands into an encapsulate, that automatically produces a
witnessing function, and then adds the following definition rule:

(defthm run-def
  (equal (run s) (if (halting s) s (run (step s))))
  :rule-classes :definition)

All this is nice, but it does not allow you to actually "run" from a state,
even if the machine halts from that state.

The goal of this book is to add such executability.

For example, consider another example of a factorial program:

(defpun fact (n a) (if (equal n 0) a (fact (1- n) (* n a))))

Of course this halts only for positive integers n, but you will not be able to
"compute" (fact 5 1) and say it is 120. (Of course you can prove a theorem
saying (fact 5 1) is 120, but you cannot execute the function fact to do it.)

The macro defpun-exec we develop strives to rectify that. In particular, you
introduce an executable function that you can run in Lisp, but only after you
have shown that the executable body corresponds to the logic body under the
values. This is done by the use of guards in ACL2, and the :mbe which is
introduced in v2-8.

Form:
-----

The general form of defpun-exec is as follows:

(defpun-exec foo params lbody :ebody ebody :guard guard)

This provides a function named foo with parameters params, and (logically
speaking) a defining equation saying that foo is exactly equal to the
lbody. The guards are verified then, to show that under the guards, you
can show that lbody is equal to ebody. Hence you simply can use the
exec-body to execute foo on arguments that satisfy the guard.

By default, i.e., if the executable body ebody is not provided, it is simply
the same as lbody. Thanks to Matt Kaufmann for suggesting this.

Spec:
-----

Define a macro defpun-exec with the following properties:

(1) It takes as argument fname, params, lbody, ebody, and guard, say

(defpun-exec foo (x) (lbody x) :ebody (ebody x) :guard (guard x))

The guard argument is optional.

(2) If guards are not provided, a :guard of nil is assumed.  Thus calls of
    foo will never be evaluated.

(3) If the guards are verified, (foo x) can be evaluated for constant x, and
the value is (ebody x)

(4) If possible do it without changing the defpun macro provided by Manolios
and Moore.

(5) If guards are provided but the verification fails, I don't want anything to
be in the ACL2 universe.

(6) If :ebody is not provided, then a :ebody of (lbody x) is assumed. Hence
executing the function is the same as executing the logical body.

Now I show how to do it.

Assumptions and acknowledgments:
-------------------------------

(1) We would assume that the user works with this book using the relevant
theories as provided, and will not attempt to enable other (auxilliary)
functions we created in the process, for example the -logic functions and their
theorems. If they do, they run the risk of infinite loops in simplification
(which they of course run anyway...). We have provided a couple of theory
invariants to help the user not do something inadvertently, but we do not think
that is sufficient. However, the natural way of using it is to have the -logic
events disabled.

(2) We thank Matt Kaufmann for providing the idea of the -logic-to- theorem
described below to make :expand hints natural.

|#


#| Some helper functions. |#

;; The only helper function I require is the function replace-fsymb, which
;; replaces every occurrence of the function symbol orig with the function
;; symbol new. This is somewhat brittle, since we are operating on untranslated
;; terms; for example, if we want to replace bar1 with bar2 then (foo (bar1 x))
;; would be replaced by (foo (bar2 x)), which would be wrong if foo is defined
;; by (defmacro foo (v) (list 'quote (car v))).  But our goal is simply to
;; provide a convenient macro that tends to do what the user expects; we offer
;; no soundness guarantee.

(mutual-recursion

 (defun replace-fsymb (orig new term)
   (declare (xargs :mode :program))
   (cond ((atom term) term)
         ((eq (car term) orig)
          (cons new (replace-fsymb-list orig new (rest term))))
         (t (cons (first term) (replace-fsymb-list orig new (rest term))))))

 (defun replace-fsymb-list (orig new terms)
   (declare (xargs :mode :program))
   (cond ((endp terms) nil)
         (t (cons (replace-fsymb orig new (first terms))
                  (replace-fsymb-list orig new (rest terms))))))

 )

#| Now we get into the actual macro defpun-exec |#

;; We comment on the macro below assuming that you have given us a defpun-exec
;; of the form:

;; (defpun-exec foo (x) (lbody x) :ebody (ebody x) :guard (guard x))


(include-book "misc/defpun" :dir :system)

(defmacro defpun-exec (fname params lbody
                             &key
                             (ebody 'nil)
                             (guard 'nil))
  (declare (xargs :guard (and (symbolp fname)
                              (symbol-listp params))))
  (let* ((ebody (if (null ebody) lbody ebody))
         (lfname (packn (list fname '-logic)))
         (defn-thm (packn (list fname '-def))))

    `(encapsulate nil

      ;; First we define a standard defpun function, call it defpun foo-logic,
      ;; and the body of foo-logic (which we will call (defpun-body x) is
      ;; simply lbody with all calls to foo replaced by (recursive) calls to
      ;; foo-logic.

      (defpun ,lfname ,params
        ,(replace-fsymb fname lfname lbody))

      ;; Now we define the function foo as:
      ;;  (defexec foo (x)
      ;;    (declare (xargs :guard (guard x)))
      ;;    (mbe :logic (foo-logic x) :exec (ebody x)))

      ;; Note: It is possible to use defun to define foo. That is logically
      ;; sound, and the macro would go thru. However, the use of defexec
      ;; insures that when we do execute the function using ebody, the
      ;; execution eventually terminates.

      (defexec ,fname ,params
        (declare (xargs :guard ,guard))
        (mbe :logic ,(cons lfname params)
             :exec ,ebody))


      ;; We have therefore achieved the goal of the executable part. Now we
      ;; provide a definition rule in accordance with the spec.

      ;; (defthm foo-def (equal (foo x) (lbody x)) :rule-classes :definition)

      (defthm ,defn-thm
        (equal ,(cons fname params)
               ,lbody)
        :rule-classes :definition)

      ;; So we have achieved the goal. We have provided a definition rule and
      ;; we have provided an executable counterpart. So I would think that we
      ;; satisfied ourselves. I would disable some stuff now, but before that,
      ;; I would like to comment on some suggestions by Matt Kaufmann and
      ;; during the ACL2 meeting on 06/18/2003.

      ;; When I first did this, I was dissatisfied by the following:
      ;;
      ;; Once the definition rule is present you would think that you don't want
      ;; anything to do with foo-logic. So I would not like to have the logical
      ;; body of foo enabled, but rather I would simply have the definition
      ;; rule foo-def above to do what we want with foo. Unfortunately, if the
      ;; user gives a :expand hint, the definition ACL2 opens up is the logical
      ;; which is (foo-logic x) rather than the last definition rule. So I
      ;; still have something to do with it. When I raised the question in the
      ;; ACL2 meeting, Matt came up with the following suggestion:

      ;; Add a rule foo-logic-def of the form (equal (foo-logic x) (lbody
      ;; x)). The idea, then, should be to disable the theorem foo-logic-def
      ;; (introduced by defpun) so that when a :expand hint occurs to foo it
      ;; will use the definition of foo to get logic-body and that will
      ;; immediately be rewritten to (lbody x). That was a nice
      ;; suggestion. Thanks, Matt.

      ;; (defthm foo-logic-to-foo
      ;;   (equal (foo-logic x) (lbody s))
      ;;  :rule-classes :definition)

      (defthm ,(packn (list lfname '-to- fname))
        (equal ,(cons lfname params) ,lbody)
        :rule-classes :definition)

      ;; Now we do simply want the definition rule foo-def to apply, and (only
      ;; in case of an expand hint would we want to have the special rule
      ;; foo-logic-to-foo. So I would rather disable the body of foo in
      ;; general, and also the theorem foo-logic-def which was provided by the
      ;; defpun.

      ;; (in-theory (disable foo (:definition foo-logic-def)))

      (in-theory (disable ,fname (:definition ,(packn (list lfname '-def)))))

      ;; I think some form of theory invariants should be present here, since I
      ;; don't quite like the body of foo and definition foo-def to be both
      ;; enabled, because then foo-def ought never to be used. (foo is
      ;; non-recursive.) Of course it is not a big point to have a theory
      ;; invariant, but here is what I am thinking. A user can either use
      ;; foo-def to deduce properties of foo, or should use the body of foo along
      ;; with facts about foo-logic. To me these are two different (incompatible)
      ;; strategies. So either he should leave foo enabled, not use foo-def or
      ;; foo-logic-to-foo, and provide rules to reason about foo-logic. Or he
      ;; should heve foo disabled, not use foo-logic-def, and use foo-def, and (in
      ;; case of expand hints) foo-logic-to-foo. I think we should have an
      ;; invariant saying that  one of the two theories is used.

      ;; So, here are the theory invariants I provide with this macro. If these
      ;; are not useful then simply comment them out and recertify the book.

      ;; (theory-invariant (incompatible (:definition foo)
      ;;                                 (:definition foo-def)))

      (theory-invariant (incompatible (:defintitiion ,fname)
                                      (:definition
                                       ,(packn (list fname '-def)))))

      ;; (theory-invariant (incompatible (:definition foo-logic-to-foo)
      ;;                                 (:definition foo-logic-def)))

      (theory-invariant (incompatible (:definition
                                       ,(packn (list lfname '-to- fname)))
                                      (:definition
                                       ,(packn (list lfname '-def))))))

      ;; And that is it. We might have to add more theory invariants, but I
      ;; think that is only important if the user wants to tweak with the
      ;; current structure. The structure is foo is disabled, and only opens
      ;; via an expand hint which would immediately rewrite to (lbody x) using
      ;; the  definition foo-logic-to-foo, and the rest are taken care of by
      ;; the rule foo-def which was the only rule in the defpun
      ;; anyway. However, if the user wants to open up other definitions, he
      ;; better be structured.

))


#|

Testing
=======

(1) I don't verify the guard below. So it will produce the logic definition and
the definition rule, but will produce a guard of nil, and hence in effect
disable the executable counterpart. This has the precise effect of simply
providing a defpun.

ACL2 !>(defpun-exec fact (n a)
             (if (equal n 0) a (fact (1- n) (* n a)))
             :ebody (if (zp n) a (* n (fact (1- n) a))))

So this will produce everything but you cannot evaluate it.

ACL2 !>(trace$ fact)
NIL
ACL2 !>(thm (equal (fact 5 1) 120))
1> (ACL2_*1*_ACL2::FACT 5 1)

By case analysis we reduce the conjecture to

Goal'
(EQUAL (HIDE (FACT 5 1)) 120).
  2> (ACL2_*1*_ACL2::FACT 5 1)

Name the formula above *1.

No induction schemes are suggested by *1.  Consequently, the proof
attempt has failed.

Summary
Form:  ( THM ...)
Rules: ((:DEFINITION HIDE))
Warnings:  None
Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)

******** FAILED ********  See :DOC failure  ******** FAILED ********
ACL2 !>

(2) However, now observe that the verified guards work.

ACL2 !>(defpun-exec trfact (n a)
             (if (equal n 0) a (trfact (1- n) (* n a)))
             :ebody (if (zp n) a  (trfact (1- n) (* n a)))
             :guard (and (integerp n) (integerp a) (>= n 0) (>= a 0)))

ACL2 !>(trace$ trfact)
NIL
ACL2 !>(thm (equal (trfact 5 1) 120))
1> (ACL2_*1*_ACL2::TRFACT 5 1)
  2> (TRFACT 5 1)
    3> (TRFACT 4 5)
      4> (TRFACT 3 20)
        5> (TRFACT 2 60)
          6> (TRFACT 1 120)
            7> (TRFACT 0 120)
            <7 (TRFACT 120)
          <6 (TRFACT 120)
        <5 (TRFACT 120)
      <4 (TRFACT 120)
    <3 (TRFACT 120)
  <2 (TRFACT 120)
<1 (ACL2_*1*_ACL2::TRFACT 120)

But we reduce the conjecture to T, by the :executable-counterparts
of EQUAL and TRFACT.

Q.E.D.

Summary
Form:  ( THM ...)
Rules: ((:EXECUTABLE-COUNTERPART EQUAL)
        (:EXECUTABLE-COUNTERPART TRFACT))
Warnings:  None
Time:  0.00 seconds (prove: 0.00, print: 0.00, other: 0.00)

Proof succeeded.
ACL2 !>

(3) Now let use just check that even if you do not provide an ebody then it can
    evaluate the lbody (as long as the lbody can be defined with defpun and
    defexec shows that the guard proof guarantees termination).

ACL2 !>(defpun-exec trfact-without-ebody (n a)
           (if (equal n 0) a (trfact-without-ebody (1- n) (* n a)))
           :guard (and (integerp n) (integerp a) (>= n 0) (>= a 0)))

ACL2 !>(trace$ trfact)
NIL
ACL2 !>(trace$ trfact-without-ebody)
NIL
ACL2 !>(thm (equal (trfact-without-ebody 5 1) 120))
1> (ACL2_*1*_ACL2::TRFACT-WITHOUT-EBODY 5 1)
  2> (TRFACT-WITHOUT-EBODY 5 1)
    3> (TRFACT-WITHOUT-EBODY 4 5)
      4> (TRFACT-WITHOUT-EBODY 3 20)
        5> (TRFACT-WITHOUT-EBODY 2 60)
          6> (TRFACT-WITHOUT-EBODY 1 120)
            7> (TRFACT-WITHOUT-EBODY 0 120)
            <7 (TRFACT-WITHOUT-EBODY 120)
          <6 (TRFACT-WITHOUT-EBODY 120)
        <5 (TRFACT-WITHOUT-EBODY 120)
      <4 (TRFACT-WITHOUT-EBODY 120)
    <3 (TRFACT-WITHOUT-EBODY 120)
  <2 (TRFACT-WITHOUT-EBODY 120)
<1 (ACL2_*1*_ACL2::TRFACT-WITHOUT-EBODY 120)

But we reduce the conjecture to T, by the :executable-counterparts
of EQUAL and TRFACT-WITHOUT-EBODY.

Q.E.D.

Summary
Form:  ( THM ...)
Rules: ((:EXECUTABLE-COUNTERPART EQUAL)
        (:EXECUTABLE-COUNTERPART TRFACT-WITHOUT-EBODY))
Warnings:  None
Time:  0.01 seconds (prove: 0.01, print: 0.00, other: 0.00)

Proof succeeded.
ACL2 !>

|#

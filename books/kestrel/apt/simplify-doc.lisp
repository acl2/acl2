; Simplify Transformation -- Documentation
;
; Copyright (C) 2017, Regents of the University of Texas
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.
;
; Author: Matt Kaufmann (kaufmann@cs.utexas.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; This file documents the simplify data transformation,
; which is used for simplifying a definition.  Currently, the
; definition must have been introduced by defun or defun-sk
; (or wrappers for these).

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "APT")

(include-book "xdoc/top" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc simplify
  :parents (apt)
  :short "Simplify the definition of a given function."
  :long "<p>For any function symbol @('f') defined using @(tsee defun), @(tsee
 defun-sk), or the the @(see soft::SOFT) tool, @('defun-sk2'), @('simplify')
 defines a corresponding new function whose body results from simplifying the
 body of the definition of @('f').  @('Simplify') may also be used to simplify
 a given term.</p>

 <p>@('Simplify') operates in related but different ways depending on its
 input: a function symbol introduced with @('defun') (or a wrapper such as
 @('defun-nx')), a function symbol introduced with @('defun-sk') (or a wrapper
 such as the @(see soft::SOFT) tool @('defun-sk2')), or a term other than a
 symbol or a constant.  In the first case, @('(simplify fn ...)')  expands
 directly to @('(simplify-defun fn ...)'); see @(see simplify-defun).  In the
 second case, @('(simplify fn ...)') expands directly to @('(simplify-defun-sk
 fn ...)'); see @(see simplify-defun-sk).  Otherwise, the call, which is of the
 form @('(simplify term ...)'), expands to @('(simplify-term term ...)'); see
 @(see simplify-term).  In all three cases, the corresponding documentation
 topic carefully describes keyword arguments and links to a corresponding topic
 that contains examples.</p>

 <p>Here are three very simple examples you may wish to read before you visit
 those documentation topics.  They give a sense of @('simplify-defun'),
 @('simplify-defun-sk'), and @('simplify-term'), respectively.</p>

 @({
 ACL2 !>(defun f1 (x) (car (cons x x)))
 [[.. output omitted here ..]]
  F1
 ACL2 !>(simplify f1 :new-name f2 :theorem-name f1-is-f2)
 (DEFUN F2 (X)
        (DECLARE (XARGS :GUARD T
                        :VERIFY-GUARDS NIL))
        X)
 (DEFTHM F1-IS-F2 (EQUAL (F1 X) (F2 X)))
 ACL2 !>

 ACL2 !>(defun-sk g1 (x y) (exists z (equal (* z 2) (* x y))))
 [[.. output omitted here ..]]
  T
 ACL2 !>(simplify g1 :theorem-disabled t)
 (DEFUN-SK G1$1 (X Y) (EXISTS (Z) (EQUAL (* 2 Z) (* X Y))) :QUANT-OK T)
 (DEFTHMD G1-BECOMES-G1$1 (IFF (G1 X Y) (G1$1 X Y)))
 ACL2 !>

 ACL2 !>(simplify (+ x (- x) 17) :thm-name foo)
 (DEFTHM FOO (EQUAL (+ X (- X) 17) 17))
 ACL2 !>
 })

 <p>See @(see simplify-failure) for tips on how to deal with failures and other
 undesirable results from evaluating calls of @('simplify').</p>")

(defxdoc simplify-failure

; In the section "Recursion and equivalence relations" there is reference to a
; comment about a possible future applicability condition, to allow the use of
; :equiv with recursive definitions.  The following comment comes from an email
; sent by Alessandro Coglio on August 18, 2018, included here with his
; permission.

;   Maybe an approach is to generate an applicability condition asserting that
;   the equivalence in question is a congruence w.r.t. the body of the
;   function. More precisely, take the body of the function, replace the
;   recursive calls with fresh variables, and make a lambda abstraction with
;   the resulting body as body and with the fresh variables as formals: this is
;   the function that should map equivalent values to equivalent values, as
;   asserted by this new applicability condition.

;   To prove that the new function is equivalent to the old function, the
;   inductive step must prove that the new body is equivalent to the old body
;   given that the new recursive calls are equivalent to the old recursive
;   calls. As your example shows, in general there's no reason why that should
;   be the case. If it is the case, it may be arbitrarily hard to prove. So an
;   applicability condition seems appropriate.

;   I haven't thought through all the details of this.

; Some such approach seems promising for the case that the original and
; simplified definition are indeed equivalent.  For the example in the :doc
; below, that is not the case; indeed, the applicability condition would fail,
; which seems appropriate.

  :parents (simplify)
  :short "Ways to address failed invocations of the @('simplify') transformation."
  :long "<p>This topic suggests steps you may take to address failed
 invocations of the @('simplify') transformation.</p>

 <h3>Dealing with a guard verification failure</h3>

 <p>When @('(simplify FN ...)') fails at guard verification, then unless option
 @(':print nil') is supplied, an attempt to run @('(verify-guards fn)') will be
 made automatically, with prover output shown as though @(':print :all') had
 been supplied.  That way, you can look at checkpoints to come up with helpful
 rules, without having to run @('simplify') again (see @(see
 acl2::the-method)).</p>

 <p>Note that in some cases, there may be initial attempts at guard
 verification that use a somewhat sophisticated @(see acl2::proof-builder)
 macro, one that users are not expected to understand.  This explains why the
 retry mentioned above is simply @('(verify-guards fn)'), with no hints: this
 supports your attempt to make adjustments so that guard verification will
 succed for your @('simplify') command.  It might be helpful to try one or more
 of the following approaches.</p>

 <ul>

 <li>Prove suitable rules, as noted above, towards removing the checkpoints.
 You may wish to specify @(':guard-hints nil') in your new call of
 @('simplify'), to match the call @('(verify-guards fn)') that generated the
 checkpoints that you considered.</li>

 <li>Provide a @(':guard-hints') option, @('(simplify FN :guard-hints ...)')
 that specifies a suitable theory and, perhaps, include @(':use (:guard-theorem
 FN)').</li>

 <li>Delay guard verification with @('(simplify FN :verify-guards nil ...)').
 Then, after this @('simplify') completes successfully, call @(tsee
 verify-guards) on @('FN'), perhaps with suitable hints as suggested
 above.</li>

 <li>If you use @(':print info') or @(':print :all'), you may see a message
 like the following.
 @({
 Saving proof-builder error state; see :DOC instructions.  To retrieve:
 (RETRIEVE :ERROR1)
 })
 If you invoke that command in the ACL2 loop, e.g., @('(RETRIEVE :ERROR1)'),
 then you will be in the @(see acl2::proof-builder).  You can run the
 @('prove') command there and look at the checkpoints.  Consider the following
 (admittedly artificial) example.
 @({
 (defun my-consp (x) (declare (xargs :guard t)) (consp x))
 (defun my-cdr (x) (declare (xargs :guard (my-consp x))) (cdr x))
 (defun f1 (x)
   (if (consp x)
       (if (my-consp (f1 (cdr x)))
           (cons (car x) (f1 (my-cdr x)))
         x)
     x))
 (defthm f1-id (equal (f1 x) x))
 (verify-guards f1)
 (in-theory (disable my-consp my-cdr (tau-system)))
 (simplify f1 :print :info)
 })
 If you run @('(RETRIEVE :ERROR1)') and then submit @('PROVE'), you'll see the
 following checkpoint.
 @({
 Goal'
 (IMPLIES (AND (CONSP X) (MY-CONSP (CDR X)))
          (MY-CONSP X))
 })
 This checkpoint rather clearly suggests enabling @('my-consp').  Indeed, you
 can do that in the proof-builder: the command @('(IN-THEORY (ENABLE
 MY-CONSP))') followed by @('PROVE') completes the proof in the proof-builder.
 With that information you can exit the proof-builder and successfully run the
 following command in the ACL2 loop.
 @({
 (simplify f1 :guard-hints ((\"Goal\" :in-theory (enable my-consp))))
 })
 </li>

 </ul>

 <h3>Applicability condition failure</h3>

 <p>If the failure is in the @(':assumptions-preserved') applicability
 condition, consider supplying @(':hints'), first proving useful rules, or
 both.</p>

 <h3>Preserving special behavior such as side-effects</h3>

 <p>Maybe your call of @('simplify') succeeded, but the result failed to
 preserve a desired call of @(tsee prog2$), @(tsee ec-call), @(tsee time$), or
 another such operator that provides special behavior.  See @(see
 acl2::return-last-blockers).</p>

 <h3>Recursion and equivalence relations</h3>

 <p>As of this writing, the @('simplify') transformation does not fully support
 the use of the @(':equiv') option for recursive definitions, though it might
 succeed on occasion.  Consider the following example.</p>

 @({
 (defun f (x)
   (and x 3))

 (defun g (x)
   (if (consp x)
       (equal (g (cdr x)) (car (cons 3 x)))
     (f x)))

 (simplify g :equiv iff)
 })

 <p>The result is an error with the following message.</p>

 @({
 ACL2 Error in (APT::SIMPLIFY G ...):  An attempt to simplify the definition
 of G has failed, probably because the definition of the new function,
 G$1, is recursive and the equivalence relation specified by :EQUIV
 is IFF, not EQUAL.  See :DOC apt::simplify-failure.
 })

 <p>By adding the option @(':show-only t'), we can see the generated
 definition:</p>

 @({
 (DEFUN G$1 (X)
        (DECLARE (XARGS :GUARD T
                        :MEASURE (ACL2-COUNT X)
                        :VERIFY-GUARDS NIL))
        (IF (CONSP X)
            (EQUAL (G$1 (CDR X)) 3)
            (AND X 3)))
 })

 <p>In this example, the original and proposed simplified definitions are
 actually <i>not</i> Boolean equivalent.  But in some cases, they might be
 equivalent but ACL2 fails to prove this.</p>

 <p>A solution for these other cases, where equivalence holds but was not
 successfully proved, might be first to prove suitable congruence rules, so
 that at each recursive call in the simplified definition (usually the new
 definition, as in the error above), it suffices to preserve the specified
 congruence relation.  This may eventually be worked into a new applicability
 condition.  (A comment about this may be found in the source code for
 this :doc topic.)</p>

 <h3>General approaches to unsuccessful invocations of @('simplify')</h3>

 <p>Here are several ways to get more information about what is happening.</p>

 <ul>

 <li>Use @(':print :info') to get a running commentary and perhaps a more
 detailed error.</li>

 <li>Use @(':print :all') to get even more output.  This maximal level of
 output may be distracting, but near the end of it you might find useful
 simplification checkpoints, for example from a failed attempt to prove the
 measure conjecture.  Those checkpoints may serve, as is common when using
 ACL2, to help you to discover additional theorems to prove first, in
 particular, to be stored as rewrite rules.</li>

 <li>Use @('show-simplify') with the same arguments as you used for
 @('simplify'), to get the event form that is actually submitted by your call
 of @('simplify').  Then use @(':')@(tsee redo-flat) to get to the failed
 event, perhaps using @(':')@(tsee pbt) to see which event failed by seeing
 which events from @('show-simplify') are now in the @(see world).  Then p
 submit that failed event and see if the output helps you to fix your
 @('simplify') call.</li>

 </ul>

 <p>(If you have any suggestions for other steps to take upon failure, by all
 means add them here or ask someone to do so!)</p>

 ")

(defxdoc acl2::return-last-blockers
  :parents (simplify)
  :short "Functions and rules for @(tsee prog2$) and other macros implemented with @(tsee return-last)."
  :long "<p><b>Summary</b>.  The theory named @('return-last-blockers'), in the
 @('\"ACL2\"') package, contains @(see acl2::rune)s that can be @(see disable)d
 to preserve calls of certain special operators &mdash; including @(tsee
 prog2$), @(tsee mbe), @(tsee time$), and others &mdash; when invoking the
 @(see simplify) transformation.  Included are the definition runes for
 corresponding functions @('acl2::prog2$-fn'), @('acl2::mbe-fn'),
 @('acl2::time$-fn').  This is all explained further below.</p>

 <p>The ACL2 system makes use of many special macros that are implemented using
 an operator, @(tsee return-last), that provides special behavior in the
 underlying Lisp implementation.  These include @(tsee prog2$), @(tsee time$),
 @(tsee mbe), and several others.  Evaluate the form @('(table
 return-last-table)') to get an idea of what they are, for example as follows
 (comments added).</p>

 @({
 ACL2 !>(table return-last-table)
  ((TIME$1-RAW . TIME$1) ; time$
   (WITH-PROVER-TIME-LIMIT1-RAW . WITH-PROVER-TIME-LIMIT1) ; with-prover-time-limit
   (WITH-FAST-ALIST-RAW . WITH-FAST-ALIST) ; with-fast-alist
   (WITH-STOLEN-ALIST-RAW . WITH-STOLEN-ALIST) ; with-stolen-alist
   (FAST-ALIST-FREE-ON-EXIT-RAW . FAST-ALIST-FREE-ON-EXIT) ; fast-alist-free-on-exit
   (PROGN . PROG2$) ; prog2$
   (MBE1-RAW . MBE1) ; mbe
   (EC-CALL1-RAW . EC-CALL1) ; ec-call
   (WITH-GUARD-CHECKING1-RAW . WITH-GUARD-CHECKING1)) ; with-guard-checking
 ACL2 !>
 })

 <p>For each such operator @('op') (those in the comments just above), the
 @('\"simplify\"') book defines a ``return-last blocker'' function, @('op-fn'),
 that is obtained by adding the suffix @('\"-FN\"') to its name.  For example,
 corresponding to @('prog2$') is a function, @('prog2$-fn').  Each such
 function is defined logically to return the second of its two arguments, and
 thus it agrees logically with the corresponding macro; for example,
 @('(prog2$-fn x y)') is provably equal to @('y') and hence also to @('(prog2$
 x y)').</p>

 <p>The theory named @('return-last-blockers'), in the @('\"ACL2\"') package,
 contains three rules for each return-last blocker: its @(see acl2::definition)
 rule, its @(see acl2::executable-counterpart) rule, and its @(see
 acl2::type-prescription) rule.  These rules are all @(see enable)d by
 default.</p>

 <p>@(tsee Return-last) is in a class of operators, @(see acl2::guard-holders),
 whose calls are typically expanded before a rule or a ``@(see
 acl2::normalize)d'' definition body is stored.  This can be unfortunate for
 simplification if one intends to preserve the special behavior afforded by the
 operator, such as @(tsee prog2$) or @(tsee time$), that generated that use of
 @('return-last').  The following edited log shows that by disabling blockers
 one can get the desired result in such cases.</p>

 @({
 ACL2 !>(defun foo (n) (time$ (reverse (make-list n))))
 [[.. output elided ..]]
  FOO
 ACL2 !>(simplify foo)
 ; Notice that the time$ call has been eliminated!
 (DEFUN FOO$1 (N)
        (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
        (REPEAT N NIL))
 (DEFTHM FOO-BECOMES-FOO$1 (EQUAL (FOO N) (FOO$1 N)))
 ACL2 !>:u ; Undo and try again, this time to preserve the time$ call.
  L         3:x(DEFUN FOO (N) ...)
 ACL2 !>(simplify foo

 ; Disable time$-fn to preserve the time$ call.  It might be good to disabled
 ; associated runes (:e time$-fn) and (:t time$-fn) as well, but in this case,
 ; at least, that wasn't necessary.

                  :disable (time$-fn))
 (DEFUN FOO$1 (N)
        (DECLARE (XARGS :GUARD T :VERIFY-GUARDS NIL))
        (TIME$ (REPEAT N NIL)))
 (DEFTHM FOO-BECOMES-FOO$1 (EQUAL (FOO N) (FOO$1 N)))
 ACL2 !>
 })")

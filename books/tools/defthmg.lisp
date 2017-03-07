; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

; IMPLIEZ is defined in std/basic/defs.lisp:
(include-book "std/basic/defs" :dir :system)

(program)
(set-state-ok t)

(defun impliez-ify (form ctx state)

; We return a special value, (value nil), if IMPLIES does not occur in the
; translation of form.  The caller should handle that appropriately.

  (let ((wrld (w state)))
    (er-let*
     ((term1 (translate form t t t ctx wrld state)))
     (cond
      ((ffnnamep 'implies term1)
       (mv-let (vars term2)

; This is an odd use of sublis-fn, since it replaces a function with a macro.
; But it seems to be OK, and since defthmg generates event forms that are
; checked, there is no soundness issue.

         (sublis-fn '((implies . impliez)) term1 nil)
         (declare (ignore vars))
         (value (untranslate term2 nil wrld))))
      (t (value nil))))))

(defun defthmg-rule-classes (rule-classes thm)

; We leave some of the error-checking to the generated defthm.

  (cond ((atom rule-classes) rule-classes) ; should be nil
        (t (cons (let ((x (car rule-classes)))

; The following code is adapted from source function translate-rule-class.

                   (cond
                    ((keywordp x)
                     (list x
                           :COROLLARY
                           thm
                           :hints
                           '(("Goal" :in-theory (theory 'minimal-theory)))))
                    ((and (consp x)
                          (keywordp (car x))
                          (keyword-value-listp (cdr x)))
                     (cond
                      ((assoc-keyword :COROLLARY (cdr x)) x)
                      (t `(,(car x)
                           :COROLLARY ,thm
                           ,@(if (assoc-keyword :hints (cdr x))
                                 nil
                               `(:hints
                                 '(("Goal"
                                    :in-theory (theory 'minimal-theory)))))
                           ,@(cdr x)))))
                    (t ; bad rule-class; let defthm catch this
                     x)))
                 (defthmg-rule-classes (cdr rule-classes) thm)))))

(defun defthmg-fn (event-form name term rule-classes verify-guards
                              verify-guards-p guard-hints state)

; Note that rule-classes is (:REWRITE) if no rule-classes were supplied with
; the original defthm.

  (let ((ctx (cons 'defthmg name)))
    (er-let* ((term-z (impliez-ify term ctx state)))
      (mv-let (implies-p term-z)
        (cond ((null term-z)
               (mv nil term))
              (t
               (mv t term-z)))
        (let ((rule-classes
               (if implies-p
                   (defthmg-rule-classes
; Borrowing code from source function translate-rule-classes:
                     (cond ((null rule-classes) nil)
                           ((atom rule-classes) (list rule-classes))
                           (t rule-classes))
                     term)
                 rule-classes)))
          (cond
           ((eq rule-classes :error)

; This error message is less informative than one gets with defthm.  But it
; doesn't seem worth the effort to improve it, since it already points to
; suitable :doc.

            (er soft ctx
                "Illegal :RULE-CLASSES argument.  See :DOC rule-classes."))
           (t
            (let ((defthm-form
                    `(defthm ,name
                       ,term-z
                       :rule-classes ,rule-classes
                       ,@(remove-keyword
                          :verify-guards
                          (remove-keyword
                           :guard-hints
                           (remove-keyword
                            :rule-classes
                            (cdddr event-form))))))
                  (vg (if verify-guards-p
                          verify-guards
                        (not (eql (default-verify-guards-eagerness (w state))
                                  0)))))
              (value (cond
                      (vg `(progn ,defthm-form
                                  (verify-guards ,name
                                    ,@(and guard-hints
                                           `(:hints ,guard-hints)))))
                      (t defthm-form)))))))))))

(defmacro defthmg (&whole event-form
                          name term
                          &key (rule-classes '(:REWRITE))
                          (verify-guards 'nil ; irrelevant value
                            verify-guards-p)
                          guard-hints
                          &allow-other-keys) ; other defthm keyword args
  (declare (xargs :guard (booleanp verify-guards)))
  `(make-event (defthmg-fn ',event-form ',name ',term ',rule-classes
                          ',verify-guards ',verify-guards-p ',guard-hints
                          state)))

(defxdoc defthmg

; Technical point: because defthmg's implementation using make-event, one might
; think that the make-event expansion during the second pass of encapsulate or
; certify-book could differ from that of the first pass, because of the
; dependence on the world.  However, that dependence is only on
; verify-guards-eagerness, which is carried in the acl2-defaults-table and
; hence must actually be the same at expansion time on both passes.  This seems
; like too subtle a point to make in user-level documentation, so we only make
; it here in a Lisp comment.

  :parents (events guard)
  :short "Variant of @(tsee defthm) supporting @(see guard) verification"
  :long "<p>After a @(tsee defthm) event introduces a name, @(tsee
 verify-guards) can be called on that theorem name, just as it can be called on
 a function symbol.  However, the proof obligation for verifying @(see guard)s
 is often not a theorem.  After presenting the general form for @('defthmg'),
 we give a running example, which illustrates a problem with @('implies') for
 guard verification and how @('defthmg') solves that problem.</p>

 @({
 Example Form:
 (defthmg true-listp-member-equal
   (implies (true-listp x)
            (true-listp (member-equal a x))))

 General Form:
 (defthmg name
   body
 ;;; defthm arguments:
   :rule-classes  rule-classes
   :instructions  instructions
   :hints         hints
   :otf-flg       otf-flg
 ;;; new arguments:
   :verify-guards verify-guards
   :guard-hints   guard-hints)
 })

 <p>where all but the last two keyword arguments are exactly as for @(tsee
 defthm).  If @(':verify-guards') is supplied then it must be @('t') or
 @('nil'), indicating that a call of @(tsee verify-guards) on @('name') will or
 won't be attempted, respectively.  If @(':verify-guards') is omitted, then its
 value is normally treated as @('t'); but it is treated as @('nil') if the
 @(see default-verify-guards-eagerness) is 0 (rather than either 2 or its usual
 value of 1, as we will assume for the rest of this documentation topic).
 Finally, if @(':guard-hints') is supplied and @('verify-guards') is attempted
 on @('name'), then the specified @('guard-hints') will become the value of
 @(':hints') for that @('verify-guards') event.</p>

 <p>We now consider in some detail the example displayed above.  Consider it
 again, but this time with @('defthm') instead of @('defthmg').</p>

 @({
 (defthm true-listp-member-equal
   (implies (true-listp x)
            (true-listp (member-equal a x))))
 })

 <p>The proof succeeds, after which we might try to call @(tsee verify-guards).
 But @('verify-guards') would guarantee that the indicated form will evaluate
 without a Lisp guard violation for all values of @('a') and @('x'), and that's
 not always the case!  Suppose for example that @('x') is @('17').  Since
 @('implies') is an ordinary function, evaluation will take place for both its
 arguments, even though @('(true-listp x)') is false.  The call
 @('(member-equal a 17)') will cause a guard violation, regardless of the value
 of @('a'), since the guard for @(tsee member-equal) requires that its second
 argument satisfy @(tsee true-listp).</p>

 <p>A way to allow guard verification for such a theorem is to replace
 @('implies') by the macro, @(tsee impliez), whose calls expand to calls of
 @('IF'), for example as follows (see @(tsee trans1)).</p>

 @({
 ACL2 !>:trans1 (impliez (true-listp x)
                         (true-listp (member-equal a x)))
  (IF (TRUE-LISTP X)
      (TRUE-LISTP (MEMBER-EQUAL A X))
      T)
 ACL2 !>
 })

 <p>When @('x') is 17, evaluation of the form above (either the @('impliez')
 version or its expansion to an @('IF') call) will <i>not</i> lead to
 evaluation of the @('member-equal') call.  Guard verification will then be
 possible.</p>

 <p>But simply changing @('implies') to @('impliez') doesn't work.</p>

 @({
 ACL2 !>(defthm true-listp-member-equal
          (impliez (true-listp x)
                   (true-listp (member-equal a x))))


 ACL2 Error in ( DEFTHM TRUE-LISTP-MEMBER-EQUAL ...):  A :REWRITE rule
 generated from TRUE-LISTP-MEMBER-EQUAL is illegal because it rewrites
 the IF-expression (IF (TRUE-LISTP X) (TRUE-LISTP (MEMBER-EQUAL A X)) 'T).
 For general information about rewrite rules in ACL2, see :DOC rewrite.
 })

 <p>The error message is basically telling us that we need @('implies'), not
 @('impliez') (or @('IF')), in order to store the indicated theorem as a @(see
 rewrite) rule, which is the default.  We can overcome this problem by
 supplying an explicit @(':')@(tsee corollary) equal to the original theorem,
 as follows.</p>

 @({
 (defthm true-listp-member-equal
   (impliez (true-listp x)
            (true-listp (member-equal a x)))
   :rule-classes
   ((:rewrite :corollary
              (implies (true-listp x)
                       (true-listp (member-equal a x))))))
 })

 <p>Now the intended rewrite rule is stored, and also we can verify guards,
 since the guard proof obligation is based on the body of the @('defthm')
 event (with @('impliez')), not the corollary.</p>

 @({
 (verify-guards true-listp-member-equal)
 })

 <p>The purpose of @('defthmg') is to automate the process described above.
 Our example @('defthmg') call generates a @(tsee progn) containing the
 @('defthm') and @('verify-guards') forms displayed just above (except for the
 addition of suitable @(':')@(tsee hints) to streamline the process).</p>

 @({
 (DEFTHM TRUE-LISTP-MEMBER-EQUAL
   (IMPLIEZ (TRUE-LISTP X)
            (TRUE-LISTP (MEMBER-EQUAL A X)))
   :RULE-CLASSES
   ((:REWRITE
     :COROLLARY (IMPLIES (TRUE-LISTP X)
                         (TRUE-LISTP (MEMBER-EQUAL A X)))
     :HINTS ((\"Goal\" :IN-THEORY (THEORY 'MINIMAL-THEORY))))))

 (VERIFY-GUARDS TRUE-LISTP-MEMBER-EQUAL)
 })

 <p>If @(':')@(tsee rule-classes) are supplied explicitly, these will be
 handled appropriately: for each rule class, if a @(':corollary') is supplied
 explicitly then that rule class is not changed, and otherwise a
 @(':corollary') is specified to be the original theorem (hence with
 @('implies'), not changed to @('impliez')), and the @(':in-theory') hint
 displayed just above will be generated in order to make the proof of the
 corollary very fast.</p>

 <p>The following more complex (but rather nonsensical) example illustrates the
 various arguments of @('defthmg').</p>

 @({
 (defthmg true-listp-member-equal
   (implies (true-listp x)
            (true-listp (member-equal a x)))
   :verify-guards t
   :guard-hints ((\"Goal\" :use car-cons))
   :hints ((\"Goal\" :induct (member-equal a x)))
   :rule-classes
   (:rewrite
    (:rewrite ; awful rule with free variable
     :corollary (implies (not (true-listp (member-equal a x)))
                         (not (true-listp x))))
    :type-prescription)
   :otf-flg t)
 })

 <p>Here are the two events generated after successfully evaluating the form
 above.  Notice that the rule class with an explicit @(':corollary') is not
 modified.</p>

 @({
 (DEFTHM TRUE-LISTP-MEMBER-EQUAL
   (IMPLIEZ (TRUE-LISTP X)
            (TRUE-LISTP (MEMBER-EQUAL A X)))
   :RULE-CLASSES
   ((:REWRITE
     :COROLLARY (IMPLIES (TRUE-LISTP X)
                         (TRUE-LISTP (MEMBER-EQUAL A X)))
     :HINTS ((\"Goal\" :IN-THEORY (THEORY 'MINIMAL-THEORY))))
    (:REWRITE
     :COROLLARY (IMPLIES (NOT (TRUE-LISTP (MEMBER-EQUAL A X)))
                         (NOT (TRUE-LISTP X))))
    (:TYPE-PRESCRIPTION
     :COROLLARY (IMPLIES (TRUE-LISTP X)
                         (TRUE-LISTP (MEMBER-EQUAL A X)))
     :HINTS ((\"Goal\" :IN-THEORY (THEORY 'MINIMAL-THEORY)))))
   :HINTS ((\"Goal\" :INDUCT (MEMBER-EQUAL A X)))
   :OTF-FLG T)

 (VERIFY-GUARDS TRUE-LISTP-MEMBER-EQUAL
   :HINTS ((\"Goal\" :USE CAR-CONS)))
 })")

; Copyright (C) 2018, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc acl2-pc::when-not-proved
  :parents (proof-builder-commands)
  :short "(macro)
Run the given instructions unless all goals have been proved"
  :long "@({
 Example:
 (when-not-proved (succeed bash) induct (repeat prove))

 General Form:
 (when-not-proved instr1 ... instrk)
 })

 <p>where each @('instri') is a proof-builder instruction.</p>")

(defxdoc acl2-pc::insist-all-proved
  :parents (proof-builder-commands)
  :short "(macro)
Run the given instructions, then fail if there remain unproved goals"
  :long "@({
 Example:
 (insist-all-proved (succeed bash) induct (repeat prove))

 General Form:
 (insist-all-proved instr1 ... instrk)
 })

 <p>where each @('instri') is a proof-builder instruction.</p>

 <p>Run the given instructions until one fails, as with the @(':do-strict')
 command.  The call of @(':insist-all-proved') succeeds only when none of those
 instructions fails and, moreover, all goals are proved when the instructions
 complete.</p>")

(defxdoc acl2-pc::prove-guard
  :parents (proof-builder-commands verify-guards guard-theorem)
  :short "(macro)
Verify @(see guard)s efficiently by using a previous guard theorem."
  :long "@({
 Example:
 (prove-guard f1 (disable h))

 Example of typical usage:
 (defun f2 (x)
   (declare
    (xargs :guard
           (g x)
           :guard-hints
           ((\"Goal\"
             :instructions
             ((prove-guard f1
                           (disable h)))))))
   (f2-body x))

 General Forms:
 (prove-guard fn)
 (prove-guard fn thy)
 (prove-guard fn thy alt-thy)
 (prove-guard fn thy alt-thy verbose)
 })

 <p>where @('fn') is a known function symbol and @('thy') and @('alt-thy'),
 when supplied and non-@('nil'), are @(see theory) expressions.</p>

 <p>This @(see proof-builder) macro attempts to prove a theorem, typically a
 @(see guard) proof obligation, by applying the hint @(':guard-theorem fn') in
 a carefully controlled, efficient manner (using the @(':fancy-use') @(see
 proof-builder) macro).  This proof is attempted in the theory, @('thy'), if
 supplied and non-@('nil'), else in the @(tsee current-theory).  If that proof
 fails, then a single, ordinary prover call is made with that @(':use') hint
 and in the following theory: @('alt-thy') if supplied and non-@('nil'), else
 @('thy') if supplied and non-@('nil'), else the @(see current-theory).  If the
 proof has not yet succeeded and the original theory is not @('nil') or
 @('(current-theory :here)'), then a final proof is attempted in the same
 careful manner as the first proof attempt.</p>

 <p>Output is inhibited by default.  However, if @('verbose') is @('t') then
 output is as specified by the enclosing environment; and if @('verbose') is
 any other non-@('nil') value, then output is mostly inhibited for that attempt
 by use of the proof-builder command, @(':quiet').  In all of those
 non-@('nil') cases for the @('verbose') input, a little message will be
 started at the beginning of the second and third proof attempts, if any.</p>

 <p>For a few small examples, see community book
 @('kestrel/utilities/proof-builder-macros-tests.lisp.')</p>

 <p>For a way to use lemma instances other than guard theorems, see @(see
 acl2-pc::fancy-use).</p>

 <p>Hacker tip: Invoke @('(trace$ acl2::pc-fancy-use-fn)') to see the
 proof-builder instruction created when invoking @('prove-guard').</p>")

(defxdoc acl2-pc::prove-termination
  :parents (proof-builder-commands verify-termination termination-theorem)
  :short "(macro)
Prove termination efficiently by using a previous termination theorem."
  :long "@({
 Example:
 (prove-termination f1 (disable h))

 Example of typical usage:
 (defun f2 (x)
   (declare
    (xargs :hints
           ((\"Goal\"
             :instructions
             ((prove-termination
               f1
               (disable h)))))))
   (f2-body x))

 General Forms:
 (prove-termination fn)
 (prove-termination fn thy)
 (prove-termination fn thy alt-thy)
 (prove-termination fn thy alt-thy verbose)
 })

 <p>where @('fn') is a known function symbol and @('thy') and @('alt-thy'),
 when supplied and non-@('nil'), are @(see theory) expressions.</p>

 <p>This @(see proof-builder) macro attempts to prove a theorem, typically a
 termination proof obligation, by applying the hint @(':termination-theorem
 fn') in a carefully controlled, efficient manner (using the @(':fancy-use')
 @(see proof-builder) macro).  This proof is attempted in the theory, @('thy'),
 if supplied and non-@('nil'), else in the @(tsee current-theory).  If that
 proof fails, then a single, ordinary prover call is made with that @(':use')
 hint and in the following theory: @('alt-thy') if supplied and non-@('nil'),
 else @('thy') if supplied and non-@('nil'), else the @(see current-theory).
 If the proof has not yet succeeded and the original theory is not @('nil') or
 @('(current-theory :here)'), then a final proof is attempted in the same
 careful manner as the first proof attempt.</p>

 <p>Output is inhibited by default.  However, if @('verbose') is @('t') then
 output is as specified by the enclosing environment; and if @('verbose') is
 any other non-@('nil') value, then output is mostly inhibited for that attempt
 by use of the proof-builder command, @(':quiet').  In all of those
 non-@('nil') cases for the @('verbose') input, a little message will be
 started at the beginning of the second and third proof attempts, if any.</p>

 <p>For a few small examples, see community book
 @('kestrel/utilities/proof-builder-macros-tests.lisp.')</p>

 <p>For a way to use lemma instances other than termination theorems, see @(see
 acl2-pc::fancy-use).</p>

 <p>Hacker tip: Invoke @('(trace$ acl2::pc-fancy-use-fn)') to see the
 proof-builder instruction created when invoking @('prove-termination').</p>")

(defxdoc acl2-pc::fancy-use
  :parents (proof-builder-commands)
  :short "(macro)
Use one or more previously-proved theorems efficiently."
  :long "@({
 Examples:
 (fancy-use (:instance my-thm (x a) (y b))
            (disable h))
 (fancy-use (foo (:instance bar (x a))))

 Example of typical usage:
 (defun f2 (x)
   (declare
    (xargs :hints
           ((\"Goal\"
             :instructions
             ((fancy-use ((:instance my-thm (x a) (y b)))
                         (disable h)))))))
   (f2-body x))

 General Forms:
 (fancy-use lmi+)
 (fancy-use lmi+ thy)
 (fancy-use lmi+ thy alt-thy)
 (fancy-use lmi+ thy alt-thy verbose)
 })

 <p>where @('lmi+') is a @(see lemma-instance) or a true list of
 lemma-instances, that is, an object that can be supplied as a @(':use') hint
 (see @(see hints)); and @('thy') and @('alt-thy'), when supplied and
 non-@('nil'), are @(see theory) expressions.</p>

 <p>This @(see proof-builder) macro attempts to prove a theorem by applying the
 @(':use') hint constructed from @('lmi+') in a carefully controlled, efficient
 manner.  This proof is attempted in the theory, @('thy'), if supplied and
 non-@('nil'), else in the @(tsee current-theory).  If that proof fails, then a
 single, ordinary prover call is made with that @(':use') hint and in the
 following theory: @('alt-thy') if supplied and non-@('nil'), else @('thy') if
 supplied and non-@('nil'), else the @(see current-theory).  If the proof has
 not yet succeeded and the original theory is not @('nil') or
 @('(current-theory :here)'), then a final proof is attempted in the same
 careful manner as the first proof attempt.</p>

 <p>Output is inhibited by default.  However, if @('verbose') is @('t') then
 output is as specified by the enclosing environment; and if @('verbose') is
 any other non-@('nil') value, then output is mostly inhibited for that attempt
 by use of the proof-builder command, @(':quiet').</p>

 <p>For a few small examples, see community book
 @('kestrel/utilities/proof-builder-macros-tests.lisp.')</p>

 <p>For convenient shortcuts in the case of using guard or termination
 theorems, see @(see acl2-pc::prove-guard) and @(see
 acl2-pc::prove-termination), respectively.</p>

 <p>Hacker tip: Invoke @('(trace$ acl2::pc-fancy-use-fn)') to see the
 proof-builder instruction created when invoking @('fancy-use').</p>")

(define-pc-macro when-not-proved (&rest instrs)
  (when-goals-trip
   (value (cons 'do-all instrs))))

(define-pc-macro insist-all-proved (&rest instrs)
  (value `(do-strict ,@instrs
                     (when-not-proved fail))))

(defun lmi+-to-lmi-lst (lmi+)

; This function takes an object that can be given as a :use hint, and it
; returns a list of lemma-instance objects.  It is closely patterned after ACL2
; source function translate-use-hint, but unlike that function it ignores the
; world and operates purely syntactically, providing equivalent functionality
; if lmi+ is legal.

  (cond ((atom lmi+) (list lmi+))
        ((keywordp (car lmi+)) ; (:instance ...), (:rewrite ...), etc.
         (list lmi+))
        (t lmi+)))

(define-pc-help print-msg (str args &optional evisc-tuple)

; This is kind of a hack in support of the prove-guard and prove-termination
; macro commands.  Maybe we'll add xdoc later if this has broader utility.

; Example:
;   ->: (:PRINT-MSG "hello ~x0~|List: ~&1" (WORLD (a b c)))
;   hello WORLD
;   List: A, B and C
;   ->:

  (let ((msg (cons str (pairlis$ *base-10-chars* args))))
    (fms0 "~|~@0~|" (list (cons #\0 msg)) 0 evisc-tuple)))

(defun pc-fancy-use-fn1 (lmi-lst theory)
  `(protect
    (insist-all-proved
     ,@(and theory `((in-theory ,theory)))
     (succeed s-prop) ; expand implies, etc.
     (when-not-proved
      (use ,@lmi-lst)
      (when-not-proved
       (demote)
       (dv 1)
       (succeed s-prop) ; expand implies, etc.
       (when-not-proved ; probably unnecessary here, but harmless
        (add-abbreviation @hyp@)
        (= & (hide (? @hyp@)) 0) ; hide the used theorem
        cg                       ; Prove that hyp = (hide hyp).
        (succeed drop) ; Proof of hyp = (hide hyp) does not need hypotheses.
        (:prove :hints (("Goal"

; It's not clear that the following :do-not '(preprocess) is important.  It
; seems potentially helpful to avoid the use of preprocessing for complex
; Boolean reasoning, since clausify is probably much more efficient.

                         :do-not '(preprocess)
                         :expand ((:free (v) (hide v)))
                         :in-theory nil)))
        top ; back to top of main goal: (implies (hide hyp) new-thm)
        split
        (repeat
         (protect
          (comment "Start next goal")
          (demote 1)        ; demote (hide hyp)
          (dv 1)            ; at (hide hyp)
          (= & (? @hyp@) 0) ; replace with hyp
          up                ; back to the top
          prove
          ;; We are now at the goal to prove (equal (hide hyp) hyp).
          (succeed drop) ; Proof of hyp = (hide hyp) does not need hypotheses.
          (:prove :hints (("Goal"
                           :do-not '(preprocess) ; probably unnecessary
                           :expand ((:free (v) (hide v)))
                           :in-theory nil)))))))))))

(defun pc-fancy-use-fn (lmi+ theory fallback-theory verbose expl)

; If verbose is non-nil then we print a message when starting the second or
; third attempt at proving with the given lemma-instance(s).  The message is
; then as follows (substituting "Third" for "Second" if it's the third try):

;   Second try <expl>: calling prover directly ....

; For example, if expl is "at guard verification" then we see:

;   Second try at guard verification: calling prover directly ....

  (flet ((vb (verbose instr)
             (case verbose
               ((t) instr)
               ((nil) `(:quiet! ,instr))
               (otherwise `(:quiet ,instr)))))
    (let* ((lmi-lst (lmi+-to-lmi-lst lmi+))
           (instr1 (vb verbose (pc-fancy-use-fn1 lmi-lst theory)))
           (instr2a
            (let ((thy (or fallback-theory theory)))
              `(do-all-no-prompt
                ,(if verbose
                     `(:print-msg "~%Second try~@0: calling the prover ~
                                   directly...~|"
                                  (,(if expl
                                        (msg " ~@0" expl)
                                      "")))
                   :skip)
                ,(vb verbose
                     `(:prove
                       :hints (("Goal"
                                :use ,lmi-lst
                                ,@(and thy
                                       `(:in-theory ,thy)))))))))
           (instr2b (if (or (null theory)
                            (equal theory '(current-theory :here)))
                        nil ; already tried the proof attempt with instr1
                      `(do-all-no-prompt
                        ,(if verbose
                             `(:print-msg "~%~@0 try~@1: proving carefully ~
                                           using the current theory...~|"
                                          (,(if instr2a "Third" "Second")
                                           ,(if expl
                                                (msg " ~@0" expl)
                                              "")))
                           :skip)
                        ,(vb verbose
                             (pc-fancy-use-fn1 lmi-lst nil)))))
           (instr2 (if instr2b
                       `(orelse ,instr2a ,instr2b)
                     instr2a)))
      `(orelse ,instr1 ,instr2))))

(define-pc-macro prove-guard (old-fn
                              &optional theory fallback-theory verbose)
  (value (pc-fancy-use-fn `(:guard-theorem ,old-fn)
                          theory fallback-theory verbose
                          "at guard verification")))

(define-pc-macro prove-termination (old-fn
                                    &optional theory fallback-theory verbose)
  (value (pc-fancy-use-fn `(:termination-theorem ,old-fn)
                          theory fallback-theory verbose
                          "at proving termination")))

(define-pc-macro fancy-use (lmi+
                            &optional theory fallback-theory verbose)
  (value (pc-fancy-use-fn lmi+
                          theory fallback-theory verbose nil)))

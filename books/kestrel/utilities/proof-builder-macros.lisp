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

(defxdoc acl2-pc::check-all-proved
  :parents (proof-builder-commands)
  :short "(macro)
Run the given instructions, then fail if there remain unproved goals"
  :long "@({
 Example:
 (check-all-proved (succeed bash) induct (repeat prove))

 General Form:
 (check-all-proved instr1 ... instrk)
 })

 <p>where each @('instri') is a proof-builder instruction.</p>")

(defxdoc acl2-pc::prove-guard
  :parents (proof-builder-commands verify-guards guard-theorem)
  :short "(macro)
Verify guards efficiently by using a previous guard theorem."
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
 guard proof obligation, by applying the hint @(':guard-theorem fn') in a
 carefully controlled, efficient manner; this is done in the theory, @('thy'),
 if supplied and non-@('nil'), else in the @(tsee current-theory).  If that
 proof fails, then the proof is tried again without that @(':use') hint, this
 time in the following theory, @('thy''): @('thy') if supplied and
 non-@('nil'), else @('alt-thy') if supplied and non-@('nil'), else the
 current-theory.</p>

 <p>By default, that attempt is done without output.  However, if @('verbose')
 is @('t') then there is no inhibition of output, and if @('verbose') is any
 other non-@('nil') value, then output is mostly inhibited by use of the
 proof-builder command, @(':quiet').</p>

 <p>If that attempt fails, then the prover is called directly (discarding all
 of that attempt), in the theory @('thy'') defined above.  The @('verbose')
 output is ignored for this prover call.</p>

 <p>For a few small examples, see community book
 @('kestrel/utilities/proof-builder-macros-tests.lisp.')</p>

 <p>Hacker tip: Invoke @('(trace$ acl2::prove-termination-or-guard-fn)') to see
 the proof-builder instruction created when invoking @('prove-guard').</p>")

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
 fn') in a carefully controlled, efficient manner; this is done in the theory,
 @('thy'), if supplied and non-@('nil'), else in the @(tsee current-theory).
 If that proof fails, then the proof is tried again without that @(':use')
 hint, this time in the following theory, @('thy''): @('thy') if supplied and
 non-@('nil'), else @('alt-thy') if supplied and non-@('nil'), else the
 current-theory.</p>

 <p>By default, that attempt is done without output.  However, if @('verbose')
 is @('t') then there is no inhibition of output, and if @('verbose') is any
 other non-@('nil') value, then output is mostly inhibited by use of the
 proof-builder command, @(':quiet').</p>

 <p>If that attempt fails, then the prover is called directly (discarding all
 of that attempt), in the theory @('thy'') defined above.  The @('verbose')
 output is ignored for this prover call.</p>

 <p>For a few small examples, see community book
 @('kestrel/utilities/proof-builder-macros-tests.lisp.')</p>

 <p>Hacker tip: Invoke @('(trace$ acl2::prove-termination-or-guard-fn)') to see
 the proof-builder instruction created when invoking
 @('prove-termination').</p>")

(define-pc-macro when-not-proved (&rest instrs)
  (when-goals-trip
   (value (cons 'do-all instrs))))

(define-pc-macro check-all-proved (&rest instrs)
  (value `(do-all ,@instrs
                  (when-not-proved fail))))

(defun prove-termination-or-guard-fn (kwd old-fn theory fallback-theory verbose)
  (let* ((thy (or fallback-theory theory))
         (instr1
          `(protect
            ,@(and theory `((in-theory ,theory)))
            (succeed s-prop) ; expand implies, etc.
            (when-not-proved
             (use (,kwd ,old-fn))
             (when-not-proved
              (demote)
              (dv 1)
              (succeed s-prop) ; expand implies, etc.
              (when-not-proved ; probably unnecessary here, but harmless
               (add-abbreviation @hyp@)
               (= & (hide (? @hyp@)) 0) ; hide the used guard-theorem
               cg                       ; Prove that hyp = (hide hyp).
               (succeed (drop 1)) ; Proof of hyp = (hide hyp) does not need hypotheses.
               (:prove :hints (("Goal"

; It's not clear that the following :do-not '(preprocess) is important.  It
; seems potentially helpful to avoid the use of preprocessing for complex
; Boolean reasoning, since clausify is probably much more efficient.

                                :do-not '(preprocess)
                                :expand ((:free (v) (hide v)))
                                :in-theory nil)))
               top ; back to top of main goal: (implies (hide hyp) new-guard-thm)
               split
               (repeat
                (protect
                 (comment "Start next goal")
                 (demote 1)        ; demote (hide hyp)
                 (dv 1)            ; at (hide hyp)
                 (= & (? @hyp@) 0) ; replace with hyp
                 up                ; back to the top
                 (orelse prove
                         (do-all
                          (comment "Trying without a :use hint ....")
                          (:prove
                           ,@(and thy
                                  `(:hints (("Goal" :in-theory ,thy)))))))
                 ;; We are now at the goal to prove (equal (hide hyp) hyp).
                 (succeed drop) ; Proof of hyp = (hide hyp) does not need hypotheses.
                 (:prove :hints (("Goal"
                                  :do-not '(preprocess) ; probably unnecessary
                                  :expand ((:free (v) (hide v)))
                                  :in-theory nil))))))))))
         (instr2
          `(:prove
            :hints (("Goal"
                     :use ((,kwd ,old-fn))
                     ,@(and thy
                            `(:in-theory ,thy)))))))
    (case verbose
      ((t) `(orelse (check-all-proved ,instr1) ,instr2))
      ((nil) `(orelse (:quiet! (check-all-proved ,instr1)) ,instr2))
      (otherwise `(orelse (:quiet (check-all-proved ,instr1)) ,instr2)))))

(define-pc-macro prove-guard (old-fn
                              &optional theory fallback-theory verbose)
  (value (prove-termination-or-guard-fn :guard-theorem
                                        old-fn theory fallback-theory
                                        verbose)))

(define-pc-macro prove-termination (old-fn
                                    &optional theory fallback-theory verbose)
  (value (prove-termination-or-guard-fn :termination-theorem
                                        old-fn theory fallback-theory
                                        verbose)))

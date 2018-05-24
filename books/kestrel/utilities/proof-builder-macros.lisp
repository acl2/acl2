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
             ; Or below: ((quiet! (prove-guard f1 (disable h))))
             ((prove-guard
               f1
               (disable h))) ))))
   (f2-body x))

 General Forms:
 (prove-guard fn)
 (prove-guard fn thy)
 (prove-guard fn thy alt-thy)
 })

 <p>where @('fn') is a known function symbol and @('thy') and @('alt-thy'),
 when supplied and non-@('nil'), are @(see theory) expression.</p>

 <p>This proof-builder macro attempts to prove a theorem, typically a guard
 proof obligation, by applying the hint @(':guard-theorem fn') in a carefully
 controlled, efficient manner; this is done in the theory, @('thy'), if
 supplied, else in the @(tsee current-theory).  If that proof fails, then the
 proof is tried again without that @(':use') hint, again in the theory @('thy')
 if supplied unless @('alt-thy') is supplied and non-@('nil'), in which case
 that second proof is attempted in that theory.</p>

 <p>For a few small examples, see community book
 @('kestrel/utilities/proof-builder-macros-tests.lisp.')</p>")

(defxdoc acl2-pc::prove-termination
  :parents (proof-builder-commands verify-guards guard-theorem)
  :short "(macro)
Prove termination efficiently by using a previous guard theorem."
  :long "@({
 Example:
 (prove-termination f1 (disable h))

 Example of typical usage:
 (defun f2 (x)
   (declare
    (xargs :hints
           ((\"Goal\"
             :instructions
             ; Or below: ((quiet! (prove-termination f1 (disable h))))
             ((prove-termination
               f1
               (disable h))) ))))
   (f2-body x))

 General Forms:
 (prove-termination fn)
 (prove-termination fn thy)
 (prove-termination fn thy alt-thy)
 })

 <p>where @('fn') is a known function symbol and @('thy') and @('alt-thy'),
 when supplied and non-@('nil'), are @(see theory) expression.</p>

 <p>This proof-builder macro attempts to prove a theorem, typically a
 termination proof obligation, by applying the hint @(':termination-theorem
 fn') in a carefully controlled, efficient manner; this is done in the theory,
 @('thy'), if supplied, else in the @(tsee current-theory).  If that proof
 fails, then the proof is tried again without that @(':use') hint, again in the
 theory @('thy') if supplied unless @('alt-thy') is supplied and non-@('nil'),
 in which case that second proof is attempted in that theory.</p>

 <p>For a few small examples, see community book
 @('kestrel/utilities/proof-builder-macros-tests.lisp.')</p>")

(define-pc-macro when-not-proved (&rest instrs)
  (when-goals-trip
   (value (cons 'do-all instrs))))

(defun prove-termination-or-guard-fn (kwd old-fn theory fallback-theory)
  `(do-all
    ,@(and theory `((in-theory ,theory)))
    (succeed s-prop) ; expand implies, etc.
    (when-not-proved
     (quiet (use (,kwd ,old-fn)))
     (when-not-proved
      (demote)
      (:dv 1)
      (succeed s-prop)  ; expand implies, etc.
      (when-not-proved  ; probably unnecessary here, but harmless
       (:add-abbreviation @hyp@)
       (quiet (= & (hide (? @hyp@)) 0)) ; hide the used guard-theorem
       cg                               ; Prove that hyp = (hide hyp).
       (succeed (drop 1)) ; Proof of hyp = (hide hyp) does not need hypotheses.
       (:prove :hints (("Goal"

; It's not clear that the following :do-not '(preprocess) is important.  It
; seems potentially helpful to avoid the use of preprocessing for complex
; Boolean reasoning, since clausify is probably much more efficient.

                        :do-not '(preprocess)
                        :expand ((:free (v) (hide v)))
                        :in-theory nil)))
       top ; back to top of main goal: (implies (hide hyp) new-guard-thm)
       (quiet split)
       (quiet
        (repeat
         (do-strict
          (comment "Start next goal")
          (demote 1)                 ; demote (hide hyp)
          (dv 1)                     ; at (hide hyp)
          (quiet (= & (? @hyp@) 0))  ; replace with hyp
          up                         ; back to the top
          (orelse prove
                  (do-all
                   (comment "Trying without a :use hint ....")
                   (:prove
                    ,@(let ((thy (or fallback-theory
                                     theory)))
                        (and thy
                             `(:hints
                               (("Goal" :in-theory ,(or fallback-theory
                                                        theory)))))))))
          ;; We are now at the goal to prove (equal (hide hyp) hyp).
          (succeed drop) ; Proof of hyp = (hide hyp) does not need hypotheses.
          (:prove :hints (("Goal"
                           :do-not '(preprocess) ; probably unnecessary
                           :expand ((:free (v) (hide v)))
                           :in-theory nil)))))))))))

(define-pc-macro prove-guard (old-fn &optional theory fallback-theory)
  (value
   (prove-termination-or-guard-fn :guard-theorem old-fn theory fallback-theory)))

(define-pc-macro prove-termination (old-fn &optional theory fallback-theory)
  (value
   (prove-termination-or-guard-fn
    :termination-theorem old-fn theory fallback-theory)))

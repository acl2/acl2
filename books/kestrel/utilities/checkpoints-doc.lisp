; Copyright (C) 2021, ForrestHunt, Inc.
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "xdoc/top" :dir :system)

(defxdoc checkpoint-list

; A wart, documented below, is that we get <GOAL> when aborting the proof to
; use induction on the original goal.  That's because this tool is built on the
; same code base that prints during proof attempts.  One might consider a
; variant of this tool that takes the original input as an argument, and if it
; finds <GOAL> (in the ACL2 package) in the top-stack, that is changed to the
; input (suitably translated or not).  But it might make more sense to store
; the original goal in the ACL2 gag-state structure, which would require a
; change to ACL2.

   :parents (kestrel-utilities output-controls)
   :short "Return prover key checkpoint clauses programmatically."
   :long "<p>Recall the key checkpoints printed at the end of a failed proof
 attempt.  Some are labeled ``Key checkpoint at the top level''; let us call
 these checkpoints ``top-level'', and denote others as ``not top-level''.  When
 the most recent proof attempt was one that failed, @('(checkpoint-list top-p
 state)') returns clauses corresponding to key checkpoints, as follows.  If
 @('top-p') is @('t'), then the list of top-level checkpoints is returned.
 Otherwise the list of checkpoints that are not top-level is returned.  In each
 case, the order of checkpoints is the same as would be found in the summary of
 a proof attempt; that is, their order agrees with the order in which they are
 generated during the proof attempt.</p>

 <p><b>Related tools.</b>  Note that each returned checkpoint is a clause, that
 is, a list of @(see term)s, implicitly disjoined.  For a similar utility that
 instead returns each checkpoint as an untranslated @(see term) such as one
 would see during a proof, see @(see checkpoint-list-pretty).  See also @(see
 show-checkpoint-list) for a related tool that displays checkpoints rather than
 returning them, and see @(see checkpoint-info-list) for a tool similar to
 @('checkpoint-list') that returns additional information.</p>

 <p>Examples may be found in the @(see community-books) file
 @('checkpoints-tests-input.lsp'), with corresponding output (using the @(tsee
 run-script) tool) in that same directory, in file
 @('checkpoints-tests-log.txt').</p>

 <p>Here are details to keep in mind.</p>

 <ul>

 <li>A return value of @(':UNAVAILABLE') indicates that no information on
 checkpoints is available, presumably because the most recent proof attempt
 succeeded.</li>

 <li>This utility produces the appropriate result even when inhibited
 @('SUMMARY') output (see @(see set-inhibit-output-lst)) suppresses the
 printing of key checkpoints in a proof attempt.</li>

 <li>Each forcing round (see @(see forcing-round)) is considered a new proof
 attempt for purposes of this tool.</li>

 <li>Suppose a proof attempt is aborted in favor of proving the original goal
 by induction, as typically indicated with the following prover output.

 @({
 We therefore abandon our previous work on this conjecture and
 reassign the name *1 to the original conjecture.
 })

 In that case, the unique top-level checkpoint is @('(<GOAL>)').  Moreover, all
 information stored for the proof attempt is based on the part of the attempt
 starting after returning to prove the original goal by induction; all
 checkpoints produced before that happens will be lost.  If that isn't what you
 want, consider using @(':')@(tsee otf-flg).</li>

 <li>The notion of ``most recent proof attempt'' includes proof attempts made
 during @(tsee make-event) expansion.</li>

 </ul>")

(defxdoc checkpoint-list-pretty
   :parents (kestrel-utilities output-controls)
   :short "Return prover key checkpoint goals programmatically."
   :long "<p>See @(see checkpoint-list) for relevant background and related
 utilities.  Here we explain only how @('checkpoint-list-pretty') differs from
 @('checkpoint-list').</p>

 <p>Recall that @('checkpoint-list') returns a list of clauses or the keyword
 @(':UNAVAILABLE').  The corresponding value @('(checkpoint-list-pretty top-p
 state)') is obtained by replacing each such clause by a corresponding
 untranslated @(see term), which is the goal displayed during output from the
 corresponding failed proof.  For a clause with only one member, that is simply
 the untranslation of that member.  Otherwise the clause is a list @('(t0
 ... tn)'), in which case the corresponding untranslated term is an implication
 @('(implies p q)') , where @('p') is formed by conjoining the untranslation
 the negations of the @('ti') for each @('i < n'), and @('q') is the
 untranslation of @('tn').</p>

 <p><b>Remarks.</b></p>

 <ul>

 <li>Untranslation is sensitive to @(tsee let*) abstraction; see @(see
 set-let*-abstractionp).</li>

 <li>Unlike functions @('checkpoint-list') and @('checkpoint-info-list'), which
 are @(see guard)-verified @(see logic)-mode functions,
 @('checkpoint-list-pretty') is a @(see program)-mode function.</li>

 </ul>")

(defxdoc checkpoint-info-list
   :parents (kestrel-utilities output-controls)
   :short "Return prover key checkpoint information programmatically."
   :long "<p>See @(see checkpoint-list) for relevant background and related
 utilities.  Here we explain only how @('checkpoint-info-list') differs from
 @('checkpoint-list').  The difference is that instead of a list of clauses,
 it returns a list of alists each of the following form.</p>

 @({
 ((:clause-id . clause-id)
  (:clause . clause)
  (:pushed . pushed))
 })

 <p>Here, @('clause-id') is the @(see clause-identifier) of the indicated
 clause.  The value of @('pushed') is left undocumented here (low-level
 technical note: it comes from the @(':pushed') field of the corresponding
 @('gag-info') record).</p>")

(defxdoc show-checkpoint-list
   :parents (kestrel-utilities output-controls)
   :short "Display prover key checkpoint information."
   :long "<p>See @(see checkpoint-list) for relevant background.  Evaluation of
 the macro call @('(show-checkpoint-list)') prints checkpoint clauses (as
 returned by @('checkpoint-list')) as well as related information.  An optional
 argument has default @('nil'); when it is not @('nil'), then the checkpoints
 are printed as untranslated terms, as described in the documentation for
 @(tsee checkpoint-list-pretty).  Whether printed as a clause or as an
 untranslated term, each checkpoint is printed with its @(see goal-spec), i.e.,
 the user-friendly goal name that one sees in prover output for a @(see
 clause-identifier).</p>

 <p>Also shown are whether or not at least one goal was @(see force)d during
 the failed proof and whether the proof was aborted, and (briefly) why.</p>")

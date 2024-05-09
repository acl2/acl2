; WARNING: Keep this in sync with customize.lsp.

; WARNING: Fix the path on the include-book below.

(in-package "ACL2")

(set-raw-mode-on!)
(push :acl2data *features*)
; (push :skip-hyp *features*)
; (push :skip-book-runes *features*)
; (push :skip-rune *features*)
; (push :acl2-advice *features*)
(set-raw-mode nil)

(f-put-global
 'skip-retry-alist
 '(

;;;;; Initial excludes

; run-script books, found by running the following in books/
; and eliminating duplicates:
;   time fgrep --include='*.acl2' -ri run-script .
; Their certification will fail anyhow, but there's no point in doing retries,
; so we include them.

   ((:system . "demos/big-proof-talks/talk1-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "demos/big-proof-talks/talk2-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "demos/brr-free-variables-book.lisp"))
   ((:system . "demos/congruent-stobjs-book.lisp"))
   ((:system . "demos/defabsstobj-example-4-book.lisp"))
   ((:system . "demos/ld-history-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "demos/marktoberdorf-08/lecture1-book.lisp"))
   ((:system . "demos/marktoberdorf-08/lecture2-book.lisp"))
   ((:system . "demos/marktoberdorf-08/lecture3-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "demos/marktoberdorf-08/lecture4-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "demos/marktoberdorf-08/lecture5-book.lisp"))
   ((:system . "demos/memoize-invoke-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "demos/memoize-partial-book.lisp"))
   ((:system . "demos/mini-proveall-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "kestrel/utilities/checkpoints-tests-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "projects/apply/prog-mode-tests-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "projects/paco/books/proveall-book.lisp"))
   ((:system . "std/system/irrelevant-formals-book.lisp"))
   ((:system . "system/tests/abstract-stobj-nesting/aliasing-tests-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "system/tests/abstract-stobj-nesting/nested-abstract-stobjs-book.lisp"))
   ((:system . "system/tests/nested-stobj-errors-book.lisp"))
;  originally here, but subsumed by :fail entry later:
;  ((:system . "system/tests/stobj-table-tests-book.lisp"))
   ((:system . "tools/rewrite-dollar-book.lisp"))
   ((:system . "workshops/2022/kaufmann-moore/do-loops-book.lisp"))

; Failures from failures-run5.txt, skipping those that I hope will be
; solved by (reset-prehistory) in patch.lsp.

   ((:system . "bdd/benchmarks.lisp"))
   ((:system . "centaur/bitops/equal-by-logbitp.lisp"))
   ((:system . "kestrel/axe/translate-dag-to-stp.lisp"))
   ((:system . "system/hl-nat-combine-onto.lisp"))
   ((:system . "workshops/2022/young-asymptotic/asymptotic-analysis-support.lisp"))

; Not sure if we really need to exclude the following three.

   ((:system . "centaur/bitops/congruences.lisp"))
   ((:system . "centaur/truth/truth.lisp"))
   ((:system . "centaur/bitops/sparseint.lisp"))

   ((:system . "workshops/2022/young-asymptotic/complexity-of-binary-search.lisp"))
   ((:system . "workshops/2022/young-asymptotic/complexity-of-linear-search.lisp"))
   ((:system . "projects/rp-rewriter/lib/mult/multiplier-rules.lisp"))
; Excluded until the last-chance run:
;  ((:system . "projects/arm/second/fdiv2/first.lisp"))
   ((:system . "projects/async/serial-adder/32-bit-serial-adder-old/32-bit-serial-adder.lisp"))
; Excluded until the last-chance run:
;  ((:system . "projects/x86isa/proofs/wordCount/wc.lisp"))

; I seem to have had problems with the following completing.

   ((:system . "centaur/truth/sizes.lisp"))
   ((:system . "centaur/sv/svex/s4vec.lisp"))
   ((:system . "centaur/aignet/construction.lisp"))
   ((:system . "centaur/sv/svex/a4vec-ops.lisp"))

; Hmmm, in run5 I gave up on svex/, so others besides the following two might
; need to be excluded.

   ((:system . "centaur/sv/svex/rewrite-rules.lisp"))
   ((:system . "centaur/sv/svex/symbolic.lisp.lisp"))

; Excluded until the last-chance run:
;  ((:system . "projects/filesystems/abs-syscalls.lisp"))

   ((:system . "centaur/esim/tutorial/alu16-book.lisp"))
   ((:system . "centaur/fgl/interp.lisp"))
; Excluded until the last-chance run:
;  ((:system . "projects/x86isa/tools/execution/examples/dataCopy/dataCopy.lisp"))
   ((:system . ( "projects/x86isa/proofs/utilities/sys-view/non-marking-view-top.lisp")))
   ((:system . "kestrel/x86/tools/support32.lisp"))
   ((:system . "kestrel/x86/tools/read-and-write.lisp"))
; Oops, already excluded above.
;  ((:system . "projects/async/serial-adder/32-bit-serial-adder-old/32-bit-serial-adder.lisp"))
; Excluded until the last-chance run:
;  ((:system . "projects/filesystems/lofat/lofat-remove-file.lisp"))
; fail until the last-chance run: ; not tried
;  ((:system . "projects/filesystems/lofat/lofat-place-file.lisp"))
   ((:system . "projects/x86isa/proofs/dataCopy/loop-recur.lisp")) ; not tried
; Oops, already excluded above.
;  ((:system . "projects/x86isa/proofs/wordCount/wc.lisp"))
; Excluded until the last-chance run:
;  ((:system . "projects/rp-rewriter/lib/mult3/demo/demo-3.lisp"))
; Excluded until the last-chance run:
;  ((:system . "projects/x86isa/proofs/utilities/sys-view/paging/pml4-table-lemmas.lisp"))

;;;;;; End of initial excludes.  Start excludes #2.

; Build system issue (uncertified book)
; Marked with :fail for last-chance run:
;  ((:system . "workshops/2003/greve-wilding-vanfleet/support/firewallworks.lisp"))

; Cutom makefile: "Undefined function REMOVE-HYP-CHECKPOINTS"
; (removed .out file, size 72,994,336,461, after 494:32)
   ((:system . "workshops/2004/sumners-ray/support/total-order.lisp"))
; (removed .out file, size 73,977,135,480, after over 500 min.)
   ((:system . "workshops/2004/sumners-ray/support/basis.lisp"))

; Stalled at "Start retries: :HINT-SETTING."; killed at 504:04.
   ((:system . "workshops/2009/sumners/support/examples.lisp"))

; Stalled at 83G of memory after proof phase of certify-book;
; killed at 503:44.
; [Oops, second run tried it again because of typo below that I've fixed.]
   ((:system . "misc/hons-tests.lisp"))

; Proof failure, probably from (logbitp-reasoning)
   ((:system . "centaur/bitops/logrepeat.lisp"))
   ((:system . "centaur/misc/bound-rewriter.lisp"))
   ((:system . "centaur/sv/svex/4vmask.lisp"))
   ((:system . "centaur/sv/svex/lattice.lisp"))
   ((:system . "centaur/sv/svex/override.lisp"))

; Proof-builder failure
   ((:system . "rtl/rel9/support/support/land0-proofs.lisp"))
   ((:system . "rtl/rel11/rel9-rtl-pkg/support/support/land0-proofs.lisp"))
   ((:system . "workshops/2022/young-asymptotic/recursivebs2-searches.lisp"))
   ((:system . "projects/filesystems/l-models/file-system-6.lisp"))
   ((:system . "workshops/2018/mehta/file-system-6.lisp"))

;;; Errors from first run at "Start retries: :HINT-SETTING.

; Stack overflow
   ((:system . "coi/defung/defung-stress.lisp") :hint-setting)
   ((:system . "centaur/bigmem/bigmem.lisp") :hint-setting)

;;; Errors from first run at "Start retries: :RUNE.":

; Backtrace (bdd stuff):
   ((:system . "workshops/2006/hunt-reeber/support/bdd.lisp") :rune)

; hard error: loop
   ((:system . "coi/nary/rewrite-equal-hint.lisp") :rune)

; Maximum id for bdds exceeded:
   ((:system . "bdd/hamming.lisp") :rune)

; Make-event error
   ((:system . "misc/misc2/step-limits.lisp") :rune)

; Backtrace (tau)
   ((:system . "centaur/misc/dag-measure-thms.lisp") :rune)
   ((:system . "workshops/2004/ruiz-et-al/support/q-dag-unification.lisp") :rune)
   ((:system . "centaur/vl2014/util/echars.lisp") :rune)
   ((:system . "centaur/vl/util/echars.lisp") :rune)
   ((:system . "kestrel/axe/axe-syntax-functions.lisp") :rune)
   ((:system . "centaur/esim/vcd/vcd-impl.lisp") :rune)

; Attempt to force nil
   ((:system . "centaur/fgl/mark-bfrs-base.lisp") :rune)

; Giant ash call
   ((:system . "kestrel/solidity/integer-operations.lisp") :rune)

; HARD ACL2 ERROR in ACL2::VARIFY
   ((:system . "acl2s/defdata/splitnat.lisp") :rune)

; Killed at "Start retries: :RUNE." at 500:02
   ((:system . "nonstd/workshops/2017/cayley/cayley1c.lisp"))

; Killed at "Start retries: :RUNE." at 498:02
   ((:system . "workshops/2013/hardin-hardin/support/APSP.lisp"))

; Killed at "Start retries: :RUNE." at 486:23
   ((:system . "workshops/2004/legato/support/generic-theory-tail-recursion-mult.lisp"))

; Killed at "Start retries: :RUNE." at 487:58
   ((:system . "workshops/2004/legato/support/generic-theory-loop-invariant-mult.lisp"))

; Killed at "Start retries: :RUNE." at 482:56
   ((:system . "projects/cache-coherence/vi/vi-correct.lisp"))

; Might complete:
; books/projects/legacy-defrstobj/basic-tests.lisp

;;; Taking much too long (over 6 hours)

   ((:system . "workshops/2017/sumners/support/bakery.lisp"))
   ((:system . "projects/apply/loop-recursion-examples.lisp"))
   ((:system . "projects/stateman/byte-addressed-state.lisp"))
   ((:system . "tau/bounders/elementary-bounders.lisp"))
   ((:system . "workshops/2018/greve-gacek/poly-proofs.lisp"))
   ((:system . "workshops/2011/verbeek-schmaltz/sources/invariants.lisp"))
   ((:system . "workshops/2011/krug-et-al/support/MinVisor/setup-nested-page-tables.lisp"))
   ((:system . "projects/async/fifo/round-robin1.lisp"))
   ((:system . "kestrel/bv/rules5.lisp"))
   ((:system . "workshops/2011/verbeek-schmaltz/sources/correctness.lisp"))
   ((:system . "workshops/2011/verbeek-schmaltz/sources/correctness2.lisp"))
   ((:system . "projects/quadratic-reciprocity/support/gauss.lisp"))
   ((:system . "kestrel/crypto/r1cs/sparse/gadgets/range-check.lisp"))

;;; Already ran 1.5 hours; stuck on :RUNE retries

   ((:system . "projects/dpss/Collins/level-1-initial-synchronization.lisp") :rune)
   ((:system . "projects/async/serial-adder/serial-sub.lisp") :rune)
   ((:system . "projects/async/serial-adder/serial-add.lisp") :rune)

;;; Taking over an hour, so restrict not to use :RUNE.

   ((:system . "projects/filesystems/lofat-to-string-inversion.lisp") :rune)
; Dealt with below, with :fail for last-chance run:
;  ((:system . "projects/filesystems/hifat-to-lofat-inversion.lisp") :rune)
   ((:system . "projects/dpss/Base/step-time-induction.lisp") :rune)
   ((:system . "projects/dpss/AvD/invariants.lisp") :rune)
   ((:system . "centaur/svl/4vec-lemmas.lisp")) ; checkpoints from proof failures in run10
   ((:system . "projects/rp-rewriter/lib/mult/meta/f2-new-meta.lisp") :rune)
   ((:system . "projects/rp-rewriter/lib/mult3/pp-flatten-meta-correct.lisp") :rune)

;;;;;; Start excludes #2.
;;;;;; (At this point, 8206 .cert files and
;;;;;; 5611 (non-empty) __acl2data.out files.

; Backtrace (tau)
   ((:system . "centaur/misc/dag-measure.lisp") :rune)
   ((:system . "projects/stateman/stateman22.lisp") :rune)
   ((:system . "kestrel/axe/r1cs/axe-prover-r1cs.lisp") :rune)
   ((:system . "kestrel/axe/prover-basic.lisp") :rune)

; Proof failure, probably from (logbitp-reasoning)
   ((:system . "centaur/sv/svex/argmasks.lisp")) ; maybe from :bdd hint:
   ((:system . "centaur/sv/svex/compose-theory-split.lisp"))

; Giant ash call, under :rune:
   ((:system . "projects/quadratic-reciprocity/support/pratt.lisp") :rune)

; These both were running over three hours when I killed them, with last tries
; involving :rune.
   ((:system . "kestrel/java/language/keywords-validation.lisp") :rune)
   ((:system . "kestrel/java/language/hexadecimal-digits-validation.lisp") :rune)

; HARD ACL2 ERROR in ACL2::VARIFY
   ((:system . "rtl/rel11/support/injection.lisp") :rune)
   ((:system . "rtl/rel11/support/harrison.lisp") :rune)

; Just plain slow (over 15 hours and not done):
   ((:system . "projects/filesystems/abs-separate.lisp"))
; Dealt with below, with :fail for last-chance run:
;  ((:system . "projects/filesystems/hifat-to-lofat-inversion.lisp"))
   ((:system . "nonstd/workshops/2017/cayley/cayley1d.lisp"))

; Just plain slow (over 8 hours and not done):
   ((:system . "models/jvm/m5/apprentice.lisp"))

; 246G .out files (both custom makefiles)
   ((:system . "workshops/2004/sumners-ray/support/sets.lisp"))
   ((:system . "projects/translators/l3-to-acl2/translator/l3.lisp"))

;;;;;; Start excludes #3.  I killed #2 quickly when I saw these, so that I
;;;;;; could get more make-evel parallelism.

; Backtrace (tau)
   ((:system . "centaur/vl2014/mlib/hier-measure.lisp") :rune)
   ((:system . "centaur/vl/mlib/hier-measure.lisp") :rune)
   ((:system . "centaur/sv/mods/svmods.lisp") :rune)

;;;;;; Start excludes #4, after killing #3.

; Probably bitops
   ((:system . "centaur/sv/svex/symbolic.lisp"))
   ((:system . "centaur/sv/svtv/svtv-fsm-override-fgl-theory.lisp"))

; Backtrace (stack overflow)
   ((:system . "kestrel/ethereum/semaphore/r1cs-proof-rules.lisp") :rune)

; Simply taking too long (over 7 hours for all but that last, over 6 for that)
; Dealt with below, with :fail for last-chance run:
;  ((:system . "projects/filesystems/hifat-to-lofat-inversion.lisp"))
   ((:system . "projects/curve25519/ecp.lisp"))
   ((:system . "kestrel/zcash/jubjub.lisp"))
   ((:system . "kestrel/crypto/ecurve/edwards-bls12.lisp"))
   ((:system . "kestrel/ethereum/semaphore/baby-jubjub.lisp"))
   ((:system . "projects/filesystems/absfat/abs-find-file.lisp"))
   ((:system . "workshops/2004/sumners-ray/support/crit.lisp"))

; Takes too long (only about 10% through file at 1.5 hours)
   ((:system . "projects/filesystems/absfat/partial-collapse.lisp"))

; Only about half-way through after an hour -- seems stuck on :rune
   ((:system . "centaur/sv/vl/vl-svstmt.lisp") :rune)

;;;;;; Uncertified books awaiting a final try in "last-chance" run:

; I'll initially mark as :fail ones I see that have already failed, with a
; comment "; before last" to that effect; the rest I'll label with :rune just
; before the last-chance run, but will change to :fail if the last-chance run
; doesn't certify the book.  These are books in books/build/Makefile-books for
; which there is no .cert file.

; THEN.... after the run ....

; After the "last chance" run, I changed :rune to :fail for all such books
; without a .cert file.  I added a comment "; not tried" to the end of the line
; for each such book without a *out file, indicating that its certification
; hadn't been attempted, presumably because of its dependence on an uncertified
; book.  For those with a *out file I added a comment "; aborted" if the proof
; was (probably) interrupted, else "; failed".

;;;
; NOTE: The following two changes suggest how we might get more coverage at the
; potential cost of more manual effort.  (1) Comment out each line below with a
; "not tried" comment.  (2) Remove :fail from each item below with comment
; "aborted", so that we just have the filename in a one-element list.  Then for
; each book from (2), certification will be attempted without retries, so
; there's a good chance that certification will succeed without an "aborted"
; being necessary.  This could enable certification, with retries, of the books
; from (1), now that their lines are commented out.
;;;

   ((:system . "kestrel/x86/top.lisp") :rune)
   ((:system . "kestrel/x86/tools/unroll-x86-code-old.lisp") :rune)
   ((:system . "kestrel/x86/tools/support-axe.lisp") :rune)
   ((:system . "kestrel/x86/tools/top.lisp") :rune)
   ((:system . "kestrel/x86/tools/support2.lisp") :rune)
   ((:system . "kestrel/x86/tools/support.lisp") :rune)
   ((:system . "kestrel/top.lisp") :rune)
   ((:system . "kestrel/zcash/jubjub-montgomery.lisp") :rune)
   ((:system . "kestrel/zcash/jubjub-r-properties.lisp") :rune)
   ((:system . "kestrel/zcash/top.lisp") :rune)
   ((:system . "kestrel/zcash/gadgets/a-3-3-6-proof.lisp") :rune)
   ((:system . "kestrel/zcash/gadgets/a-3-3-4-proof.lisp") :rune)
   ((:system . "kestrel/zcash/gadgets/top.lisp") :rune)
   ((:system . "kestrel/zcash/gadgets/a-3-3-4-spec.lisp") :rune)
   ((:system . "kestrel/axe/tests-top.lisp") :fail) ; not tried
   ((:system . "kestrel/axe/x86/unroll-x86-code.lisp") :rune)
   ((:system . "kestrel/axe/x86/top.lisp") :rune)
   ((:system . "kestrel/axe/x86/lifter.lisp") :rune)
   ((:system . "kestrel/axe/x86/examples/popcount/popcount-32-proof.lisp") :fail) ; not tried
   ((:system . "kestrel/axe/x86/examples/popcount/popcount-64-proof.lisp") :fail) ; not tried
   ((:system . "kestrel/axe/x86/examples/popcount/top.lisp") :fail) ; not tried
   ((:system . "kestrel/axe/x86/examples/top.lisp") :fail) ; not tried
   ((:system . "kestrel/axe/stp-clause-processor-tests.lisp") :fail) ; not tried
   ((:system . "kestrel/axe/defthm-stp-tests.lisp") :fail) ; not tried
   ((:system . "kestrel/axe/query-tests.lisp") :fail) ; not tried
   ((:system . "kestrel/axe/top.lisp") :rune)
   ((:system . "kestrel/axe/tactic-prover-tests.lisp") :fail) ; not tried
   ((:system . "kestrel/axe/prove-with-stp-tests.lisp") :fail) ; not tried
   ((:system . "kestrel/doc") "./kestrel/top-doc.lisp" :rune)
   ((:system . "kestrel/utilities/checkpoints-tests-book.lisp") :fail) ; before last
   ((:system . "kestrel/number-theory/tonelli-shanks-proof.lisp") :rune)
   ((:system . "kestrel/number-theory/top") "./top.lisp" :rune)
   ((:system . "system/tests/stobj-table-tests-book.lisp") :fail) ; before last
   ((:system . "system/tests/abstract-stobj-nesting/nested-abstract-stobjs-book.lisp") :fail) ; before last
   ((:system . "system/toothbrush/make-toothbrush.lisp") :fail) ; not tried
   ((:system . "system/toothbrush/tests/test1/test1.lisp") :fail) ; not tried
   ((:system . "system/toothbrush/tests/test-par/test-par.lisp") :fail) ; not tried
   ((:system . "system/toothbrush/tests/test2/test2.lisp") :fail) ; not tried
   ((:system . "projects/include-doc.lisp") :rune)
   ((:system . "projects/paco/books/proveall-book.lisp") :fail) ; before last
   ((:system . "projects/rp-rewriter/lib/mult3/demo/demo-2.lisp") :fail) ; aborted
   ((:system . "projects/rp-rewriter/lib/mult3/demo/demo-3.lisp") :fail) ; aborted
   ((:system . "projects/rp-rewriter/lib/mult3/demo/demo-1.lisp") :fail) ; aborted
   ((:system . "projects/rp-rewriter/lib/mult3/svtv-top.lisp") :rune)
   ((:system . "projects/rp-rewriter/lib/mult/demo.lisp") :fail) ; aborted
   ((:system . "projects/rp-rewriter/lib/mult2/demo.lisp") :fail) ; aborted
   ((:system . "projects/smtlink/examples/ringosc.lisp") :fail) ; not tried
   ((:system . "projects/smtlink/examples/examples.lisp") :fail) ; not tried
   ((:system . "projects/top-doc.lisp") :rune)
   ((:system . "projects/curve25519/terms.lisp") :rune)
   ((:system . "projects/curve25519/reduce.lisp") :rune)
   ((:system . "projects/curve25519/tripp.lisp") :rune)
   ((:system . "projects/curve25519/top.lisp") :rune)
   ((:system . "projects/curve25519/axioms.lisp") :rune)
   ((:system . "projects/hybrid-systems/phi-exists.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/phi-unique.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/tm-floor.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/computed-hints.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/o-real-p.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/arith-nsa4.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/phi-properties.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/eexp.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/example.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/nsa.lisp") :fail) ; not tried
   ((:system . "projects/hybrid-systems/abs.lisp") :fail) ; not tried
   ((:system . "projects/doc.lisp") :rune)
   ((:system . "projects/x86isa/proofs/top.lisp") :fail) ; not tried
   ((:system . "projects/x86isa/proofs/dissertation-examples/clc-stc-system-level-marking-view.lisp") :rune)
   ((:system . "projects/x86isa/proofs/utilities/sys-view/top.lisp") :rune)
   ((:system . "projects/x86isa/proofs/utilities/sys-view/marking-view-top.lisp") :rune)
   ((:system . ( "projects/x86isa/proofs/utilities/sys-view/paging/page-dir-ptr-table-lemmas.lisp")) :rune)
   ((:system . "projects/x86isa/proofs/utilities/sys-view/paging/gather-paging-structures-thms.lisp") :rune)
   ((:system . ( ( "projects/x86isa/proofs/utilities/sys-view/paging/page-walk-side-effects.lisp"))) :rune)
   ((:system . "projects/x86isa/proofs/utilities/sys-view/paging/top.lisp") :rune)
   ((:system . "projects/x86isa/proofs/utilities/sys-view/paging/la-to-pa-lemmas.lisp") :rune)
   ((:system . ( ( "projects/x86isa/proofs/utilities/sys-view/paging/page-directory-lemmas.lisp"))) :rune)
   ((:system . "projects/x86isa/proofs/utilities/sys-view/paging/pml4-table-lemmas.lisp") :rune)
   ((:system . "projects/x86isa/proofs/utilities/sys-view/paging/page-table-lemmas.lisp") :rune)
   ((:system . ( "projects/x86isa/proofs/utilities/sys-view/paging/gather-paging-structures.lisp")) :rune)
   ((:system . "projects/x86isa/proofs/utilities/sys-view/marking-view-utils.lisp") :rune)
   ((:system . "projects/x86isa/proofs/utilities/top.lisp") :rune)
   ((:system . "projects/x86isa/proofs/wordCount/wc.lisp") :fail) ; failed ("Call stack error")
   ((:system . "projects/x86isa/proofs/zeroCopy/marking-view/zeroCopy.lisp") :fail) ; not tried
; The following was marked as :fail in run9.  But in run10 after 6+
; hours; "Start retries: :HINT-SETTING." -- final event, e/d with 6 enables, 28
; disables -- and then over an hour on "Start retries: :HYP.".
   ((:system . "projects/x86isa/proofs/zeroCopy/marking-view/zeroCopy-part-1.lisp"))
   ((:system . "projects/x86isa/proofs/zeroCopy/marking-view/zeroCopy-part-2.lisp") :fail) ; failed ("Call stack error")
   ((:system . "projects/x86isa/proofs/zeroCopy/marking-view/zeroCopy-init.lisp") :rune)
   ((:system . "projects/x86isa/proofs/zeroCopy/marking-view/read-page-after-write-to-page-table.lisp") :rune)
   ((:system . "projects/x86isa/proofs/zeroCopy/non-marking-view/zeroCopy.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/execloaders.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/top.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/instrument/top.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/init-page-tables.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/examples/dataCopy/dataCopy.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/examples/factorial.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/examples/fibonacci32.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/examples/fibonacci.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/examples/nop-sequence/nop.lisp") :rune)
   ((:system . "projects/x86isa/tools/execution/examples/top.lisp") :rune)
   ((:system . "projects/x86isa/doc.lisp") :rune)
   ((:system . "projects/x86isa/top.lisp") :fail) ; not tried
   ((:system . "projects/translators/l3-to-acl2/examples/mips/mips.lisp") :fail) ; not tried
   ((:system . "projects/translators/l3-to-acl2/examples/thacker/gold/tiny-logic.lisp") :fail) ; not tried
   ((:system . "projects/translators/l3-to-acl2/examples/thacker/gold/tiny.lisp") :fail) ; not tried
; I think the next two are weird artifacts of a custom makefile that shouldn't be here:
;  ((:system . "projects/translators/l3-to-acl2/examples/thacker/workxxx.tiny.lisp") :rune)
;  ((:system . "projects/translators/l3-to-acl2/examples/thacker/workxxx.tiny-logic.lisp") :rune)
   ((:system . "projects/filesystems/lofat/lofat-mkdir.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/lofat/lofat-pwrite.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/lofat/lofat-remove-file.lisp") :rune)
   ((:system . "projects/filesystems/lofat/lofat-place-file.lisp") :rune)
   ((:system . "projects/filesystems/oracle.lisp") :fail) ; not tried
; Tried several times before last-chance run, so marking with :fail:
   ((:system . "projects/filesystems/hifat-to-lofat-inversion.lisp") :fail) ; before last
   ((:system . "projects/filesystems/abs-syscalls.lisp") :fail) ; failed (proof-builder)
   ((:system . "projects/filesystems/eqfat.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/examples/ls-rm-example.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/examples/wc-truncate-example.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/tar-stuff.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test-stuff.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/absfat/path-clear.lisp") :rune)
   ((:system . "projects/filesystems/lofat.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/lofat-syscalls.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/examples.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/wc-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/mkfs.fat-3.0.28-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/truncate-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/mkfs.fat-4.1-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/cp-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/tar-reader.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/compare-disks.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/tar-writer.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/mv-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/rm-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/stat-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/ls-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/mkfs.fat-3.0.20-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/mkdir-replicant.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/read-disk-image-write-disk-image.lisp") :fail) ; not tried
   ((:system . "projects/filesystems/test/rmdir-replicant.lisp") :fail) ; not tried
   ((:system . "projects/apply/prog-mode-tests-book.lisp") :fail) ; before last
   ((:system . "projects/arm/fdiv/clz.lisp") :rune)
   ((:system . "projects/arm/fdiv/summary.lisp") :fail) ; not tried
   ((:system . "projects/arm/fdiv/quotient.lisp") :rune)
   ((:system . "projects/arm/fdiv/prescale.lisp") :rune)
   ((:system . "projects/arm/fdiv/normalize.lisp") :rune)
   ((:system . "projects/arm/fdiv/induct.lisp") :rune)
   ((:system . "projects/arm/fdiv/rounder.lisp") :rune)
   ((:system . "projects/arm/fdiv/special.lisp") :rune)
   ((:system . "projects/arm/fdiv/final.lisp") :fail) ; aborted
   ((:system . "projects/arm/fsqrt/final.lisp") :rune)
   ((:system . "projects/arm/fsqrt/quotient.lisp") :rune)
   ((:system . "projects/arm/fsqrt/rounder.lisp") :rune)
   ((:system . "projects/arm/fsqrt/induct.lisp") :rune)
   ((:system . "projects/arm/fsqrt/summary.lisp") :rune)
   ((:system . "projects/arm/utils/rtl-utils.lisp") :rune)
   ((:system . "projects/arm/utils/aarch64-specs.lisp") :rune)
   ((:system . "projects/arm/second/fmul64/rndbits.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fmul64/unrounded.lisp") :fail) ; failed (large power of 2)
   ((:system . "projects/arm/second/fmul64/product.lisp") :rune)
   ((:system . "projects/arm/second/fmul64/clz.lisp") :rune)
   ((:system . "projects/arm/second/fmul64/summary.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fmul64/denorm.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fmul64/fused.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fmul64/final.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fmul64/expinc.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fmul64/special.lisp") :rune)
   ((:system . "projects/arm/second/fmul64/norm.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fma32/prelim.lisp") :rune)
   ((:system . "projects/arm/second/fma32/lza.lisp") :rune)
   ((:system . "projects/arm/second/fma32/summary.lisp") :rune)
   ((:system . "projects/arm/second/fma32/final.lisp") :rune)
   ((:system . "projects/arm/second/fma32/resrnd.lisp") :rune)
   ((:system . "projects/arm/second/fma32/spec.lisp") :rune)
   ((:system . "projects/arm/second/fma32/special.lisp") :rune)
   ((:system . "projects/arm/second/fma32/hc52.lisp") :rune)
   ((:system . "projects/arm/second/fma32/sumshft.lisp") :rune)
   ((:system . "projects/arm/second/fma32/sum.lisp") :rune)
   ((:system . "projects/arm/second/fma32/addends.lisp") :rune)
   ((:system . "projects/arm/second/idiv8/post.lisp") :rune)
   ((:system . "projects/arm/second/idiv8/summary.lisp") :rune)
   ((:system . "projects/arm/second/idiv8/quot.lisp") :rune)
   ((:system . "projects/arm/second/idiv8/induct.lisp") :rune)
   ((:system . "projects/arm/second/fadd64/comp.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/addition.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/clz.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/prelim.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/fma.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/special.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/lshift.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/fadd.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/lza.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/alignment.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/round.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fadd64/summary.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fdiv8/summary.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fdiv8/normalize.lisp") :rune)
   ((:system . "projects/arm/second/fdiv8/final.lisp") :fail) ; aborted
   ((:system . "projects/arm/second/fdiv8/induct.lisp") :rune)
   ((:system . "projects/arm/second/fdiv8/algorithm.lisp") :rune)
   ((:system . "projects/arm/second/fdiv8/first.lisp") :rune)
   ((:system . "projects/arm/second/fdiv8/special.lisp") :rune)
   ((:system . "projects/arm/second/fdiv8/clz.lisp") :rune)
   ((:system . "projects/arm/second/fdiv8/rounder.lisp") :rune)
   ((:system . "projects/arm/second/fdiv8/quotient.lisp") :rune)
   ((:system . "projects/arm/second/fdiv2/special.lisp") :rune)
   ((:system . "projects/arm/second/fdiv2/quotient.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fdiv2/prelim.lisp") :rune)
   ((:system . "projects/arm/second/fdiv2/round.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fdiv2/normalize.lisp") :rune)
   ((:system . "projects/arm/second/fdiv2/induct.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fdiv2/first.lisp") :fail) ; failed (large power of 2)
   ((:system . "projects/arm/second/fdiv2/summary.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fdiv2/algorithm.lisp") :rune)
   ((:system . "projects/arm/second/fdiv2/final.lisp") :fail) ; not tried
   ((:system . "projects/arm/second/fsqrt4/rounder.lisp") :rune)
   ((:system . "projects/arm/second/fsqrt4/normalize.lisp") :rune)
   ((:system . "projects/arm/second/fsqrt4/clz.lisp") :rune)
   ((:system . "projects/arm/second/fsqrt4/summary.lisp") :rune)
   ((:system . "projects/arm/second/fsqrt4/algorithm.lisp") :rune)
   ((:system . "projects/arm/second/fsqrt4/final.lisp") :rune)
   ((:system . "projects/arm/second/fsqrt4/quotient.lisp") :rune)
   ((:system . "projects/arm/second/fsqrt4/induct.lisp") :rune)
   ((:system . "projects/arm/fadd/fma.lisp") :fail) ; aborted
   ((:system . "projects/arm/fadd/clz.lisp") :rune)
   ((:system . "projects/arm/fadd/summary.lisp") :fail) ; not tried
   ((:system . "projects/arm/fadd/prelim.lisp") :rune)
   ((:system . "projects/arm/fadd/comp.lisp") :rune)
   ((:system . "projects/arm/fadd/lshift.lisp") :rune)
   ((:system . "projects/arm/fadd/addition.lisp") :rune)
   ((:system . "projects/arm/fadd/alignment.lisp") :rune)
   ((:system . "projects/arm/fadd/special.lisp") :rune)
   ((:system . "projects/arm/fadd/round.lisp") :rune)
   ((:system . "projects/arm/fadd/fadd.lisp") :rune)
   ((:system . "projects/arm/fadd/lza.lisp") :rune)
   ((:system . "projects/arm/fmul/special.lisp") :rune)
   ((:system . "projects/arm/fmul/denorm.lisp") :rune)
   ((:system . "projects/arm/fmul/expinc.lisp") :rune)
   ((:system . "projects/arm/fmul/final.lisp") :rune)
   ((:system . "projects/arm/fmul/fused.lisp") :rune)
   ((:system . "projects/arm/fmul/summary.lisp") :rune)
   ((:system . "projects/arm/fmul/norm.lisp") :rune)
   ((:system . "projects/arm/fmul/rndbits.lisp") :rune)
   ((:system . "projects/arm/fmul/product.lisp") :rune)
   ((:system . "projects/arm/fmul/unrounded.lisp") :rune)
   ((:system . "projects/arm/fmul/clz.lisp") :rune)
   ((:system . "tools/book-conflicts/conflicts.lisp") :fail) ; not tried
   ((:system . "tools/book-conflicts/bookdata-types.lisp") :fail) ; not tried
   ((:system . "centaur/vl/kit/lint.lisp") :rune)
   ((:system . "centaur/vl/kit/top.lisp") :rune)
   ((:system . "centaur/vl/top-doc.lisp") :rune)
   ((:system . "centaur/vl/transforms/unparam/override.lisp") :rune)
   ((:system . "centaur/vl/transforms/unparam/top.lisp") :rune)
   ((:system . "centaur/glmc/counter.lisp") :fail) ; not tried
   ((:system . "centaur/glmc/glmc-test.lisp") :fail) ; not tried
   ((:system . "centaur/ipasir/ipasir-backend.lisp") :fail) ; not tried
   ((:system . "centaur/ipasir/ipasir-backend-extra.lisp") :fail) ; not tried
   ((:system . "centaur/ipasir/ipasir-tests.lisp") :fail) ; not tried
   ((:system . "centaur/ipasir/soundness-bug2-fixed.lisp") :fail) ; not tried
   ((:system . "centaur/ipasir/soundness-bug-fixed.lisp") :fail) ; not tried
   ((:system . "centaur/fgl/equivcheck-test.lisp") :fail) ; not tried
   ((:system . "centaur/fgl/tests-ipasir.lisp") :fail) ; not tried
   ((:system . "centaur/fgl/tests.lisp") :fail) ; not tried
   ((:system . "centaur/sv/tutorial/boothpipe.lisp") :fail) ; not tried
   ((:system . "centaur/sv/tutorial/sums.lisp") :fail) ; not tried
   ((:system . "centaur/sv/tutorial/alu.lisp") :fail) ; not tried
   ((:system . "centaur/sv/tutorial/counter.lisp") :fail) ; not tried
   ((:system . "centaur/sv/tutorial/boothpipe-new.lisp") :fail) ; not tried
   ((:system . "centaur/sv/vl/moddb.lisp") :rune)
   ((:system . "centaur/sv/vl/elaborate.lisp") :rune)
   ((:system . "centaur/sv/vl/top") "./centaur/sv/top.lisp" :rune)
   ((:system . "centaur/sv/top-doc.lisp") :rune)
   ((:system . "centaur/sv/cosims/cosims.lisp") :rune)
   ((:system . "centaur/esim/tests/common.lisp") :fail) ; not tried
   ((:system . "centaur/esim/tests/subtract.lisp") :fail) ; not tried
   ((:system . "centaur/esim/tests/add.lisp") :fail) ; not tried
   ((:system . "centaur/esim/tests/regs.lisp") :fail) ; not tried
   ((:system . "centaur/esim/tests/idiv.lisp") :fail) ; not tried
   ((:system . "centaur/esim/tests/divide.lisp") :fail) ; not tried
   ((:system . "centaur/esim/tests/multiply.lisp") :fail) ; not tried
   ((:system . "centaur/esim/tutorial/boothmul.lisp") :fail) ; not tried
   ((:system . "centaur/aig/aig-sat-tests.lisp") :fail) ; not tried
   ((:system . "acl2s/demos/refinement-sfm06-with-hazards.lisp") :fail) ; not tried
   ((:system . "acl2s/demos/dsp-fixer-rules.lisp") :fail) ; not tried
   ((:system . "acl2s/demos/alloy-support.lisp") :fail) ; not tried
   ((:system . "acl2s/demos/dsp-type-and-fixer-defuns.lisp") :fail) ; not tried
   ((:system . "acl2s/demos/dsp-defthms.lisp") :fail) ; not tried
   ((:system . "acl2s/demos/dsp-preservation-rules.lisp") :fail) ; not tried
   ((:system . "acl2s/demos/dsp-defuns.lisp") :fail) ; not tried
   ((:system . "demos/memoize-partial-book.lisp") :fail) ; before last
   ((:system . "demos/brr-free-variables-book.lisp") :fail) ; before last
   ((:system . "demos/marktoberdorf-08/lecture1-book.lisp") :fail) ; before last
   ((:system . "demos/marktoberdorf-08/lecture4-book.lisp") :fail) ; before last
   ((:system . "demos/marktoberdorf-08/lecture5-book.lisp") :fail) ; before last
   ((:system . "demos/big-proof-talks/talk2-book.lisp") :fail) ; before last
   ((:system . "doc/top.lisp") :rune)
   ((:system . "workshops/2020/gamboa-cowles-gamboa/polylist.lisp") :fail) ; not tried
   ((:system . "workshops/2020/gamboa-cowles-gamboa/norm-1C.lisp") :fail) ; not tried
   ((:system . "workshops/2020/gamboa-cowles-gamboa/number-field.lisp") :fail) ; not tried
   ((:system . "workshops/2020/gamboa-cowles-gamboa/floor1-non-R.lisp") :fail) ; not tried
   ((:system . "workshops/2020/gamboa-cowles-gamboa/prior/raise-to.lisp") :fail) ; not tried
   ((:system . "workshops/2020/hardin/fact-leg64.lisp") :fail) ; failed (stack overflow)
   ((:system . "workshops/2020/sumners/gen-models.lisp") :fail) ; not tried
   ((:system . "workshops/2020/sumners/bake-proofs.lisp") :fail) ; not tried
   ((:system . "workshops/2020/sumners/top.lisp") :fail) ; not tried
   ((:system . "workshops/2020/sumners/gl-fin-set.lisp") :fail) ; not tried
   ((:system . "workshops/2020/sumners/bake-models.lisp") :fail) ; not tried
   ((:system . "workshops/2020/kwan-peng-greenstreet/abstract-cs.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/defunt-tests.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/termination-database-utilities.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/defunt.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/termination-database.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/subsetp-eq-linear.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/injections.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/td-cands.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/defunt-top.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/fms-bang-list.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/top.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kaufmann/strict-merge-sort.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/norm.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/nesterov-top.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/nesterov-3.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/nesterov-2.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/convex.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/top.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/ftc-2.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/nesterov-4.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/vectors.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/continuity.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/cauchy-schwarz.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/nesterov-1.lisp") :fail) ; not tried
   ((:system . "workshops/2018/kwan-greenstreet/metric.lisp") :fail) ; not tried
   ((:system . "workshops/2018/mehta/test/mkfs.fat-3.0.28-replicant.lisp") :fail) ; not tried
   ((:system . "workshops/2018/mehta/test/mkfs.fat-3.0.20-replicant.lisp") :fail) ; not tried
   ((:system . "workshops/2018/mehta/test/cp-replicant.lisp") :fail) ; not tried
   ((:system . "workshops/2018/sumners/readme.lisp") :rune)
   ((:system . "workshops/2018/sumners/exa.lisp") :rune)
   ((:system . "workshops/2018/gamboa-cowles/norm2.lisp") :fail) ; not tried
   ((:system . "workshops/2018/gamboa-cowles/de-moivre.lisp") :fail) ; not tried
   ((:system . "workshops/2018/gamboa-cowles/complex-continuity.lisp") :fail) ; not tried
   ((:system . "workshops/2018/gamboa-cowles/complex-lemmas.lisp") :fail) ; not tried
   ((:system . "workshops/2018/gamboa-cowles/complex-polynomials.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/int-sum.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/fourier-coefficients.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/sines-orthog.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/fourier-coefficients-2.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/fourier-inner-product.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/sine-cosine-orthog.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/utils.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/int-infinite-sum-2.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/riemann-integral/continuous-function-2.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/riemann-integral/ftc-1-2.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/riemann-integral/continuity-2.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/cosines-orthog.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/fourier-sums.lisp") :fail) ; not tried
   ((:system . "workshops/2015/chau-kaufmann-hunt/support/int-infinite-sum-1.lisp") :fail) ; not tried
   ((:system . "workshops/2002/manolios-kaufmann/support/total-order/total-order.lisp") :fail) ; not tried
   ((:system . "workshops/2002/manolios-kaufmann/support/total-order/soundness.lisp") :fail) ; not tried
   ((:system . "workshops/2002/manolios-kaufmann/support/total-order/total-order-easy-direction.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai5.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/rTarai8.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai1.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai9.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai8.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai4.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/rTarai9.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/rTarai7.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai10.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai6.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai2.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai11.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai7.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/tarai3.lisp") :fail) ; not tried
   ((:system . "workshops/2000/cowles/books/rTarai6.lisp") :fail) ; not tried
   ((:system . "workshops/2004/sumners-ray/support/mesi.lisp") :fail) ; not tried
   ((:system . "workshops/2004/sumners-ray/support/records.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/5s.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/cxs-bp-ex-inp.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/fxs-bp-ex-inp.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/cxs-bp-ex-inp-safety.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/fxs-bp-ex-safety.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/fxs.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/cxs-bp-ex-safety.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/cxs-safety.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/fxs-bp-safety.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/fxs-bp-ex.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/fxs-safety.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/cxs-bp-ex.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/fxs-bp.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/cxs-bp-safety.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/cxs-bp.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/cxs.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/fxs-bp-ex-inp-safety.lisp") :fail) ; not tried
   ((:system . "workshops/2004/manolios-srinivasan/support/Benchmark-Problems/5s-part.lisp") :fail) ; not tried
   ((:system . "workshops/2017/swords/support/demos.lisp") :fail) ; not tried
   ((:system . "workshops/2022/gamboa-primitive-roots/pfield-polynomial.lisp") :fail) ; not tried
   ((:system . "workshops/2022/gamboa-primitive-roots/order-constructions.lisp") :fail) ; not tried
   ((:system . "workshops/2003/kaufmann/support/output/defs-out.lisp") :fail) ; not tried
   ((:system . "workshops/2003/kaufmann/support/output/defs-eq.lisp") :fail) ; not tried
   ((:system . "workshops/2003/kaufmann/support/output/lemmas-out.lisp") :fail) ; not tried
   ((:system . "workshops/2003/greve-wilding-vanfleet/support/make.lisp") :fail) ; not tried
   ((:system . "workshops/2003/greve-wilding-vanfleet/support/consistency-test-passed.lisp") :fail) ; failed (custom makefile?)
   ((:system . "workshops/2003/greve-wilding-vanfleet/support/firewallworks.lisp") :fail) ; before last
   ((:system . "workshops/2003/greve-wilding-vanfleet/support/consistency-test.lisp") :fail) ; not tried
   ((:system . "workshops/2003/greve-wilding-vanfleet/support/make-consistency-test.lisp") :fail) ; not tried
   ((:system . "nonstd/arc-length/length-of-a-rectifiable-curve.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/integral-of-polynomials.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/integration-composition-equivalences.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/ftc-2.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/equivalence-ftc.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/continuous-function.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/u-substitution.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/equivalence-continuous-function.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/integrable-functions.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/ftc-1.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/make-partition.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/equivalence-integrals.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/split-integral-by-subintervals.lisp") :fail) ; not tried
   ((:system . "nonstd/integrals/integration-composition.lisp") :fail) ; not tried
   ((:system . "nonstd/circles/area-of-a-circle/area-of-a-circle-1.lisp") :fail) ; not tried
   ((:system . "nonstd/circles/area-of-a-circle/area-of-a-circle-2.lisp") :fail) ; not tried
   ((:system . "nonstd/circles/circumference-of-a-circle.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/equivalence-continuity.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/inverse-trig.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/exp.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/factorial.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/inverse-square.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/norm.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/equivalence-limits.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/ln") :fail) ; not tried (possibly due to clerical error)
   ((:system . "nonstd/nsa/exp-sum.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/equivalence-derivatives.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/continuity-product.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/complex-polar.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/continuity.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/equivalence-derivatives-composition.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/sqrt.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/banach-tarski-s2.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/countable-sets.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/hausdorff-paradox-2.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/banach-tarski-b-0.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/hausdorff-paradox-1.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/supportive-theorems.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/rotations.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/banach-tarski.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/free-group.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/Banach-Tarski/groups.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/nsa.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/inverse-derivatives.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/derivative-raise.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/overspill-proof.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/trig-approx.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/exp-continuous.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/trig.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/inverse-monotone.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/alternating-series.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/intervals.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/overspill-test.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/chain-rule.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/derivatives-composition.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/next-integer.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/inverses.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/raise.lisp")) ; not tried (possibly due to clerical error)
   ((:system . "nonstd/nsa/sine.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/overspill.lisp") :fail) ; not tried
   ((:system . "nonstd/nsa/derivatives.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/exercise5.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/exercise1.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/exercise4.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/exercise8.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/exercise6.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/exercise2.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/continuity.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/exercise7.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/derivatives.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/analysis/exercise3.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-sum-approximates-integral-2.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/rcfn-standard-part.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/standard-part-equal-if-i-close.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/integral-rcfn-equal-if-i-close.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/min-x-and-max-x-lemmas.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-rcfn-between.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-rcfn-upper-bound.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-sum-approximates-integral.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/standard-part-preserves-between.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/standard-part-riemann-rcfn-is-standard.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/max-and-min-attained.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/two-times-r-is-not-less-than-standard-part.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/proof-outline.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/make-partition.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/defaxioms.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-rcfn-refinement-is-riemann-rcfn.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/i-small-maxlist-abslist-difflist-maps.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/map-rcfn-close-to-map-rcfn-refinement.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-lemmas.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/integral-rcfn-quotient-between-non-classical.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/rcfn-next-gte-close.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/partitions-give-i-close-riemann-sum.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/nsa.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/map-rcfn-refinement-cdr-co-member.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/max-x-between.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-bound.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-rcfn-lower-bound.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/nsa-lemmas.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/min-max-x-rec-lemmas.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/next-gte-close.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/min-x-between.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-sum-approximates-integral-1.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/fundamental-theorem-of-calculus.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/refinement-makes-i-small-change.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/split-integral-by-subintervals.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/i-limited-rcfn.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/maxlist-abslist-difflist-maps-lt.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/i-close-implies-abs-difference-small.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/integral-rcfn.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/refinement-makes-i-small-change-1.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/ftoc-lemma.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/riemann-defuns.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/between-limited-implies-limited.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/equal-riemann-rcfn-refinement-reduction.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/integral-rcfn-lemmas.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/1999/calculus/book/between-i-close-implies-i-close.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2013/helms-gamboa-quantum/support/quantum.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/exp-properties.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/product-composition.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/abs-derivative.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/sum-composition.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/differentiator.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/chain-composition.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/exp-minimal.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/sqrt-derivative.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/inverse-square.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/sin-cos-minimal.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/inverse-composition.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/inverse-derivative.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/nsa-ex.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/inverse-trig-ex.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/ln-derivative-real.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/composition-elem.lisp") :fail) ; not tried
   ((:system . "nonstd/workshops/2011/reid-gamboa-differentiator/support/inverse-trig-derivatives.lisp") :fail) ; not tried
   ((:system . "nonstd/polynomials/polynomial-lemmas.lisp") :fail) ; not tried
   ((:system . "nonstd/polynomials/polynomial-calculus.lisp") :fail) ; not tried
   ((:system . "nonstd/polynomials/polynomial-defuns.lisp") :fail) ; not tried
   ((:system . "nonstd/transcendentals/reals-are-uncountable-2.lisp") :fail) ; not tried
   ((:system . "nonstd/transcendentals/nested-intervals-revised.lisp") :fail) ; not tried
   ((:system . "nonstd/transcendentals/reals-are-uncountable-1.lisp") :fail) ; not tried
   ((:system . "nonstd/transcendentals/nested-intervals.lisp") :fail) ; not tried
   ((:system . "nonstd/fft/fft-trig-with-axioms.lisp") :fail) ; not tried
   ((:system . "nonstd/fft/fft-trig.lisp") :fail) ; not tried

; I'm commenting out all the quicklisp stuff below, even though I went ahead
; and marked it as :fail and "not tried", because I suspect it won't ever be
; tried given what else is going on, I don't want to blow up the alist, and
; anyhow I see no reason why retries should make these fail since presumably
; none of them call defthm-fn1.

#|
   ((:system . "quicklisp/bundle/bundle.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/common-lisp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/lisp-build.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/pathname.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/stream.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/run-program.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/driver.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/filesystem.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/version.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/os.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/configuration.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/image.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/debug.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/backward-driver.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/utility.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/uiop-3.3.4/launch-program.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/doc/docstrings.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-2/lists.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-2/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-2/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-2/control-flow.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/io.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/strings.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/functions.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/arrays.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/control-flow.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/sequences.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/binding.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/types.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/hash-tables.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/macros.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/numbers.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/conditions.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/definitions.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/lists.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/symbols.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/alexandria-20200715-git/alexandria-1/features.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/src/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/src/fd-streams.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/src/time.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/src/osicat.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/src/osicat-sys.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/windows/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/windows/windows.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/mach/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/mach/mach.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/unix.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/unixint.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/misc.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/basic-unix.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/linux.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/wrappers.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/windows.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/basic-unixint.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/early.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/posix/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/tests/posix.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/tests/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/osicat-20200715-git/tests/osicat.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/in-memory.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/length.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/specials.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/ascii.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/lw-char-stream.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/util.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/external-format.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/mapping.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/iso-8859.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/decode.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/enc-cn-tbl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/test/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/test/test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/conditions.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/stream.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/io.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/input.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/code-pages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/encode.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/output.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/koi8-r.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/flexi-streams-20200715-git/strings.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-gray-streams-20181018-git/streams.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-gray-streams-20181018-git/test/test-framework.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-gray-streams-20181018-git/test/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-gray-streams-20181018-git/test/test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-gray-streams-20181018-git/test/run-on-many-lisps.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-gray-streams-20181018-git/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/rfc2388-20180831-git/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/rfc2388-20180831-git/rfc2388.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/rfc2388-20180831-git/test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-garbage-20200325-git/trivial-garbage.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-garbage-20200325-git/release.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-garbage-20200325-git/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-garbage-20200325-git/gendocs.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/html-template-20171227-git/test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/html-template-20171227-git/load.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/html-template-20171227-git/util.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/html-template-20171227-git/errors.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/html-template-20171227-git/api.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/html-template-20171227-git/specials.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/html-template-20171227-git/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/html-template-20171227-git/template.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/doc/colorize-lisp-examples.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/toolchain/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/toolchain/bundle.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/toolchain/static-link.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/toolchain/c-toolchain.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/libffi/type-descriptors.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/libffi/libffi-types.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/libffi/libffi.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/libffi/funcall.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/libffi/libffi-functions.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/mapping.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/gettimeofday.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/run-examples.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/translator-test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/main-example.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/grovel-example.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/wrapper-example.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/examples.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/gethostname.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/examples/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/uffi-compat/uffi-compat.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-gcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/c2ffi/generator.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/c2ffi/c2ffi.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/c2ffi/asdf.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/c2ffi/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-ecl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-openmcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/types.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-mkcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-clisp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/utils.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/early-types.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-lispworks.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/enum.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-abcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/foreign-vars.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/libraries.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/structures.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/functions.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-clasp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-sbcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-mcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-allegro.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-cmucl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-scl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/features.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/cffi-corman.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/src/strings.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/strings.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/random-tester.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/misc.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/misc-types.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/union.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/bindings.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/fsbv.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/struct.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/run-tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/defcfun.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/arrays.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/grovel.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/memory.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/callbacks.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/funcall.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/enum.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/test-asdf.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/tests/foreign-globals.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/scripts/release.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/grovel/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/grovel/grovel.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cffi_0.23.0/grovel/asdf.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-mocl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-abcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-ecl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-clisp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-openmcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-mkcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-lispworks.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-xcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-corman.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-mezzano.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-clasp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-mcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-allegro.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-cmucl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-sbcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/src/tf-scl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/tests/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/tests/utsname.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/tests/sysinfo.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/tests/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-features-20200715-git/release.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-abcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-clisp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/pkgdcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-clozure.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-ecl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-lispworks-condition-variables.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/default-implementations.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-mezzano.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-mkcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-allegro.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/bordeaux-threads.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/condition-variables.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-clasp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-lispworks.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-mcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-corman.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-null.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-sbcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-genera.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-cmucl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/src/impl-scl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bordeaux-threads-v0.8.8/test/bordeaux-threads-test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bt-semaphore-20180711-git/t/semaphore.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bt-semaphore-20180711-git/t/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bt-semaphore-20180711-git/src/semaphore.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/bt-semaphore-20180711-git/src/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/md5-20180228-git/md5.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/shellpool-20200610-git/src/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/shellpool-20200610-git/src/main.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/shellpool-20200610-git/test/top.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/shellpool-20200610-git/test/kill.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/shellpool-20200610-git/test/background.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/shellpool-20200610-git/test/basic.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/shellpool-20200610-git/test/utils.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-gbk.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-koi8.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/gbk-map.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-ebcdic-int.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-ebcdic.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-cp437.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/strings.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/jpn-table.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-cp1252.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-iso-8859.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-jpn.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/sharp-backslash.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-ascii.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/streams.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-cp1251.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/encodings.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/external-format.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/src/enc-unicode.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/scripts/release.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/tests/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/tests/streams.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/babel-20200715-git/tests/benchmarks.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-backtrace-20200610-git/test/test-setup.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-backtrace-20200610-git/test/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-backtrace-20200610-git/test/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-backtrace-20200610-git/dev/map-backtrace.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-backtrace-20200610-git/dev/fallback.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-backtrace-20200610-git/dev/mucking.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-backtrace-20200610-git/dev/backtrace.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-backtrace-20200610-git/dev/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/trivial-backtrace-20200610-git/dev/utilities.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/chunga-20200427-git/read.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/chunga-20200427-git/output.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/chunga-20200427-git/streams.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/chunga-20200427-git/util.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/chunga-20200427-git/specials.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/chunga-20200427-git/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/chunga-20200427-git/input.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/chunga-20200427-git/conditions.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/chunga-20200427-git/known-words.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-base64-20150923-git/encode.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-base64-20150923-git/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-base64-20150923-git/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-base64-20150923-git/decode.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/specials.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/cl-ppcre-unicode/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/cl-ppcre-unicode/resolver.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/regex-class-util.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/util.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/convert.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/lexer.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/charmap.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/optimize.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/scanner.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/repetition-closures.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/parser.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/charset.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/test/perl-tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/test/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/test/unicode-tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/test/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/chartest.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/regex-class.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/errors.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/closures.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-ppcre-20190521-git/api.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/taskmaster.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/test/script-engine.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/test/script.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/test/test-handlers.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/test/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/run-test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/headers.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/specials.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/cookie.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/make-docstrings.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/log.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/url-rewrite/specials.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/url-rewrite/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/url-rewrite/url-rewrite.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/url-rewrite/util.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/url-rewrite/primitives.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/session.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/easy-handlers.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/reply.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/misc.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/conditions.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/set-timeouts.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/lispworks.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/util.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/mime-types.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/compat.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/request.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/acceptor.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/hunchentoot-v1.3.0/ssl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/packages.test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/temporary-files.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/load.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/fad.test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/fad.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/openmcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/temporary-files.test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/path.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl-fad-20200610-git/corman.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/split-sequence-v2.0.0/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/split-sequence-v2.0.0/vector.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/split-sequence-v2.0.0/tests.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/split-sequence-v2.0.0/documentation.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/split-sequence-v2.0.0/extended-sequence.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/split-sequence-v2.0.0/api.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/split-sequence-v2.0.0/list.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test/run-on-many-lisps-and-openssls/run-home.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test/run-on-many-lisps-and-openssls/run-on-server.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test/run-on-many-lisps-and-openssls/run-on-many-lisps-and-openssls.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test/verify-hostname.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test/version.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test/badssl-com.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test/dummy.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test/sni.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/example.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/ffi-buffer.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/ffi-buffer-all.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/context.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/bio.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/conditions.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/streams.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/verify-hostname.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/random.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/ffi.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/ffi-buffer-clisp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/reload.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/x509.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/src/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/cl+ssl-20200610-git/ssl-verify-test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/usocket.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/condition.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/server.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/test/wait-for-input.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/test/udp-one-shot.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/test/test-usocket.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/test/test-condition.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/test/test-datagram.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/test/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/option.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/sbcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/cmucl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/mcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/openmcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/clasp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/scl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/lispworks.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/ecl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/mezzano.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/genera.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/allegro.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/iolib.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/clisp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/clozure.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/abcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/backend/mocl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/vendor/kqueue.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/vendor/OpenTransportUDP.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/software/usocket-0.8.3/package.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/asdf.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-null.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-cmucl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-sbcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-allegro.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-mcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/default-implementations.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-clozure.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-scl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-lispworks.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-mkcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/pkgdcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-ecl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/condition-variables.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-corman.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-abcl.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-clisp.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/bordeaux-threads.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/src/impl-lispworks-condition-variables.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/bordeaux-threads/test/bordeaux-threads-test.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/fastnumio/read-hex.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/fastnumio/packages.lisp") :fail) ; not tried
   ((:system . "quicklisp/bundle/local-projects/fastnumio/write-hex.lisp") :fail) ; not tried (possibly due to clerical error)
|#

;;;;;;;;;;;;;;;; new for run9

; Raw lisp backtrace shows tau issue
   ((:system . "kestrel/acl2-arrays/bounded-integer-alistp.lisp") :rune)
   ((:system . "kestrel/acl2-arrays/bounded-nat-alists.lisp") :rune)
   ((:system . "workshops/2003/sumners/support/n2n.lisp") :rune)
   ((:system . "kestrel/java/language/floating-point-value-set-parameters.lisp") :rune)
   ((:system . "projects/sat/lrat/early/rev1/satisfiable-add-proof-clause-base.lisp") :rune)
   ((:system . "workshops/2004/ruiz-et-al/support/dags.lisp") :rune)
   ((:system . "defexec/dag-unification/dag-unification-rules.lisp") :rune)
   ((:system . "workshops/2002/manolios-kaufmann/support/finite-set-theory/set-theory.lisp") :rune)
   ((:system . "centaur/4v-sexpr/bitspecs.lisp") :rune)
   ((:system . "projects/paco/type-set.lisp") :rune)
   ((:system . "powerlists/cla-adder.lisp") :rune)
   ((:system . "workshops/2000/lusk-mccune/lusk-mccune-final/stepproc1.lisp") :rune)
   ((:system . "centaur/aignet/aignet-logic.lisp") :rune)
   ((:system . "centaur/vl2014/util/sum-nats.lisp") :rune)
   ((:system . "centaur/vl/util/sum-nats.lisp") :rune)
   ((:system . "workshops/1999/ivy/ivy-v2/ivy-sources/paramod.lisp") :rune)
   ((:system . "projects/x86isa/utils/utilities.lisp") :rune)
; ... and in second pass:
   ((:system . "workshops/2004/ruiz-et-al/support/dag-unification-rules.lisp") :rune)
   ((:system . "kestrel/acl2-arrays/expandable-arrays.lisp") :rune)
   ((:system . "kestrel/acl2-arrays/aset1-list.lisp") :rune)
   ((:system . "kestrel/axe/stp-counterexamples.lisp") :rune)
   ((:system . "kestrel/bv/logext.lisp") :rune)
   ((:system . "models/y86/y86-two-level/common/x86-memory-low.lisp") :rune)
; ... and in third pass:
   ((:system . "kestrel/axe/unguarded-defuns.lisp") :rune)
   ((:system . "kestrel/axe/dag-arrays.lisp") :rune)
   ((:system . "kestrel/bv/rules.lisp") :rune)
   ((:system . "workshops/2004/ruiz-et-al/support/q-dag-unification-st.lisp") :rune)
   ((:system . "centaur/fgl/pathcond-aignet-ipasir.lisp") :rune)
; ... and in fourth pass:
   ((:system . "kestrel/axe/prove-with-stp.lisp") :rune)
   ((:system . "kestrel/bv/rules3.lisp") :rune)
   ((:system . "kestrel/axe/prune-with-contexts.lisp") :rune)
   ((:system . "kestrel/axe/dagify.lisp") :rune)
   ((:system . "projects/x86isa/machine/x86.lisp") :rune)
; ... and in fifth pass:
   ((:system . "kestrel/axe/rules3.lisp") :rune)
; ... and in sixth or seventh pass:
   ((:system . "kestrel/bv/rules10.lisp") :rune)
; ... and in the potential tenth pass but maybe earlier too (a .pert1 file is involved):
   ((:system . "workshops/2011/verbeek-schmaltz/sources/invariants2.lisp") :rune)
; ... and in run10:
   ((:system . "kestrel/axe/equivalence-checker.lisp") :rune)

; HARD ACL2 ERROR in BDD:  Maximum id for bdds exceeded.  Current maximum
; id is 3508959.
   ((:system . "bdd/pg-theory.lisp") :rune)
   ((:system . "bdd/alu-proofs.lisp") :rune)

; HARD ACL2 ERROR in VARIFY:  This should not have happened.  The supposed
; variable, '0, is instead a constant.
   ((:system . "arithmetic-3/floor-mod/floor-mod.lisp") :rune)
   ((:system . "centaur/bitops/signed-byte-p.lisp") :rune)

; Backtrace from raw Lisp shows this sort of entry:
#|
 (8256159D0) : 8 (FIND-PREV-STOBJ-BINDING (MV-NTH '-2 'NIL) ACL2_INVISIBLE::|The Live State Itself|) 909
|#
   ((:system . "centaur/fgl/symbolic-arithmetic.lisp") :rune)
   ((:system . "centaur/fgl/mark-bfrs.lisp") :rune)
   ((:system . "centaur/glmc/glmc-generic-proof.lisp") :rune)
; ... and in second pass:
   ((:system . "centaur/aignet/from-hons-aig.lisp") :rune)
   ((:system . "centaur/aignet/supergate-construction.lisp") :rune)
   ((:system . "centaur/aignet/cnf.lisp") :rune)
   ((:system . "centaur/aignet/copying.lisp") :rune)
   ((:system . "centaur/aignet/cuts4.lisp") :rune)
; ... and in third pass:
   ((:system . "centaur/aignet/aiger.lisp") :rune)
   ((:system . "centaur/aignet/prune.lisp") :rune)
   ((:system . "centaur/aignet/self-constprop.lisp") :rune)
; ... and in fourth pass:
   ((:system . "centaur/aignet/balance.lisp") :rune)
   ((:system . "centaur/fgl/pathcond-fix.lisp") :rune)
   ((:system . "centaur/fgl/simplify.lisp") :rune)
; ... and in sixth or seventh pass:
   ((:system . "centaur/aignet/observability.lisp") :rune)
   ((:system . "centaur/truth/dsd4-aignet.lisp") :rune)
   ((:system . "centaur/fgl/clauseproc.lisp") :rune)
; ... and in eighth/ninth pass:
   ((:system . "centaur/fgl/ipasir-sat.lisp") :rune)

; Took too long in second pass (as shown):
   ((:system . "projects/rp-rewriter/lib/mult3/unpack-booth-correct.lisp") :rune) ; 5+ hr
   ((:system . "workshops/2015/jain-manolios/support/stack-machine/buffered-stack-cap-2.lisp") :rune) ; 13+ hr
   ((:system . "projects/x86isa/machine/register-readers-and-writers.lisp")) ; 13+ hr; still 3 hr with :rune
; Took too long in the fourth pass (as shown):
   ((:system . "kestrel/bv/adder.lisp") :rune) ; 3 hrs
; Took too long in fifth pass (as shown):
   ((:system . "kestrel/axe/rewriter-basic.lisp")) ; 7 hours
   ((:system . "kestrel/axe/jvm/rewriter-jvm.lisp")) ; 7 hours
; Took too long in sixth pass (as shown):
   ((:system . "projects/x86isa/proofs/dataCopy/loop-base") :rune) ; 3.5 hr
   ((:system . "projects/x86isa/proofs/dataCopy/loop-recur") :rune); 3.5 hr
   ((:system . "projects/x86isa/proofs/codewalker-examples/factorial") :rune); 3.5 hr

; For run10:

; ~10 hours; "Start retries: :RUNE." stuck in GC; then :book-runes on retry.  I
; see a huge e/d hint -- I'll just skip this one.
   ((:system . "projects/x86isa/proofs/dataCopy/loop-base.lisp"))
; ~10 hours; "Start retries: :RUNE." no output for over 7 hours:
   ((:system . "projects/x86isa/proofs/codewalker-examples/factorial.lisp") :rune)
; Killed after 1/2 hour because it was only 9% through the file:
   ((:system . "projects/x86isa/proofs/dataCopy/dataCopy.lisp") :rune)
; Odd define-trusted-clause-processor error:
   ((:system . "clause-processors/basic-examples.lisp"))
; Checkpoints from proof failures:
   ((:system . "demos/loop-primer/lp6.lisp"))
   ((:system . "centaur/sv/svex/fixpoint-eval.lisp"))
   ((:system . "centaur/sv/svtv/svtv-spec.lisp"))

; I killed the final run10 run while these were running:
; (18 min. elapsed) centaur/svl/svex-reduce/svex-reduce-with-env.lisp
; (45 min. elapsed) projects/rp-rewriter/lib/mult2/pp-flatten-meta-correct.lisp

   )
 state)

; This might be worth doing once, but at this point I don't see a need to keep
; this here.
; (or (no-duplicatesp-equal (strip-cars (@ skip-retry-alist)) )
;     (er hard 'top "Fix customize.lisp to avoid duplicate filenames."))

(include-book "kestrel/acl2data/gather/patch-book-advice"
              :ttags :all
              :load-compiled-file nil)

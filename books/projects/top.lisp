; projects/top.lisp
;
; Previously, this book was called doc.lisp and collected xdoc.  But now we
; have top-doc.lisp to collect the xdoc.  So Eric Smith repurposed this book to
; be a regular 'top' book, intended to collect as much of the material from
; this projects/ directory as we can, for inclusion in books/top.lisp.

(in-package "ACL2")

(include-book "include-doc")

;; Brings in many top and doc books:
(include-projects-doc)


; It is desirable that users of the ACL2 Community Books be able to include
; projects and libraries to suite their purposes without issue.  In order to
; detect symbol conflicts at build time, we include as many projects as possible
; in this book.
;
; Include "top" (or topmost) books below for each project.  Keep this list in
; sync with the contents of the projects directory, alphabetically ordered.
; Include dedicated "doc" books in `INCLUDE-PROJECTS-DOC' in the book
; projects/include-doc.
;
; Skipped projects have no apparent topmost book, exist purely for archival
; purposes, have non-standard build requirements, or have multiple symbol
; conflicts with other books.  These qualities do not prevent inclusion here.
; However, these skipped books require additional effort to include them.
; Converting any such SKIP comment to an `INCLUDE-BOOKS' form is encouraged.
(include-book "abnf/top")
; acl2-in-hol -- SKIP
(include-book "aleo/top")
(include-book "apply/top")
; apply-model -- SKIP
; apply-model-2 -- SKIP
; arm -- SKIP
; async -- SKIP
(include-book "avr-isa/avr8_isa_lemmas")
(include-book "bls12-377-curves/top")
(include-book "cache-coherence/top")
(ifdef "ACL2_HAS_REALS"
       (include-book "cholesky/chol")
       :endif)
(include-book "codewalker/codewalker")
; concurrent-programs -- SKIP
(include-book "curve25519/top")
; die-hard-bottle-game -- SKIP
; dpss -- SKIP
; equational -- SKIP
(include-book "execloader/top")
(include-book "farray/farray")
; fields -- SKIP
(include-book "fifo/fifo-list-based")
; filesystems -- SKIP
; fm9001 -- SKIP
; fm9801 -- SKIP
; gaussian-elim-solvers -- SKIP
; groups -- SKIP
; hexnet -- SKIP
; hol-in-acl2 -- SKIP
; hybrid-systems -- SKIP
(include-book "irv/top")
(include-book "leftist-trees/top")
; legacy-defrstobj -- SKIP
; linear -- SKIP
(include-book "milawa/doc")
(include-book "numbers/euler")
(ifdef "ACL2_HAS_REALS"
       (include-book "omp/top")
       :endif)
; oracle -- SKIP
; paco -- SKIP
; pdf-parser -- SKIP
(include-book "pfcs/top")
; pltpa -- SKIP
(include-book "poseidon/top")
(include-book "python/embedding/top")
; rac -- SKIP
(include-book "regex/regex-ui")
(include-book "rp-rewriter/top")
(include-book "sat/proof-checker-itp13/top")
(include-book "sat/proof-checker-array/top")
(include-book "sat/dimacs-reader/reader")
; sb-machine -- SKIP
(include-book "schroeder-bernstein/schroeder-bernstein")
; security -- SKIP
(include-book "set-theory/top")
(include-book "shnf/top")
(include-book "sidekick/top")
(include-book "simple-url-parser/parse-url")
(include-book "smtlink/top" :ttags :all)
(ifdef "OS_HAS_SMTLINK"
       (include-book "smtlink/examples/examples")
       :endif)
(ifdef "OS_HAS_SMTLINK"
       (include-book "smtlink/examples/ringosc")
       :endif)
(include-book "srt/srt")
(include-book "stateman/stateman22")
; symbolic -- SKIP
(include-book "taspi/taspi-xdoc")
; translators -- SKIP
; (include-book "vescmul/top") ; TODO: resolve build issue
; vwsim -- SKIP
(include-book "wp-gen/wp-gen")
(include-book "x86isa/top")

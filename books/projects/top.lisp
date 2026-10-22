; projects/top.lisp
;
; Previously, this book was called doc.lisp and collected xdoc.  But now we
; have top-doc.lisp to collect the xdoc.  So Eric Smith repurposed this book to
; be a regular 'top' book, intended to collect as much of the material from
; this projects/ directory as we can, for inclusion in books/top.lisp.

(in-package "ACL2")

(include-book "build/ifdef" :dir :system)
(include-book "include-doc")

;; Brings in many top and doc books:
(include-projects-doc)


; It is desirable that users of the ACL2 Community Books be able to include
; projects and libraries to suit their purposes without issue.  In order to
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
; Converting any such SKIP comment to an `INCLUDE-BOOK' form is encouraged.
(ifndef "ACL2_HAS_REALS"
        (include-book "abnf/top")
        :endif)
; acl2-in-hol -- SKIP
(ifndef "ACL2_HAS_REALS"
        (include-book "aleo/top")
        :endif)
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
; die-hard-bottle-game -- SKIP:
;; The proofs in die-hard-bottle-game are not robust to the reordering in the
;; prover induced by changing packages.
; dpss -- SKIP
(include-book "equational/prover")
(include-book "execloader/top")
(include-book "farray/farray")
; fields -- SKIP
(include-book "fifo/fifo-list-based")
; filesystems -- SKIP
(include-book "filesystems/utilities/cpp-syntax/top")
; fm9001 -- SKIP
; fm9801 -- SKIP
; gaussian-elim-solvers -- SKIP
; groups -- SKIP
; hexnet -- SKIP
; hol-in-acl2 -- SKIP
; hybrid-systems -- SKIP, uses-acl2r
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
(ifndef "ACL2_HAS_REALS"
        (ifndef "ACL2_HAS_PARALLEL"
                (include-book "python/embedding/top")
                :endif)
        :endif)
; rac -- SKIP
(ifndef "ACL2_HAS_REALS"
        (include-book "regex/regex-ui")
        :endif)
(ifndef "ACL2_HAS_REALS"
        (include-book "rp-rewriter/top")
        :endif)
(include-book "sat/proof-checker-itp13/top")
(include-book "sat/proof-checker-array/top")
(include-book "sat/dimacs-reader/reader")
; sb-machine -- SKIP
(include-book "schroeder-bernstein/schroeder-bernstein")
; security -- SKIP, non-acl2r
(ifndef "ACL2_HAS_REALS"
        (include-book "set-theory/top")
        :endif)
(include-book "shnf/top")
; Do not include sidekick/top here.  That book is a wrapper for sidekick/server
; that also starts the server.
(ifndef "ACL2_HAS_REALS"
        (include-book "sidekick/server")
        :endif)
(include-book "simple-url-parser/parse-url")
(include-book "smtlink/top" :ttags :all)
(ifdef "OS_HAS_SMTLINK"
       (include-book "smtlink/examples/examples")
       :endif)
(ifdef "OS_HAS_SMTLINK"
       (include-book "smtlink/examples/ringosc")
       :endif)
; srt -- SKIP
(include-book "stateman/stateman22")
; symbolic -- SKIP
(ifndef "ACL2_HAS_REALS"
        (include-book "taspi/taspi-xdoc")
        :endif)
; translators -- SKIP
; vescmul -- SKIP
; vwsim -- SKIP, non-acl2r
(include-book "wp-gen/wp-gen")
(include-book "x86isa/top")

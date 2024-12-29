; Checking for package conflicts

; Copyright (C) 2022-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; This book attempts to include as many different packages as possible, by
;; including portcullis many books.  Packages that do not have portcullis.lisp
;; files are brought in via packages.acl2 instead, so see that file as well.

;; These came from running 'find ../../.. -name portcullis.lisp':

;; TODO: Bring in M5 package once modernized

(include-book "acl2s/portcullis" :dir :system)
(include-book "build/portcullis" :dir :system)
(include-book "centaur/4v-sexpr/portcullis" :dir :system)
(include-book "centaur/acre/portcullis" :dir :system)
(include-book "centaur/aignet/portcullis" :dir :system)
(include-book "centaur/aig/portcullis" :dir :system)
(include-book "centaur/bed/portcullis" :dir :system)
(include-book "centaur/bigmems/bigmem/portcullis" :dir :system)
(include-book "centaur/bigmems/bigmem-asymmetric/portcullis" :dir :system)
(include-book "centaur/bigmems/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)
(include-book "centaur/bridge/portcullis" :dir :system)
(include-book "centaur/clex/portcullis" :dir :system)
(include-book "centaur/defrstobj2/portcullis" :dir :system)
(include-book "centaur/defrstobj/portcullis" :dir :system)
(include-book "centaur/depgraph/portcullis" :dir :system)
(include-book "centaur/esim/portcullis" :dir :system)
(include-book "centaur/fgl/portcullis" :dir :system)
(include-book "centaur/fty/portcullis" :dir :system)
(include-book "centaur/getopt/portcullis" :dir :system)
(include-book "centaur/glmc/portcullis" :dir :system)
(include-book "centaur/gl/portcullis" :dir :system)
(include-book "centaur/ipasir/portcullis" :dir :system)
(include-book "centaur/lispfloat/portcullis" :dir :system)
(include-book "centaur/memoize/portcullis" :dir :system)
(include-book "centaur/meta/portcullis" :dir :system)
(include-book "centaur/nrev/portcullis" :dir :system)
(include-book "centaur/satlink/portcullis" :dir :system)
;(include-book "centaur/svl/portcullis" :dir :system) ; todo: this includes an include-book !
(include-book "centaur/sv/portcullis" :dir :system)
(include-book "centaur/truth/portcullis" :dir :system)
;(include-book "centaur/vl2014/portcullis" :dir :system) ; todo: brings in extra stuff
(include-book "centaur/vl/portcullis" :dir :system)
(include-book "coi/adviser/portcullis" :dir :system)
(include-book "coi/alists/portcullis" :dir :system)
(include-book "coi/bags/portcullis" :dir :system)
(include-book "coi/defstructure/portcullis" :dir :system)
(include-book "coi/defung/portcullis" :dir :system)
(include-book "coi/dtrees/portcullis" :dir :system)
(include-book "coi/gacc/portcullis" :dir :system)
(include-book "coi/lists/portcullis" :dir :system)
(include-book "coi/maps/portcullis" :dir :system)
(include-book "coi/nary/portcullis" :dir :system)
(include-book "coi/paths/portcullis" :dir :system)
(include-book "coi/quantification/portcullis" :dir :system)
(include-book "coi/records/portcullis" :dir :system)
(include-book "coi/symbol-fns/portcullis" :dir :system)
(include-book "coi/syntax/portcullis" :dir :system)
(include-book "coi/util/portcullis" :dir :system)
(include-book "cowles/portcullis" :dir :system)
(include-book "data-structures/memories/portcullis" :dir :system)
(include-book "data-structures/portcullis" :dir :system)
(include-book "projects/abnf/portcullis" :dir :system)
(include-book "kestrel/acl2pl/portcullis" :dir :system)
(include-book "kestrel/apt/portcullis" :dir :system)
(include-book "kestrel/bitcoin/portcullis" :dir :system)
(include-book "kestrel/c/portcullis" :dir :system)
(include-book "kestrel/crypto/blake/portcullis" :dir :system)
(include-book "kestrel/crypto/ecdsa/portcullis" :dir :system)
(include-book "kestrel/crypto/ecurve/portcullis" :dir :system)
(include-book "kestrel/crypto/hmac/portcullis" :dir :system)
(include-book "kestrel/crypto/kdf/portcullis" :dir :system)
(include-book "kestrel/crypto/keccak/portcullis" :dir :system)
(include-book "kestrel/crypto/mimc/portcullis" :dir :system)
(include-book "kestrel/crypto/padding/portcullis" :dir :system)
(include-book "kestrel/crypto/portcullis" :dir :system)
(include-book "kestrel/crypto/r1cs/portcullis" :dir :system)
(include-book "kestrel/crypto/salsa/portcullis" :dir :system)
(include-book "kestrel/crypto/sha-2/portcullis" :dir :system)
(include-book "kestrel/ethereum/portcullis" :dir :system)
(include-book "kestrel/ethereum/semaphore/portcullis" :dir :system)
(include-book "kestrel/hdwallet/portcullis" :dir :system)
(include-book "kestrel/isar/portcullis" :dir :system)
(include-book "kestrel/java/portcullis" :dir :system)
(include-book "kestrel/json/portcullis" :dir :system)
(include-book "kestrel/jvm/portcullis" :dir :system)
(include-book "kestrel/number-theory/portcullis" :dir :system)
(include-book "kestrel/prime-fields/portcullis" :dir :system)
(include-book "kestrel/risc-v/portcullis" :dir :system)
(include-book "kestrel/simpl-imp/portcullis" :dir :system)
(include-book "kestrel/soft/portcullis" :dir :system)
(include-book "kestrel/solidity/portcullis" :dir :system)
(include-book "kestrel/syntheto/portcullis" :dir :system)
(include-book "std/omaps/portcullis" :dir :system)
(include-book "kestrel/x86/portcullis" :dir :system)
(include-book "kestrel/yul/portcullis" :dir :system)
(include-book "kestrel/zcash/portcullis" :dir :system)
(include-book "oslib/portcullis" :dir :system)
(include-book "projects/apply-model-2/portcullis" :dir :system)
;; (include-book "projects/apply-model/portcullis" :dir :system) ; frozen directory in support of a paper
(include-book "projects/async/portcullis" :dir :system)
(include-book "projects/execloader/portcullis" :dir :system)
(include-book "projects/farray/portcullis" :dir :system)
(include-book "projects/fm9001/portcullis" :dir :system)
(include-book "projects/irv/portcullis" :dir :system)
;; (include-book "projects/legacy-defrstobj/portcullis" :dir :system) ; conflict on RSTOBJ package
;; (include-book "projects/milawa/ACL2/portcullis" :dir :system) ; error
;; (include-book "projects/paco/portcullis" :dir :system) ; doesn't exist: see packages.acl2
(include-book "projects/pfcs/portcullis" :dir :system)
(include-book "projects/regex/portcullis" :dir :system)
;; (include-book "projects/rp-rewriter/meta/portcullis" :dir :system)  ; has an include book but brings in no new packages
(include-book "projects/rp-rewriter/portcullis" :dir :system)
(include-book "projects/sat/dimacs-reader/portcullis" :dir :system)
(include-book "projects/sat/lrat/portcullis" :dir :system)
(include-book "projects/sat/proof-checker-array/portcullis" :dir :system)
(include-book "projects/sat/proof-checker-itp13/portcullis" :dir :system)
(include-book "projects/sb-machine/portcullis" :dir :system)
(include-book "projects/sb-machine/proofs/completed/portcullis" :dir :system)
(include-book "projects/sidekick/portcullis" :dir :system)
(include-book "projects/smtlink/portcullis" :dir :system)
(include-book "projects/stateman/portcullis" :dir :system)
(include-book "projects/x86isa/portcullis/portcullis" :dir :system)
(include-book "rtl/rel11/portcullis" :dir :system)
(include-book "std/obags/portcullis" :dir :system)
(include-book "std/portcullis" :dir :system)
(include-book "std/typed-lists/portcullis" :dir :system)
(include-book "system/doc/portcullis" :dir :system)
(include-book "tools/prettygoals/portcullis" :dir :system)
(include-book "workshops/2018/sumners/portcullis" :dir :system)
(include-book "workshops/2020/sumners/portcullis" :dir :system)
(include-book "workshops/2022/gamboa-primitive-roots/portcullis" :dir :system)
(include-book "workshops/2022/walter-manolios/acl2s-utils/portcullis" :dir :system)
(include-book "workshops/2022/walter-manolios/portcullis" :dir :system)

;; See above for reasons:
(defconst *excluded-prefixes-due-to-packages*
  '("projects/apply-model/"
    "projects/legacy-defrstobj/"
    ;; todo: old copies of coi, set-theory, osets
    "projects/milawa/ACL2/"))

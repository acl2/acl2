; Top level book for the Community Books
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

;; Previously, this book generated a manual, but books/doc/top now does that
;; better.  So the sole purpose of this book now is to check for name conflicts
;; after including as many community books as possible.

;; Note about the following commented-out form.  This allows a significant
;; reduction of memory usage by this book: of ~130 million conses in the ACL2
;; world after all books are loaded, 51 million are due to tau automatically
;; computing implicants from theorems/definitions -- 42 million conses are
;; stored in various POS-IMPLICANTS and 9.2 million in various NEG-IMPLICANTS
;; properties.  So overriding the default setting of tau-auto-mode saves a
;; significant amount of memory when loading this book.  Question is whether
;; it's worth the cheating.

#||
(defttag :override-tau-auto-mode)
(progn!
 (set-raw-mode t)
 (setf (cdr (assoc :tau-auto-modep *initial-acl2-defaults-table*)) nil)
 (set-raw-mode nil))
||#

(progn ;; use progn to time including all the books
(include-book "build/ifdef" :dir :system)

; Note, 7/28/2014: if we include
; (include-book "std/system/top" :dir :system)
; instead of the following, we get a name conflict.
(include-book "std/system/non-parallel-book" :dir :system)

(include-book "xdoc/defxdoc-raw" :dir :system) ; for xdoc::all-xdoc-topics

 ;; Disabling waterfall parallelism because the include-books are too slow with
 ;; it enabled, since waterfall parallelism unmemoizes the six or so functions
 ;; that ACL2(h) memoizes by default (in particular, fchecksum-obj needs to be
 ;; memoized to include centaur/esim/tutorial/alu16-book).

 ;; [Jared] BOZO: is the above comment about include books even true anymore?
 ;; If so, maybe waterfall parallelism doesn't have to do this with the new
 ;; thread-safe memo code?

 ;; [Jared] BOZO: even if waterfall parallelism still disables this memoization,
 ;; do we care?  The alu16-book demo has been removed from the manual.  (Maybe
 ;; we should put it back in.  Do we care how long the manual takes to build?)
(non-parallel-book)

(include-book "centaur/misc/tshell" :dir :system)
(value-triple (acl2::tshell-ensure))

(include-book "centaur/misc/memory-mgmt" :dir :system)
(value-triple (set-max-mem (* 10 (expt 2 30))))

;; this is included in some other books, but I'm putting it here so we never
;; accidentally leave it out -- important for getting reasonable performance
;; when building the final documentation.
(include-book "std/strings/fast-cat" :dir :system)

(include-book "relnotes")
(include-book "practices")

(include-book "xdoc/save" :dir :system)
(include-book "xdoc/archive" :dir :system)
(include-book "xdoc/archive-matching-topics" :dir :system)

(include-book "build/doc" :dir :system)

(include-book "centaur/4v-sexpr/top" :dir :system)
(include-book "centaur/aig/top" :dir :system)

(include-book "centaur/aignet/top" :dir :system)

; The rest of ihs is included elsewhere transitively.
; We load logops-lemmas first so that the old style :doc-strings don't get
; stripped away when they're loaded redundantly later.
(include-book "ihs/logops-lemmas" :dir :system)
(include-book "ihs/math-lemmas" :dir :system)

(include-book "centaur/bitops/top" :dir :system)
(include-book "centaur/bitops/congruences" :dir :system)
(include-book "centaur/bitops/defaults" :dir :system)

(include-book "centaur/acre/top" :dir :system)

(include-book "centaur/bigmem/bigmem" :dir :system)

(include-book "centaur/bridge/top" :dir :system)

(include-book "centaur/clex/example" :dir :system)
(include-book "centaur/nrev/demo" :dir :system)
(include-book "centaur/lispfloat/top" :dir :system)

(include-book "centaur/defrstobj/defrstobj" :dir :system)
(include-book "centaur/defrstobj2/defrstobj" :dir :system)

(include-book "centaur/esim/stv/stv-top" :dir :system)
(include-book "centaur/esim/stv/stv-debug" :dir :system)
(include-book "centaur/esim/esim-sexpr-correct" :dir :system)

(include-book "centaur/getopt/top" :dir :system)
(include-book "centaur/getopt/demo" :dir :system)
(include-book "centaur/getopt/demo2" :dir :system)
(include-book "centaur/bed/top" :dir :system)

(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/gl/bfr-aig-bddify" :dir :system)
(include-book "centaur/gl/gl-ttags" :dir :system)
(include-book "centaur/gl/gobject-type-thms" :dir :system)
(include-book "centaur/gl/bfr-satlink" :dir :system)
(include-book "centaur/gl/bfr-fraig-satlink" :dir :system)
(include-book "centaur/gl/def-gl-rule" :dir :system)
(include-book "centaur/gl/defthm-using-gl" :dir :system)

(include-book "centaur/glmc/glmc" :dir :system)
(include-book "centaur/glmc/bfr-mcheck-abc" :dir :system)

(include-book "centaur/satlink/top" :dir :system)
(include-book "centaur/satlink/check-config" :dir :system)
(include-book "centaur/satlink/benchmarks" :dir :system)

(include-book "centaur/depgraph/top" :dir :system)

(include-book "quicklisp/top" :dir :system)

(include-book "centaur/misc/top" :dir :system)
(include-book "centaur/misc/smm" :dir :system)
(include-book "centaur/misc/tailrec" :dir :system)
(include-book "centaur/misc/hons-remove-dups" :dir :system)
(include-book "centaur/misc/seed-random" :dir :system)
(include-book "centaur/misc/load-stobj" :dir :system)
(include-book "centaur/misc/load-stobj-tests" :dir :system)
(include-book "centaur/misc/count-up" :dir :system)
(include-book "centaur/misc/fast-alist-pop" :dir :system)
(include-book "centaur/misc/spacewalk" :dir :system)
(include-book "centaur/misc/dag-measure" :dir :system)
(include-book "centaur/misc/try-gl-concls" :dir :system)

(include-book "centaur/svl/top" :dir :system)

;; BOZO conflicts with something in 4v-sexpr?

;; (include-book "misc/remove-assoc")
;; (include-book "misc/sparsemap")
;; (include-book "misc/sparsemap-impl")
(include-book "centaur/misc/stobj-swap" :dir :system)

(include-book "oslib/top" :dir :system)

(include-book "std/top" :dir :system)
(include-book "std/basic/inductions" :dir :system)
(include-book "std/io/unsound-read" :dir :system)
(include-book "std/bitsets/top" :dir :system)

(include-book "std/strings/top" :dir :system)
(include-book "std/strings/base64" :dir :system)
(include-book "std/strings/pretty" :dir :system)


(include-book "centaur/ubdds/lite" :dir :system)
(include-book "centaur/ubdds/param" :dir :system)

(include-book "centaur/sv/top" :dir :system)
(include-book "centaur/fgl/top" :dir :system)

(ifdef "OS_HAS_GLUCOSE"
       (include-book "centaur/sv/tutorial/alu" :dir :system)
       (include-book "centaur/sv/tutorial/boothpipe" :dir :system)

       (ifdef "OS_HAS_ABC"
              (include-book "centaur/glmc/glmc-test" :dir :system)
              (include-book "centaur/glmc/counter" :dir :system)
              :endif)

       (ifdef "OS_HAS_IPASIR"
              (include-book "centaur/sv/tutorial/sums" :dir :system)
              :endif)
       :endif)

(ifndef "OS_HAS_GLUCOSE"
        ;; This is needed to avoid broken topic link errors
        (defxdoc sv::sv-tutorial
          :parents (sv::sv)
          :short "Stub for missing topic"
          :long "<p>This topic was omitted from the manual because it is in a
book that depends on Glucose being installed.</p>")
        (defxdoc sv::stvs-and-testing
          :parents (sv::sv-tutorial)
          :short "Stub for missing topic"
          :long "<p>This topic was omitted from the manual because it is in a
book that depends on Glucose being installed.</p>")
        :endif)




(include-book "centaur/esim/vcd/vcd" :dir :system)
(include-book "centaur/esim/vcd/esim-snapshot" :dir :system)
(include-book "centaur/esim/vcd/vcd-stub" :dir :system)
;; BOZO causes some error with redefinition?  Are we loading the right
;; books above?  What does stv-debug load?
;; (include-book "centaur/esim/vcd/vcd-impl")

(include-book "centaur/vl/doc" :dir :system)

;; Try to avoid some expensive type-prescription problems
(in-theory (disable true-listp-append (:t append)))

(include-book "centaur/vl/kit/top" :dir :system)
(include-book "centaur/vl/mlib/atts" :dir :system)

(include-book "centaur/vl2014/doc" :dir :system)
(include-book "centaur/vl2014/kit/top" :dir :system)
(include-book "centaur/vl2014/mlib/clean-concats" :dir :system)
(include-book "centaur/vl2014/lint/use-set" :dir :system)
(include-book "centaur/vl2014/transforms/clean-selects" :dir :system)
(include-book "centaur/vl2014/transforms/propagate" :dir :system)
(include-book "centaur/vl2014/transforms/expr-simp" :dir :system)
(include-book "centaur/vl2014/transforms/inline" :dir :system)
(include-book "centaur/vl2014/util/prefix-hash" :dir :system)

;; BOZO conflict with prefix-hash stuff above.  Need to fix this.  Also, are
;; these being used at all?

;; (include-book "centaur/vl2014/util/prefixp" :dir :system)

(include-book "hacking/all" :dir :system)
(include-book "hints/consider-hint" :dir :system)
(include-book "hints/hint-wrapper" :dir :system)

(include-book "ordinals/e0-ordinal" :dir :system)

(include-book "tools/do-not" :dir :system)
(include-book "tools/plev" :dir :system)
(include-book "tools/plev-ccl" :dir :system)
(include-book "tools/with-supporters" :dir :system)
(include-book "tools/remove-hyps" :dir :system)
(include-book "tools/removable-runes" :dir :system)
(include-book "tools/oracle-time" :dir :system)
(include-book "tools/oracle-timelimit" :dir :system)
(include-book "tools/defthmg" :dir :system)
(include-book "tools/trivial-ancestors-check" :dir :system)
(include-book "tools/without-subsumption" :dir :system)
(include-book "tools/rewrite-dollar" :dir :system)
(include-book "tools/open-trace-file-bang" :dir :system)
(include-book "tools/prove-dollar" :dir :system)
(include-book "coi/util/rewrite-equiv" :dir :system)

;; This book memoizes several functions including translate11, translate11-lst,
;; translate11-call, which end up taking a lot of space and causing us to spend
;; a lot of time GCing.
(include-book "tools/memoize-prover-fns" :dir :system)
(unmemoize-lst (f-get-global 'memoized-prover-fns state))

(include-book "tools/untranslate-for-exec" :dir :system)
(include-book "tools/er-soft-logic" :dir :system)
(include-book "tools/run-script" :dir :system)
(include-book "clause-processors/doc" :dir :system)
(include-book "system/event-names" :dir :system)
(include-book "system/acl2-system-exports" :dir :system)
(include-book "system/doc/developers-guide" :dir :system)
(include-book "system/pseudo-tests-and-calls-listp" :dir :system)

;; [Jared] removing these to speed up the manual build
;; BOZO should we put them back in?
;(include-book "centaur/esim/tutorial/intro" :dir :system)
;(include-book "centaur/esim/tutorial/alu16-book" :dir :system)
;(include-book "centaur/esim/tutorial/counter" :dir :system)

;; [Jared] removed this to avoid depending on glucose and to speed up
;; the manual build
; (include-book "centaur/esim/tests/common" :dir :system)


;; Not much doc here, but some theorems from arithmetic-5 are referenced by
;; other topics...
(include-book "arithmetic-5/top" :dir :system)
(include-book "arithmetic/top" :dir :system)

(include-book "rtl/rel11/lib/top" :dir :system)
; And books not included in lib/top:
(include-book "rtl/rel11/lib/add" :dir :system)
(include-book "rtl/rel11/lib/mult" :dir :system)
(include-book "rtl/rel11/lib/div" :dir :system)
(include-book "rtl/rel11/lib/srt" :dir :system)
(include-book "rtl/rel11/lib/sqrt" :dir :system)

(include-book "centaur/fty/top" :dir :system)
(include-book "centaur/fty/bitstruct" :dir :system)

(include-book "std/testing/assert" :dir :system)
(include-book "misc/bash" :dir :system)
(include-book "misc/defmac" :dir :system)
(include-book "misc/defopener" :dir :system)
(include-book "misc/defpm" :dir :system)
(include-book "misc/defpun" :dir :system)
(include-book "misc/dft" :dir :system)
(include-book "misc/dump-events" :dir :system)
(include-book "std/testing/eval" :dir :system)
(include-book "misc/expander" :dir :system)
(include-book "misc/file-io" :dir :system)
(include-book "misc/find-lemmas" :dir :system)
(include-book "misc/hons-help" :dir :system)
; The definition of QCAR in misc/hons-tests.lisp conflicts with that
; in centaur/ubdds/core.lisp.
; (include-book "misc/hons-tests" :dir :system)
(include-book "misc/install-not-normalized" :dir :system)
(include-book "misc/meta-lemmas" :dir :system)
(include-book "misc/records" :dir :system)
(include-book "misc/seq" :dir :system)
(include-book "misc/seqw" :dir :system)
(include-book "misc/simp" :dir :system)
(include-book "misc/sin-cos" :dir :system)
(include-book "misc/total-order" :dir :system)
(include-book "misc/trace-star" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)
(include-book "misc/with-waterfall-parallelism" :dir :system)
(include-book "misc/without-waterfall-parallelism" :dir :system)

(include-book "make-event/proof-by-arith" :dir :system)
(include-book "make-event/eval-check" :dir :system)

(include-book "centaur/memoize/old/profile" :dir :system)
(include-book "centaur/memoize/old/watch" :dir :system)

(include-book "acl2s/doc" :dir :system)
(include-book "projects/smtlink/top" :dir :system :ttags :all)

(include-book "projects/doc" :dir :system)

;(include-book "kestrel/top" :dir :system)
(include-book "kestrel/top-doc" :dir :system) ; for now

(include-book "centaur/ipasir/ipasir-tools" :dir :system)

;; [Jared] keep these near the end to avoid expensive type prescription rules,
;; especially related to consp-append.
(include-book "data-structures/top" :dir :system)
(include-book "data-structures/memories/memory" :dir :system)

(include-book "coi/documentation" :dir :system)
(include-book "clause-processors/pseudo-term-fty" :dir :system)

(include-book "std/util/defretgen" :dir :system)
) ;; end progn for including all the books

#||

;; This is a nice place to put include-book scanner hacks that trick cert.pl
;; into certifying unit-testing books that don't actually need to be included
;; anywhere.  This just tricks the dependency scanner into building
;; these books.

(include-book "xdoc/all" :dir :system)

(include-book "xdoc/tests/preprocessor-tests" :dir :system)
(include-book "xdoc/tests/unsound-eval-tests" :dir :system)
(include-book "xdoc/tests/defsection-tests" :dir :system)
(include-book "centaur/defrstobj/basic-tests" :dir :system)
(include-book "std/util/tests/top" :dir :system)
(include-book "std/util/extensions/assert-return-thms" :dir :system)
(include-book "centaur/misc/tshell-tests" :dir :system)
(include-book "centaur/misc/stobj-swap-test" :dir :system)
(include-book "oslib/tests/top" :dir :system)

(include-book "centaur/ubdds/sanity-check-macros" :dir :system)

(include-book "centaur/memoize/old/case" :dir :system)
(include-book "centaur/memoize/old/profile" :dir :system)
(include-book "centaur/memoize/old/watch" :dir :system)
(include-book "centaur/memoize/portcullis" :dir :system)
(include-book "centaur/memoize/tests" :dir :system)
(include-book "centaur/memoize/top" :dir :system)

||#

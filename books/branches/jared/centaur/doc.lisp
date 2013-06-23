; Centaur Book Documentation
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")

(make-event

; Disabling waterfall parallelism because the include-books are too slow with
; it enabled, since waterfall parallelism unmemoizes the six or so functions
; that ACL2(h) memoizes by default (in particular, fchecksum-obj needs to be
; memoized to include centaur/tutorial/alu16-book).

 (if (and (hons-enabledp state)
          (f-get-global 'parallel-execution-enabled state))
     (er-progn (set-waterfall-parallelism nil)
               (value '(value-triple nil)))
   (value '(value-triple nil))))


(include-book "vl/top")
(include-book "vl/lint/lint")
(include-book "vl/mlib/clean-concats")
(include-book "vl/mlib/atts")
(include-book "vl/mlib/json")
(include-book "vl/transforms/xf-clean-selects")
(include-book "vl/transforms/xf-propagate")
(include-book "vl/transforms/xf-expr-simp")
(include-book "vl/transforms/xf-inline")

(include-book "aig/aiger")
(include-book "aig/aig-equivs")
(include-book "aig/aig-vars")
(include-book "aig/aig-vars-fast")
(include-book "aig/base")
(include-book "aig/bddify")
(include-book "aig/bddify-correct")
(include-book "aig/eval-restrict")
(include-book "aig/g-aig-eval")
(include-book "aig/induction")
(include-book "aig/misc")
(include-book "aig/three-four")
(include-book "aig/witness")
(include-book "aig/vuaig")

(include-book "ubdds/lite")
(include-book "ubdds/param")

(include-book "bitops/top")

(include-book "clex/example")

(include-book "gl/gl")
(include-book "gl/bfr-aig-bddify")

(include-book "4v-sexpr/top")

(include-book "esim/stv/stv-top")
(include-book "esim/stv/stv-debug")
(include-book "esim/esim-sexpr-correct")


; The following are included automatically by the xdoc::save command below, but
; we include them explicitly to support the hons `make' target in the books/
; directory (and hence the regression-hons `make' target in the acl2-sources
; directory).
(include-book "../xdoc/save")
(include-book "../xdoc/defxdoc-raw")
(include-book "../xdoc/mkdir-raw")
(include-book "../xdoc/topics")
(include-book "../xdoc/extra-packages")

(include-book "misc/hons-remove-dups")
(include-book "misc/seed-random")
(include-book "std/lists/nth" :dir :system)
(include-book "misc/load-stobj")
(include-book "misc/load-stobj-tests")

(include-book "tutorial/intro")
(include-book "tutorial/alu16-book")
(include-book "tutorial/counter")

(include-book "bridge/top")

(include-book "defrstobj/defrstobj")

(include-book "misc/smm")
(include-book "bitops/install-bit")
(include-book "bitops/rotate")
(include-book "misc/tailrec")
(include-book "vl/mlib/sub-counts")
(include-book "vl/util/prefix-hash")

(include-book "regex/regex-ui" :dir :system)

(include-book "countereg-gen/top" :dir :system)

(include-book "std/top" :dir :system)

#||

;; This really doesn't belong here, but I want it out of cutil/top to improve
;; the critical path.  This just tricks the dependency scanner into building these
;; books.
(include-book "bitops/congruences")
(include-book "defrstobj/basic-tests")
(include-book "cutil/deflist-tests" :dir :system)
(include-book "cutil/defalist-tests" :dir :system)
(include-book "cutil/defmapappend-tests" :dir :system)
(include-book "cutil/defprojection-tests" :dir :system)

;; Here is more tricking of the dependency scanner, to avoid leaving out books
;; under books/centaur/ from the certification process invoked by running 'make
;; regression-hons' from the acl2-sources directory.  Note that at least one of
;; these can't be moved to outside this comment: defrstobj/groundwork/demo1
;; gives a conflicting definition of a stobj, st.

(include-book "bitops/sign-extend")
(include-book "defrstobj/groundwork/demo1")
(include-book "defrstobj/groundwork/demo2")
(include-book "defrstobj/groundwork/demo3")
(include-book "defrstobj/groundwork/demo4")
(include-book "defrstobj/groundwork/demo5")
(include-book "misc/top")
(include-book "ubdds/sanity-check-macros")
(include-book "vl/checkers/use-set-tool")
(include-book "vl/lint/xf-drop-unresolved-submodules")
(include-book "vl/mlib/lvalues-mentioning")
(include-book "vl/mlib/rvalues")
(include-book "vl/util/prefixp")

; Another useful book:
(include-book "gl/bfr-satlink")

; Let's just put down the rest of the books that were discovered missing on
; 5/10/2013, when we certified with the legacy makefile (books/Makefile.legacy)
; instead of the new makefile (books/Makefile).

(include-book "aig/best-aig")
(include-book "aignet/aig-sim")
(include-book "aignet/copying")
(include-book "aignet/from-hons-aig-fast")
(include-book "aignet/prune")
(include-book "aignet/to-hons-aig")
(include-book "aignet/types")
(include-book "aignet/vecsim")
(include-book "aig/random-sim")
(include-book "bitops/ash-bounds")
(include-book "bitops/defaults")
(include-book "bitops/saturate")
(include-book "bitops/signed-byte-p")
(include-book "gl/gl-ttags")
(include-book "gl/gobject-type-thms")
(include-book "misc/count-up")
(include-book "misc/memory-mgmt")
(include-book "misc/remove-assoc")
(include-book "std/lists/resize-list" :dir :system)
(include-book "misc/sparsemap")
(include-book "misc/sparsemap-impl")
(include-book "misc/stobj-swap")
(include-book "vcd/esim-snapshot")
(include-book "vcd/vcd")
(include-book "vcd/vcd-impl")
(include-book "vcd/vcd-stub")
(include-book "vl/mlib/ram-tools")
(include-book "../coi/records/fast/log2")
(include-book "../coi/records/fast/memory")
(include-book "../coi/records/fast/memory-impl")
(include-book "../coi/records/fast/memtree")
(include-book "../coi/records/fast/private")
(include-book "../cutil/tools/assert-return-thms")
(include-book "../memoize/old/case")
(include-book "../memoize/old/profile")
(include-book "../memoize/old/watch")
(include-book "../memoize/portcullis")
(include-book "../memoize/tests")
(include-book "../memoize/top")

||#

(make-event
; xdoc::save is an event, so we might have just called it directly.  But for
; reasons Jared doesn't understand this is screwing up the extended manual we
; build at Centaur.  So, I'm putting the save event into a make-event to try
; to localize its effects to just this book's certification.
  (er-progn (xdoc::save "./manual")
            (value `(value-triple :manual))))

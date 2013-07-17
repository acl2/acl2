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

; This file generates doc/manual, an XDOC manual for the Community Books.

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

(include-book "misc/memory-mgmt")
(value-triple (set-max-mem (* 10 (expt 2 30))))


; [Jared]: I suspect the following comment may be out of date?  But this
; seems harmless enough anyway...
;
;   The following are included automatically by the xdoc::save command below,
;   but we include them explicitly to support the hons `make' target in the
;   books/ directory (and hence the regression-hons `make' target in the
;   acl2-sources directory).

(include-book "../xdoc/save")
(include-book "../xdoc/defxdoc-raw")
(include-book "../xdoc/mkdir-raw")
(include-book "../xdoc/topics")
(include-book "../xdoc/extra-packages")

(include-book "4v-sexpr/top")

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
(include-book "aig/best-aig")
(include-book "aig/random-sim")

(include-book "aignet/aig-sim")
(include-book "aignet/copying")
(include-book "aignet/from-hons-aig-fast")
(include-book "aignet/prune")
(include-book "aignet/to-hons-aig")
(include-book "aignet/types")
(include-book "aignet/vecsim")

(include-book "bitops/top")
(include-book "bitops/congruences")
(include-book "bitops/sign-extend")
(include-book "bitops/install-bit")
(include-book "bitops/rotate")
(include-book "bitops/ash-bounds")
(include-book "bitops/defaults")
(include-book "bitops/saturate")
(include-book "bitops/signed-byte-p")

(include-book "bridge/top")

(include-book "clex/example")

(include-book "countereg-gen/top" :dir :system)

(include-book "defrstobj/defrstobj")

(include-book "esim/stv/stv-top")
(include-book "esim/stv/stv-debug")
(include-book "esim/esim-sexpr-correct")

(include-book "centaur/getopt/top" :dir :system)
(include-book "centaur/getopt/demo" :dir :system)

(include-book "gl/gl")
(include-book "gl/bfr-aig-bddify")
(include-book "gl/gl-ttags")
(include-book "gl/gobject-type-thms")
(include-book "gl/bfr-satlink")

(include-book "misc/top")
(include-book "misc/smm")
(include-book "misc/tailrec")
(include-book "misc/hons-remove-dups")
(include-book "misc/seed-random")
(include-book "misc/load-stobj")
(include-book "misc/load-stobj-tests")
(include-book "misc/count-up")

;; BOZO conflicts with something in 4v-sexpr?

;; (include-book "misc/remove-assoc")
;; (include-book "misc/sparsemap")
;; (include-book "misc/sparsemap-impl")
(include-book "misc/stobj-swap")

(include-book "oslib/top" :dir :system)

(include-book "regex/regex-ui" :dir :system)

(include-book "regression/common")

(include-book "std/top" :dir :system)
(include-book "std/lists/resize-list" :dir :system)
(include-book "std/lists/nth" :dir :system)

(include-book "tutorial/intro")
(include-book "tutorial/alu16-book")
(include-book "tutorial/counter")

(include-book "ubdds/lite")
(include-book "ubdds/param")

(include-book "vcd/vcd")
(include-book "vcd/esim-snapshot")
(include-book "vcd/vcd-stub")
;; BOZO causes some error with redefinition?  Are we loading the right
;; books above?  What does stv-debug load?
;; (include-book "vcd/vcd-impl")

(include-book "vl/top")
(include-book "vl/lint/lint")
(include-book "vl/mlib/clean-concats")
(include-book "vl/mlib/atts")
(include-book "vl/mlib/json")
(include-book "vl/transforms/xf-clean-selects")
(include-book "vl/transforms/xf-propagate")
(include-book "vl/transforms/xf-expr-simp")
(include-book "vl/transforms/xf-inline")
(include-book "vl/mlib/sub-counts")

;; BOZO these are incompatible?  which is right?
(include-book "vl/util/prefix-hash")
;;(include-book "vl/util/prefixp")

(include-book "vl/checkers/use-set-tool")

;; BOZO uh, incompatible with lint?  is this dead?
;; (include-book "vl/lint/xf-drop-unresolved-submodules")
(include-book "vl/mlib/lvalues-mentioning")
(include-book "vl/mlib/rvalues")
(include-book "vl/mlib/ram-tools")


#||

;; This is a nice place to put include-book scanner hacks that trick cert.pl
;; into certifying unit-testing books that don't actually need to be included
;; anywhere.  This just tricks the dependency scanner into building
;; these books.

(include-book "defrstobj/basic-tests")
(include-book "cutil/deflist-tests" :dir :system)
(include-book "cutil/defalist-tests" :dir :system)
(include-book "cutil/defmapappend-tests" :dir :system)
(include-book "cutil/defprojection-tests" :dir :system)
(include-book "cutil/tools/assert-return-thms" :dir :system)

(include-book "defrstobj/groundwork/demo1")
(include-book "defrstobj/groundwork/demo2")
(include-book "defrstobj/groundwork/demo3")
(include-book "defrstobj/groundwork/demo4")
(include-book "defrstobj/groundwork/demo5")

(include-book "ubdds/sanity-check-macros")

;; BOZO why do we care about coi/records/fast?
(include-book "../coi/records/fast/log2")
(include-book "../coi/records/fast/memory")
(include-book "../coi/records/fast/memory-impl")
(include-book "../coi/records/fast/memtree")
(include-book "../coi/records/fast/private")

(include-book "../memoize/old/case")
(include-book "../memoize/old/profile")
(include-book "../memoize/old/watch")
(include-book "../memoize/portcullis")
(include-book "../memoize/tests")
(include-book "../memoize/top")

||#



; Before saving the manual, some last minute changes to make some slight
; improvements to how topics are organized...

(defsection boolean-reasoning
  :short "Libraries related to representing and processing Boolean functions,
e.g., BDDs, AIGs, CNF, SAT solving, etc.")

(defsection arithmetic
  :short "Libraries for reasoning about basic arithmetic, bit-vector
arithmetic, modular arithmetic, etc.")

(defsection hardware-verification
  :short "Libraries for working with hardware description languages, modeling
circuits, etc.")

;; IHS is documented with :DOC, but I want to put it under "arithmetic".  So
;; to do that, we need to do some crazy stuff to get the ACL2 docs loaded...

(local (include-book "xdoc/topics" :dir :system))
(local (include-book "xdoc/extra-packages" :dir :system))
(local (xdoc::import-acl2doc))


;; And then we can muck around with the topic's parents, directly.

#!XDOC
(defun change-parents-fn (name new-parents all-topics)
  (declare (xargs :mode :program))
  (b* (((when (atom all-topics))
        (er hard? 'change-parents-fn "Topic ~x0 was not found." name))
       (topic (car all-topics))
       ((unless (equal (cdr (assoc :name topic)) name))
        (cons (car all-topics)
              (change-parents-fn name new-parents (cdr all-topics))))
       (topic (cons (cons :parents new-parents)
                    (delete-assoc-equal :parents topic))))
    (cons topic (cdr all-topics))))

#!XDOC
(defmacro change-parents (name new-parents)
  `(table xdoc 'doc
          (change-parents-fn ',name ',new-parents
                             (get-xdoc-table world))))

(local (xdoc::change-parents ihs (arithmetic)))

; Similarly redirect esim to hardware-verification
(local (xdoc::change-parents esim (hardware-verification)))

(make-event
; xdoc::save is an event, so we might have just called it directly.  But for
; reasons Jared doesn't understand this is screwing up the extended manual we
; build at Centaur.  So, I'm putting the save event into a make-event to try
; to localize its effects to just this book's certification.
  (er-progn (xdoc::save "./manual"
                        ;; Don't import again since we just imported.
                        :import nil)
            (value `(value-triple :manual))))
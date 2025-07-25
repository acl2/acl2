; ACL2 System+Books Combined XDOC Manual
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

(progn ;; group together include-books to see total time
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
  (include-book "centaur/misc/tshell-unsound" :dir :system)
  (value-triple (acl2::tshell-ensure))

  (include-book "centaur/misc/memory-mgmt" :dir :system)
  (value-triple (set-max-mem (* 10 (expt 2 30))))

  ;; this is included in some other books, but I'm putting it here so we never
  ;; accidentally leave it out -- important for getting reasonable performance
  ;; when building the final documentation.
  (include-book "std/strings/fast-cat" :dir :system)

  (include-book "relnotes")
  (include-book "practices")
  (include-book "publications")

  (include-book "100-theorems")

  (include-book "xdoc/save" :dir :system)
  (include-book "xdoc/archive" :dir :system)

  (include-book "build/doc" :dir :system)

  (include-book "clause-processors/stobj-preservation" :dir :system)

; The rest of ihs is included elsewhere transitively.
; We load logops-lemmas first so that the old style :doc-strings don't get
; stripped away when they're loaded redundantly later.
  (include-book "ihs/logops-lemmas" :dir :system)
  (include-book "ihs/math-lemmas" :dir :system)

; Matt K. comment, July 2021.  I considered using xdoc::archive-matching-topics
; to create an analogue of centaur/bitops/top-doc.lisp to include in
; doc/top.lisp in place of centaur/bitops/top.lisp, to reduce the time a bit
; for building the manual.  But that led to 36 more duplicated topics (of which
; 20 had bitops::bitops/extra-defs as a parent).  I also considered doing
; similarly for centaur/satlink/top, but got extra duplicates there as well.
; My guess is that by including only the top-doc.lisp version, some books that
; had been redundant with centaur/bitops/top.lisp were not redundant with
; centaur/bitops/top-doc.lisp (and similarly for centaur/satlink/), leading to
; the duplication.

  (include-book "centaur/bitops/top" :dir :system) ; see July 2021 comment above
  (include-book "centaur/bitops/congruences" :dir :system)
  (include-book "centaur/bitops/defaults" :dir :system)
  (include-book "centaur/bitops/sparseint" :dir :system)
  (include-book "centaur/bitops/limited-shifts" :dir :system)

  (include-book "centaur/acre/top" :dir :system)

  (include-book "centaur/bigmems/top" :dir :system)

  (include-book "centaur/bridge/top" :dir :system)

  (include-book "centaur/clex/example" :dir :system)
  (include-book "centaur/nrev/demo" :dir :system)
  (include-book "centaur/lispfloat/top" :dir :system)

  (include-book "centaur/defrstobj/defrstobj" :dir :system)
  (include-book "centaur/defrstobj2/defrstobj" :dir :system)


  (include-book "centaur/getopt/top" :dir :system)
  (include-book "centaur/getopt/demo" :dir :system)
  (include-book "centaur/getopt/demo2" :dir :system)
  (include-book "centaur/bed/top" :dir :system)
  (include-book "centaur/misc/def-bounds" :dir :system)

  (include-book "centaur/satlink/top" :dir :system) ; see July 2021 comment above
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
  (include-book "centaur/misc/alphanum-sort" :dir :system)

  (include-book "centaur/svl/top-doc" :dir :system)

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
  (include-book "std/util/defretgen" :dir :system)

  (include-book "std/strings/top" :dir :system)
  (include-book "std/strings/base64" :dir :system)
  (include-book "std/strings/pretty" :dir :system)


  (include-book "centaur/ubdds/lite" :dir :system)
  (include-book "centaur/ubdds/param" :dir :system)


  ;; BOZO conflict with prefix-hash stuff above.  Need to fix this.  Also, are
  ;; these being used at all?

  ;; (include-book "centaur/vl2014/util/prefixp" :dir :system)

  (include-book "hacking/all" :dir :system)
  (include-book "hints/consider-hint" :dir :system)
  (include-book "hints/hint-wrapper" :dir :system)

  (include-book "ordinals/e0-ordinal" :dir :system)

  ;; todo: consider making a tools/doc and including it here instead:
  (include-book "tools/top" :dir :system)

  (include-book "coi/util/rewrite-equiv" :dir :system)

  (include-book "clause-processors/doc" :dir :system)
  (include-book "system/event-names" :dir :system)
  (include-book "system/acl2-system-exports" :dir :system)
  (include-book "system/doc/developers-guide" :dir :system)
  (include-book "system/pseudo-tests-and-calls-listp" :dir :system)
  (include-book "workshops/2025/whats-new-in-acl2-2025" :dir :system)
  (include-book "demos/divp-by-casting" :dir :system)
  (include-book "demos/majority-vote" :dir :system)

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
  (include-book "misc/file-io-doc" :dir :system)
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

  (include-book "acl2s/top-doc" :dir :system)
  (include-book "projects/smtlink/top-doc" :dir :system :ttags :all)

  (include-book "centaur/ipasir/ipasir-tools" :dir :system)
  (include-book "clause-processors/pseudo-term-fty" :dir :system)

  ;; [Jared] keep these near the end to avoid expensive type prescription rules,
  ;; especially related to consp-append.
  (include-book "data-structures/top" :dir :system)
  (include-book "data-structures/memories/memory" :dir :system)

  (include-book "coi/documentation" :dir :system)

  (include-book "centaur/aignet/top-doc" :dir :system)
  (include-book "centaur/gl/top-doc" :dir :system)
  (include-book "centaur/vl/top-doc" :dir :system)
  (include-book "centaur/sv/top-doc" :dir :system)
  (include-book "centaur/fgl/top-doc" :dir :system)
  (include-book "centaur/vl2014/top-doc" :dir :system)
  (include-book "projects/top-doc" :dir :system)
  (include-book "kestrel/top-doc" :dir :system)
  (include-book "rtl/rel11/lib/top-doc" :dir :system)
  (include-book "centaur/esim/top-doc" :dir :system)
  (include-book "centaur/aig/top-doc" :dir :system)
  (include-book "std/util/termhints" :dir :system)

  ;; omitted from gl
  (include-book "centaur/misc/outer-local" :dir :system)

  ;; omitted from aignet
  (include-book "std/stobjs/nested-stobjs" :dir :system)
  (include-book "std/stobjs/updater-independence" :dir :system)
  (include-book "centaur/misc/iter" :dir :system)
  (include-book "centaur/misc/nth-equiv" :dir :system)

  ;; omitted from aig
  (include-book "system/random" :dir :system)
  (include-book "std/util/defretgen" :dir :system)

  ) ;; end progn so we can see total include-book time


(defpointer assocs patbind-assocs)

; Historically we had a completely ad-hoc organization that grew organically as
; topics were added.  This turned out to be a complete mess.  To make the
; manual more approachable and relevant, we now try to impose a better
; hierarchy and add some context.

;; Jared moved the documentation that used to be here into more-topics.lisp so
;; that it can be easily included in other manuals without including top.
(include-book "more-topics")


(include-book "xdoc/topics" :dir :system)
(include-book "xdoc/constructors" :dir :system)
(include-book "xdoc/defxdoc-plus" :dir :system)
(include-book "xdoc/alter" :dir :system)

(local

; The TOP topic will be the first thing the user sees when they open the
; manual!  We localize this because you may want to write your own top topics
; for custom manuals.

 (include-book "top-topic"))

(comp t)

(local (deflabel doc-rebuild-label))

(make-event
 (b* ((state (serialize-write "xdoc.sao"
                              (xdoc::get-xdoc-table (w state))
                              :verbosep t)))
   (value '(value-triple "xdoc.sao"))))


; Once upon a time we had a an out-of-control macro generating automatic docs
; that included every event in the world(!).  To make this sort of problem
; easier to spot, we now print out a brief listing of the longest topics.

#!XDOC
(defun find-long-topics (all-topics)
  (if (atom all-topics)
      nil
    (cons (cons (length (cdr (assoc :long (car all-topics))))
                (cdr (assoc :name (car all-topics))))
          (find-long-topics (cdr all-topics)))))

#!XDOC
(value-triple
 (b* ((lengths->names (find-long-topics (get-xdoc-table (w state)))))
   (cw "Longest topics listing (length . name):~%~x0~%"
       (take 30 (reverse (mergesort lengths->names))))))

; GC so the fork for the zip call of xdoc::save has a smaller chance of running
; out of memory.
(value-triple (hons-clear t))

(value-triple
 (progn$ (cw "--- Writing ACL2+Books Manual ----------------------------------~%")
         :invisible))

(make-event
; xdoc::save is an event, so we might have just called it directly.  But for
; reasons Jared doesn't understand this is screwing up the extended manual we
; build at Centaur.  So, I'm putting the save event into a make-event to try
; to localize its effects to just this book's certification.
 (er-progn (xdoc::save "./manual"
                       ;; Allow redefinition so that we don't have to get
                       ;; everything perfect (until it's release time)
                       :redef-okp t
                       :logo-image "./acl2-big.png"
                       :error t
                       :broken-links-limit 1)
           (value `(value-triple :manual))))

(value-triple
 (progn$ (cw "--- Done Writing ACL2+Books Manual -----------------------------~%")
         :invisible))

(local
 (defmacro doc-rebuild ()

; It is sometimes useful to make tweaks to the documentation and then quickly
; be able to see your changes.  This macro can be used to do this, as follows:
;
; SETUP:
;
;  (ld "top.lisp")  ;; slow, takes a few minutes to get all the books loaded
;
; DEVELOPMENT LOOP: {
;
;   1. make documentation changes in new-doc.lsp; e.g., you can add new topics
;      there with defxdoc, or use commands like change-parents, etc.
;
;   2. type (doc-rebuild) to rebuild the manual with your changes; this only
;      takes 20-30 seconds
;
;   3. view your changes, make further edits
;
; }
;
; Finally, move your changes out of new-doc.lsp and integrate them properly
; into the other sources, and do a proper build.

   `(er-progn
     (ubt! 'doc-rebuild-label)
     (ld ;; newline to fool dependency scanner
      "new-doc.lsp")
     (xdoc::save "./manual"
                 :redef-okp t
                 :zip-p nil
                 :logo-image "./acl2-big.png"
                 :error t)
     (value `(value-triple :manual)))))


#||

(redef-errors (get-xdoc-table (w state)))

(defun collect-topics-with-name (name topics)
  (if (atom topics)
      nil
    (if (equal (cdr (assoc :name (car topics))) name)
        (cons (Car topics) (collect-topics-with-name name (Cdr topics)))
      (collect-topics-with-name name (Cdr topics)))))

(b* (((list a b) (collect-topics-with-name 'oslib::lisp-type (get-xdoc-table (w state)))))
  (equal a b))

(b* (((list a b) (collect-topics-with-name 'acl2::ADD-LISTFIX-RULE (get-xdoc-table (w state)))))
  (equal a b))



(defun map-topic-names (x)
  (if (atom x)
      nil
    (cons (cdr (assoc :name (car x)))
          (map-topic-names (cdr x)))))

(map-topic-names (get-xdoc-table (w state)))


(b* (((list a b) (collect-topics-with-name 'oslib::lisp-type (get-xdoc-table (w state)))))
  (equal a b))



(collect-topics-with-name 'acl2::add-listfix-rule (get-xdoc-table (w state)))
||#

; Support for the Emacs-based Manual

(defconsts (& *acl2_doc_generate_supporting_files* state)
  (getenv$ "ACL2_DOC_GENERATE_SUPPORTING_FILES" state))

(make-event
  (if (or (null *acl2_doc_generate_supporting_files*)
          (member-string-equal *acl2_doc_generate_supporting_files*
                               '("" "SKIP")))
      '(value-triple :SKIP-ACL2_DOC_GENERATE_SUPPORTING_FILES)
    ;; else build the supporting files for acl2-doc
    '(progn

; Historically this was part of system/doc/render-doc-combined.lisp.  However,
; that file ended up being quite expensive and in the critical path.  Most of
; the expense was that it just had to include-book doc/top.lisp, which takes
; a lot of time because of how many books are included.
;
; So now, instead, to improve performance, we just merge the export of the
; text-based manual into doc/top.lisp.

       (include-book "system/doc/render-doc-base" :dir :system)

       (include-book "xdoc/save-rendered" :dir :system)

       (defconst *rendered-doc-combined-header*
         "; Documentation for acl2+books
; WARNING: GENERATED FILE, DO NOT HAND EDIT!
; The contents of this file are derived from the full acl2+books
; documentation.  For license and copyright information, see community book
; xdoc/fancy/LICENSE.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.
")

       (encapsulate
           ()
         (defttag :save-rendered-event)

         (defconsts (& *tags-acl2-doc* state) (getenv$ "TAGS_ACL2_DOC" state))

         (xdoc::save-rendered-event
           (extend-pathname (cbd)
                            "../system/doc/rendered-doc-combined.lsp"
                            state)
           *rendered-doc-combined-header*
           '*acl2+books-documentation*
           t ; error if there is any xdoc-error
           :timep t
           :write-acl2-doc-search-file t

; The following assumes that the community books are in the books/ subdirectory
; of the local ACL2 distribution.  We use the same environment variable,
; TAGS_ACL2_DOC, as is used in the ACL2 top-level GNUmakefile to determine
; whether or not to build tags table TAGS-acl2-doc.  However, by default, here
; want to build TAGS-acl2-doc.  So rather than checking that the environment
; variable value is neither undefined (which it will be for most users) nor the
; empty string, here we check against a special value, SKIP.  So for example,
; the build server can set TAGS_ACL2_DOC to SKIP in order to avoid building
; TAGS-acl2-doc, an operation that apparently (as of June 2017) can cause an
; out-of-memory-error.

; If we find that users complain about out-of-memory errors here, we could test
; below against the empty string (or nil) instead, and users who want
; TAGS-acl2-doc could explicitly set TAGS_ACL2_DOC if they want the tags table.

           :script-file
           (and (not (equal *tags-acl2-doc* "SKIP")) ; e.g., for build server
                (extend-pathname (cbd)
                                 "../../bin/make-tags-acl2-doc.sh"
                                 state)) )
         ) ; end encapsulate
       ) ; end progn
    ) ; end if
  ) ; end make-event

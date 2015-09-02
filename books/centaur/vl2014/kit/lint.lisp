; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "../loader/top")
(include-book "../lint/lucid")
(include-book "../lint/check-case")
(include-book "../lint/check-namespace")
(include-book "../mlib/hierarchy")

(include-book "../lint/drop-missing-submodules")
(include-book "../lint/drop-user-submodules")
(include-book "../lint/lint-stmt-rewrite")
(include-book "../lint/remove-toohard")
(include-book "../lint/suppress-warnings")
(include-book "../lint/condcheck")
(include-book "../lint/duplicate-detect")
(include-book "../lint/dupeinst-check")
(include-book "../lint/duperhs")
(include-book "../lint/leftright")
(include-book "../lint/oddexpr")
(include-book "../lint/portcheck")
(include-book "../lint/qmarksize-check")
(include-book "../lint/selfassigns")
(include-book "../lint/skip-detect")

(include-book "../transforms/cn-hooks")
(include-book "../transforms/unparam/top")
(include-book "../transforms/annotate/argresolve")
(include-book "../transforms/annotate/resolve-indexing")
(include-book "../transforms/annotate/origexprs")
(include-book "../transforms/annotate/make-implicit-wires")
(include-book "../transforms/annotate/portdecl-sign")
(include-book "../transforms/annotate/udp-elim")

(include-book "../transforms/assign-trunc")
(include-book "../transforms/blankargs")
(include-book "../transforms/clean-params")
(include-book "../transforms/clean-warnings")
(include-book "../transforms/drop-blankports")
(include-book "../transforms/expr-split")
(include-book "../transforms/expand-functions")
(include-book "../transforms/oprewrite")
(include-book "../transforms/resolve-ranges")
(include-book "../transforms/replicate-insts")
(include-book "../transforms/selresolve")
(include-book "../transforms/sizing")
(include-book "../transforms/unused-vars")

(include-book "../../misc/sneaky-load")

(include-book "../mlib/json")

(include-book "centaur/getopt/top" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "progutils")

(local (include-book "../mlib/modname-sets"))
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (non-parallel-book))

(defsection lint
  :parents (vl2014)
  :short "A linting tool for Verilog and SystemVerilog."

  :long "<p>A <a
href='http://en.wikipedia.org/wiki/Lint_%28software%29'>linter</a> is a tool
that looks for possible bugs in a program.  We have used @(see VL2014) to
implement a linter for Verilog and SystemVerilog designs.  It can scan your
Verilog designs for potential bugs like size mismatches, unused wires, etc.</p>

<p>Note: Most of the documentation here is about the implementation of various
linter checks.  If you just want to run the linter on your own Verilog designs,
you should see the VL @(see kit).  After building the kit, you should be able
to run, e.g., @('vl lint --help') to see the @(see *vl-lint-help*)
message.</p>")

(defoptions vl-lintconfig
  :parents (lint)
  :short "Command-line options for running @('vl lint')."
  :tag :vl-lint-opts

  ((start-files string-listp
                "The list of files to process."
                :hide t)

   (help        booleanp
                "Show a brief usage message and exit."
                :rule-classes :type-prescription
                :alias #\h)

   (readme      booleanp
                "Show a more elaborate README and exit."
                :rule-classes :type-prescription)

   (search-path string-listp
                :longname "search"
                :alias #\s
                :argname "DIR"
                "Control the search path for finding modules.  You can give
                 this switch multiple times, to set up multiple search paths in
                 priority order."
                :parser getopt::parse-string
                :merge acl2::rcons)

   (search-exts string-listp
                :longname "searchext"
                :argname "EXT"
                "Control the search extensions for finding modules.  You can
                 give this switch multiple times.  By default we just look for
                 files named \"foo.v\" in the --search directories.  But if you
                 have Verilog files with different extensions, this won't work,
                 so you can add these extensions here.  EXT should not include
                 the period, e.g., use \"--searchext vv\" to consider files
                 like \"foo.vv\", etc."
                :parser getopt::parse-string
                :merge acl2::rcons
                :default '("v"))

   (include-dirs string-listp
                 :longname "incdir"
                 :alias #\I
                 :argname "DIR"
                 "Control the list of directories for `include files.  You can
                  give this switch multiple times.  By default, we look only in
                  the current directory."
                 :parser getopt::parse-string
                 :merge acl2::rcons
                 :default '("."))

   (topmods    string-listp
               :longname "topmod"
               :argname "MOD"
               "Limit the scope of the report to MOD.  By default we include
                all warnings for any module we encounter.  But if you say
                \"--topmod foo\", we suppress all warnings for modules that foo
                does not depend on.  You can give this switch multiple times,
                e.g., \"--topmod foo --topmod bar\" means: only show warnings
                for foo, bar, and modules that they depend on."
               :parser getopt::parse-string
               :merge cons)

   (quiet      string-listp
               :alias #\q
               :argname "MOD"
               "Suppress all warnings that about MOD.  You can give this switch
                multiple times, e.g., \"-q foo -q bar\" will hide the warnings
                about modules foo and bar."
               :parser getopt::parse-string
               :merge cons)

   (dropmods   string-listp
               :longname "drop"
               :alias #\d
               :argname "MOD"
               "Delete MOD from the module hierarchy before doing any linting
                at all.  This is a gross (but effective) way to work through
                any bugs in the linter that are triggered by certain modules.
                The dropped modules are removed from the module list without
                destroying modules above them.  This may occasionally lead to
                false warnings about the modules above (e.g., it may think some
                wires are unused, because the module that uses them has been
                removed.)"
               :parser getopt::parse-string
               :merge cons)

   (ignore     string-listp
               :alias #\i
               :argname "TYPE"
               "Ignore warnings of this TYPE.  For instance, \"--ignore
                oddexpr\" will suppress VL_WARN_ODDEXPR warnings.  Note that
                there are much finer-grained ways to suppress warnings; see
                \"vl lint --readme\" for more information."
                :parser getopt::parse-string
                :merge cons)

   (cclimit     natp
                :argname "N"
                "Limit for the const check.  This is a beta feature that is not
                 yet released.  Setting N to 0 (the default) disables the
                 check.  Otherwise, limit the scope of the check to at most N
                 sub-expressions."
                :default 0)

   (edition     vl-edition-p
                :argname "EDITION"
                "Which edition of the Verilog standard to implement?
                 Default: \"SystemVerilog\" (IEEE 1800-2012).  You can
                 alternately use \"Verilog\" for IEEE 1364-2005, i.e.,
                 Verilog-2005."
                :default :system-verilog-2012)

   (strict      booleanp
                :rule-classes :type-prescription
                "Disable VL extensions to Verilog.")

   (mem         posp
                :alias #\m
                :argname "GB"
                "How much memory to try to use.  Default: 4 GB.  Raising this
                 may improve performance by avoiding garbage collection.  To
                 avoid swapping, keep this below (physical_memory - 2 GB)."
                :default 4
                :rule-classes :type-prescription)

   (debug       booleanp
                "Print extra information for debugging."
                :rule-classes :type-prescription)))

(defval *vl-lint-help*
  :parents (lint)
  :short "Usage message for vl lint."
  :showdef nil
  :showval t

  (str::cat "
vl lint:  A linting tool for Verilog.  Scans your Verilog files for things
          that look like bugs (size mismatches, unused wires, etc.)

Example:  vl lint engine.v wrapper.v core.v \\
            --search ./simlibs \\
            --search ./baselibs

Usage:    vl lint [OPTIONS] file.v [file2.v ...]

Options:" *nls* *nls* *vl-lintconfig-usage* *nls*))


;; (define vl-filter-mods-with-good-paramdecls
;;   ((x    vl-modulelist-p "List of modules to filter.")
;;    (good vl-modulelist-p "Accumulator for good modules.")
;;    (bad  vl-modulelist-p "Accumulator for bad modules."))
;;   :returns (mv (good vl-modulelist-p :hyp :fguard)
;;                (bad  vl-modulelist-p :hyp :fguard))
;;   :parents (lint)
;;   :short "(unsound transform) Throw away modules with too-complex parameter
;; declarations. "

;;   :long "<p>@(csee unparameterization) requires that the module list is
;; complete and that all modules have good parameters.  In our ordinary
;; translation process (e.g., @(see vl-simplify)), we throw away any modules with
;; bad parameters, any then transitively throw away any modules with instances of
;; missing modules.  But for linting, we'd like to try to carry out
;; unparameterization with as little damage as possible.</p>

;; <p>As a pre-unparameterization step, in this transform we throw away any
;; modules with bad parameters and then throw away any instances of missing
;; modules.  This is obviously unsound, so it should never be used in our ordinary
;; translation process.</p>"

;;   (cond ((atom x)
;;          (mv good bad))
;;         ((vl-good-paramdecllist-p (vl-module->paramdecls (car x)))
;;          (vl-filter-mods-with-good-paramdecls (cdr x)
;;                                               (cons (car x) good)
;;                                               bad))
;;         (t
;;          (vl-filter-mods-with-good-paramdecls (cdr x)
;;                                               good
;;                                               (cons (car x) bad)))))


(define vl-print-certain-warnings
  ((mods vl-modulelist-p "Modules to print warnings for.")
   (show symbol-listp    "Types of warnings to show.")
   (hide symbol-listp    "Types of warnings to hide."))
  :parents (lint)
  :short "Print warnings of interest to standard output, while hiding other
warnings."

  :long "<p>You can use this to print just a few warnings you are interested in
while hiding other warnings you know you are not interested in.  If there are
warnings of other types (that you haven't said to show or hide), they too will
be hidden but you'll at least get a message saying that they aren't being
shown.</p>"

  (b* ((warnings (vl-modulelist-flat-warnings-exec mods nil))
       (types    (mergesort (vl-warninglist->types-exec warnings nil)))
       (hide     (if hide
                     (mergesort hide)
                   types))
       (show     (mergesort show))
       ;; Misc is all the warning types that we aren't told to show, but aren't
       ;; told to ignore.  We'll print a note that these warnings exist but
       ;; that we weren't told to show or hide them.
       (misc     (difference types (union show hide)))
       (warnings (vl-keep-warnings show warnings)))
    (vl-cw-ps-seq
     (vl-ps-update-autowrap-col 65)
     (vl-print-warnings warnings)
     (vl-println "")
     (if (not misc)
         ps
       (vl-ps-seq
        (vl-cw "Note: not showing ~&0 warnings.~%" misc)
        (vl-println ""))))))


(defaggregate vl-lintresult
  :parents (lint)
  :short "Results from running the linter."
  :tag :vl-lintresult
  ((design    vl-design-p
              "Final, transformed list of modules.  Typically this isn't very
               interesting or relevant to anything.")

   (design0   vl-design-p
              "Almost: the initial, pre-transformed modules.  The only twist is
               that we have already removed modules that are unnecessary or
               that we wanted to drop; see, e.g., the @('topmods') and
               @('ignore') options of @(see vl-lintconfig-p).  This is used for
               @(see skip-detection), for instance.")

   (reportcard vl-reportcard-p
               "The main result: binds \"original\" (pre-unparameterization)
                module names to their warnings.")

   (sd-probs  sd-problemlist-p
              "Possible problems noticed by @(see skip-detection).  These are
               in a different format than ordinary @(see warnings), so they
               aren't included in the @('reportcard').")))


(define vl-delete-sd-problems-for-modnames-aux
  ((fal "Fast alist binding names to T or whatever")
   (x   sd-problemlist-p))
  :returns (new-x sd-problemlist-p :hyp :fguard)
  (b* (((when (atom x))
        nil)
       ((sd-problem x1) (car x))
       ((vl-context1 x1.ctx) x1.ctx)
       ((when (hons-get x1.ctx.mod fal))
        (vl-delete-sd-problems-for-modnames-aux fal (cdr x))))
    (cons (car x)
          (vl-delete-sd-problems-for-modnames-aux fal (cdr x)))))

(define vl-delete-sd-problems-for-modnames ((names string-listp)
                                            (probs sd-problemlist-p))
  :returns (new-x sd-problemlist-p
                  :hyp (force (sd-problemlist-p probs)))
  (b* ((fal (make-lookup-alist names))
       (ret (vl-delete-sd-problems-for-modnames-aux fal probs)))
    (fast-alist-free fal)
    ret))


(local (defthm no-duplicatesp-when-setp
         (implies (setp x)
                  (no-duplicatesp x))))

(local (defthm VL-MODULELIST-P-OF-APPEND-fast
         (implies (and (force (vl-modulelist-p x))
                       (force (vl-modulelist-p y)))
                  (vl-modulelist-p (append x y)))))

(local (in-theory (disable
                   NO-DUPLICATESP-EQUAL-WHEN-SAME-LENGTH-MERGESORT
                   SUBSETP-OF-VL-MODINSTLIST->MODNAMES-WHEN-SUBSETP
                   CDR-OF-VL-MODULELIST-DUPERHS-CHECK
                   CDR-OF-VL-MODULELIST-ORIGEXPRS
                   vl-modulelist-p-of-append
                   NO-DUPLICATESP-EQUAL-OF-APPEND
                   acl2::no-duplicatesp-equal-append-iff
                   mergesort)))

(define vl-design-remove-unnecessary-modules ((keep string-listp)
                                              (design vl-design-p))
  :returns (new-design vl-design-p)
  (b* ((design (vl-design-fix design))
       (keep   (mergesort (string-list-fix keep)))
       ((unless keep)
        ;; Special feature: if the user didn't specify any top modules,
        ;; then we want to keep everything.
        design))
    (vl-remove-unnecessary-elements keep design)))

;; (define vl-lint-unparam ((good vl-design-p))
;;   :returns (good vl-design-p)
;;   (b* ((good (vl-design-fix good))

;;        ;; Subtle thing.  Move any bad modules out of the way before doing
;;        ;; unparameterization.
;;        ((mv ok-mods bad-mods)
;;         (vl-filter-mods-with-good-paramdecls (vl-design->mods good) nil nil))

;;        (- (or (not bad-mods)
;;               (progn$
;;                (cw "~%~%Note: deleting ~x0 module~s1 because they include ~
;;                     unsupported parameter declarations.~%~%~
;;                     Module~s1 being deleted: ~&2~%~%~
;;                     Details:~%~%"
;;                    (len bad-mods)
;;                    (if (vl-plural-p bad-mods) "s" "")
;;                    (mergesort (vl-modulelist->names bad-mods)))
;;                (vl-print-certain-warnings bad-mods
;;                                           (list :vl-bad-paramdecl
;;                                                 :vl-bad-paramdecls)
;;                                           nil))))

;;        (good (change-vl-design good :mods ok-mods))
;;        (good (cwtime (vl-design-drop-missing-submodules good)))
;;        (good (vl-design-unparameterize good))
;;        (good (change-vl-design good :mods (append-without-guard
;;                                            bad-mods (vl-design->mods good)))))
;;     (or (uniquep (vl-modulelist->names (vl-design->mods good)))
;;         (raise "Programming error.  Expected modules to have unique names ~
;;                 after vl-unparameterize, but found duplicate modules named ~
;;                 ~x0.  Please tell Jared."
;;                (duplicated-members (vl-modulelist->names (vl-design->mods good)))))
;;     good))

(define vl-lint-apply-quiet ((quiet string-listp)
                             (design vl-design-p))
  :returns (new-design vl-design-p)
  (b* ((design (vl-design-fix design))
       (mods   (vl-design->mods design))
       (mods   (vl-delete-modules quiet mods)))
    (change-vl-design design :mods mods)))

(define run-vl-lint-main ((design vl-design-p)
                          (config vl-lintconfig-p))
  :guard-debug t
  :returns (result vl-lintresult-p :hyp :fguard)

  (b* (((vl-lintconfig config) config)
       (design (cwtime (vl-design-drop-user-submodules design config.dropmods)))

       ;; You might expect that we'd immediately throw out modules that we
       ;; don't need for topmods.  Historically we did that.  But then we found
       ;; that we'd get a bunch of complaints in other modules about
       ;; hierarchical identifiers that pointed into the modules we'd just
       ;; thrown away!  So now we deal with this stuff after HID resolution.
       ;; Except that for skip-detection, we also need to remove them from
       ;; mods0, so do that now:
       (design0 (vl-design-remove-unnecessary-modules config.topmods design))

       (- (cw "~%vl-lint: initial processing...~%"))
       (design (cwtime (vl-design-make-implicit-wires design)))
       (design (cwtime (vl-design-portdecl-sign design)))
       (design (cwtime (vl-design-udp-elim design)))
       (design (cwtime (vl-design-portcheck design)))
       (design (cwtime (vl-design-argresolve design)))
       (design (cwtime (vl-design-resolve-indexing design)))

       ;; Pre-unparameterization Lucidity Check.
       (design (cwtime (vl-design-lucid design
                                        ;; This is a good time to check parameter uses
                                        :paramsp t
                                        ;; This is a bad time to check generates
                                        :generatesp nil)))

       (- (cw "~%vl-lint: starting general checks...~%"))
       (design (cwtime (vl-design-check-namespace design)))
       (design (cwtime (vl-design-check-case design)))
       (design (cwtime (vl-design-duperhs-check design)))
       (design (cwtime (vl-design-duplicate-detect design)))
       (design (cwtime (vl-design-condcheck design)))
       (design (cwtime (vl-design-leftright-check design)))
       (design (cwtime (vl-design-origexprs design)))
       (design (cwtime (vl-design-dupeinst-check design)))

       (- (cw "~%vl-lint: elaborating the design...~%"))

       ;; BOZO we need to do something to throw away instances with unresolved
       ;; arguments to avoid programming-errors in drop-blankports... and actually
       ;; we hit errors like that later, too.
       ;; (design (cwtime (vl-design-drop-blankports design)))
       ;;(design (cwtime (vl-design-follow-hids design)))
       ;; (design (cwtime (vl-design-clean-params design)))
       ;; (design (cwtime (vl-design-check-good-paramdecls design)))
       (design (cwtime (vl-design-unparameterize design)))
       (design (cwtime (vl-design-rangeresolve design)))
       (design (cwtime (vl-design-selresolve design)))

       (design
        ;; Running another dupeinst check here, after unparameterization, may
        ;; create redundant warnings, but it may also help to catch things that
        ;; become duplicates after unparameterization.
        (cwtime (vl-design-dupeinst-check design)))

       ;; Post-unparameterization Lucidity Check -- this is a bad time for
       ;; checking parameters (because they've been eliminated) but it's a
       ;; much better time to do bit-level analysis, because things like
       ;; foo[width-1:0] should hopefully be resolved now.  Also we can
       ;; sensibly check generates now.
       (design (cwtime (vl-design-lucid design
                                        :paramsp nil
                                        :generatesp t)))

       (design
        ;; Best not to do this until after lucid checking.
        (cwtime (vl-design-drop-missing-submodules design)))

       ;; BOZO do we even need to do this?
       ;; BOZO not exactly sure where this should go, maybe this will work.


       ;; (design
       ;;  ;; Bug fixed 2014-12-19: don't do this until after argresolve, because
       ;;  ;; in SystemVerilog it can get confused by .* or .foo style port
       ;;  ;; connections.  Also it's best not to do this until after lucid
       ;;  ;; checking because it would screw up lucid's checks.  Actually why
       ;;  ;; are we even doing this?
       ;;  (cwtime (vl-design-elim-unused-vars design)))

       (design (cwtime (vl-design-check-selfassigns design)))
       (design (cwtime (vl-design-lint-stmt-rewrite design)))
       (design (cwtime (vl-design-stmtrewrite design 1000)))
       ;;(design (cwtime (vl-design-hid-elim design)))

       ;; Now that HIDs are gone, we can throw away any modules we don't care
       ;; about, if we have been given any topmods.
       (design (b* ((names1 (vl-modulelist->names (vl-design->mods design)))
                    (design (vl-design-drop-missing-submodules design))
                    (names2 (vl-modulelist->names (vl-design->mods design)))
                    (lost   (difference (mergesort names1) (mergesort names2))))
                 (or (not lost)
                     (cw "BOZO lost ~x0 modules somewhere (probably unparameterizing): ~x1~%"
                         (len lost) lost))
                 design))

       (design (cwtime (vl-design-remove-unnecessary-modules config.topmods design)))

       (- (cw "~%vl-lint: processing expressions...~%"))
       (design (cwtime (vl-design-oddexpr-check design)))

       ;; [Jared] -- Trying to NOT do oprewrite anymore.  Our sizing warnings
       ;; do better if we can tell the difference between == and ~^ operators,
       ;; for instance.
       ;; (design (cwtime (vl-design-oprewrite design)))


       ;; Sizing doesn't do well unless we expand functions
       (design (cwtime (vl-design-expand-functions design)))
       (design (cwtime (vl-design-exprsize design)))
       (design (cwtime (vl-design-constcheck-hook design config.cclimit)))
       (design (cwtime (vl-design-qmarksize-check design)))

       (- (cw "~%vl-lint: processing assignments...~%"))
       (design (cwtime (vl-design-split design)))
       (design (cwtime (vl-design-replicate design)))
       (design (cwtime (vl-design-blankargs design)))
       (design (cwtime (vl-design-trunc design)))

       (- (cw "~%vl-lint: finding skipped and multiply driven wires...~%"))
       ;; NOTE: use design0, not design, if you ever want this to finish. :)
       (sd-probs (cwtime (sd-analyze-design design0)))

       (- (cw "~%vl-lint: cleaning up...~%"))
       (design   (cwtime (vl-design-clean-warnings design)))
       (design   (cwtime (vl-design-suppress-lint-warnings design)))
       (design   (cwtime (vl-design-lint-ignoreall design config.ignore)))
       (design   (cwtime (vl-lint-apply-quiet config.quiet design)))
       (sd-probs (cwtime (vl-delete-sd-problems-for-modnames config.quiet sd-probs)))
       (reportcard  (cwtime (vl-design-origname-reportcard design))))

    (make-vl-lintresult :design design
                        :design0 design0
                        :reportcard reportcard
                        :sd-probs sd-probs
                        )))

(define run-vl-lint ((config vl-lintconfig-p) &key (state 'state))
  :returns (mv (res vl-lintresult-p :hyp :fguard)
               (state state-p1 :hyp (state-p1 state)))
  (b* ((- (cw "Starting VL-Lint~%"))
       ((vl-lintconfig config) config)
       (- (or (not config.debug)
              (cw "Lint configuration: ~x0~%" config)))

       (loadconfig (make-vl-loadconfig
                    :edition       config.edition
                    :strictp       config.strict
                    :start-files   config.start-files
                    :search-path   config.search-path
                    :search-exts   config.search-exts
                    :include-dirs  config.include-dirs))
       (- (or (not config.debug)
              (cw "Load configuration: ~x0~%" loadconfig)))

       (- (cw "~%vl-lint: loading modules...~%"))
       ((mv loadres state) (cwtime (vl-load loadconfig)))

       (lintres
        (cwtime (run-vl-lint-main (vl-loadresult->design loadres)
                                  config))))
    (mv lintres state)))


(define sd-problem-major-p ((x sd-problem-p))
  (b* (((sd-problem x) x))
    (or (>= x.priority 10)
        (and (>= x.priority 6) (>= x.groupsize 4))
        (>= (sd-problem-score x) 8))))

(define sd-filter-problems ((x     sd-problemlist-p)
                            (major sd-problemlist-p)
                            (minor sd-problemlist-p))
  :returns (mv (major sd-problemlist-p :hyp :fguard)
               (minor sd-problemlist-p :hyp :fguard))
  (cond ((atom x)
         (mv major minor))
        ((sd-problem-major-p (car x))
         (sd-filter-problems (cdr x) (cons (car x) major) minor))
        (t
         (sd-filter-problems (cdr x) major (cons (car x) minor))))
  ///
  (defthm true-listp-sd-filter-problems
    (and (implies (true-listp major)
                  (true-listp (mv-nth 0 (sd-filter-problems x major minor))))
         (implies (true-listp minor)
                  (true-listp (mv-nth 1 (sd-filter-problems x major minor)))))))


(define vl-lint-print-warnings ((filename stringp)
                                (label    stringp)
                                (types    symbol-listp)
                                (reportcard   vl-reportcard-p)
                                &key (ps 'ps))
  (b* ((reportcard (vl-keep-from-reportcard types reportcard))
       (reportcard (vl-clean-reportcard reportcard))
       (count  (length (append-alist-vals reportcard)))
       (-      (cond ((eql count 0)
                      (cw "~s0: No ~s1 Warnings.~%" filename label))
                     ((eql count 1)
                      (cw "~s0: One ~s1 Warning.~%" filename label))
                     (t
                      (cw "~s0: ~x1 ~s2 Warnings.~%" filename count label)))))
    (vl-ps-seq
     (cond ((eql count 0)
            (vl-cw "No ~s0 Warnings.~%~%" label))
           ((eql count 1)
            (vl-cw "One ~s0 Warning:~%~%" label))
           (t
            (vl-cw "~x0 ~s1 Warnings:~%~%" count label)))
     (vl-print-reportcard reportcard :elide nil))))

(define vl-jp-reportcard-aux ((x vl-reportcard-p) &key (ps 'ps))
  (b* (((when (atom x))
        ps)
       ((cons modname warnings) (car x))
       (modname (if (eq modname :design)
                    "Design Root"
                  modname)))
    (vl-ps-seq (vl-indent 1)
               (jp-str modname)
               (vl-print ":")
               (vl-jp-warninglist warnings)
               (if (atom (cdr x))
                   ps
                 (vl-println ","))
               (vl-jp-reportcard-aux (cdr x))))
  :prepwork
  ((local (defthm l0
            (implies (and (vl-reportcardkey-p x)
                          (not (equal x :design)))
                     (stringp x))
            :hints(("Goal" :in-theory (enable vl-reportcardkey-p)))))))

(define vl-jp-reportcard ((x vl-reportcard-p) &key (ps 'ps))
  (vl-ps-seq (vl-print "{")
             (vl-jp-reportcard-aux x)
             (vl-println "}")))

(define vl-remove-nameless-descriptions ((x vl-descriptionlist-p))
  :returns (new-x vl-descriptionlist-p)
  (cond ((atom x)
         nil)
        ((not (vl-description->name (car x)))
         (vl-remove-nameless-descriptions (cdr x)))
        (t
         (cons (vl-description-fix (car x))
               (vl-remove-nameless-descriptions (cdr x))))))

(define vl-jp-description-locations ((x vl-descriptionlist-p) &key (ps 'ps))
  (b* (((when (atom x))
        ps)
       (name (or (vl-description->name (car x))
                 (raise "Shouldn't have nameless descriptions here but got ~x0" (car x))
                 ""))
       (loc  (vl-description->minloc (car x))))
    (vl-ps-seq (vl-indent 1)
               (jp-str name)
               (vl-print ":")
               (jp-str (vl-location-string loc))
               (if (atom (cdr x))
                   ps
                 (vl-println ", "))
               (vl-jp-description-locations (cdr x)))))

(define vl-jp-locations ((x vl-design-p) &key (ps 'ps))
  (vl-ps-seq (vl-print "{")
             (vl-jp-description-locations
              (vl-remove-nameless-descriptions
               (vl-design-descriptions x)))
             (vl-println "}")))

(defconst *basic-warnings*
  (list :bad-mp-verror
        :vl-bad-range
        :vl-warn-duplicates
        :vl-bad-instance
        :vl-unresolved-hid
        :vl-warn-unused-var
        :vl-warn-blank
        :vl-undefined-names
        :vl-port-mismatch))

(defconst *trunc-warnings*
  (list :vl-warn-extension
        :vl-warn-truncation
        :vl-warn-integer-size))

(defconst *trunc-minor-warnings*
  (list :vl-warn-extension-minor
        :vl-warn-truncation-minor
        :vl-warn-integer-size-minor
        :vl-warn-vague-spec))

(defconst *smell-warnings*
  (list :vl-warn-qmark-width
        :vl-warn-qmark-const
        :vl-warn-leftright
        :vl-warn-selfassign
        :vl-warn-instances-same
        :vl-warn-case-sensitive-names
        :vl-warn-same-rhs
        :vl-const-expr))

(defconst *smell-minor-warnings*
  (list :vl-warn-partselect-same
        :vl-warn-instances-same-minor
        :vl-const-expr-minor))

(defconst *fussy-size-warnings*
  (list :vl-fussy-size-warning-1
        :vl-fussy-size-warning-2
        :vl-fussy-size-warning-3
        :vl-fussy-size-warning-1-const-toobig
        :vl-fussy-size-warning-2-const-toobig
        :vl-fussy-size-warning-3-const-toobig
        :vl-fussy-size-warning-1-complex
        :vl-fussy-size-warning-2-complex
        :vl-fussy-size-warning-3-complex
        ))

(defconst *same-ports-warnings*
  (list :vl-warn-same-ports
        :vl-warn-same-inputs))

(defconst *same-ports-minor-warnings*
  (list :vl-warn-same-ports-minor
        :vl-warn-same-inputs-minor))

(defconst *fussy-size-minor-warnings*
  (list :vl-fussy-size-warning-1-minor
        :vl-fussy-size-warning-2-minor
        :vl-fussy-size-warning-3-minor))

(defconst *lucid-warnings*
  (list :vl-lucid-error
        :vl-lucid-unused
        :vl-lucid-spurious
        :vl-lucid-unset
        :vl-lucid-multidrive))



(defconst *warnings-covered*

  ;; Warnings that are covered by our regular reports.  Other warnings besides
  ;; these will get put into vl-other.txt

  (append *basic-warnings*
          *trunc-warnings*
          *trunc-minor-warnings*
          *smell-warnings*
          *smell-minor-warnings*
          *fussy-size-warnings*
          *fussy-size-minor-warnings*
          *same-ports-warnings*
          *same-ports-minor-warnings*
          *lucid-warnings*
          ))

(defconst *warnings-ignored*

  ;; Warnings that aren't covered but which we don't want to put into vl-other.txt
  ;; anyway.

  (list
   :vl-warn-taskdecl
   :vl-warn-function

   ))

(local (in-theory (disable set::in set::in-tail
                           set::difference set::mergesort)))

(defun vl-lint-report (lintresult state)
  (declare (xargs :guard (vl-lintresult-p lintresult)
                  :stobjs state))

  (b* (((vl-lintresult lintresult) lintresult)
       (reportcard   lintresult.reportcard)
       (sd-probs lintresult.sd-probs)

       ((mv major minor)
        (cwtime (sd-filter-problems sd-probs nil nil)))
       (major (reverse major))
       (minor (reverse minor))

       (- (cw "~%vl-lint: saving results...~%~%"))

       (othertypes  (difference (mergesort (vl-reportcard-types reportcard))
                                (mergesort (append *warnings-covered*
                                                   *warnings-ignored*))))

       (state
        (with-ps-file
         "vl-basic.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-basic.txt" "Basic" *basic-warnings* reportcard)))

       (state
        (with-ps-file
         "vl-trunc.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-print "
NOTE: see the bottom of this file for an explanation of what these warnings
mean and how to avoid them.

")

         (vl-lint-print-warnings "vl-trunc.txt" "Truncation/Extension" *trunc-warnings* reportcard)

         (vl-print "

UNDERSTANDING THESE WARNINGS.

1. VL-WARN-TRUNCATION warnings are issued when the left-hand side of an
assignment statement is not as wide as the right-hand side.

False positives here can typically be suppressed by using part-selects to make
the intended truncations explicit.  For instance:

    wire [47:0] foo ;
    wire [63:0] bar ;

    assign foo = bar ;        // implicit truncation, causes warning
    assign foo = bar[47:0] ;  // explicit truncation, no warning

    assign foo = condition ? bar : 0 ;      // implicit truncation, causes warning
    assign foo = condition ? bar[47:0] : 0; // explicit truncation, no warning


2. VL-WARN-EXTENSION warnings are the opposite: they are issued when the
left-hand side is wider than the right-hand side would have been on its own.

False-positives can again typically be suppressed by explicitly concatenting in
zeroes, or by using part-selects to cut the left-hand side to the right size.
For instance:

    wire [47:0] foo ;
    wire [63:0] bar ;

    assign bar = foo ;             // implicit extension, causes warning
    assign bar = { 16'b0, foo } ;  // explicit extension, no warning
    assign bar[47:0] = foo;        // no extension, no warning


Note that we consider certain truncation and extension warnings to be \"minor\"
and do not report them here.  Such warnings are unlikely to be a problem, but
you can see \"vl-trunc-minor.txt\" to review them.")))

       (state
        (with-ps-file
         "vl-fussy.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-fussy.txt" "Fussy Size Warnings" *fussy-size-warnings* reportcard)))

       (state
        (with-ps-file
         "vl-fussy-minor.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-fussy-minor.txt" "Minor Fussy Size Warnings" *fussy-size-minor-warnings* reportcard)))

       (state
        (with-ps-file
         "vl-lucid.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-lucid.txt" "Lucidity Checking" *lucid-warnings* reportcard)))

       (state
        (if (not major)
            (progn$
             (cw "; No Skip-Detect Warnings.~%")
             state)
          (progn$
           (cw "vl-skipdet.txt: ~x0 Skip-Detect Warnings.~%" (len major))
           (with-ps-file "vl-skipdet.txt"
                         (vl-ps-update-autowrap-col 68)
                         (vl-cw "Skip-Detect Warnings.~%~%")
                         (sd-pp-problemlist-long major)))))

       (state
        (with-ps-file
         "vl-trunc-minor.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-print "
NOTE: see the bottom of this file for an explanation of what these warnings
mean and how to avoid them.

")
         (vl-lint-print-warnings "vl-trunc-minor.txt" "Minor Truncation/Extension" *trunc-minor-warnings* reportcard)
         (vl-print "

UNDERSTANDING THESE WARNINGS.

1.  VL-WARN-TRUNCATION-32 warnings are generated for any assignments that are
being truncated and whose right-hand sides are 32-bits wide.  This is a minor
warning because it typically arises from assignments where plain integers are
involved, e.g., if foo and bar are 10 bits wide, then a truncation-32 warning
will be generated for:

    assign foo = bar ^ 5;

This is because \"5\" has an implementation-dependent width (of at least 32
bits), and in VL-Lint we treat it as being 32-bits wide.  So, the above
describes a 32-bit XOR that is then truncated down to 10 bits.  Fixing these
warnings is usually easy: just explicitly specify the sizes of the numbers
involved, e.g., a \"corrected\" version might be:

    assign foo = bar ^ 10'd 5;

This is generally a good idea since it avoids any implementation-dependent
sizing (which can occasionally affect the results of expressions).


2.  VL-WARN-EXTENSION-MINOR warnings are generated for any assignments where
the width of the left-hand side is used to size the expression, and where the
right-hand side involves only addition operations.  For instance, given:

    wire [9:0] foo;
    wire [9:0] bar;
    wire [9:0] sum;
    wire carry;

Then an assignment like this:

    assign { carry, sum } = foo + bar;

would result in a minor extension warning.  These warnings are typically quite
minor since you frequently want to get the carry out of a sum.  But you could
suppress them by writing something like this:

    Variant 1: assign {carry, sum} = {1'b0,foo} + bar;
    Variant 2: assign {carry, sum} = foo + bar + 11'b0;

or similar, to make explicit on the right-hand side that you want an 11-bit
wide addition instead of a 10-bit wide addition.")))

       (state
        (if (not minor)
            (prog2$
             (cw "; No Minor Skip-Detect Warnings.~%")
             state)
          (prog2$
           (cw "vl-skipdet-minor.txt: ~x0 Minor Skip-Detect Warnings.~%" (len minor))
           (with-ps-file "vl-skipdet-minor.txt"
                         (vl-ps-update-autowrap-col 68)
                         (vl-cw "Minor Skip-Detect Warnings.~%~%")
                         (sd-pp-problemlist-long minor)))))

       (state
        (with-ps-file
         "vl-smells.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-smells.txt" "Code-Smell Warnings" *smell-warnings* reportcard)))

       (state
        (with-ps-file
         "vl-smells-minor.txt"
         (vl-ps-update-autowrap-col 68)
         (vl-lint-print-warnings "vl-smells-minor.txt" "Minor Code-Smell Warnings" *smell-minor-warnings* reportcard)))


      (state
       (with-ps-file "vl-same-ports.txt"
                     (vl-ps-update-autowrap-col 68)
                     (vl-lint-print-warnings "vl-same-ports.txt"
                                             "Same-ports Warnings"
                                             *same-ports-warnings*
                                             reportcard)))
      (state
       (with-ps-file "vl-same-ports-minor.txt"
                     (vl-ps-update-autowrap-col 68)
                     (vl-lint-print-warnings "vl-same-ports-minor.txt"
                                             "Minor same-ports Warnings"
                                             *same-ports-minor-warnings*
                                             reportcard)))

      (state
       (with-ps-file
        "vl-other.txt"
        (vl-ps-update-autowrap-col 68)
        (vl-lint-print-warnings "vl-other.txt" "Other/Unclassified" othertypes reportcard)))

      (- (cw "~%"))

      (state
       (cwtime
        (with-ps-file "vl-warnings.json"
                      (vl-print "{\"warnings\":")
                      (vl-jp-reportcard reportcard)
                      (vl-print ",\"locations\":")
                      (vl-jp-locations lintresult.design0)
                      (vl-println "}"))
        :name write-warnings-json)))

    state))


(defconsts (*vl-lint-readme* state)
  (b* (((mv contents state) (acl2::read-file-characters "lint.readme" state))
       ((when (stringp contents))
        (raise contents)
        (mv "" state)))
    (mv (implode contents) state)))

(define vl-lint ((args string-listp) &key (state 'state))
  :parents (kit lint)
  :short "The @('vl lint') command."

  (b* (((mv errmsg config start-files)
        (parse-vl-lintconfig args))
       ((when errmsg)
        (die "~@0~%" errmsg)
        state)
       (config
        (change-vl-lintconfig config
                              :start-files start-files))
       ((vl-lintconfig config) config)

       (- (acl2::set-max-mem ;; newline to appease cert.pl
           (* (expt 2 30) config.mem)))

       ((when config.help)
        (vl-cw-ps-seq (vl-print *vl-lint-help*))
        (exit-ok)
        state)

       ((when config.readme)
        (vl-cw-ps-seq (vl-print *vl-lint-readme*))
        (exit-ok)
        state)

       (- (or (not config.debug)
              (vl-cw-ps-seq
               (vl-cw "Raw args: ~x0~%" args)
               (vl-cw "Start-files: ~x0~%" start-files))))

       ((unless (consp config.start-files))
        (die "No files to process.")
        state)

       (state (must-be-regular-files! config.start-files))
       (state (must-be-directories! config.search-path))
       (state (must-be-directories! config.include-dirs))

       ((mv result state)
        (cwtime (run-vl-lint config)
                :name vl-lint))
       (state
        (cwtime (vl-lint-report result state))))
    (exit-ok)
    state))


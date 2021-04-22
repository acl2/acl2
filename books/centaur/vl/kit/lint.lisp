; VL Verilog Toolkit
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

(in-package "VL")
(include-book "../loader/top")
(include-book "../lint/lucid")
(include-book "../lint/check-case")
(include-book "../lint/check-namespace")
(include-book "../mlib/hierarchy")
(include-book "../lint/alwaysstyle")
(include-book "../lint/drop-user-submodules")
(include-book "../lint/suppress-warnings")
(include-book "../lint/suppress-files")
(include-book "../lint/condcheck")
(include-book "../lint/duplicate-detect")
(include-book "../lint/dupeinst-check")
(include-book "../lint/duperhs")
(include-book "../lint/leftright")
(include-book "../lint/oddexpr")
(include-book "../lint/qmarksize-check")
(include-book "../lint/arith-compare")
(include-book "../lint/selfassigns")
(include-book "../lint/skip-detect")
(include-book "../lint/logicassign")
(include-book "../lint/check-globalparams")
(include-book "../lint/ifdef-report")
(include-book "../lint/unpacked-range")
(include-book "../transforms/cn-hooks")
(include-book "../transforms/unparam/top")
(include-book "../transforms/annotate/top")
(include-book "../transforms/addnames")
(include-book "../transforms/clean-warnings")
(include-book "../transforms/lintstub")
(include-book "centaur/sv/vl/moddb" :dir :system)
(include-book "centaur/sv/vl/use-set" :dir :system)
(include-book "../../misc/sneaky-load")
(include-book "../mlib/json")
(include-book "centaur/getopt/top" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "progutils")
(include-book "shell")
(local (include-book "xdoc/display" :dir :system))
(local (include-book "../mlib/modname-sets"))
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (non-parallel-book))
(local (in-theory (disable (:e tau-system))))

(defsection vl-lint
  :parents (kit)
  :short "A linting tool for Verilog and SystemVerilog."

  :long "<h3>Introduction</h3>

<p>A <a href='http://en.wikipedia.org/wiki/Lint_%28software%29'>linter</a> is a
tool that looks for possible bugs in a program.  We have used @(see VL) to
implement a linter for Verilog and SystemVerilog designs.  It can warn you
about things such as:</p>

<ul>
<li>Wires driven by multiple sources</li>
<li>Width mismatches in assignments and subexpressions</li>
<li>Strange expressions like @('a & a')</li>
<li>Duplicated module elements</li>
<li>Unused and unset wires and parts of wires</li>
<li>Possible confusion about operator precedence</li>
<li>Strange statements that sometimes indicate copy/paste errors</li>
</ul>

<h3>Running the Linter</h3>

<p>For detailed usage run @('vl lint --help') or see @(see *vl-lint-help*).</p>

<p>A typical invocation might look like this:</p>

@({
      vl lint my_mod1.v my_mod2.v \     <-- starting files to load
               -s libs/my_lib1 \        <-- search paths for finding
               -s libs/my_lib2               additional modules
})

<p>The linter will print some progress messages as it runs, then writes its
report in both <b>text</b> and <b>json</b> formats.</p>

<h5>Output Text Files</h5>

<p>The linter generally produces many warnings.  To try to filter this out and
make it easy to focus on the most important warnings, we split the output into
several files.  Here is a summary;</p>

<dl>
<dt>Generic warnings: (probably the most interesting)</dt>
<dd>vl-basic.txt - basic warnings</dd>

<dt>Size warnings: (often interesting)</dt>
<dd>vl-trunc.txt - truncations and extensions in assignments</dd>
<dd>vl-fussy.txt - size mismatches inside of expressions like @('a & b')</dd>
<dd>vl-trunc-minor.txt - unlikely to be problems</dd>
<dd>vl-fussy-minor.txt - unlikely to be problems</dd>

<dt>Code cleanup: (helpful when refactoring)</dt>
<dd>vl-lucid.txt - unused/undriven and multiply driven wires</dd>
<dd>vl-same-ports.txt - redundant submodule instances</dd>
<dd>vl-same-ports-minor.txt - unlikely to be problems</dd>

<dt>Code smells (sometimes interesting)</dt>
<dd>vl-smells.txt - weird expressions, duplicate rhs expressions</dd>

<dt>Skipped wire detection (only occasionally useful)</dt>
<dd>vl-skipdet.txt - high-scoring expressions, more likely to be problems</dd>
<dd>vl-skipdet-minor.txt - low-scoring expressions, unlikely to be problems</dd>

<dt>Other unclassified warnings</dt>
<dd>vl-other.txt - tool errors, misc garble</dd>
</dl>

<h5>Output JSON files</h5>

<p>All warnings produced by the linter are also put into @('vl-warnings.json').
This file is intended for use in scripts that process the linter's output, such
as lint warning emailers or similar.</p>


<h3>Suppressing False Positives</h3>

<p>You can tell the linter to ignore certain things by adding comments to your
Verilog source files.  For instance:</p>

@({
    //@VL LINT_IGNORE_TRUNCATION     // to suppress the truncation warning
    assign foo[3:0] = bar[5:0];

    //@VL LINT_IGNORE                // to suppress all warnings
    assign foo[3:0] = bar[5:0];
})

<p>This feature is probably fancier than anyone needs; see @(see
lint-warning-suppression) for details.</p>

<p>Note that there are also some command-line options to suppress all warnings
for particular modules, or all warnings of particular types, etc.  See @(see
*vl-lint-help*) for details.</p>")

(local (xdoc::set-default-parents vl-lint))

(defoptions vl-lintconfig
  :short "Command-line options for running @('vl lint')."
  :tag :vl-lint-opts

  ((start-files string-listp
                "The list of files to process."
                :hide t)

   (plusargs    string-listp
                "The list of +args, with plusses removed."
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

   (ignore-files string-listp
                 :longname "ignore-file"
                 :argname "FILENAME"
                 "Ignore warnings from modules in filename.  For instance,
                  \"--ignore-file foo.v\" will suppress all warnings from
                  modules in foo.v (from any directory).  You can also give
                  absolute paths, in which case only exact matches will be
                  suppressed.  Note that there are much finer-grained ways
                  to suppress warnings; see \"vl lint --readme\" for more
                  information."
                 :parser getopt::parse-string
                 :merge cons)

   (defines    string-listp
               :longname "define"
               :alias #\D
               :argname "VAR"
               "Set up definitions to use before parsing begins.  For instance,
                \"--define foo\" is similar to \"`define foo\" and \"--define
                foo=3\" is similar to \"`define foo 3\".  Note: these defines
                are \"sticky\" and will override subsequent `defines in your
                Verilog files unless your Verilog explicitly uses `undef.  You
                can give this option multiple times."
               :parser getopt::parse-string
               :merge cons)

   (cclimit     natp
                :argname "N"
                "Limit for the const check.  This is a beta feature that is not
                 yet released.  Setting N to 0 (the default) disables the
                 check.  Otherwise, limit the scope of the check to at most N
                 sub-expressions."
                :default 0)

   (global-packages string-listp
                    :longname "global-package"
                    :argname "PACKAGE"
                    "Consider the given package to be global for purposes of the
                     globalparams check; i.e., parameters defined in this package
                     should not be defined anywhere else."
                    :merge cons
                    :parser getopt::parse-string)
   (elab-limit  natp
                :argname "N"
                "Default 10000.  Recursion limit for elaboration.  This usually
                 shouldn't matter or need tinkering.  It's a safety valve
                 against possible loops in elaboration, e.g., to resolve
                 parameter P you need to evaluate parameter Q, which might
                 require you to resolve R, which might depend hierarchically on
                 P, and so on.  So if you hit this there's probably something
                 wrong with your design."
                :rule-classes :type-prescription
                :default 10000)

   (stmt-limit natp
               :argname "N"
               "Default 80.  Recursion limit for compiling statements, e.g.,
                unrolling loops and figuring out when they terminate.  For
                linting we use a low default limit that is meant to avoid
                wasting an inordinate amount of time compiling troublesome
                loops.  Increasing this may avoid svex translation warnings,
                but may result in bad performance in some cases."
               :rule-classes :type-prescription
               :default 80)

   (no-typo     booleanp
                "Disable typo detection (it is sometimes slow)."
                :rule-classes :type-prescription)

   (no-html     booleanp
                "Reduce the file size of vl-warnings.json by printing the
                 warnings there in text-only mode."
                :rule-classes :type-prescription)

   (no-sv-use-set booleanp
                  "Disable sv-use-set check."
                  :rule-classes :type-prescription)

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
                :rule-classes :type-prescription)

   (shell        booleanp
                "Instead of running the linter, enter an ACL2 shell where the linter
                 configuration has been saved as constant
                 @('vl::*vl-user-lintconfig*').")

   (post-shell  booleanp
                "After running the linter, enter an ACL2 shell where the linter
                 configuration has been saved as constant
                 @('vl::*vl-user-lintconfig*')."))
  ;; Note: would be nice to use the default alist layout here but it's ~14x
  ;; faster to admit this with :fulltree (23 sec vs 320 sec.)
  :layout :fulltree)

(defval *vl-lint-help*
  :short "Usage message for vl lint."
  :showdef nil
  :showval t

  (str::cat "
vl lint:  A linting tool for Verilog.  Scans your Verilog files for things
          that look like bugs (size mismatches, unused wires, etc.)

Example:  vl lint engine.v wrapper.v core.v \\
            --search ./simlibs \\
            --search ./baselibs

Usage:    vl lint [OPTIONS] file.v [file2.v ...] [+mymode ...]

Options:" *nls* *nls* *vl-lintconfig-usage* *nls*))

(defconsts (*vl-lint-readme* state)
  (b* ((topic (xdoc::find-topic 'vl::vl-lint (xdoc::get-xdoc-table (w state))))
       ((mv text state) (xdoc::topic-to-text topic nil state)))
    (mv text state)))

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


(defprod vl-lintresult
  :short "Results from running the linter."
  :tag :vl-lintresult
  ((design    vl-design-p
              "Final, transformed list of modules.  Useful to know whether a module
               is unexpectedly included or not included.")

   (design0   vl-design-p
              "Almost: the initial, pre-transformed modules.  The only twist is
               that we have already removed modules that are unnecessary or
               that we wanted to drop; see, e.g., the @('topmods') and
               @('ignore') options of @(see vl-lintconfig-p).  This is used for
               @(see skip-detection), for instance.")

   (design-orig   vl-design-p
              "Really the initial, pre-transformed modules.")

   (sv-modalist sv::modalist-p
                "The result of converting the elaborated design into SV modules.")

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
                   ;; CDR-OF-VL-MODULELIST-ORIGEXPRS
                   vl-modulelist-p-of-append
                   NO-DUPLICATESP-EQUAL-OF-APPEND
                   acl2::no-duplicatesp-equal-append-iff
                   mergesort)))

(define vl-collect-new-names-from-orignames ((keep-orignames string-listp)
                                             (mods vl-modulelist-p))
  :returns (keep-newnames string-listp)
  (b* (((when (atom mods))
        nil)
       ((vl-module x1) (car mods))
       ((when (member-equal x1.origname (string-list-fix keep-orignames)))
        (cons x1.name (vl-collect-new-names-from-orignames keep-orignames (cdr mods)))))
    (vl-collect-new-names-from-orignames keep-orignames (cdr mods))))

(define vl-design-remove-unnecessary-modules ((keep string-listp)
                                              (design vl-design-p))
  :returns (new-design vl-design-p)
  (b* ((design (vl-design-fix design))
       ((unless keep)
        ;; Special feature: if the user didn't specify any top modules, then we
        ;; want to keep everything.
        design)
       (keep1 (mergesort (string-list-fix keep)))
       ;; If the user wants to keep a parameterized module, we need to go
       ;; through and find all of its new names.
       (keep2 (mergesort (vl-collect-new-names-from-orignames keep1 (vl-design->mods design))))
       (keep  (union keep1 keep2)))
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


(encapsulate
  ()
  (defund vl-lint-suppress-large-integer-problems (suppressp)
    (declare (xargs :guard t)
             (ignorable suppressp))
    t)

  (defttag :vl-lint-suppress-large-integer-problems)
  (acl2::include-raw "lint-raw.lsp"))


(defconst *vl-svbad-limit* (expt 2 20))

(define vl-datatype-svbad-p ((x vl-datatype-p))
  (b* (((unless (vl-datatype-resolved-p x))
        t)
       ((mv err size)
        (vl-datatype-size x)))
    (or err
        (and size (> size *vl-svbad-limit*)))))

(define vl-vardecl-svbad-warnings ((x        vl-vardecl-p)
                                   (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((vl-vardecl x))
       ((unless (vl-datatype-svbad-p x.type))
        (ok)))
    (fatal :type :vl-warn-svbad-p
           :msg "~a0: type ~a1 looks like it will cause problems for SV."
           :args (list x x.type))))

(define vl-vardecllist-svbad-warnings ((x        vl-vardecllist-p)
                                       (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (warnings (vl-vardecl-svbad-warnings (car x) warnings)))
    (vl-vardecllist-svbad-warnings (cdr x) warnings)))

(define vl-module-add-svbad-warnings ((x    vl-module-p)
                                      (good vl-modulelist-p)
                                      (bad  vl-modulelist-p))
  :returns (mv (good vl-modulelist-p)
               (bad  vl-modulelist-p))
  (b* (((vl-module x) (vl-module-fix x))
       (good (vl-modulelist-fix good))
       (bad  (vl-modulelist-fix bad))
       (warnings (vl-vardecllist-svbad-warnings x.vardecls nil))
       ((unless warnings)
        ;; no obvious problems, so keep this module
        (mv (cons x good) bad))
       ;; some wire looks really big and is probably going to cause
       ;; problems for SV, so drop this module
       (new-x (change-vl-module x :warnings (append-without-guard warnings x.warnings))))
    (mv good (cons new-x bad))))

(define vl-modulelist-add-svbad-warnings ((x    vl-modulelist-p)
                                          (good vl-modulelist-p)
                                          (bad  vl-modulelist-p))
  :returns (mv (good vl-modulelist-p)
               (bad  vl-modulelist-p))
  (b* (((when (atom x))
        (mv (vl-modulelist-fix good) (vl-modulelist-fix bad)))
       ((mv good bad) (vl-module-add-svbad-warnings (first x) good bad)))
    (vl-modulelist-add-svbad-warnings (rest x) good bad)))

(define vl-lint-design->svex-modalist-wrapper ((x      vl-design-p)
                                               (config vl-simpconfig-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x))
       (- (sneaky-save :vl-lint-svconfig config))
       (- (sneaky-save :vl-lint-pre-sv-design x))

       ((mv good bad) (vl-modulelist-add-svbad-warnings x.mods nil nil))

       ;; Strip out the bad mods so that we don't try to build SV
       ;; modules for them.
       (good-x (change-vl-design x :mods good))
       ((mv reportcard ?modalist)
        (xf-cwtime (vl-design->svex-modalist good-x :config config)))

       ;; Reattach the bad mods so that we get their warning.
       (merged-x (change-vl-design x :mods (append-without-guard good bad)))

       ;; Finally get the warnings from SV translation from the reportcard.
       (final-x (xf-cwtime (vl-apply-reportcard merged-x reportcard))))
    final-x))

(define run-vl-lint-main ((design vl-design-p)
                          (config vl-lintconfig-p))
  :guard-debug t
  :returns (result vl-lintresult-p :hints(("Goal" :in-theory (disable (force)))))

  (b* (((vl-lintconfig config) config)
       (design-orig design)
       (- (vl-lint-suppress-large-integer-problems t))

       (simpconfig
        (change-vl-simpconfig *vl-default-simpconfig*
                              :sv-simplify nil
                              :elab-limit config.elab-limit
                              :sc-limit config.stmt-limit))

       (design (vl-annotate-design design simpconfig))
       ;; We originally did this before annotate, but that doesn't work in the
       ;; new world of loaditems.  we need to annotate first.
       (design (xf-cwtime (vl-design-drop-user-submodules design config.dropmods)))

       ;; BOZO where did lvaluecheck go??

       ;; Taken care of by annotate
       ;; (design (cwtime (vl-design-resolve-ansi-portdecls design)))
       ;; (design (cwtime (vl-design-resolve-nonansi-interfaceports design)))
       ;; (design (cwtime (vl-design-add-enumname-declarations design)))
       ;; (design (cwtime (vl-design-make-implicit-wires design)))
       ;; (design (cwtime (vl-design-portdecl-sign design)))
       ;; (design (cwtime (vl-design-udp-elim design)))

       ;; BOZO I have no idea why we're doing this.
       ;; Old comments:

       ;; You might expect that we'd immediately throw out modules that we
       ;; don't need for topmods.  Historically we did that.  But then we found
       ;; that we'd get a bunch of complaints in other modules about
       ;; hierarchical identifiers that pointed into the modules we'd just
       ;; thrown away!  So now we deal with this stuff after HID resolution.
       ;; Except that for skip-detection, we also need to remove them from
       ;; mods0, so do that now:
       (design0 (vl-design-remove-unnecessary-modules config.topmods design))


       (design (xf-cwtime (vl-design-check-globalparams design config.global-packages)))
       (design (xf-cwtime (vl-design-duplicate-detect design)))
       (design (xf-cwtime (vl-design-alwaysstyle design)))

       ;; Note: don't want to addnames before duplicate-detect, because it
       ;; would name unnamed duplicated blocks in different ways.
       (design (xf-cwtime (vl-design-addnames design)))

       ;; all done in annotate now:
       ;; (design (cwtime (vl-design-portcheck design)))
       ;; (design (cwtime (vl-design-argresolve design)))
       ;; (design (cwtime (vl-design-type-disambiguate design)))

       (design (xf-cwtime (vl-design-oddexpr-check design)))

       ;; this goes away (design (cwtime (vl-design-resolve-indexing design)))

       ;; Pre-unparameterization Lucidity Check.
       (typosp (not config.no-typo))
       (design (xf-cwtime (vl-design-lucid design
                                           :modportsp t    ;; Good time to check modports
                                           :paramsp t      ;; Good time to check params
                                           :typosp typosp  ;; Good time to check for typos
                                           :generatesp nil ;; Bad time to check generates
                                           )))

       (design (xf-cwtime (vl-design-check-namespace design)))
       (design (xf-cwtime (vl-design-check-case design)))
       (design (xf-cwtime (vl-design-duperhs-check design)))
       (design (xf-cwtime (vl-design-condcheck design)))
       (design (xf-cwtime (vl-design-leftright-check design)))
       (design (xf-cwtime (vl-design-dupeinst-check design)))
       (design (xf-cwtime (vl-centaur-seqcheck-hook design)))
       (design (xf-cwtime (vl-design-logicassign design)))

       ;; BOZO we need to do something to throw away instances with unresolved
       ;; arguments to avoid programming-errors in drop-blankports... and actually
       ;; we hit errors like that later, too.
       ;; (design (cwtime (vl-design-drop-blankports design)))
       ;;(design (cwtime (vl-design-follow-hids design)))
       ;; (design (cwtime (vl-design-clean-params design)))
       ;; (design (cwtime (vl-design-check-good-paramdecls design)))
       (design (xf-cwtime (vl-design-elaborate design simpconfig)))

       ((mv design stubnames) (vl-design-lint-stubs design))

       ;; these are part of elaboration now
       ;;(design (cwtime (vl-design-rangeresolve design)))
       ;;(design (cwtime (vl-design-selresolve design)))

       (design
        ;; Running another dupeinst check here, after unparameterization, may
        ;; create redundant warnings, but it may also help to catch things that
        ;; become duplicates after unparameterization.
        (xf-cwtime (vl-design-dupeinst-check design)))

       ;; Post-unparameterization Lucidity Check -- this is a bad time for
       ;; checking parameters (because they've been eliminated) and modports
       ;; (because the interface names have changed and we won't be able to
       ;; find them correctly).  But it's a much better time to do bit-level
       ;; analysis, because things like foo[width-1:0] should hopefully be
       ;; resolved now.  Also we can sensibly check generates now.
       (design (xf-cwtime (vl-design-lucid design
                                           :modportsp nil
                                           :paramsp nil
                                           :typosp nil
                                           :generatesp t)))

;;*** do we want to do thsi???  I can't think of why
       ;; (design
       ;;  ;; Best not to do this until after lucid checking.
       ;;  (cwtime (vl-design-drop-missing-submodules design)))

       ;; BOZO do we even need to do this?
       ;; BOZO not exactly sure where this should go, maybe this will work.


       ;; (design
       ;;  ;; Bug fixed 2014-12-19: don't do this until after argresolve, because
       ;;  ;; in SystemVerilog it can get confused by .* or .foo style port
       ;;  ;; connections.  Also it's best not to do this until after lucid
       ;;  ;; checking because it would screw up lucid's checks.  Actually why
       ;;  ;; are we even doing this?
       ;;  (cwtime (vl-design-elim-unused-vars design)))

       (design (xf-cwtime (vl-design-check-selfassigns design)))
       (design (xf-cwtime (vl-design-qmarksize-check design)))
       (design (xf-cwtime (vl-design-arith-compare-check design)))
       (design (xf-cwtime (vl-design-unpacked-range-check design)))
       (sd-probs (xf-cwtime (sd-analyze-design design0)))

;; Not sure we care abotu this for anything
       ;; (design (cwtime (vl-design-lint-stmt-rewrite design)))
       ;; (design (cwtime (vl-design-stmtrewrite design 1000)))
       ;;(design (cwtime (vl-design-hid-elim design)))

;; maaaaybe we don't watn this?
       ;; ;; Now that HIDs are gone, we can throw away any modules we don't care
       ;; ;; about, if we have been given any topmods.
       ;; (design (b* ((names1 (vl-modulelist->names (vl-design->mods design)))
       ;;              (design (vl-design-drop-missing-submodules design))
       ;;              (names2 (vl-modulelist->names (vl-design->mods design)))
       ;;              (lost   (difference (mergesort names1) (mergesort names2))))
       ;;           (or (not lost)
       ;;               (cw "BOZO lost ~x0 modules somewhere (probably unparameterizing): ~x1~%"
       ;;                   (len lost) lost))
       ;;           design))

       ((mv reportcard modalist) (xf-cwtime (vl-design->svex-modalist
                                              design :config simpconfig)))
       (design (xf-cwtime (vl-apply-reportcard design reportcard)))
       (design (if (not config.no-sv-use-set)
                   (xf-cwtime (vl-design-sv-use-set design modalist))
                 design))

       (design (xf-cwtime (vl-design-remove-unnecessary-modules config.topmods design)))


       ;; [Jared] -- Trying to NOT do oprewrite anymore.  Our sizing warnings
       ;; do better if we can tell the difference between == and ~^ operators,
       ;; for instance.
       ;; (design (cwtime (vl-design-oprewrite design)))


       ;; Sizing doesn't do well unless we expand functions
;       (design (cwtime (vl-design-expand-functions design)))
;       (design (cwtime (vl-design-exprsize design)))
;       (design (cwtime (vl-design-constcheck-hook design config.cclimit)))


;       (- (cw "~%vl-lint: processing assignments...~%"))
;       (design (cwtime (vl-design-split design)))

; BOZO argument width checking?
;       (design (cwtime (vl-design-replicate design)))

;; BOZO are we checking for connecting blanks to interface ports
;;        (design (cwtime (vl-design-blankargs design)))
;;       (design (cwtime (vl-design-trunc design)))

;       (- (cw "~%vl-lint: finding skipped and multiply driven wires...~%"))
       ;; NOTE: use design0, not design, if you ever want this to finish. :)


       (design   (xf-cwtime (vl-design-clean-warnings design)))
       (design   (xf-cwtime (vl-design-suppress-file-warnings design config.ignore-files)))
       (design   (xf-cwtime (vl-design-suppress-lint-warnings design)))
       (design   (xf-cwtime (vl-design-lint-ignoreall design config.ignore)))
       (design   (xf-cwtime (vl-lint-apply-quiet (append stubnames config.quiet) design)))
       (sd-probs (xf-cwtime (vl-delete-sd-problems-for-modnames (append stubnames config.quiet) sd-probs)))
       (reportcard  (xf-cwtime (vl-design-origname-reportcard design))))
    (vl-lint-suppress-large-integer-problems nil)
    (make-vl-lintresult :design design
                        :design0 design0
                        :design-orig design-orig
                        :sv-modalist modalist
                        :reportcard reportcard
                        :sd-probs sd-probs
                        )))

(defsection vl-lint-extra-actions
  :parents (vl-lint)
  :short "Customizable hook to run at the end of VL Lint."
  :long "<p>This is an attachment that allows you to extend VL Lint with
  support additional, customized (e.g., methodology-specific) checks and custom
  reports.</p>

  <p>It gets called as the last step of @(see run-vl-lint) and has access to
  the entire @(see vl-lintconfig) and the corresponding @(see vl-loadconfig),
  the full @(see vl-loadresult), and also the full @(see vl-lintresult) which
  contains all the warnings and the final, fully processed design.</p>"

  (encapsulate
    (((vl-lint-extra-actions * * * * state) => state
      :formals (lintconfig loadconfig loadresult lintresult state)
      :guard (and (vl-lintconfig-p lintconfig)
                  (vl-loadconfig-p loadconfig)
                  (vl-loadresult-p loadresult)
                  (vl-lintresult-p lintresult))))

    (local (defun vl-lint-extra-actions
             (lintconfig loadconfig loadresult lintresult state)
             (declare (ignore lintconfig loadconfig loadresult lintresult)
                      (xargs :stobjs state))
             state))

    (defthm state-p1-of-vl-lint-extra-actions
      (implies (state-p1 state)
               (state-p1 (vl-lint-extra-actions lintconfig loadconfig
                                                loadresult lintresult
                                                state))))))

(define vl-lint-extra-actions-default ((lintconfig vl-lintconfig-p)
                                       (loadconfig vl-loadconfig-p)
                                       (loadresult vl-loadresult-p)
                                       (lintresult vl-lintresult-p)
                                       state)
  :parents (vl-lint-extra-actions)
  :short "Does nothing -- this is the default implementation for
          @('vl-lint-extra-actions')."
  (declare (ignore lintconfig loadconfig loadresult lintresult))
  state
  ///
  (defattach vl-lint-extra-actions vl-lint-extra-actions-default))

(define vl-lintconfig-loadconfig ((config vl-lintconfig-p)
                                  (defines vl-defines-p))
  :returns (loadconfig vl-loadconfig-p)
  (b* (((vl-lintconfig config)))
    (make-vl-loadconfig
     :edition       config.edition
     :strictp       config.strict
     :start-files   config.start-files
     :search-path   config.search-path
     :search-exts   config.search-exts
     :include-dirs  config.include-dirs
     :plusargs      config.plusargs
     :defines       defines
     :mintime       1/100
     :debugp        config.debug)))

(define run-vl-lint ((config vl-lintconfig-p) &key (state 'state))
  :returns (mv (res vl-lintresult-p)
               (loadres vl-loadresult-p)
               (loadconfig vl-loadconfig-p)
               (state state-p1 :hyp (state-p1 state)))
  (b* ((- (cw "Starting VL-Lint~%"))
       ((vl-lintconfig config) config)
       (- (or (not config.debug)
              (cw "Lint configuration: ~x0~%" config)))

       ((mv cmdline-warnings defines)
        (vl-parse-cmdline-defines config.defines
                                  (make-vl-location :filename "vl cmdline"
                                                    :line 1
                                                    :col 0)
                                  ;; Command line defines are sticky
                                  t))

       (- (or (not cmdline-warnings)
              (vl-cw-ps-seq (vl-print-warnings cmdline-warnings))))

       (loadconfig (vl-lintconfig-loadconfig config defines))

       (- (or (not config.debug)
              (cw "Load configuration: ~x0~%" loadconfig)))

       (- (cw "~%vl-lint: loading modules...~%"))
       ((mv loadres state) (cwtime (vl-load loadconfig)))

       (design (vl-loadresult->design loadres))
       (design (change-vl-design design
                :warnings
                (append-without-guard cmdline-warnings
                                      (vl-design->warnings design))))

       (lintres (cwtime (run-vl-lint-main design config)))
       (state (cwtime (vl-lint-extra-actions
                       config loadconfig loadres lintres state))))

    (mv lintres loadres loadconfig state)))


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

(define vl-lint-print-all-warnings ((filename stringp)
                                    (label    stringp)
                                    (reportcard   vl-reportcard-p)
                                    &key (ps 'ps))
  (b* ((reportcard (vl-clean-reportcard reportcard))
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

(define vl-jp-reportcard-aux ((x vl-reportcard-p) &key (no-html booleanp) (ps 'ps))
  (b* (((when (atom x))
        ps)
       ((cons modname warnings) (car x))
       (modname (if (eq modname :design)
                    "Design Root"
                  modname)))
    (vl-ps-seq (vl-indent 1)
               (jp-str modname)
               (vl-print ":")
               (vl-jp-warninglist warnings :no-html no-html)
               (if (atom (cdr x))
                   ps
                 (vl-println ","))
               (vl-jp-reportcard-aux (cdr x) :no-html no-html)))
  :prepwork
  ((local (defthm l0
            (implies (and (vl-reportcardkey-p x)
                          (not (equal x :design)))
                     (stringp x))
            :hints(("Goal" :in-theory (enable vl-reportcardkey-p)))))))

(define vl-jp-reportcard ((x vl-reportcard-p) &key (no-html booleanp) (ps 'ps))
  (vl-ps-seq (vl-print "{")
             (vl-jp-reportcard-aux x :no-html no-html)
             (vl-println "}")))

(define vl-remove-nameless-descriptions ((x vl-descriptionlist-p))
  :returns (new-x vl-descriptionlist-p)
  (cond ((atom x)
         nil)
        ((not (vl-description->origname (car x)))
         (vl-remove-nameless-descriptions (cdr x)))
        (t
         (cons (vl-description-fix (car x))
               (vl-remove-nameless-descriptions (cdr x))))))

(define vl-jp-description-locations ((x vl-descriptionlist-p) &key (ps 'ps))
  (b* (((when (atom x))
        ps)
       (name (or (vl-description->origname (car x))
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

(define vl-jp-design-locations ((x vl-design-p) &key (ps 'ps))
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
        :vl-port-mismatch
        :vl-warn-scary-translate-comment
        :vl-preprocessor-error
        :vl-preprocess-failed
        :vl-parse-error
        :vl-parse-failed
        :vl-search-failed
        :vl-unreachable-module
        :vl-warn-define-smashed
        :vl-warn-undef
        :vl-warn-define-ignored
        :vl-bindelim-fail))

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
        :vl-warn-qmark-always-true
        :vl-warn-leftright
        :vl-warn-selfassign
        :vl-warn-instances-same
        :vl-warn-case-sensitive-names
        :vl-warn-same-rhs
        :vl-const-expr
        :vl-warn-vardecl-assign
        :vl-warn-oddexpr
        :vl-warn-possible-typo
        :vl-warn-include-guard
        :vl-warn-plain-always
        :vl-warn-always-latch
        :vl-warn-arithmetic-comparison
        ))

(defconst *smell-minor-warnings*
  (list :vl-warn-partselect-same
        :vl-warn-instances-same-minor
        :vl-const-expr-minor
        :vl-warn-empty-dotstar))

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
        :vl-fussy-size-warning-3-minor
        :vl-fussy-size-warning-1-minor-intsize
        :vl-fussy-size-warning-2-minor-intsize
        :vl-fussy-size-warning-3-minor-intsize
        ))

(defconst *lucid-warnings*
  (list :vl-lucid-error
        :vl-lucid-unused
        :vl-lucid-spurious
        :vl-lucid-unset
        :vl-lucid-multidrive))

(defconst *lucid-variable-warnings*
  (list :vl-lucid-unused-variable
        :vl-lucid-spurious-variable
        :vl-lucid-unset-variable))

(defconst *sv-use-set-warnings*
  (list 
   :sv-use-set-spurious
   :sv-use-set-spurious-inout
   :sv-use-set-unused-input
   :sv-use-set-unset-output
   :sv-use-set-partly-unset-output
   :sv-use-set-unused
   :sv-use-set-unset
   :sv-use-set-partly-unset
   :sv-use-set-partly-unused
   :sv-use-set-partly-spurious))
   


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
          *lucid-variable-warnings*
          *sv-use-set-warnings*
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

(define vl-warninglist-remove-suppressed ((x vl-warninglist-p))
  :returns (new-x vl-warninglist-p)
  (if (atom x)
      nil
    (if (vl-warning->suppressedp (car x))
        (vl-warninglist-remove-suppressed (cdr x))
      (cons (vl-warning-fix (car x))
            (vl-warninglist-remove-suppressed (cdr x))))))

(define vl-reportcard-remove-suppressed ((x vl-reportcard-p))
  :returns (new-reportcard vl-reportcard-p)
  :measure (len (vl-reportcard-fix x))
  (b* ((x (vl-reportcard-fix x))
       ((when (atom x)) nil)
       ((cons key warnings) (car x))
       (warnings (vl-warninglist-remove-suppressed warnings)))
    (if warnings
        (cons (cons (vl-reportcardkey-fix key)
                    warnings)
              (vl-reportcard-remove-suppressed (cdr x)))
      (vl-reportcard-remove-suppressed (cdr x)))))

(define vl-warninglist-keep-suppressed ((x vl-warninglist-p))
  :returns (new-x vl-warninglist-p)
  (if (atom x)
      nil
    (if (vl-warning->suppressedp (car x))
        (cons (vl-warning-fix (car x))
              (vl-warninglist-keep-suppressed (cdr x)))
      (vl-warninglist-keep-suppressed (cdr x)))))

(define vl-reportcard-keep-suppressed ((x vl-reportcard-p))
  :returns (new-reportcard vl-reportcard-p)
  :measure (len (vl-reportcard-fix x))
  (b* ((x (vl-reportcard-fix x))
       ((when (atom x)) nil)
       ((cons key warnings) (car x))
       (warnings (vl-warninglist-keep-suppressed warnings)))
    (if warnings
        (cons (cons (vl-reportcardkey-fix key)
                    warnings)
              (vl-reportcard-keep-suppressed (cdr x)))
      (vl-reportcard-keep-suppressed (cdr x)))))


(define vl-pp-stringlist-lines ((x string-listp)
                          &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-println (string-fix (car x)))
               (vl-pp-stringlist-lines (cdr x)))))

(define vl-print-eliminated-descs ((final vl-design-p "final design")
                                   (orig vl-design-p "original design")
                                   &key (ps 'ps))
  (b* ((final-descs (mergesort
                     (vl-descriptionlist->orignames
                      (vl-remove-nameless-descriptions
                       (vl-design-descriptions final)))))
       (orig-descs (mergesort
                    (vl-descriptionlist->orignames
                     (vl-remove-nameless-descriptions
                      (vl-design-descriptions orig)))))
       (missing (difference orig-descs final-descs)))
    (vl-pp-stringlist-lines missing)))


(define vl-lint-report ((config vl-lintconfig-p)
                        (loadresult vl-loadresult-p)
                        (lintresult vl-lintresult-p)
                        state)
  :returns (state state-p1 :hyp (state-p1 state))
  (b* (((vl-lintresult lintresult))
       ((vl-loadresult loadresult))
       ((vl-lintconfig config))
       (reportcard   lintresult.reportcard)
       (suppressed (vl-reportcard-keep-suppressed reportcard))
       (reportcard (vl-reportcard-remove-suppressed reportcard))
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
        (with-ps-file
          "vl-lucid-vars.txt"
          (vl-ps-update-autowrap-col 68)
          (vl-lint-print-warnings "vl-lucid-vars.txt" "Lucidity Checking" *lucid-variable-warnings* reportcard)))

       (state
        (with-ps-file
          "vl-sv-use-set.txt"
          (vl-ps-update-autowrap-col 68)
          (vl-lint-print-warnings "vl-sv-use-set.txt" "SV Use/Set Checking" *sv-use-set-warnings* reportcard)))

       (state
        (with-ps-file
          "vl-eliminated-mods.txt"
          (vl-ps-update-autowrap-col 68)
          (vl-print "
Note: These modules were eliminated because they were never instantiated anywhere in the top module's hierarchy.
")
          (vl-print-eliminated-descs lintresult.design lintresult.design-orig)))

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

       (state
        (with-ps-file
          "vl-suppressed.txt"
          (vl-ps-update-autowrap-col 58)
          (vl-lint-print-all-warnings "vl-suppressed.txt" "suppressed" suppressed)))

       (- (cw "~%"))

       (state
        (cwtime
         (with-ps-file "vl-warnings.json"
           (vl-print "{\"warnings\":")
           (vl-jp-reportcard reportcard :no-html config.no-html)
           (vl-print ",\"locations\":")
           (vl-jp-design-locations lintresult.design)
           (vl-println "}"))
         :name write-warnings-json))

       (state
        ;; This has historically been part of vl-warnings.json, which is fine
        ;; and we will leave it there, but since the warnings files can get
        ;; large, it's nice to emit this separately as well.
        (cwtime
         (with-ps-file "vl-locations.json"
           (vl-print "{\"locations\":")
           (vl-jp-design-locations lintresult.design)
           (vl-println "}"))
         :name write-locations-json))

       (state
        (cwtime
         (with-ps-file "vl-ifdefs.txt"
           (vl-print-ifdef-report-main loadresult.ifdefmap))
         :name write-ifdef-report))

       (state
        (cwtime
         (with-ps-file "vl-ifdef-usage.json"
           (vl-jp-definfo loadresult.defines loadresult.ifdefmap loadresult.defmap))
         :name write-ifdef-usage.json))

       (state
        (cwtime
         (with-ps-file "vl-warnings-suppressed.json"
           (vl-print "{\"warnings\":")
           (vl-jp-reportcard suppressed)
           (vl-print ",\"locations\":")
           (vl-jp-design-locations lintresult.design)
           (vl-println "}"))
         :name write-warnings-json)))

    state))

(define vl-lint-top ((args string-listp) &key (state 'state))
  :short "Top-level @('vl lint') command."

  (b* (((mv errmsg config start-files-and-plusargs)
        (parse-vl-lintconfig args))
       ((when errmsg)
        (die "~@0~%" errmsg)
        state)
       ((mv start-files plusargs) (split-plusargs start-files-and-plusargs))
       (config
        (change-vl-lintconfig config
                              :plusargs plusargs
                              :start-files start-files))
       ((vl-lintconfig config) config)

       (- (acl2::set-max-mem ;; newline to appease cert.pl
           (* (expt 2 30) config.mem)))

       ;; Arrange to eagerly GC when we expect it to be beneficial when
       ;; we're past 60% of the desired memory ceiling.
       (- (set-vl-gc-threshold (floor (* 6 (expt 2 30) config.mem) 10)))
       (- (set-vl-gc-baseline))

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

       ((when config.shell)
        (vl-shell-entry `((defconst *vl-user-lintconfig* ',config))))

       ((mv result loadres loadconfig state)
        (cwtime (run-vl-lint config)
                :name vl-lint))
       (state
        (cwtime (vl-lint-report config loadres result state)))

       ((when config.post-shell)
        (b* ((print (and (boundp-global 'acl2::ld-pre-eval-print state) ;; for guard
                         (f-get-global 'acl2::ld-pre-eval-print state))))
          (vl-shell-entry `((acl2::set-ld-pre-eval-print nil state)
                            (defconst *vl-user-lintconfig* ',config)
                            (defconst *vl-user-loadconfig* ',loadconfig)
                            (defconst *vl-user-loadres* ',loadres)
                            (defconst *vl-user-design* (vl-loadresult->design *vl-user-loadres*))
                            (defconst *vl-user-lintresult* ',result)
                            (acl2::set-ld-pre-eval-print ',print state))))))

    (exit-ok)
    state))


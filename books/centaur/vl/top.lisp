; VL Verilog Toolkit
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

(in-package "VL")
(include-book "checkers/checkers")
(include-book "checkers/duplicate-detect")
(include-book "checkers/multidrive-detect")
(include-book "checkers/portcheck")
(include-book "checkers/use-set")
(include-book "loader/loader")
(include-book "mlib/comment-writer")
(include-book "toe/toe-top")
(include-book "transforms/cn-hooks")
(include-book "transforms/always/top")
(include-book "transforms/occform/top")
(include-book "transforms/xf-addinstnames")
(include-book "transforms/xf-argresolve")
(include-book "transforms/xf-assign-trunc")
(include-book "transforms/xf-blankargs")
(include-book "transforms/xf-clean-params")
(include-book "transforms/xf-designregs")
(include-book "transforms/xf-designwires")
(include-book "transforms/xf-delayredux")
(include-book "transforms/xf-drop-blankports")
(include-book "transforms/xf-elim-supply")
(include-book "transforms/xf-expand-functions")
(include-book "transforms/xf-expr-split")
(include-book "transforms/xf-follow-hids")
(include-book "transforms/xf-gateredux")
(include-book "transforms/xf-gatesplit")
(include-book "transforms/xf-gate-elim")
(include-book "transforms/xf-hid-elim")
(include-book "transforms/xf-oprewrite")
(include-book "transforms/xf-optimize-rw")
(include-book "transforms/xf-orig")
(include-book "transforms/xf-portdecl-sign")
(include-book "transforms/xf-replicate-insts")
(include-book "transforms/xf-resolve-ranges")
(include-book "transforms/xf-sizing")
(include-book "transforms/xf-unparameterize")
(include-book "transforms/xf-unused-reg")
(include-book "transforms/xf-weirdint-elim")
(include-book "transforms/xf-annotate-mods")
(include-book "util/clean-alist")
(include-book "translation")
(include-book "centaur/misc/sneaky-load" :dir :system)
(local (include-book "mlib/modname-sets"))
(local (include-book "util/arithmetic"))
(local (include-book "util/osets"))
(local (include-book "system/f-put-global" :dir :system))
(local (in-theory (disable put-global)))

#||

; Fool the dependency scanner into certifying lexer-tests and
; preprocessor-tests as part of building top.cert

(include-book "loader/lexer-tests")
(include-book "loader/preprocessor-tests")

||#


;; These seemed to be slowing us down.  This reduced the certification
;; time from 324 to 101 seconds on 2010-01-19.
(local (in-theory (disable consp-under-iff-when-true-listp
                           mergesort
                           setp-of-vl-modulelist->names-when-no-duplicates)))

;; These aren't as big of a deal, but were able to cut it down to 82
;; seconds.  Actually, at this point almost everything is the cost of
;; including the books above.
(local (in-theory (disable string-listp
                           subsetp-equal-when-first-two-same-yada-yada
                           no-duplicatesp-equal
                           ;; No longer included after emod changes
                           ;; acl2::subsetp-equal-implies-subsetp-equal-cdr
                           true-listp)))




(defxdoc vl
  :short "VL Verilog Toolkit."
  :long "<box><p><b>Note</b>: this documentation is mainly a reference manual.
If you are new to VL, please see @(see getting-started) first.</p></box>")

(defxdoc getting-started
  :parents (vl)
  :short "Getting started with VL."

  :long "<h3>Introduction</h3>

<p><b>VL</b> is an <a
href=\"http://www.cs.utexas.edu/users/moore/acl2/\">ACL2</a> library for
working with Verilog source code.  It includes:</p>

<ul>
 <li>A representation for Verilog @(see modules),</li>
 <li>A @(see loader) for parsing Verilog source code into this representation,</li>
 <li>Utilities for inspecting and analyzing these modules,</li>
 <li>Various transforms that can simplify these modules, and</li>
 <li>Pretty-printing and other report-generation functions.</li>
</ul>

<p>The original (and still primary) purpose of VL is to translate Verilog
modules into E-language modules for formal verification.  E is a comparatively
simple, hierarchical, register-transfer level hardware description language.
Because E is still under active development we have not yet released it, but an
early version is described in the following paper:</p>

<p>Warren A. Hunt, Jr. and Sol Swords.  \"Centaur technology media unit
verification.  Case study: Floating point addition.\" in Computer Aided
Verification (CAV '09), June 2009.</p>

<p>Our overall approach to E translation is to apply several Verilog-to-Verilog
source-code @(see transforms).  Together, these transforms work to simplify the
input Verilog into a form that is very close to E, where modules consist only
of gates and submodules.  Then, the final conversion into E is quite
straightforward.</p>

<p>A feature of this approach is that the majority of VL has nothing to do with
E, and VL can be used to implement other Verilog tools.  For instance:</p>

<ul>

<li>We have used it to developed linting tools like @(see use-set) and a more
powerful linter which is available in @('vl/lint') but is not yet
documented.</li>

<li>We have implemented an equivalence checking tool (which is not yet
released) that has a unit-based timing model and handles transistor-level
constructs.  This tool uses the same parser and most of VL's transforms, but
also has a couple of additional transformation steps.</li>

<li>We have also used it to implement a web-based \"module browser\" (which
will probably not be released since it is very Centaur specific) that lets
users see the original and translated source code for our modules, and has
several nice features (e.g., hyperlinks for navigating between wires and
following wires, and integrated linting and warning/error reporting).</li>

</ul>

<p>We imagine that other users of VL may wish to use it:</p>

<ul>

<li>As a convenient way to load Verilog files to implement their own static
checks (i.e., as Lisp functions that inspect the parse tree), or</li>

<li>As a frontend to some other kind of tool, e.g., use VL to deal with tricky
Verilog things like expressions so that your tool only has to deal with gates
and hierarchical modules.  (This is really how we use it.)</li>

</ul>


<h3>Supported Constructs</h3>

<p>Verilog is a huge language, and VL supports only part of it.</p>

<p>VL is based on our reading of the Verilog-2005 standard, IEEE Std 1364-2005.
Page and section numbers given throughout the VL documentation are in reference
to this document.  VL does not have any support for SystemVerilog.</p>

<p>VL's @(see preprocessor) is somewhat incomplete.  It basically just supports
@('`define') and @('`ifdef')-related stuff and can @('`include') files in the
style of the @('+incdir') options for tools like Verilog-XL (but we often use
search paths, which are more similar to @('+libdir') arguments.)</p>

<p>The @(see lexer) is complete.</p>

<p>The @(see parser) doesn't currently support user-defined primitives,
generate statements, specify blocks, specparams, genvars, functions, and tasks.
The parser will just skip over some of these constructs, and depending on what
you are doing, this behavior may be actually appropriate (e.g., skipping task
statements is probably okay if they are only used in the development of test
benches.)</p>

<p>Each of VL's @(see transforms) have certain capabilities and limitations,
which vary from transform to transform.  As a general rule, VL mainly supports
RTL-level constructs and some of its transforms will not be able to cope
with:</p>

<ul>

<li>transistor-level things like @('tran') gates and @('inout') ports, or</li>

<li>simulation-level things like hierarchical identifiers and @('always')
statements beyond the simplest latches and flops.</li>

</ul>

<p>VL has some ability to tolerate constructs that aren't really supported, and
the general philsophy is that an error in some particular module shouldn't
affect other modules.  If the parser runs into an syntax error or an
unsupported construct, it often only causes that particular module to be
skipped.  When transforms encounter unsupported things or run into problems, we
usually avoid hard errors and instead just add \"fatal @(see warnings)\" to the
module with the problem.</p>



<h3>Starting Points</h3>

<p>The first step in using VL for anything is probably to try to get it to
parse your design; see the documentation for the @(see loader).</p>

<p>Once you have parsed your design (or at least some portion of it) you will
have a list of modules.  You might want to at least glance through the
documentation for @(see modules), which explains how modules are represented.
This may be particularly useful if you are going to write your own checkers or
transforms.</p>

<p>You may find it useful to pretty-print modules, see for instance @(see
vl-ppcs-module) and perhaps more generally the VL @(see printer).</p>

<p>After getting a feel for how modules are represented, it would be good to
look at the available @(see transforms).  A good way to do this might be to
look at the code for @(see vl-simplify) (see @('centaur/vl/top.lisp')) to see
the order that we normally apply the transforms in.  You could also look at
@('centaur/vl/lint/lint.lisp') which uses a different transformation sequence
that is more geared toward linting.  You should probably also read through how
VL deals with @(see warnings).</p>

<p>If you are going to write any transforms or checkers of your own, you should
probably look at @(see mlib).  This provides many functions for working with
expressions and ranges, finding modules and module items, working with the
module hierarchy, generating fresh names, and working with modules at the bit
level.</p>")

(define vl-warn-problem-module ((x vl-module-p)
                                (problems string-listp))
  :returns (new-x vl-module-p :hyp :fguard)
  :parents (vl-simplify)
  :short "@(call vl-warn-problem-module) determines if the module @('x') is
considered a \"problem module\", and if so annotates it with a fatal warning
explaining this."

  :long "<p>See @(see vl-simplify) for a description of problem modules.
@('problems') are a list of the problem module names that have been supplied by
the caller.</p>"

  (if (member-equal (vl-module->name x) problems)
      (let ((warning
             (make-vl-warning
              :type :vl-problem-module
              :msg "Module ~m0 has been flagged by the user as a \"problem ~
                    module.\"  This ordinarily indicates that the module ~
                    leads to some poorly handled exceptional condition, e.g., ~
                    perhaps we cannot sort the module's occurrences. At any ~
                    rate, the module is being discarded not because the ~
                    translator has seen some problem, but because the user ~
                    has explicitly said not to look at this module."
              :args (list (vl-module->name x))
              :fatalp t
              :fn __function__)))
        (change-vl-module x :warnings (cons warning (vl-module->warnings x))))
    x)
  ///
  (defthm vl-module->name-of-vl-warn-problem-module
    (equal (vl-module->name (vl-warn-problem-module x problems))
           (vl-module->name x))))


(defprojection vl-warn-problem-modulelist (x problems)
  (vl-warn-problem-module x problems)
  :guard (and (vl-modulelist-p x)
              (string-listp problems))
  :parents (vl-simplify)
  :short "Extend @(see vl-warn-problem-modulelist) to a list of modules."
  :result-type vl-modulelist-p
  :rest
  ((defthm vl-modulelist->names-of-vl-warn-problem-modulelist
     (equal (vl-modulelist->names (vl-warn-problem-modulelist x problems))
            (vl-modulelist->names x)))))


(define vl-simplify-part1-annotate-mods ((mods vl-modulelist-p))
  :returns (new-mods vl-modulelist-p :hyp :fguard)

  (b* (;;this was never any good
       ;;mods (xf-cwtime (vl-modulelist-cross-active mods)
       ;;                :name xf-cross-active))

       (mods (xf-cwtime (vl-modulelist-lvaluecheck mods)
                        :name xf-lvaluecheck)))
    mods)

  ///
  (defthm vl-modulelist->names-of-vl-simplify-part1-annotate-mods
    (equal (vl-modulelist->names (vl-simplify-part1-annotate-mods mods))
           (vl-modulelist->names mods))))



(define vl-simplify-part1-sanify-mods
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods))))
   (problem-mods string-listp))
  :returns (mv (mods vl-modulelist-p :hyp :fguard)
               (failmods vl-modulelist-p :hyp :fguard))

; Sanifying the module list.
;
; Our later transforms want a clean module list.  To provide this, we are now
; going to throw away modules which:
;   (1) had any problems with argresolve, above
;   (2) have been marked as problem modules by the user,
;   (3) are incomplete (instantiate missing modules),
;   (4) are unreasonable (use unsupported constructs), or
;   (5) have always blocks that we do not support.
;
; In addition, all modules that depend upon modules thrown away for one of
; these reasons must be removed.  The general approach is discussed in the
; documentation for warnings.  In short: we annotate any bad module with a
; fatal warning, then use vl-propagate-errors to throw these modules away.

  (b* ((mods (xf-cwtime (vl-warn-problem-modulelist mods problem-mods)
                        :name warn-problem-mods))

       (mods (xf-cwtime (vl-modulelist-check-reasonable mods)
                        :name warn-unreasonable-mods))

       (mods (xf-cwtime
              ;; BOZO ugly.  Change check-complete to use an aux function and
              ;; build the modalist on its own, and do the clearing of the memo
              ;; table on its own, too.
              (b* ((modalist (vl-modalist mods))
                   (mods (vl-modulelist-check-complete mods mods modalist))
                   (- (flush-hons-get-hash-table-link modalist))
                   (- (clear-memoize-table 'vl-necessary-direct-for-module)))
                mods)
              :name warn-incomplete-mods))

; New: do not throw away always blocks (yet)
;      (mods (cwtime (vl-modulelist-check-always mods)
;                    :name warn-unsupported-always-mods))

       (mods (xf-cwtime (vl-modulelist-check-good-paramdecls mods)
                        :name warn-bad-paramdecl-mods))

       ((mv mods failmods) (xf-cwtime (vl-propagate-errors mods)
                                      :name propagate-errors))
;(- (cw "~x0 modules remain.~%" (len mods)))
       )

    (mv mods failmods))

  ///
  (defmvtypes vl-simplify-part1-sanify-mods (true-listp true-listp))

  (defthm no-duplicatesp-equal-of-vl-simplify-part1-sanify-mods-0
    (implies (no-duplicatesp-equal (vl-modulelist->names mods))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-simplify-part1-sanify-mods mods problem-mods)))))))



(define vl-simplify-part1
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods))))
   (problem-mods string-listp)
   (omit-wires   string-listp))
  :returns (mv (mods vl-modulelist-p :hyp :fguard)
               (failmods vl-modulelist-p :hyp :fguard)
               (use-set-report vl-useset-report-p :hyp :fguard))
  :parents (vl-simplify)
  :short "Initial transformations up through unparameterization."

  :long "<p>Part 1 addresses:</p>

<ul>
 <li>Initial, simple transforms such as resolving arguments to modules,</li>
 <li>Generating the @(see use-set) report,</li>
 <li>Sanifying the module list by throwing away unreasonable, incomplete, or
     otherwise problematic modules, and</li>
 <li>Carrying out @(see unparameterization).</li>
</ul>"

  (b* ((- (cw "Beginning simplification of ~x0 modules.~%" (len mods)))

; We begin by trying to resolve argument lists and adding other basic
; annotations.  This is the minimum we need for use-set generation.  These
; transforms are quite robust and can deal with pretty much any constructs in
; the modules, so we don't need to eliminate the unreasonable modules and such
; first.  This is good, because it means the use-set report can span the entire
; list of modules, rather than just the reasonable ones.

       (mods (vl-simplify-part1-annotate-mods mods))

; Use-Set report generation.  Even though argresolve can sometimes produce
; fatal warnings, the use-set report is intended to do as much as it can for
; all of the modules, so we want to go ahead with it before throwing anything
; away.

       ((mv mods use-set-report)
        (xf-cwtime (vl-mark-wires-for-modulelist mods omit-wires)
                   :name use-set-analysis))

; I'll eliminate functions before cleaning params, since we don't want to
; allow function parameters to overlap with module parameters.

       (mods (xf-cwtime (vl-modulelist-expand-functions mods)
                        :name xf-expand-functions))

       (mods (xf-cwtime (vl-modulelist-clean-params mods)
                        :name xf-clean-params))

       ((mv mods failmods)
        (vl-simplify-part1-sanify-mods mods problem-mods))

; Unparameterization.  Our final move is to carry out the unparameterization.
; The guard for unparameterize is rather confining, so we want to make sure
; that these criteria are met.  We might eventually try to prove these away.

;<< BOZO doublecheck-reasonable, always-known in safe-mode? >>

       ((unless
            (and ;; proven now, eh?
             ;;  (cwtime (uniquep (vl-modulelist->names mods))
             ;;         :name doublecheck-unique-names)
             (xf-cwtime (vl-modulelist-complete-p mods mods)
                        :name doublecheck-completeness)
             (xf-cwtime (vl-good-paramdecllist-list-p-of-vl-modulelist->paramdecls mods)
                        :name doublecheck-paramdecls)))
        (prog2$
         (er hard? 'vl-simplify-part1
             "Programming error.  Sanify incomplete.  Thought this was impossible.")
         (mv nil nil nil)))

; BOZO unparam is kind of ugly.  Consider changing it to just annotate with
; fatal warnings instead of returning failmods?  We could also consider moving
; the uniqueness check into unparam itself, so that we do not need to
; explicitly carry it out.

; <<We previously deleted top-level modules with params and warned that they
; might be dead code before unparameterizing.  Do we want to bring that back?>>

       ((mv mods failmods2) (xf-cwtime (vl-unparameterize mods 30)
                                       :name vl-unparameterize))
       (failmods (append failmods2 failmods))
;(- (cw "~x0 modules remain.~%" (len mods)))

       ((unless (xf-cwtime (uniquep (vl-modulelist->names mods))
                           :name doublecheck-unique-names))
        (prog2$
         (er hard? 'vl-simplify-part1
             "Programming error.  Unparam name clash.  Thought this was impossible.")
         (mv nil nil nil))))

    (mv mods failmods use-set-report))

  ///
  (defmvtypes vl-simplify-part1 (true-listp true-listp nil))

  (defthm no-duplicatesp-equal-of-vl-simplify-part1
    (implies (and (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-simplify-part1 mods problem-mods omit-wires))))))

  (defthm vl-useset-report-p-of-vl-simplify-part1-report
    (implies (and (force (vl-modulelist-p mods))
                  (force (string-listp omit-wires)))
             (vl-useset-report-p
              (mv-nth 2 (vl-simplify-part1 mods problem-mods omit-wires))))))



(define vl-simplify-part2
  ((mods         (and (vl-modulelist-p mods)
                      (uniquep (vl-modulelist->names mods))))
   (failmods     vl-modulelist-p)
   (safe-mode-p  booleanp)
   (unroll-limit natp))
  :returns (mv (mods vl-modulelist-p :hyp :fguard)
               (failmods vl-modulelist-p :hyp :fguard))
  :parents (vl-simplify)
  :short "Expression rewriting, sizing, splitting; instance replication,
assignment truncation, etc."
  (declare (ignorable safe-mode-p))
  (b*

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free>>

      ((mods (xf-cwtime (vl-modulelist-rangeresolve mods)
                        :name xf-rangeresolve))
       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))
;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved>>

       (mods (xf-cwtime (vl-modulelist-selresolve mods)
                        :name xf-selresolve))
       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))
;(- (cw "~x0 modules remain.~%" (len mods)))




; Subtle.  Rewrite statements before doing HID elimination because our "reset
; alias detection" doesn't look very hard.

       (mods (xf-cwtime (vl-modulelist-stmtrewrite mods unroll-limit)
                        :name xf-stmtrewrite))

;      (- (acl2::sneaky-save :pre-hid-elim mods))

       (mods (xf-cwtime (vl-modulelist-hid-elim mods)
                        :name xf-hid-elim))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))
;(- (cw "~x0 modules remain.~%" (len mods)))

;      (- (acl2::sneaky-save :post-hid-elim mods))



; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds>>

; <<We used to shift-ranges here.  We don't do that anymore.>>

       ;; We rewrite statements before and after eliminating resets.  This is so
       ;; (1) reset elimination can look for simpler forms, and (2) we can
       ;; eliminate null statements produced by reset elimination.

;; no, don't do this here, now we want it to be sized
;       (mods (xf-cwtime (vl-modulelist-negedge-elim mods)
;                        :name xf-negedge-elim))

; Hrmn, maybe handling this in stmtrewrite is better?
;      (mods (cwtime (vl-modulelist-drop-vcovers-hook mods)
;                    :name xf-vcover-elim))

       (mods (xf-cwtime (vl-modulelist-stmtrewrite mods unroll-limit)
                        :name xf-stmtrewrite))

; Jared -- removing reset elimination!  Now gets handled by ordinary HID stuff.
;
;      (mods (cwtime (vl-modulelist-eliminate-resets mods)
;                    :name xf-eliminate-resets))
;
;      (mods (cwtime (vl-modulelist-stmtrewrite mods unroll-limit)
;                    :name xf-stmtrewrite))

       (mods (xf-cwtime (vl-modulelist-oprewrite mods)
                        :name xf-oprewrite))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple>>

       (mods (xf-cwtime (vl-modulelist-exprsize mods)
                        :name xf-selfsize))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>

       (mods (xf-cwtime (vl-modulelist-always-backend mods)
                        :name xf-always-backend))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))


       (mods (xf-cwtime (vl-modulelist-elim-unused-regs mods)
                        :name xf-elim-unused-regs))



       (mods (xf-cwtime (vl-modulelist-drop-blankports mods)
                        :name xf-drop-blankports))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))


       (mods (xf-cwtime (vl-modulelist-delayredux mods)
                        :name xf-delayredux))

       (mods (xf-cwtime (vl-modulelist-split mods)
                        :name xf-split))

       (- (vl-gc))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>

       (- (sneaky-save 'pre-repl mods))

       (mods (xf-cwtime (vl-modulelist-replicate mods)
                        :name xf-replicate-instance-arrays))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))


       (mods (xf-cwtime (vl-modulelist-blankargs mods)
                        :name xf-blankargs))
       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))
;(- (cw "~x0 modules remain.~%" (len mods)))


;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>

       (mods (xf-cwtime (vl-modulelist-trunc mods)
                        :name xf-trunc))


       ;; This might not be the best time to do this, but it seems like here
       ;; we've got the widths figured out and there isn't too much serious
       ;; stuff left to do.

       (mods (xf-cwtime (vl-modulelist-multidrive-detect mods)
                        :name xf-multidrive-detect))


       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>


       )

    (mv mods failmods))
  ///

  (defmvtypes vl-simplify-part2 (true-listp true-listp))

  (defthm no-duplicatesp-equal-of-vl-simplify-part2
    (implies (and (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (b* (((mv mods ?failmods)
                   (vl-simplify-part2 mods failmods safe-mode-p unroll-limit)))
               (no-duplicatesp-equal (vl-modulelist->names mods))))))


(define vl-simplify-part3
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods))))
   (failmods vl-modulelist-p)
   (safe-mode-p booleanp))
  :returns (mv (mods vl-modulelist-p :hyp :fguard)
               (failmods vl-modulelist-p :hyp :fguard))
  (declare (ignorable safe-mode-p))
  :parents (vl-simplify)
  :short "Occforming, gate simplification and splitting, naming blank
instances, supply elimination, dependency-order sorting, E translation."

  (b* ((mods (xf-cwtime (vl-modulelist-optimize mods)
                        :name optimize))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>

       (mods (xf-cwtime (vl-modulelist-occform mods)
                        :name xf-occform))

       (- (vl-gc))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))


       ;; NEW weirdint elimination -- must come after occform
       (mods (xf-cwtime (vl-modulelist-weirdint-elim mods)
                        :name xf-weirdint-elim))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))



; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>

       (mods (xf-cwtime (vl-modulelist-gateredux mods)
                        :name xf-gateredux))

       ((unless (uniquep (vl-modulelist->names mods)))
        (prog2$
         (er hard? 'vl-simplify-part3
             "Programming error: gateredux resulted in name clashes?")
         (mv nil nil)))


       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>


       (mods (xf-cwtime (vl-modulelist-gatesplit mods)
                        :name xf-gatesplit))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>

       (mods (xf-cwtime (vl-modulelist-gate-elim mods)
                        :name xf-gate-elim))

       (mods (xf-cwtime (vl-modulelist-addinstnames mods)
                        :name xf-instname))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>

       (mods (xf-cwtime (vl-modulelist-elim-supplies mods)
                        :name xf-elim-supplies))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

;(- (cw "~x0 modules remain.~%" (len mods)))


; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>

       ;; Note: adding this here because one-bit selects from scalars make Verilog
       ;; simulators mad, and this gets rid of them... blah.
       (mods (xf-cwtime (vl-modulelist-optimize mods)
                        :name optimize))

       ;; This is just a useful place to add on any additional transforms you want
       ;; before E generation.
       (mods (xf-cwtime (vl-modulelist-pre-toe-hook mods)
                        :name pre-toe))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

       (- (sneaky-save 'pre-defm mods))

       (mods (xf-cwtime (vl-modulelist-to-e mods)
                        :name xf-convert-to-e))

       ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                      :name propagate-errors))

       (mods (xf-cwtime (vl-modulelist-clean-warnings mods)
                        :name xf-clean-warnings))

       (failmods (xf-cwtime (vl-modulelist-clean-warnings failmods)
                            :name xf-clean-warnings-failmods))

       (- (vl-gc))
;(- (cw "~x0 modules remain.~%" (len mods)))

       )

    (mv mods failmods))
  ///
  (defmvtypes vl-simplify-part3 (true-listp true-listp))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-simplify-part3
    (implies (and (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (b* (((mv mods ?failmods)
                   (vl-simplify-part3 mods failmods safe-mode-p)))
               (no-duplicatesp-equal (vl-modulelist->names mods))))))


(define vl-simplify-main
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods))))
   (problem-mods string-listp)
   (omit-wires   string-listp)
   (safe-mode-p  booleanp)
   (unroll-limit natp))
  :returns (mv (mods :hyp :fguard
                     (and (vl-modulelist-p mods)
                          (no-duplicatesp-equal (vl-modulelist->names mods))))
               (failmods vl-modulelist-p :hyp :fguard)
               (use-set-report vl-useset-report-p :hyp :fguard))
  ;; Combines parts 1-3, but doesn't do the annotations.
  (b* (((mv mods failmods use-set-report)
        (vl-simplify-part1 mods problem-mods omit-wires))
       ((mv mods failmods)
        (vl-simplify-part2 mods failmods safe-mode-p (nfix unroll-limit)))
       ((mv mods failmods)
        (vl-simplify-part3 mods failmods safe-mode-p)))
    (mv mods failmods use-set-report))
  ///
  (defmvtypes vl-simplify-main (true-listp true-listp nil)))


(define vl-simplify
  ((mods "parsed Verilog modules, typically from @(see vl-load)."
         (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods))))
   (problem-mods "names of modules that should thrown out, perhaps because they
                  cause some kind of problems for simplification."
                 string-listp)
   (omit-wires "names of wires to omit from the use-set report."
               string-listp)
   (safe-mode-p "enable extra, expensive run-time checks that may catch
                 problems; mostly deprecated, probably useless."
                booleanp)
   (unroll-limit "maximum number of times to unroll loops; we usually use 100,
                  but this is mainly just to avoid going crazy if we see a loop
                  with some absurd number of iterations."
                 natp))
  :returns
  (mv (mods "modules that we simplified successfully"
            :hyp :fguard
            (and (vl-modulelist-p mods)
                 (no-duplicatesp-equal (vl-modulelist->names mods))))
      (failmods "modules that we threw out due to errors"
                :hyp :fguard vl-modulelist-p)
      (use-set-report "a report about unused/unset wires"
                      :hyp :fguard vl-useset-report-p))
  :parents (vl)
  :short "Top level interface for simplifying Verilog modules."
  :long "<p>This is a high-level routine that applies our @(see transforms) in
a suitable order to simplify Verilog modules and to produce E modules.</p>"

  (vl-simplify-main (vl-annotate-mods mods)
                    problem-mods omit-wires
                    safe-mode-p unroll-limit)
  ///
  (defmvtypes vl-simplify (true-listp true-listp nil)))



(defsection defmodules
  :parents (vl)
  :short "High level command to load Verilog files, transform them, and
introduce the corresponding E modules."

  :long "<p>The @('defmodules') macro allows you to load Verilog files into
your ACL2 session \"on the fly.\"</p>

<p>Defmodules is is the preferred way to load \"small\" Verilog modules for
one-off projects.  It is basically just a thin wrapper around @(see vl-load)
and @(see vl-simplify), but it usefully hides some of the complexity with good
default values, and ensures that all of the warnings generated during
simplification are printed for you to inspect.</p>


<h3>Using Defmodules</h3>

<p>The simplest case is that you want to load some \"self-contained\" Verilog
files.  The list of files to parse is given in the @('start-files') argument;
these files will be parsed in the order they are given.</p>

@({
 (defmodules *foo*
    :start-files (list \"foo_control.v\" \"foo_datapath.v\"))
})

<p><b>BOZO</b> fix me, this doesn't currently introduce the E modules.</p>

<p>After submitting this event, E modules for all successfully translated
modules will be introduced, e.g., @('|*foo_control*|').  Additionally, the
constant @('*foo*') will be defined as a @(see vl-translation-p) that allows
you to inspect the translation in other ways.</p>


<h4>Search Paths and Include Dirs</h4>

<p>Verilog files often rely on modules defined in other files.</p>

<p>VL can use a @('search-path'), which is a list of directories that will be
searched, in order, for any modules that are used but not defined (and not
explicitly @('`include')d in the start-files).  For example:</p>

@({
 (defmodules foo
    :start-files (list \"foo_control.v\" \"foo_datapath.v\")
    :search-path (list \"/my/project/libs1\" \"/my/project/libs2\" ...))
})

<p>By default only @('.v') files will be loaded in this way, but the
@(':searchext') option can also be used to give more extensions, e.g., you
could write:</p>

@({
 (defmodules foo
    :start-files (list \"foo_control.v\" \"foo_datapath.v\")
    :search-path (list \"/my/project/libs1\" \"/my/project/libs2\" ...)
    :searchext   (list \"v\" \"V\"))
})

<p>to include both @('.v') and @('.V') files.</p>


<p>You can separately set up the @('include-dirs') that should be searched when
loading files with @('`include').  By default, @('`include \"foo.v\"') only
looks for @('foo.v') in the current directory (i.e., @('\".\"')).  But you can
add additional include directories, which will be searched in priority
order (with @('\".\"'), always implicitly taking priority).  For instance,</p>

@({
 (defmodules foo
   :start-files (list \"foo_wrapper.v\")
   :include-dirs (list \"./foo_extra1\" \"./foo_extra2\"))
})


<h4>Initial `defines</h4>

<p>The @(':defines') option can be used to set up any extra @('`define')
directives.  For instance, the following:</p>

@({
 (defmodules foo
    :start-files (list \"foo_control.v\" \"foo_datapath.v\")
    :defines     (list \"FOO_BAR\" \"FOO_BAZ\"))
})

<p>is essentially like writing:</p>

@({
`define FOO_BAR 1
`define FOO_BAZ 1
})

<p>at the top of your first start-file.  If you need more sophisticated
defines, you might add an extra start-file, instead.</p>


<h4>Overriding and Customizing Modules</h4>

<p>You can also specify an @(':override-dirs') argument to \"safely\" replace
particular Verilog modules with custom definitions.  See @(see overrides) for
details on how to write override files.</p>

<p>VL also supports a special comment syntax:</p>

@({
//+VL single-line version
/*+VL multi-line version */
})

<p>Which can be used to hide VL-specific code from other tools, e.g., if
you need your modules to work with an older Verilog implementation that
doesn't support Verilog-2005 style attributes, you might write something
like:</p>

@({
//+VL (* my_attribute *)
assign foo = bar;
})

<p>There is also a special, more concise syntax for attributes:</p>

@({
//@VL my_attribute
})


<h4>Start Modnames</h4>

<p>Instead of (or in addition to) explicitly providing @('start-files'), you
can provide the names of some modules that you want to load from the search
path, e.g.,:</p>

@({
 (defmodules foo
    :start-modnames (list \"foo_control\" \"foo_datapath\")
    :search-path (list \".\" \"/my/project/libs1\" \"/my/project/libs2\" ...))
})


<h4>Advanced Options</h4>

<p>If some module causes errors that are not handled gracefully, you can mark
it as a @(':problem-module') so that it will not be simplified.  For
instance,</p>

@({
 (defmodules foo
    :start-files (list \"foo_control.v\" \"foo_datapath.v\")
    :problem-modules (list \"bad_module_1\" \"bad_module_2\"))
})

<p>The other options taken by @(see vl-simplify) and @(see vl-load) are given
sensible defaults that are not currently configurable.  We may add these
options in the future, as the need arises.</p>"

  (defund defmodules-fn (override-dirs start-files start-modnames
                                       search-path searchext include-dirs
                                       defines problem-modules state)
    "Returns (MV TRANS STATE)"
    (declare (xargs :guard (and (string-listp override-dirs)
                                (string-listp start-files)
                                (string-listp start-modnames)
                                (string-listp search-path)
                                (string-listp searchext)
                                (string-listp include-dirs)
                                (string-listp defines)
                                (string-listp problem-modules))
                    :stobjs state))
    (b* ((- (cw "Override directories: ~&0.~%" override-dirs))
         (- (cw "Reading Verilog files ~&0.~%" start-files))
         (- (cw "Search path:~%  ~x0.~%" search-path))

         (initial-defs (vl::vl-make-initial-defines defines))
         (filemapp     t)
         ((mv successp mods filemap defines warnings state)
          (vl::vl-load :override-dirs  override-dirs
                       :start-files    start-files
                       :start-modnames start-modnames
                       :search-path    search-path
                       :searchext      searchext
                       :include-dirs   include-dirs
                       :defines        initial-defs
                       :filemapp       filemapp))

         (- (cw "Finished parsing ~x0 files; found ~x1 modules.~%"
                (len filemap)
                (len mods)))
         (- (or successp
                (cw "*** WARNING: not all modules were successfully loaded ***~%")))
         (- (or (atom warnings)
                (vl-cw-ps-seq
                 (vl-println "All warnings from parsing:")
                 (vl-print-warnings warnings))))

         (omit-wires   nil) ;; only used in use-set
         (safe-modep   nil) ;; doesn't actually do anything
         (unroll-limit 1000)
         ((mv mods failmods use-set-report)
          (vl::vl-simplify mods problem-modules omit-wires safe-modep
                           unroll-limit))

         (walist (vl-origname-modwarningalist (append mods failmods)))
         (- (vl-cw-ps-seq
             (vl-cw "Successfully simplified ~x0 module(s).~%" (len mods))
             ;; (vl-print-strings-with-commas (vl::vl-modulelist->names-exec mods nil) 4)
             ;; (vl-println "")
             (vl-cw "Failed to simplify ~x0 module~s1~%"
                    (len failmods)
                    (cond ((atom failmods) "s.")
                          ((atom (cdr failmods)) ":")
                          (t "s:")))
             (if (atom failmods)
                 ps
               (vl-print-strings-with-commas (vl::vl-modulelist->names-exec failmods nil) 4))
             (vl-println "")
             (vl-println "Warnings for all modules:")
             (vl-print-modwarningalist walist)
             (vl-println "")))
         (- (fast-alist-free walist))

         (dregs (xf-cwtime (vl-modulelist-collect-dregs mods)
                           :name :collect-dregs))

         (result (make-vl-translation :mods mods
                                      :failmods failmods
                                      :filemap filemap
                                      :defines defines
                                      :loadwarnings warnings
                                      :useset-report use-set-report
                                      :dregs dregs
                                      )))

        (mv result state)))

  (local (in-theory (enable defmodules-fn)))

  (defthm defmodules-fn-basics
    (implies (and (force (string-listp override-dirs))
                  (force (string-listp start-files))
                  (force (string-listp start-modnames))
                  (force (string-listp search-path))
                  (force (string-listp searchext))
                  (force (string-listp include-dirs))
                  (force (string-listp defines))
                  (force (string-listp problem-modules))
                  (force (state-p1 state)))
             (and
              (vl-translation-p
               (mv-nth 0 (defmodules-fn override-dirs start-files start-modnames
                           search-path searchext include-dirs
                           defines problem-modules state)))
              (state-p1
               (mv-nth 1 (defmodules-fn override-dirs start-files start-modnames
                           search-path searchext include-dirs
                           defines problem-modules state))))))

  (defmacro defmodules (name &key
                             override-dirs
                             start-files
                             start-modnames
                             search-path
                             (searchext ''("v"))
                             include-dirs
                             defines
                             problem-modules)
    `(make-event
      (b* ((name ',name)
           ((unless (symbolp name))
            (er soft 'defmodules "Expected name to be a symbol."))

           (start-files ,start-files)
           ((unless (string-listp start-files))
            (er soft 'defmodules "Expected start-files to be a string list."))

           (start-modnames ,start-modnames)
           ((unless (string-listp start-modnames))
            (er soft 'defmodules "Expected start-modnames to be a string list."))

           ((unless (or start-files start-modnames))
            (er soft 'defmodules "Expected either some start-files or start-modnames."))

           (override-dirs ,override-dirs)
           ((unless (string-listp override-dirs))
            (er soft 'defmodules "Expected override-dirs to be a string list."))

           (search-path ,search-path)
           ((unless (string-listp search-path))
            (er soft 'defmodules "Expected search-path to be a string list."))

           (include-dirs ,include-dirs)
           ((unless (string-listp include-dirs))
            (er soft 'defmodules "Expected include-dirs to be a string list."))

           (searchext ,searchext)
           ((unless (string-listp searchext))
            (er soft 'defmodules "Expected searchext to be a string list."))

           (defines ,defines)
           ((unless (string-listp defines))
            (er soft 'defmodules "Expected defines to be a string list."))

           (problem-modules ,problem-modules)
           ((unless (string-listp problem-modules))
            (er soft 'defmodules "Expected problem-modules to be a string list."))

           ((mv translation state)
            (cwtime (defmodules-fn override-dirs start-files start-modnames
                      search-path searchext include-dirs
                      defines problem-modules state)
                    :name defmodules-fn)))

          (value
           `(with-output
             :off (summary)
             (progn (defconst ,name ',translation)
                    ;; BOZO fix this to introduce the E modules again, and
                    ;; update the documentation above after it's been fixed.
                    (value-triple ',name))))))))



;; (defun vl-safe-mode-check (mods check)
;;   (declare (xargs :guard (vl-modulelist-p mods)

;;                   ;; This use of program mode is only to avoid guard
;;                   ;; verification, which won't work because some of
;;                   ;; these well-formedness checks have other guards.
;;                   ;;
;;                   ;; BOZO eventually remove the guards from the various
;;                   ;; well-formedness checks.
;;                   :mode :program
;;                   :guard-debug t))

;;   (case check
;;     (:vl-modules
;;      (cwtime (vl-modulelist-p mods)
;;              :name |Safe-Mode Check: vl-modulelist-p|))
;;     (:vl-unique-names
;;      (cwtime (uniquep (vl-modulelist->names mods))
;;                    :name |Safe-Mode Check: unique names|))
;;     (:vl-complete
;;      (cwtime (vl-modulelist-complete-p mods)
;;                    :name |Safe-Mode Check: completeness|))
;;     (:vl-reasonable
;;      (cwtime (vl-modulelist-reasonable-p mods)
;;                    :name |Safe-Mode Check: reasonable|))
;;     (:vl-param-free
;;      (cwtime (not (vl-modules-with-params mods))
;;                    :name |Safe-Mode Check: parameter-free|))
;;     (:vl-ranges-resolved
;;      (cwtime (vl-modulelist-ranges-resolved-p mods)
;;                    :name |Safe-Mode Check: ranges resolved|))
;;     (:vl-selects-resolved
;;      (cwtime (vl-modulelist-selresolved-p mods)
;;                    :name |Safe-Mode Check: selects resolved|))
;;     (:vl-selects-in-bounds
;;      (cwtime (vl-modulelist-selbounds-p mods)
;;                    :name |Safe-Mode Check: selects in bounds|))
;;     (:vl-ranges-simple
;;      (cwtime (vl-modulelist-ranges-simple-p mods)
;;                    :name |Safe-Mode Check: ranges simple|))
;;     (:vl-widths-fixed
;;      (cwtime (vl-modulelist-widthsfixed-p mods)
;;                    :name |Safe-Mode Check: widths fixed|))
;;     (:vl-args-compat
;;      (cwtime (vl-modulelist-instwidthscompat-p mods)
;;                    :name |Safe-Mode Check: argument widths compatible|))
;;     (:vl-always-known
;;      (cwtime (vl-only-known-always-blocks mods)
;;                    :name |Safe-Mode Check: only known always blocks|))
;;     (otherwise
;;      (warn$ "Unknown safe-mode check, ~x0.~%" check))))


;; (defun vl-safe-mode-checks (safe-mode-p mods checks)
;;   (declare (xargs :guard (vl-modulelist-p mods)
;;                   :mode :program))
;;   (cond ((not safe-mode-p)
;;          nil)
;;         ((atom checks)
;;          nil)
;;         (t
;;          (prog2$ (vl-safe-mode-check mods (car checks))
;;                  (vl-safe-mode-checks safe-mode-p mods (cdr checks))))))





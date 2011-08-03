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
(include-book "mlib/ram-tools")
(include-book "transforms/cn-hooks")
(include-book "transforms/occform/occform-top")
(include-book "transforms/xf-addinstnames")
(include-book "transforms/xf-argresolve")
(include-book "transforms/xf-assigndelays")
(include-book "transforms/xf-assign-trunc")
(include-book "transforms/xf-blankargs")
(include-book "transforms/xf-clean-params")
(include-book "transforms/xf-designregs")
(include-book "transforms/xf-designwires")
(include-book "transforms/xf-drop-blankports")
(include-book "transforms/xf-elim-always")
(include-book "transforms/xf-elim-supply")
(include-book "transforms/xf-expr-split")
(include-book "transforms/xf-follow-hids")
(include-book "transforms/xf-gateredux")
(include-book "transforms/xf-gatesplit")
(include-book "transforms/xf-gate-elim")
(include-book "transforms/xf-hid-elim")
(include-book "transforms/xf-infer-flops")
(include-book "transforms/xf-make-implicit-wires")
(include-book "transforms/xf-negedge-elim")
(include-book "transforms/xf-oprewrite")
(include-book "transforms/xf-optimize-rw")
(include-book "transforms/xf-orig")
(include-book "transforms/xf-portdecl-sign")
(include-book "transforms/xf-replicate-insts")
(include-book "transforms/xf-resolve-ranges")
(include-book "transforms/xf-sizing")
(include-book "transforms/xf-stmt-rewrite")
(include-book "transforms/xf-unparameterize")
(include-book "transforms/xf-unused-reg")
(include-book "transforms/xf-weirdint-elim")
(include-book "util/clean-alist")
(include-book "translation")
(include-book "centaur/misc/sneaky-load" :dir :system)
(include-book "serialize/serialize" :dir :system)
(local (include-book "mlib/modname-sets"))
(local (include-book "util/arithmetic"))
(local (include-book "util/osets"))
(local (include-book "centaur/misc/f-put-global" :dir :system))
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
  :long "<p>Note: thqis documentation is mainly a reference manual.  If you are
new to VL, you may wish to start with @(see getting-started).</p>")

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
powerful linter which is available in <tt>vl/lint</tt> but is not yet
documented.</li>

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

<p>Regarding file loading, VL's @(see preprocessor) is very incomplete and
basically just supports <tt>`define</tt> and <tt>`ifdef</tt>-related stuff; it
notably doesn't support <tt>`include</tt>; we typically just use search paths.
The @(see lexer) is complete.  The @(see parser) doesn't currently support
user-defined primitives, generate statements, specify blocks, specparams,
genvars, functions, and tasks.</p>

<p>Each of VL's @(see transforms) have certain capabilities and limitations,
which vary from transform to transform.  As a general rule, VL mainly supports
RTL-level constructs and some of its transforms will not be able to cope
with:</p>

<ul>

<li>transistor-level things like <tt>tran</tt> gates and <tt>inout</tt>
ports, or</li>

<li>simulation-level things like hierarchical identifiers and <tt>always</tt>
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
look at the code for @(see vl-simplify) (see <tt>centaur/vl/top.lisp</tt>) to
see the order that we normally apply the transforms in.  You could also look at
<tt>centaur/vl/lint/lint.lisp</tt> which uses a different transformation
sequence that is more geared toward linting.  You should probably also read
through how VL deals with @(see warnings).</p>

<p>If you are going to write any transforms or checkers of your own, you should
probably look at @(see mlib).  This provides many functions for working with
expressions and ranges, finding modules and module items, working with the
module hierarchy, generating fresh names, and working with modules at the bit
level.</p>")



(defsection vl-warn-problem-module
  :parents (vl-simplify)
  :short "@(call vl-warn-problem-module) determines if the module <tt>x</tt> is
considered a \"problem module\", and if so annotates it with a fatal warning
explaining this."

  :long "<p>See @(see vl-simplify) for a description of problem modules.
<tt>problems</tt> are a list of the problem module names that have been
supplied by the caller.</p>"

  (defund vl-warn-problem-module (x problems)
    (declare (xargs :guard (and (vl-module-p x)
                                (string-listp problems))))
    (if (member-equal (vl-module->name x) problems)
        (let ((warning
               (make-vl-warning
                :type :vl-problem-module
                :msg "Module ~m0 has been flagged by the user as a \"problem ~
                      module.\"  This ordinarily indicates that the module ~
                      leads to some poorly handled exceptional condition, ~
                      e.g., perhaps we cannot sort the module's occurrences. ~
                      At any rate, the module is being discarded not because ~
                      the translator has seen some problem, but because the ~
                      user has explicitly said not to look at this module."
                :args (list (vl-module->name x))
                :fatalp t
                :fn 'vl-warn-problem-module)))
          (change-vl-module x :warnings (cons warning (vl-module->warnings x))))
      x))

  (local (in-theory (enable vl-warn-problem-module)))

  (defthm vl-module-p-of-vl-warn-problem-module
    (implies (force (vl-module-p x))
             (vl-module-p (vl-warn-problem-module x problems))))

  (defthm vl-module->name-of-vl-warn-problem-module
    (equal (vl-module->name (vl-warn-problem-module x problems))
           (vl-module->name x))))



(defsection vl-warn-problem-modulelist
  :parents (vl-simplify)
  :short "Extend @(see vl-warn-problem-modulelist) to a list of modules."

  (defprojection vl-warn-problem-modulelist (x problems)
    (vl-warn-problem-module x problems)
    :guard (and (vl-modulelist-p x)
                (string-listp problems)))

  (local (in-theory (enable vl-warn-problem-modulelist)))

  (defthm vl-modulelist-p-of-vl-warn-problem-modulelist
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-warn-problem-modulelist x problems))))

  (defthm vl-modulelist->names-of-vl-warn-problem-modulelist
    (equal (vl-modulelist->names (vl-warn-problem-modulelist x problems))
           (vl-modulelist->names x))))



(defmacro xf-cwtime (form &key
                          name
                          (mintime '1)
                          ;; 64 MB minalloc to report
                          (minalloc '67108864))
  `(cwtime ,form
           :name ,name
           :mintime ,mintime
           :minalloc ,minalloc))



(defsection vl-annotate-mods

; Annotations that will be done to form the "origmods" in the server

  (defund vl-annotate-mods (mods)
    (declare (xargs :guard (vl-modulelist-p mods)))
    (b* ((mods (xf-cwtime (vl-modulelist-duplicate-detect mods)
                          :name xf-duplicate-detect))

         (mods (xf-cwtime (vl-modulelist-portcheck mods)
                          :name xf-portcheck))

         (mods (xf-cwtime (vl-modulelist-make-implicit-wires mods)
                          :name xf-make-implicit-wires))

         (mods (xf-cwtime (vl-modulelist-designwires mods)
                          :name xf-mark-design-wires))

         (mods (xf-cwtime (vl-modulelist-portdecl-sign mods)
                          :name xf-crosscheck-port-signedness))

         (mods (xf-cwtime (vl-modulelist-argresolve mods)
                          :name xf-argresolve))

         (mods (xf-cwtime (vl-modulelist-origexprs mods)
                          :name xf-origexprs))

         (mods (xf-cwtime (mp-verror-transform-hook mods)
                          :name xf-mp-verror))

         (mods (xf-cwtime (vl-modulelist-follow-hids mods)
                          :name xf-follow-hids))

         (mods (xf-cwtime (vl-modulelist-clean-warnings mods)
                          :name xf-clean-warnings)))

        mods))

  (local (in-theory (enable vl-annotate-mods)))

  (defthm vl-modulelist-p-of-vl-annotate-mods
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (vl-annotate-mods mods))))

  (defthm vl-modulelist->names-of-vl-annotate-mods
    (equal (vl-modulelist->names (vl-annotate-mods mods))
           (vl-modulelist->names mods))))



(defsection vl-simplify-part1-annotate-mods

  (defund vl-simplify-part1-annotate-mods (mods)
    (declare (xargs :guard (vl-modulelist-p mods)))

    (b* (; this was never any good
         ;(mods (xf-cwtime (vl-modulelist-cross-active mods)
         ;                 :name xf-cross-active))

         (mods (xf-cwtime (vl-modulelist-lvaluecheck mods)
                          :name xf-lvaluecheck)))

        mods))

  (local (in-theory (enable vl-simplify-part1-annotate-mods)))

  (defthm vl-modulelist-p-of-vl-simplify-part1-annotate-mods
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p (vl-simplify-part1-annotate-mods mods))))

  (defthm vl-modulelist->names-of-vl-simplify-part1-annotate-mods
    (equal (vl-modulelist->names (vl-simplify-part1-annotate-mods mods))
           (vl-modulelist->names mods))))



(defsection vl-simplify-part1-sanify-mods

  (defund vl-simplify-part1-sanify-mods (mods problem-mods)
    "Returns (MV MODS FAILMODS)"
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods))
                                (string-listp problem-mods))))

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

        (mv mods failmods)))

  (defmvtypes vl-simplify-part1-sanify-mods (true-listp true-listp))

  (local (in-theory (enable vl-simplify-part1-sanify-mods)))

  (defthm vl-modulelist-p-of-vl-simplify-part1-sanify-mods
    (implies (vl-modulelist-p mods)
             (and (vl-modulelist-p (mv-nth 0 (vl-simplify-part1-sanify-mods mods problem-mods)))
                  (vl-modulelist-p (mv-nth 1 (vl-simplify-part1-sanify-mods mods problem-mods))))))

  (defthm no-duplicatesp-equal-of-vl-simplify-part1-sanify-mods-0
    (implies (no-duplicatesp-equal (vl-modulelist->names mods))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-simplify-part1-sanify-mods mods problem-mods)))))))




(defsection vl-simplify-part1
  :parents (vl-simplify)
  :short "Initial transformations up through unparameterization."

  :long "<p>Because @(see vl-simplify) is so complex, we split it into a couple
of parts.  Part 1 addresses:</p>

<ul>
 <li>Initial, simple transforms such as adding declarations for implicit wires
     and resolving arguments to modules,</li>
 <li>Generating the @(see use-set) report,</li>
 <li>Sanifying the module list by throwing away unreasonable, incomplete, or
     otherwise problematic modules, and</li>
 <li>Carrying out @(see unparameterization).</li>
</ul>

<p>See @(see vl-simplify) for a description of the inputs and outputs.</p>"

  (defund vl-simplify-part1 (mods problem-mods omit-wires)
    "Returns (MV MODS FAILMODS USE-SET-REPORT)"
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods))
                                (string-listp problem-mods)
                                (string-listp omit-wires))))

    (b* ((- (cw "Beginning simplification of ~x0 modules.~%" (len mods)))

; We begin by adding wire declarations for any implicit (or port implicit)
; wires and try to resolve argument lists.  This is the minimum we need for
; use-set generation.  These transforms are quite robust and can deal with
; pretty much any constructs in the modules, so we don't need to eliminate the
; unreasonable modules and such first.  This is good, because it means the
; use-set report can span the entire list of modules, rather than just the
; reasonable ones.

         (mods (vl-simplify-part1-annotate-mods mods))

; Use-Set report generation.  Even though argresolve can sometimes produce
; fatal warnings, the use-set report is intended to do as much as it can for
; all of the modules, so we want to go ahead with it before throwing anything
; away.

         ((mv mods use-set-report)
          (xf-cwtime (vl-mark-wires-for-modulelist mods omit-wires)
                     :name use-set-analysis))

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

        (mv mods failmods use-set-report)))

  (defmvtypes vl-simplify-part1 (true-listp true-listp nil))

  (local (in-theory (enable vl-simplify-part1)))

  (defthm vl-modulelist-p-of-vl-simplify-part1-mods
    (implies (and (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (vl-modulelist-p (mv-nth 0 (vl-simplify-part1 mods problem-mods omit-wires)))))

  (defthm vl-modulelist-p-of-vl-simplify-part1-failmods
    (implies (and (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (vl-modulelist-p (mv-nth 1 (vl-simplify-part1 mods problem-mods omit-wires)))))

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




(defsection vl-simplify-part2
  :parents (vl-simplify)
  :short "Expression rewriting, sizing, splitting; instance replication,
assignment truncation, etc."

  :long "<p>Because @(see vl-simplify) is so complex, we split it into a couple
of parts.</p>

<p><b>Signature:</b> @(call vl-simplify-part2) returns <tt>(mv mods
failmods-prime)</tt>.  The input <tt>failmods</tt> are any <tt>failmods</tt>
from @(see vl-simplify-part1).</p>"

  (defund vl-simplify-part2 (mods failmods safe-mode-p unroll-limit)
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (vl-modulelist-p failmods)
                                (uniquep (vl-modulelist->names mods))
                                (booleanp safe-mode-p)
                                (natp unroll-limit)))
             (ignorable safe-mode-p))

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

      (mods (xf-cwtime (vl-modulelist-negedge-elim mods)
                       :name xf-negedge-elim))

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

      (mods (xf-cwtime (vl-modulelist-infer-latches/flops mods)
                       :name xf-infer-latches/flops))

      (mods (xf-cwtime (vl-modulelist-verrors-to-guarantees-hook mods)
                       :name xf-verror-to-guarantee))

      (mods (xf-cwtime (vl-modulelist-elim-always mods)
                       :name xf-elim-unsupported-always-mods))

      ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                     :name propagate-errors))

      ;(- (cw "~x0 modules remain.~%" (len mods)))


      (mods (xf-cwtime (vl-modulelist-elim-unused-regs mods)
                       :name xf-elim-unused-regs))

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


      (mods (xf-cwtime (vl-modulelist-drop-blankports mods)
                       :name xf-drop-blankports))

      ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                     :name propagate-errors))


      (mods (xf-cwtime (vl-modulelist-assigndelays mods)
                       :name xf-assigndelays))

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

     (mv mods failmods)))

  (defmvtypes vl-simplify-part2 (true-listp true-listp))

  (local (in-theory (enable vl-simplify-part2)))

  (defthm vl-modulelist-p-of-vl-simplify-part2-mods
    (implies (and (force (vl-modulelist-p mods))
                  (force (natp unroll-limit)))
             (vl-modulelist-p
              (mv-nth 0 (vl-simplify-part2 mods failmods safe-mode-p unroll-limit)))))

  (defthm vl-modulelist-p-of-vl-simplify-part2-failmods
    (implies (and (force (vl-modulelist-p mods))
                  (force (vl-modulelist-p failmods))
                  (force (natp unroll-limit)))
             (vl-modulelist-p
              (mv-nth 1 (vl-simplify-part2 mods failmods safe-mode-p unroll-limit)))))

  (defthm no-duplicatesp-equal-of-vl-simplify-part2
    (implies (and (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-simplify-part2 mods failmods safe-mode-p unroll-limit)))))))



(defsection vl-simplify-part3
  :parents (vl-simplify)
  :short "Occforming, gate simplification and splitting, naming blank
instances, supply elimination, dependency-order sorting, E translation."

  :long "<p>Because @(see vl-simplify) is so complex, we split it into a couple
of parts.</p>

<p><b>Signature:</b> @(call vl-simplify-part3) returns <tt>(mv mods
failmods-prime)</tt>.  The input <tt>failmods</tt> are any <tt>failmods</tt>
from @(see vl-simplify-part2).</p>"

  (defund vl-simplify-part3 (mods failmods safe-mode-p)
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (vl-modulelist-p failmods)
                                (uniquep (vl-modulelist->names mods))
                                (booleanp safe-mode-p)))
             (ignorable safe-mode-p))

    (b*

     ((mods (xf-cwtime (vl-modulelist-optimize mods)
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

      (mods (xf-cwtime (vl-deporder-sort mods)
                       :name xf-deporder-sort))

      ((unless (xf-cwtime (uniquep (vl-modulelist->names mods))
                          :name doublecheck-unique-names))
       (prog2$ (er hard? 'vl-simplify-part3
                   "Deporder sort causes name clashes??  BOZO prove this away.")
               (mv nil failmods)))

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free :vl-ranges-resolved
; :vl-selects-resolved :vl-selects-in-bounds :vl-ranges-simple :vl-widths-fixed
; :vl-args-compat>>


      (- (sneaky-save 'pre-defm mods))

      (mods (xf-cwtime (vl-modulelist-make-defm-commands-hook mods)
                       :name xf-make-defm-commands))

      ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
                                     :name propagate-errors))

      (- (vl-gc))

      (mods (xf-cwtime (vl-modulelist-esim-trans-hook mods)
                       :name xf-esim-trans))

      (- (vl-gc))

      ;; (mods (if etrans-p
      ;;           (xf-cwtime (vl-modulelist-etrans mods)
      ;;                      :name xf-etrans)
      ;;         mods))

      ;; ((mv mods failmods)
      ;;  (if etrans-p
      ;;      (xf-cwtime (vl-propagate-new-errors mods failmods)
      ;;                 :name propagate-errors)
      ;;    (mv mods failmods)))

      (mods (xf-cwtime (vl-modulelist-clean-warnings mods)
                       :name xf-clean-warnings))

      (failmods (xf-cwtime (vl-modulelist-clean-warnings failmods)
                           :name xf-clean-warnings-failmods))

      ;(- (cw "~x0 modules remain.~%" (len mods)))

      )

     (mv mods failmods)))

  (defmvtypes vl-simplify-part3 (true-listp true-listp))

  (local (in-theory (enable vl-simplify-part3)))

  (defthm vl-modulelist-p-of-vl-simplify-part3-mods
    (implies (force (vl-modulelist-p mods))
             (vl-modulelist-p
              (mv-nth 0 (vl-simplify-part3 mods failmods safe-mode-p)))))

  (defthm vl-modulelist-p-of-vl-simplify-part3-failmods
    (implies (and (force (vl-modulelist-p mods))
                  (force (vl-modulelist-p failmods)))
             (vl-modulelist-p
              (mv-nth 1 (vl-simplify-part3 mods failmods safe-mode-p)))))

  (defthm no-duplicatesp-equal-of-vl-modulelist->names-of-vl-simplify-part3
    (implies (and (force (vl-modulelist-p mods))
                  (force (no-duplicatesp-equal (vl-modulelist->names mods))))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-simplify-part3 mods failmods safe-mode-p)))))))



(defsection vl-simplify-main

; Combines parts 1-3, but doesn't do the annotations.

  (defund vl-simplify-main (mods problem-mods omit-wires
                                 safe-mode-p unroll-limit)
    "Returns (MV MODS FAILMODS USE-SET-REPORT)"
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods))
                                (string-listp problem-mods)
                                (string-listp omit-wires)
                                (booleanp safe-mode-p)
                                (natp unroll-limit))))
    (b* (((mv mods failmods use-set-report)
          (vl-simplify-part1 mods problem-mods omit-wires))
         ((mv mods failmods)
          (vl-simplify-part2 mods failmods safe-mode-p (nfix unroll-limit)))
         ((mv mods failmods)
          (vl-simplify-part3 mods failmods safe-mode-p)))
        (mv mods failmods use-set-report)))

  (defmvtypes vl-simplify-main (true-listp true-listp nil))

  (local (in-theory (enable vl-simplify-main)))

  (defthm vl-modulelist-p-of-vl-simplify-main
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods))))
             (vl-modulelist-p
              (mv-nth 0 (vl-simplify-main mods problem-mods omit-wires
                                          safe-mode-p unroll-limit)))))

  (defthm vl-modulelist-p-of-vl-simplify-main-failmods
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods))))
             (vl-modulelist-p
              (mv-nth 1 (vl-simplify-main mods problem-mods omit-wires
                                          safe-mode-p unroll-limit)))))

  (defthm vl-useset-report-p-of-vl-simplify-main-report
    (implies (and (force (vl-modulelist-p mods))
                  (force (string-listp omit-wires)))
             (vl-useset-report-p
              (mv-nth 2 (vl-simplify-main mods problem-mods omit-wires
                                          safe-mode-p unroll-limit)))))

  (defthm no-duplicatesp-equal-of-vl-simplify-main
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods))))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-simplify-main mods problem-mods omit-wires
                                           safe-mode-p unroll-limit)))))))




(defsection vl-simplify
  :parents (vl)
  :short "Top level interface for simplifying Verilog modules."

  :long "<p><b>Signature:</b> @(call vl-simplify) returns <tt>(mv mods
failmods use-set-report)</tt>.</p>

<p>This is a high-level routine that applies our @(see transformations) in a
suitable order to simplify Verilog modules and to produce E modules.</p>

<h5>Inputs</h5>

<ul>

  <li>The <tt>mods</tt> are parsed Verilog modules, typically produced by
running @(see vl-load).</li>

  <li><tt>safe-mode-p</tt> is a Boolean which can be set to <tt>t</tt> to
enable any extra run-time checks that may help to catch problems, but which may
slow down simplification.</li>

  <li><tt>unroll-limit</tt> is a natural number that says the maximum number of
times to unroll any loop in statements.  We usually use 100.  It's mainly
intended to stop us from committing suicide by trying to unrolling a loops with
some ridiculous number of iterations.</li>

  <li><tt>problem-mods</tt> are any modules which should be thrown away
after parsing, perhaps because they cause problems later on.</li>

  <li><tt>omit-wires</tt> are the names of any wires to omit from the
use-set report.</li>

</ul>

<h5>Outputs</h5>

<ul>

  <li><tt>mods</tt> are the successfully loaded and simplified modules.</li>

  <li><tt>failmods</tt> are modules which were thrown out due to errors.</li>

  <li><tt>use-set-report</tt> is an @(see vl-useset-report-p) that includes
the use-set report for all of the modules.  BOZO consider integrating this
into each module itself.</li>

</ul>"

  (defund vl-simplify (mods problem-mods omit-wires
                            safe-mode-p unroll-limit)
    "Returns (MV MODS FAILMODS USE-SET-REPORT)"
    (declare (xargs :guard (and (vl-modulelist-p mods)
                                (uniquep (vl-modulelist->names mods))
                                (string-listp problem-mods)
                                (string-listp omit-wires)
                                (booleanp safe-mode-p)
                                (natp unroll-limit))))
    (vl-simplify-main (vl-annotate-mods mods)
                      problem-mods omit-wires
                      safe-mode-p unroll-limit))

  (defmvtypes vl-simplify (true-listp true-listp nil))

  (local (in-theory (enable vl-simplify)))

  (defthm vl-modulelist-p-of-vl-simplify-mods
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods))))
             (vl-modulelist-p
              (mv-nth 0 (vl-simplify mods problem-mods omit-wires
                                     safe-mode-p unroll-limit)))))

  (defthm vl-modulelist-p-of-vl-simplify-failmods
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods))))
             (vl-modulelist-p
              (mv-nth 1 (vl-simplify mods problem-mods omit-wires
                                     safe-mode-p unroll-limit)))))

  (defthm vl-useset-report-p-of-vl-simplify-report
    (implies (and (force (vl-modulelist-p mods))
                  (force (string-listp omit-wires)))
             (vl-useset-report-p
              (mv-nth 2 (vl-simplify mods problem-mods omit-wires
                                     safe-mode-p unroll-limit)))))

  (defthm no-duplicatesp-equal-of-vl-simplify
    (implies (and (force (vl-modulelist-p mods))
                  (force (uniquep (vl-modulelist->names mods))))
             (no-duplicatesp-equal
              (vl-modulelist->names
               (mv-nth 0 (vl-simplify mods problem-mods omit-wires
                                      safe-mode-p unroll-limit)))))))




(defsection defmodules
  :parents (vl)
  :short "High level command to load Verilog files, transform them, and
introduce the corresponding E modules."

  :long "<p>The <tt>defmodules</tt> macro allows you to load Verilog files into
your ACL2 session \"on the fly.\"</p>

<p>Defmodules is is the preferred way to load \"small\" Verilog modules for
one-off projects.  It is basically just a thin wrapper around @(see vl-load)
and @(see vl-simplify), but it usefully hides some of the complexity with good
default values, and ensures that all of the warnings generated during
simplification are printed for you to inspect.</p>


<h3>Using Defmodules</h3>

<p>The simplest case is that you want to load some \"self-contained\" Verilog
files.  The list of files to parse is given in the <tt>start-files</tt>
argument; these files will be parsed in the order they are given.</p>

<code>
 (defmodules *foo*
    :start-files (list \"foo_control.v\" \"foo_datapath.v\"))
</code>

<p>After submitting this event, E modules for all successfully translated
modules will be introduced, e.g., <tt>|*foo_control*|</tt>.  Additionally, the
constant <tt>*foo*</tt> will be defined as a @(see vl-translation-p) that
allows you to inspect the translation in other ways.</p>


<h4>Search Path</h4>

<p>Verilog files often rely on modules defined in other files.  You can add a
<tt>search-path</tt>, which is a list of directories that will be searched, in
order, for any modules that are used but not defined in the start-files; see
@(see vl-load-module) and @(see vl-flush-out-modules) for details.  For
example:</p>

<code>
 (defmodules foo
    :start-files (list \"foo_control.v\" \"foo_datapath.v\")
    :search-path (list \"/my/project/libs1\" \"/my/project/libs2\" ...))
</code>

<p>You can also specify an <tt>:override-dirs</tt> argument to \"safely\"
replace particular Verilog modules with custom definitions.  See @(see
overrides) for details on how to write override files.</p>


<h4>Start Modnames</h4>

<p>Instead of (or in addition to) explicitly providing <tt>start-files</tt>,
you can provide the names of some modules that you want to load from the search
path, e.g.,:</p>

<code>
 (defmodules foo
    :start-modnames (list \"foo_control\" \"foo_datapath\")
    :search-path (list \".\" \"/my/project/libs1\" \"/my/project/libs2\" ...))
</code>


<h4>Initial `defines</h4>

<p>The <tt>:defines</tt> option can be used to set up any extra
<tt>`define</tt> directives.  For instance, the following:</p>

<code>
 (defmodules foo
    :start-files (list \"foo_control.v\" \"foo_datapath.v\")
    :defines     (list \"FOO_BAR\" \"FOO_BAZ\"))
</code>

<p>is essentially like writing:</p>

<code>
`define FOO_BAR 1
`define FOO_BAZ 1
</code>

<p>at the top of your first start-file.  If you need more sophisticated
defines, you might add an extra start-file, instead.</p>


<h4>Advanced Options</h4>

<p>If some module causes errors that are not handled gracefully, you can mark
it as a <tt>:problem-module</tt> so that it will not be simplified.  For
instance,</p>

<code>
 (defmodules foo
    :start-files (list \"foo_control.v\" \"foo_datapath.v\")
    :problem-modules (list \"bad_module_1\" \"bad_module_2\"))
</code>

<p>The other options taken by @(see vl-simplify) and @(see vl-load) are given
sensible defaults that are not currently configurable.  We may add these
options in the future, as the need arises.</p>"

  (defund defmodules-fn (override-dirs start-files start-modnames
                                       search-path defines problem-modules state)
    "Returns (MV TRANS STATE)"
    (declare (xargs :guard (and (string-listp override-dirs)
                                (string-listp start-files)
                                (string-listp start-modnames)
                                (string-listp search-path)
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
                  (force (string-listp defines))
                  (force (string-listp problem-modules))
                  (force (state-p1 state)))
             (and
              (vl-translation-p
               (mv-nth 0 (defmodules-fn override-dirs start-files start-modnames
                           search-path defines problem-modules state)))
              (state-p1
               (mv-nth 1 (defmodules-fn override-dirs start-files start-modnames
                           search-path defines problem-modules state))))))

  (defund vl-modulelist-nonnil-emods (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (cond ((atom x)
           nil)
          ((vl-module->emod (car x))
           (cons (vl-module->emod (car x))
                 (vl-modulelist-nonnil-emods (cdr x))))
          (t
           (vl-modulelist-nonnil-emods (cdr x)))))

  (defmacro defmodules (name &key
                             override-dirs
                             start-files
                             start-modnames
                             search-path
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

           (defines ,defines)
           ((unless (string-listp defines))
            (er soft 'defmodules "Expected defines to be a string list."))

           (problem-modules ,problem-modules)
           ((unless (string-listp problem-modules))
            (er soft 'defmodules "Expected problem-modules to be a string list."))

           ((mv translation state)
            (cwtime (defmodules-fn override-dirs start-files start-modnames
                      search-path defines problem-modules state)
                    :name defmodules-fn))

           (emods (vl-modulelist-nonnil-emods
                   (vl-translation->mods translation))))

          (value
           `(with-output
             :off (summary)
             (progn (defconst ,name ',translation)
                    ,@emods
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





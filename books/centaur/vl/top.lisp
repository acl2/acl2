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
(include-book "transforms/xf-designwires")
(include-book "transforms/xf-delayredux")
(include-book "transforms/xf-drop-blankports")
(include-book "transforms/xf-elim-supply")
(include-book "transforms/xf-expand-functions")
(include-book "transforms/xf-expr-split")
(include-book "transforms/xf-follow-hids")
;; (include-book "transforms/xf-gateredux")
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
(include-book "simpconfig")
(include-book "centaur/misc/sneaky-load" :dir :system)
(local (include-book "mlib/modname-sets"))
(local (include-book "util/arithmetic"))
(local (include-book "util/osets"))
(local (include-book "system/f-put-global" :dir :system))
(local (in-theory (disable put-global)))

#||

; Fool the dependency scanner into certifying testing books as part
; of building top.cert

(include-book "loader/lexer/tests")
(include-book "loader/preprocessor/tests")

||#


;; These seemed to be slowing us down.  This reduced the certification
;; time from 324 to 101 seconds on 2010-01-19.
(local (in-theory (disable acl2::consp-under-iff-when-true-listp
                           mergesort
                           setp-of-vl-modulelist->names-when-no-duplicates)))

;; These aren't as big of a deal, but were able to cut it down to 82
;; seconds.  Actually, at this point almost everything is the cost of
;; including the books above.
(local (in-theory (disable string-listp
                           subsetp-equal-when-first-two-same-yada-yada
                           no-duplicatesp-equal
                           ;; No longer included after emod changes
                           ;; acl2::subsetp-implies-subsetp-cdr
                           true-listp)))



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


(define vl-simplify-part1-annotate-mods
  ((mods vl-modulelist-p)
   (config vl-simpconfig-p))
  :returns (new-mods vl-modulelist-p :hyp :fguard)
  (declare (ignorable config))

  (b* (;;this was never any good
       ;;mods (xf-cwtime (vl-modulelist-cross-active mods)
       ;;                :name xf-cross-active))

       (mods (xf-cwtime (vl-modulelist-lvaluecheck mods)
                        :name xf-lvaluecheck)))
    mods)

  ///
  (defthm vl-modulelist->names-of-vl-simplify-part1-annotate-mods
    (equal (vl-modulelist->names (vl-simplify-part1-annotate-mods mods config))
           (vl-modulelist->names mods))))



(define vl-simplify-part1-sanify-mods
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods))))
   (config vl-simpconfig-p))
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

  (b* (((vl-simpconfig config) config)
       (mods (xf-cwtime (vl-warn-problem-modulelist mods config.problem-mods)
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
               (mv-nth 0 (vl-simplify-part1-sanify-mods mods config)))))))



(define vl-simplify-part1
  ((mods   (and (vl-modulelist-p mods)
                (uniquep (vl-modulelist->names mods))))
   (config vl-simpconfig-p))
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

  (b* (((vl-simpconfig config) config)
       (- (cw "Beginning simplification of ~x0 modules.~%" (len mods)))

; We begin by trying to resolve argument lists and adding other basic
; annotations.  This is the minimum we need for use-set generation.  These
; transforms are quite robust and can deal with pretty much any constructs in
; the modules, so we don't need to eliminate the unreasonable modules and such
; first.  This is good, because it means the use-set report can span the entire
; list of modules, rather than just the reasonable ones.

       (mods (vl-simplify-part1-annotate-mods mods config))

; Use-Set report generation.  Even though argresolve can sometimes produce
; fatal warnings, the use-set report is intended to do as much as it can for
; all of the modules, so we want to go ahead with it before throwing anything
; away.

       ((mv mods use-set-report)
        (if config.use-set-p
            (xf-cwtime (vl-mark-wires-for-modulelist mods config.use-set-omit-wires)
                       :name use-set-analysis)
          (mv mods nil)))

; I'll eliminate functions before cleaning params, since we don't want to
; allow function parameters to overlap with module parameters.

       (mods (xf-cwtime (vl-modulelist-expand-functions mods)
                        :name xf-expand-functions))

       (mods
        (if config.clean-params-p
            (xf-cwtime (vl-modulelist-clean-params mods)
                       :name xf-clean-params)
          mods))

       ((mv mods failmods)
        (vl-simplify-part1-sanify-mods mods config))

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
               (mv-nth 0 (vl-simplify-part1 mods config)))))))



(define vl-simplify-part2
  ((mods         (and (vl-modulelist-p mods)
                      (uniquep (vl-modulelist->names mods))))
   (failmods     vl-modulelist-p)
   (config       vl-simpconfig-p))
  :returns (mv (mods vl-modulelist-p :hyp :fguard)
               (failmods vl-modulelist-p :hyp :fguard))
  :parents (vl-simplify)
  :short "Expression rewriting, sizing, splitting; instance replication,
assignment truncation, etc."

  (b* (((vl-simpconfig config) config)

; <<Previous safe-mode checks: :vl-modules :vl-unique-names :vl-complete
; :vl-reasonable :vl-always-known :vl-param-free>>

       (mods (xf-cwtime (vl-modulelist-rangeresolve mods)
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

       (mods (xf-cwtime (vl-modulelist-stmtrewrite mods config.unroll-limit)
                        :name xf-stmtrewrite))

;      (- (acl2::sneaky-save :pre-hid-elim mods))

       ;; (mods (xf-cwtime (vl-modulelist-hid-elim mods)
       ;;                  :name xf-hid-elim))

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

       ;; (mods (xf-cwtime (vl-modulelist-stmtrewrite mods config.unroll-limit)
       ;;                  :name xf-stmtrewrite))

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

       (mods
        (if config.multidrive-detect-p
            (xf-cwtime (vl-modulelist-multidrive-detect mods)
                       :name xf-multidrive-detect)
          mods))


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
                     (vl-simplify-part2 mods failmods config)))
                 (no-duplicatesp-equal (vl-modulelist->names mods))))))


(define vl-simplify-part3
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods))))
   (failmods vl-modulelist-p)
   (config   vl-simpconfig-p))
  :returns (mv (mods vl-modulelist-p :hyp :fguard)
               (failmods vl-modulelist-p :hyp :fguard))
  :parents (vl-simplify)
  :short "Occforming, gate simplification and splitting, naming blank
instances, supply elimination, dependency-order sorting, E translation."

  (declare (ignorable config))
  (b* (;((vl-simpconfig config) config)
       (mods (xf-cwtime (vl-modulelist-optimize mods)
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

       ;; Used to run gateredux to get rid of MOS/tran/bufif gates etc.  Now we
       ;; have primitives for them so they're taken care of by gate-elim.
       ;; (mods (xf-cwtime (vl-modulelist-gateredux mods)
       ;;                  :name xf-gateredux))

       ;; ((unless (uniquep (vl-modulelist->names mods)))
       ;;  (prog2$
       ;;   (er hard? 'vl-simplify-part3
       ;;       "Programming error: gateredux resulted in name clashes?")
       ;;   (mv nil nil)))


       ;; ((mv mods failmods) (xf-cwtime (vl-propagate-new-errors mods failmods)
       ;;                                :name propagate-errors))

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
                   (vl-simplify-part3 mods failmods config)))
               (no-duplicatesp-equal (vl-modulelist->names mods))))))


(define vl-simplify-main
  ((mods (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods))))
   (config vl-simpconfig-p))
  :returns (mv (mods :hyp :fguard
                     (and (vl-modulelist-p mods)
                          (no-duplicatesp-equal (vl-modulelist->names mods))))
               (failmods vl-modulelist-p :hyp :fguard)
               (use-set-report vl-useset-report-p :hyp :fguard))
  ;; Combines parts 1-3, but doesn't do the annotations.
  (b* (((mv mods failmods use-set-report)
        (vl-simplify-part1 mods config))
       ((mv mods failmods)
        (vl-simplify-part2 mods failmods config))
       ((mv mods failmods)
        (vl-simplify-part3 mods failmods config)))
    (mv mods failmods use-set-report))
  ///
  (defmvtypes vl-simplify-main (true-listp true-listp nil)))



(define vl-simplify
  ((mods "parsed Verilog modules, typically from @(see vl-load)."
         (and (vl-modulelist-p mods)
              (uniquep (vl-modulelist->names mods))))
   (config "various options that govern how to simplify the modules."
           vl-simpconfig-p))
  :guard-debug t
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

  (mbe :logic
       (b* (((mv mods failmods use-set-report)
             (vl-simplify-main (vl-annotate-mods mods) config)))
         (mv mods failmods use-set-report))
       :exec
       (b* (((vl-simpconfig config) config)
            (mods (vl-annotate-mods mods))
            (mods (if config.compress-p
                      (cwtime (hons-copy mods)
                              :name compress-annotated-mods)
                    mods))
            ((mv mods failmods use-set-report)
             (vl-simplify-main mods config))
            (mods (if config.compress-p
                      (cwtime (hons-copy mods)
                              :name compress-simplified-mods)
                    mods))
            (failmods (if config.compress-p
                          (cwtime (hons-copy failmods)
                                  :name compress-failed-mods)
                        failmods)))
         (vl-gc)
         (mv mods failmods use-set-report)))
  ///
  (defmvtypes vl-simplify (true-listp true-listp nil)))



(define defmodules-fn ((loadconfig vl-loadconfig-p)
                       (simpconfig vl-simpconfig-p)
                       &key
                       (state 'state))
  :returns (mv (trans vl-translation-p :hyp :fguard)
               (state state-p1         :hyp :fguard))
  :parents (defmodules)
  :short "Load and simplify some modules."

  (b* (((mv loadresult state)
        (cwtime (vl-load loadconfig)))

       ((vl-loadresult loadresult)
        (if (vl-simpconfig->compress-p simpconfig)
            (cwtime (change-vl-loadresult
                     loadresult :mods (hons-copy (vl-loadresult->mods loadresult)))
                    :name compress-original-mods)
          loadresult))

       ((mv mods failmods use-set-report)
        (cwtime (vl-simplify loadresult.mods simpconfig)))

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

       (result (make-vl-translation :mods          mods
                                    :failmods      failmods
                                    :origmods      loadresult.mods
                                    :filemap       loadresult.filemap
                                    :defines       loadresult.defines
                                    :loadwarnings  loadresult.warnings
                                    :useset-report use-set-report
                                    )))
    (mv result state)))




(defsection defmodules
  :parents (vl)
  :short "High level command to load Verilog files, transform them, and
generate the corresponding E modules."

  :long "<p>Note: if you are new to VL and are trying to load some Verilog
modules, you might want to start with the <i>Centaur Hardware Verification
Tutorial</i> located in @({ books/centaur/tutorial/intro.lisp }), which shows
some examples of using @('defmodules') and working with the resulting
translation.</p>

<p>The @('defmodules') macro allows you to load Verilog files into your ACL2
session \"on the fly.\"</p>

<p>General Form:</p>

@({
  (defmodules *name*         ;; a name for this translation
    loadconfig               ;; required, says which files to load
    [:simpconfig simpconfig] ;; optional, simplification options
})

<p>The required @('loadconfig') is @(see vl-loadconfig-p) that says which files
to load, which directories to search for modules in, etc.  For very simple
cases where you just want to load a few self-contained Verilog files, you can
just do something like this:</p>

@({
  (defmodules *foo*
    (make-vl-loadconfig
      :start-files (list \"foo_control.v\" \"foo_datapath.v\")))
})

<p>After submitting this event, @('*foo*') will be an ACL2 @(see defconst) that
holds a @(see vl-translation-p) object.  This object contains the parsed,
simplified Verilog modules, their corresponding E modules, etc.</p>

<p>The @(see vl-loadconfig-p) has many options for setting up include paths,
search paths, search extensions, initial @('`define') settings, etc.  For
instance, to parse a larger project that makes use of library modules, you
might need a command like:</p>

@({
 (defmodules *foo*
   (make-vl-loadconfig
     :start-files  (list \"foo_control.v\" \"foo_datapath.v\")
     :search-path  (list \"/my/project/libs1\" \"/my/project/libs2\" ...)
     :searchext    (list \"v\" \"V\")
     :include-dirs (list \"./foo_incs1\" \"./foo_incs2\")
     :defines      (vl-make-initial-defines '(\"NO_ASSERTS\" \"NEW_CLKTREE\"))))
})

<p>Aside from the load configuration, you can also control certain aspects of
how simplification is done with the @('simpconfig') option; see @(see
vl-simpconfig-p).  In many cases, the defaults will probably be fine.</p>"

  (defmacro defmodules (name loadconfig
                             &key
                             (simpconfig '*vl-default-simpconfig*))
    `(make-event
      (b* ((name ',name)
           (loadconfig ,loadconfig)
           (simpconfig ,simpconfig)
           ((mv translation state)
            (cwtime (defmodules-fn loadconfig simpconfig)
                    :name defmodules-fn)))
        (value
         `(with-output
            :off (summary event)
            (progn (defconst ,name ',translation)
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





; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

;; First part mostly copied from vl-simplify

(in-package "VL")
(include-book "moddb")
(include-book "centaur/vl/simpconfig" :dir :system)
(include-book "centaur/vl/util/gc" :dir :system)
(include-book "centaur/vl/transforms/eliminitial" :dir :system)
(include-book "centaur/vl/transforms/problem-mods" :dir :system)
(include-book "centaur/vl/transforms/unparam/top" :dir :system)
(include-book "centaur/vl/transforms/annotate/top" :dir :system)
(include-book "centaur/vl/transforms/addnames" :dir :system)
(include-book "centaur/vl/util/cw-unformatted" :dir :system)
(include-book "centaur/vl/mlib/print-warnings" :dir :system)
(include-book "centaur/vl/mlib/remove-bad" :dir :system)
(include-book "centaur/vl/lint/lvaluecheck" :dir :system)
(include-book "centaur/vl/transforms/cn-hooks" :dir :system)
(include-book "centaur/vl/transforms/clean-warnings" :dir :system)
(local (include-book "centaur/vl/mlib/design-meta" :dir :system))
(local (include-book "centaur/vl/util/arithmetic" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))

(local (xdoc::set-default-parents sv::vl-to-svex))

(define vl-simplify-sv
  :short "Core transformation sequence for using VL to generate SVEX modules."
  ((design vl-design-p)
   (config vl-simpconfig-p)
   ;; &key
   ;; delay-sensitivep
   )
  :returns (mv (good vl-design-p)
               (bad  vl-design-p))

  (b* (((vl-simpconfig config) config)
       (good (vl-design-fix design))
       (bad  (make-vl-design))

       (- (cw "Simplifying ~x0 modules.~%" (len (vl-design->mods good))))

; PART 1 --------------

       ;; Throw away problem modules before doing anything else.
       (good          (xf-cwtime (vl-design-problem-mods good config.problem-mods)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad config.suppress-fatal-warning-types)))

       ;; ((mv good ?use-set-report) (vl-simplify-maybe-use-set good config))

       ;; We eliminate functions before cleaning params, since we don't want to
       ;; allow function parameters to overlap with module parameters.
       ;; (good          (xf-cwtime (vl-design-expand-functions good)))
       ;; (good          (xf-cwtime (vl-design-clean-params good)))

       ;; BOZO is this something we actually want to do?  What's our philosophy
       ;; here toward warnings?
       (good          (xf-cwtime (vl-design-lvaluecheck good)))
       ;; (good          (xf-cwtime (vl-design-check-reasonable good)))
       ;; (good          (xf-cwtime (vl-design-check-complete good)))
       ;; (good          (xf-cwtime (vl-design-check-good-paramdecls good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad config.suppress-fatal-warning-types)))
       ;; We eliminate initial blocks early because they tend to have
       ;; constructs that we can't handle.
       (good          (xf-cwtime (vl-design-eliminitial good)))
       ;;(- (sneaky-save :pre-unparam good))
       (good          (xf-cwtime (vl-design-elaborate good config)))
       ;; (good          (xf-cwtime (vl-design-argresolve good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad config.suppress-fatal-warning-types)))


; PART 2 ----------------

       ;; (good           (xf-cwtime (vl-design-rangeresolve good)))
       ;; (good           (xf-cwtime (vl-design-selresolve good)))
       ;; ??? Some question about whether stmtrewrite is useful or not
       ;; (good           (xf-cwtime (vl-design-stmtrewrite good config.unroll-limit)))
       ;; (good           (xf-cwtime (vl-design-exprsize good)))
       ;; ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; (good           (xf-cwtime (vl-design-wildelim good)))
       ;; (good           (xf-cwtime (vl-design-caseelim good)))
       ;; ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; (good           (xf-cwtime (vl-design-elim-unused-regs good)))
       ;; (good           (xf-cwtime (vl-design-drop-blankports good)))


       ;; BOZO Do we need delayredux?  Hoping not.
       ;; (good           (xf-cwtime (vl-design-delayredux
       ;;                             good :vecp t
       ;;                             :state-onlyp (not delay-sensitivep))))


       ;; (good           (xf-cwtime (vl-design-split good)))
       ;; (good           (xf-cwtime (vl-design-replicate good)))
       ;; (good           (xf-cwtime (vl-design-blankargs good)))
       ;; (good           (xf-cwtime (vl-design-trunc good)))

       ;; ;; This might not be the best time to do this, but it seems like here
       ;; ;; we've got the widths figured out and there isn't too much serious
       ;; ;; stuff left to do.
       ;; (good           (vl-simplify-maybe-multidrive-detect good config))
       ;; ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

; PART 3 -----------------------

       ;; (good          (xf-cwtime (vl-design-optimize good)))
       ;; ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; (good          (xf-cwtime (vl-design-occform good)))
       ;; ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))
       ;; (- (vl-gc))

       ;; ;; Weirdint elim must come AFTER occform, to avoid screwing up Zmux stuff.
       ;; (good          (xf-cwtime (vl-design-weirdint-elim good)))
       ;; ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; (good          (xf-cwtime (vl-design-gatesplit good)))
       ;; (good          (xf-cwtime (vl-design-gate-elim good :primalist primalist)))
       ;; ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; (good          (xf-cwtime (vl-design-elim-supplies good)))
       ;; ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; Note: adding this here because one-bit selects from scalars make Verilog
       ;; simulators mad, and this gets rid of them... blah.
       ;; (good          (xf-cwtime (vl-design-optimize good)))

       ;; ;; This is just a useful place to add on any additional transforms you want
       ;; ;; before E generation.
       ;; (good          (xf-cwtime (vl-design-pre-toe-hook good)))
       ;; ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; (good          (xf-cwtime (vl-design-to-e good)))
       ;; ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good          (xf-cwtime (vl-design-clean-warnings good)))
       (bad           (xf-cwtime (vl-design-clean-warnings bad)))
       )

    (mv good bad))

  :prepwork
  (;; This is a pretty large definition.  We make special use of HIDE, which we
   ;; exploit using the rule vl-design-p-of-hide-meta.  See the documentation
   ;; there for more information.
   (defmacro vl-design-propagate-errors* (good bad suppress-fatals)
     `(vl-design-propagate-errors (hide ,good) (hide ,bad) ,suppress-fatals))
   (local (in-theory (disable (:executable-counterpart tau-system)
                              acl2::mv-nth-cons-meta)))
   (set-default-hints '('(:do-not '(preprocess))))))

(defmacro vl-simplify-svex (&rest args)
  `(vl-simplify-sv . ,args))
(add-macro-alias vl-simplify-svex vl-simplify-sv)

(define vl-to-sv-main ((topmods string-listp)
                         (x vl-design-p)
                         (config vl-simpconfig-p)
                         &key
                         (allow-bad-topmods 'nil)
                         (post-filter 't))
  :short "Turn a VL design into an SVEX hierarchical design, with a list of top modules."
  :guard-debug t
  :returns (mv err
               (modalist sv::modalist-p)
               (good vl-design-p)
               (bad vl-design-p))
  :prepwork ((local (in-theory (enable sv::modname-p))))
  (b* ((x (vl-design-fix x))
       ;; Annotate and simplify the design, to some extent.  This does
       ;; unparametrization and expr sizing, but not e.g. expr splitting or
       ;; occforming.
       (x (if (vl-simpconfig->already-annotated config)
              x
            (cwtime (vl-annotate-design x config))))
       ;; [Jared] I pulled addnames out of annotate because it interfered with
       ;; certain linter checks.  (In particular for detecting duplicate things
       ;; we don't really want to be adding names to unnamed blocks, etc.)
       (x (cwtime (vl-design-addnames x)))

       (x (cwtime (vl-remove-unnecessary-elements topmods x)))

       ((mv good bad) (cwtime (vl-simplify-sv x config)))
       ((vl-design good) good)
       (bad-mods (difference (mergesort topmods)
                             (mergesort (vl-modulelist->names good.mods))))
       ((when (and (not allow-bad-topmods)
                   bad-mods))
        (cw "Reportcard for good mods:~%")
        (cw-unformatted (vl-reportcard-to-string (vl-design-reportcard good)))
        (cw "Reportcard for bad mods:~%")
        (cw-unformatted (vl-reportcard-to-string (vl-design-reportcard bad)))
        (mv (msg "The following modules were not among the good simplified ~
                  modules: ~x0~%"
                 bad-mods)
            nil
            good bad))
       (good.mods (redundant-mergesort good.mods))
       ((unless (uniquep (vl-modulelist->names good.mods)))
        (mv (msg "Name clash -- duplicated module names: ~&0."
                 (duplicated-members (vl-modulelist->names good.mods)))
            nil
            good bad))
       (good1 (if post-filter
                  (vl-remove-unnecessary-elements topmods
                                                  (change-vl-design good :mods
                                                                    good.mods))
                (change-vl-design good :mods good.mods)))

       ;; Translate the VL module hierarchy into an isomorphic SVEX module hierarchy.
       ((mv reportcard modalist) (vl::xf-cwtime (vl-design->svex-modalist good1 :config config)))
       ;; The reportcard can't have any warnings about bad, because it's only being
       ;; generated from a subset of good.  So, just apply it to good.
       (good (vl-apply-reportcard good1 reportcard)))
    (cw "~%")
    (cw-unformatted "--- VL->SV Translation Report -------------------------------------------------")
    (cw "~%")
    (cw-unformatted (vl-reportcard-to-string reportcard))
    (and (vl-design->warnings good)
         (progn$ (cw "Warnings for the top-level design:~%")
                 (cw-unformatted (vl-warnings-to-string (vl-design->warnings good)))))
    (cw-unformatted
     "-------------------------------------------------------------------------------")
    (cw "~%~%")
    (and bad-mods
         (progn$ (cw "Reportcard for bad mods:~%")
                 (cw-unformatted (vl-reportcard-to-string (vl-design-reportcard
                                                           bad)))
                 (cw-unformatted
                  "-------------------------------------------------------------------------------")
                 (cw "~%~%")))
    (mv nil modalist good bad))
  ///
  (defret modalist-addr-p-of-vl-to-sv-main
    (sv::svarlist-addr-p (sv::modalist-vars modalist))))

(defmacro vl-to-svex-main (&rest args)
  `(vl-to-sv-main . ,args))
(add-macro-alias vl-to-svex-main vl-to-sv-main)

(define vl-design->sv-design ((topmod stringp)
                              (x vl-design-p)
                              (config vl-simpconfig-p))
  :short "Turn a VL design into an SVEX hierarchical design."
  :guard-debug t
  :returns (mv err
               (design sv::design-p)
               (good vl-design-p)
               (bad vl-design-p))
  :prepwork ((local (in-theory (enable sv::modname-p))))
  (b* (((mv err modalist good bad)
        (vl-to-sv-main (list topmod) x config))
       (design (sv::make-design :modalist modalist :top topmod)))
    (mv err design good bad))
  ///
  (defret modalist-addr-p-of-vl-design->sv-design
    (sv::svarlist-addr-p
     (sv::modalist-vars (sv::design->modalist design)))))


(defmacro vl-design->svex-design (&rest args)
  `(vl-design->sv-design . ,args))
(add-macro-alias vl-design->svex-design vl-design->sv-design)









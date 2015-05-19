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
;; (include-book "centaur/vl/transforms/always/top-svex" :dir :system)
(include-book "centaur/vl/transforms/addnames" :dir :system)
(include-book "centaur/vl/transforms/always/eliminitial" :dir :system)

;; (include-book "centaur/vl/transforms/assign-trunc" :dir :system)
;; (include-book "centaur/vl/transforms/blankargs" :dir :system)
;; (include-book "centaur/vl/transforms/clean-params" :dir :system)
;; (include-book "centaur/vl/transforms/delayredux" :dir :system)
;; (include-book "centaur/vl/transforms/drop-blankports" :dir :system)
;; (include-book "centaur/vl/transforms/expand-functions" :dir :system)
;; (include-book "centaur/vl/transforms/gatesplit" :dir :system)
;; (include-book "centaur/vl/transforms/gate-elim" :dir :system)
(include-book "centaur/vl/transforms/problem-mods" :dir :system)
;; (include-book "centaur/vl/transforms/replicate-insts" :dir :system)
;; (include-book "centaur/vl/transforms/resolve-ranges" :dir :system)
;; (include-book "centaur/vl/transforms/selresolve" :dir :system)
;; (include-book "centaur/vl/transforms/sizing" :dir :system)
(include-book "centaur/vl/transforms/unparam/top" :dir :system)
;; (include-book "centaur/vl/transforms/wildeq" :dir :system)
(include-book "centaur/vl/transforms/annotate/top" :dir :system)
(include-book "centaur/vl/transforms/annotate/port-resolve" :dir :system)
(include-book "centaur/vl/util/cw-unformatted" :dir :system)
(include-book "centaur/vl/mlib/print-warnings" :dir :system)
(include-book "centaur/vl/mlib/remove-bad" :dir :system)

;; (include-book "compile")
(local (include-book "centaur/vl/mlib/design-meta" :dir :system))
(local (include-book "centaur/vl/util/arithmetic" :dir :system))
(local (include-book "centaur/misc/arith-equivs" :dir :system))

(defxdoc vl-svex.lisp :parents (vl-design->svex-design))
(local (xdoc::set-default-parents vl-svex.lisp))

(define vl-simplify-svex
  :parents (svex)
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
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; ((mv good ?use-set-report) (vl-simplify-maybe-use-set good config))

       ;; We eliminate functions before cleaning params, since we don't want to
       ;; allow function parameters to overlap with module parameters.
       ;; (good          (xf-cwtime (vl-design-expand-functions good)))
       ;; (good          (xf-cwtime (vl-design-clean-params good)))

       (good          (xf-cwtime (vl-design-lvaluecheck good)))
       ;; (good          (xf-cwtime (vl-design-check-reasonable good)))
       ;; (good          (xf-cwtime (vl-design-check-complete good)))
       ;; (good          (xf-cwtime (vl-design-check-good-paramdecls good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))
       ;; We eliminate initial blocks early because they tend to have
       ;; constructs that we can't handle.
       (good          (xf-cwtime (vl-design-eliminitial good)))
       ;;(- (sneaky-save :pre-unparam good))
       (good          (xf-cwtime (vl-design-elaborate good)))
       (good          (xf-cwtime (vl-design-post-unparam-hook good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))


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
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

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
   (defmacro vl-design-propagate-errors* (good bad)
     `(vl-design-propagate-errors (hide ,good) (hide ,bad)))
   (local (in-theory (disable (:executable-counterpart tau-system)
                              acl2::mv-nth-cons-meta)))
   (set-default-hints '('(:do-not '(preprocess))))))

(define vl-annotate-svex ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (xf-cwtime (vl-design-resolve-ansi-portdecls x)
                     :name xf-resolve-ansi-portdecls))
       (x (xf-cwtime (vl-design-resolve-nonansi-interfaceports x)
                     :name xf-resolve-nonansi-interfaceports))
       (x (xf-cwtime (vl-design-add-enumname-declarations x)
                     :name xf-design-add-enumname-declarations))
       (x (xf-cwtime (vl-design-make-implicit-wires x)
                     :name xf-make-implicit-wires))
       (x (xf-cwtime (vl-design-portdecl-sign x)
                     :name xf-portdecl-sign))
       (x (xf-cwtime (vl-design-udp-elim x)
                     :name xf-udp-elim))
       (x (xf-cwtime (vl-design-portcheck x)
                     :name xf-portcheck))
       ;; (x (xf-cwtime (vl-design-designwires x)
       ;;               :name xf-mark-design-wires))
       (x (xf-cwtime (vl-design-argresolve x)
                     :name xf-argresolve))
       (x (xf-cwtime (vl-design-type-disambiguate x)
                     :name xf-type-disambiguate))
       (x (xf-cwtime (vl-design-addnames x)
                     :name xf-addnames))
       (x (xf-cwtime (vl-design-origexprs x)
                     :name xf-origexprs))
       (x (xf-cwtime (vl-design-clean-warnings x)
                     :name xf-clean-warnings)))
    x))


(define vl-design->svex-design ((topmod stringp)
                                (x vl-design-p)
                                (config vl-simpconfig-p))
  :parents (svex)
  :short "Turn a VL design into an SVEX hierarchical design."
  :guard-debug t
  :returns (mv err
               (design sv::design-p)
               (good vl-design-p)
               (bad vl-design-p))
  :prepwork ((local (in-theory (enable sv::modname-p))))
  (b* ((x (vl-design-fix x))
       (topmod (str::str-fix topmod))
       ;; Annotate and simplify the design, to some extent.  This does
       ;; unparametrization and expr sizing, but not e.g. expr splitting or
       ;; occforming.

       (x (vl-annotate-svex x))

       (x (vl-remove-unnecessary-elements (list topmod) x))

       ((mv good bad)
        (vl::xf-cwtime (vl-simplify-svex x config)))
       ((vl-design good) good)
       ((unless (vl-find-module topmod good.mods))
        (cw "Reportcard for good mods:~%")
        (cw-unformatted (vl-reportcard-to-string (vl-design-reportcard good)))
        (cw "Reportcard for bad mods:~%")
        (cw-unformatted (vl-reportcard-to-string (vl-design-reportcard bad)))
        (mv (msg "Top module ~s0 was not among the good simplified modules.~%" topmod)
            (sv::make-design :top topmod :modalist nil)
            good bad))
       (good.mods (redundant-mergesort good.mods))
       ((unless (uniquep (vl-modulelist->names good.mods)))
        (mv (msg "Name clash -- duplicated module names: ~&0."
                 (duplicated-members (vl-modulelist->names good.mods)))
            (sv::make-design :top topmod :modalist nil)
            good bad))
       (good1 (vl-remove-unnecessary-elements (list topmod)
                                              (change-vl-design good :mods good.mods)))

       ;; Translate the VL module hierarchy into an isomorphic SVEX module hierarchy.
       ((mv reportcard modalist) (vl::xf-cwtime (vl-design->svex-modalist good1))))
    (cw-unformatted (vl-reportcard-to-string reportcard))
    (mv nil
        (sv::make-design :modalist modalist :top topmod)
        good bad))
  ///
  (more-returns
   (design :name modalist-addr-p-of-vl-design->svex-design
           (sv::svarlist-addr-p
            (sv::modalist-vars (sv::design->modalist design))))))

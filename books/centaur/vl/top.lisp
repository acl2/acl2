; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "transforms/xf-problem-mods")
(include-book "transforms/xf-replicate-insts")
(include-book "transforms/xf-resolve-ranges")
(include-book "transforms/xf-selresolve")
(include-book "transforms/xf-sizing")
(include-book "transforms/xf-unparameterize")
(include-book "transforms/xf-unused-reg")
(include-book "transforms/xf-weirdint-elim")
(include-book "transforms/xf-annotate-mods")
(include-book "util/clean-alist")
(include-book "translation")
(include-book "simpconfig")
(include-book "wf-reasonable-p")
(include-book "centaur/misc/sneaky-load" :dir :system)
(local (include-book "mlib/modname-sets"))
(local (include-book "mlib/design-meta"))
(local (include-book "util/arithmetic"))
(local (include-book "util/osets"))
(local (include-book "system/f-put-global" :dir :system))
(local (in-theory (disable put-global)))

#||

; Fool the dependency scanner into certifying testing books as part
; of building top.cert

(include-book "loader/lexer/tests")
(include-book "loader/preprocessor/tests")
(include-book "loader/parser/tests/top")

||#

(define vl-simplify-maybe-use-set
  :parents (vl-simplify-main)
  :short "Wrapper to hide the case split for optional use-set analysis."
  ((design vl-design-p)
   (config vl-simpconfig-p))
  :returns (mv (new-design vl-design-p)
               (report     vl-useset-report-p))
  (b* (((vl-simpconfig config) config)
       ((unless config.use-set-p)
        (mv (vl-design-fix design) nil)))
    (xf-cwtime (vl-design-use-set-report design config.use-set-omit-wires))))

(define vl-simplify-maybe-clean-params
  :parents (vl-simplify-main)
  :short "Wrapper to hide the case split for optional clean-params."
  ((design vl-design-p)
   (config vl-simpconfig-p))
  :returns (new-design vl-design-p)
  (b* (((vl-simpconfig config) config)
       ((unless config.clean-params-p)
        (vl-design-fix design)))
    (xf-cwtime (vl-design-clean-params design))))

(define vl-simplify-maybe-multidrive-detect
  :parents (vl-simplify-main)
  :short "Wrapper to hide the case split for optional multidrive detection."
  ((design vl-design-p)
   (config vl-simpconfig-p))
  :returns (new-design vl-design-p)
  (b* (((vl-simpconfig config) config)
       ((unless config.multidrive-detect-p)
        (vl-design-fix design)))
    (xf-cwtime (vl-design-multidrive-detect design))))

(define vl-simplify-main
  :parents (vl-simplify)
  :short "Core transformation sequence for using VL to generate E modules."
  ((design vl-design-p)
   (config vl-simpconfig-p))
  :returns (mv (good vl-design-p)
               (bad  vl-design-p)
               (use-set-report vl-useset-report-p))

  (b* (((vl-simpconfig config) config)
       (good (vl-design-fix design))
       (bad  (make-vl-design))

       (- (cw "Simplifying ~x0 modules.~%" (len (vl-design->mods good))))

; PART 1 --------------

       ;; Throw away problem modules before doing anything else.
       (good          (xf-cwtime (vl-design-problem-mods good config.problem-mods)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; Optional use-set analysis.
       ((mv good use-set-report) (vl-simplify-maybe-use-set good config))

       ;; We eliminate functions before cleaning params, since we don't want to
       ;; allow function parameters to overlap with module parameters.
       (good          (xf-cwtime (vl-design-expand-functions good)))
       (good          (vl-simplify-maybe-clean-params good config))

       (good          (xf-cwtime (vl-design-lvaluecheck good)))
       (good          (xf-cwtime (vl-design-check-reasonable good)))
       (good          (xf-cwtime (vl-design-check-complete good)))
       (good          (xf-cwtime (vl-design-check-good-paramdecls good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;;(- (sneaky-save :pre-unparam good))
       (good          (xf-cwtime (vl-design-unparameterize good)))
       (good          (xf-cwtime (vl-design-post-unparam-hook good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))


; PART 2 ----------------

       (good           (xf-cwtime (vl-design-rangeresolve good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good           (xf-cwtime (vl-design-selresolve good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; BOZO this statement rewriting pass is likely not useful anymore.  It
       ;; was originally intended to help with HID reset elimination, which we
       ;; haven't done in years.
       (good           (xf-cwtime (vl-design-stmtrewrite good config.unroll-limit)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good           (xf-cwtime (vl-design-oprewrite good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good           (xf-cwtime (vl-design-exprsize good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good           (xf-cwtime (vl-design-always-backend good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good           (xf-cwtime (vl-design-elim-unused-regs good)))
       (good           (xf-cwtime (vl-design-drop-blankports good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good           (xf-cwtime (vl-design-delayredux good)))
       (good           (xf-cwtime (vl-design-split good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))
       (- (vl-gc))

       (good           (xf-cwtime (vl-design-replicate good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good           (xf-cwtime (vl-design-blankargs good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good           (xf-cwtime (vl-design-trunc good)))

       ;; This might not be the best time to do this, but it seems like here
       ;; we've got the widths figured out and there isn't too much serious
       ;; stuff left to do.
       (good           (vl-simplify-maybe-multidrive-detect good config))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

; PART 3 -----------------------

       (good          (xf-cwtime (vl-design-optimize good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good          (xf-cwtime (vl-design-occform good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))
       (- (vl-gc))

       ;; Weirdint elim must come AFTER occform, to avoid screwing up Zmux stuff.
       (good          (xf-cwtime (vl-design-weirdint-elim good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good          (xf-cwtime (vl-design-gatesplit good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good          (xf-cwtime (vl-design-gate-elim good)))
       (good          (xf-cwtime (vl-design-addinstnames good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good          (xf-cwtime (vl-design-elim-supplies good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       ;; Note: adding this here because one-bit selects from scalars make Verilog
       ;; simulators mad, and this gets rid of them... blah.
       (good          (xf-cwtime (vl-design-optimize good)))

       ;; This is just a useful place to add on any additional transforms you want
       ;; before E generation.
       (good          (xf-cwtime (vl-design-pre-toe-hook good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good          (xf-cwtime (vl-design-to-e good)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good          (xf-cwtime (vl-design-clean-warnings good)))
       (bad           (xf-cwtime (vl-design-clean-warnings bad)))
       )

    (mv good bad use-set-report))

  :prepwork
  (;; This is a pretty large definition.  We make special use of HIDE, which we
   ;; exploit using the rule vl-design-p-of-hide-meta.  See the documentation
   ;; there for more information.
   (defmacro vl-design-propagate-errors* (good bad)
     `(vl-design-propagate-errors (hide ,good) (hide ,bad)))
   (local (in-theory (disable (:executable-counterpart tau-system)
                              acl2::mv-nth-cons-meta)))
   (set-default-hints '('(:do-not '(preprocess))))))


(define vl-simplify
  :parents (vl)
  :short "Top level interface for simplifying Verilog modules for use in
          formal verification with @(see esim)."

  ((design "Parsed Verilog design, typically from @(see vl-load)."
           vl-design-p)

   (config "Various options that govern how to simplify the modules."
           vl-simpconfig-p))

  :returns
  (mv (good "Portion of the design that was simplified successfully."
            vl-design-p)
      (bad  "Portion of the design that was thrown out due to errors
             or unsupported constructs."
            vl-design-p)
      (use-set-report "A report about unused/unset wires."
                      vl-useset-report-p))
  (mbe :logic
       (b* (((mv good bad use-set-report)
             (vl-simplify-main (vl-annotate-design design) config)))
         (mv good bad use-set-report))
       :exec
       (b* (((vl-simpconfig config) config)
            (design (vl-annotate-design design))
            (design (if config.compress-p
                        (xf-cwtime (hons-copy design))
                      design))
            ((mv good bad use-set-report)
             (vl-simplify-main design config))
            (good (if config.compress-p
                      (xf-cwtime (hons-copy good))
                    good))
            (bad  (if config.compress-p
                      (xf-cwtime (hons-copy bad))
                    bad)))
         (vl-gc)
         (mv good bad use-set-report))))


(define defmodules-fn ((loadconfig vl-loadconfig-p)
                       (simpconfig vl-simpconfig-p)
                       &key
                       (state 'state))
  :returns (mv (trans vl-translation-p :hyp :fguard)
               (state state-p1         :hyp :fguard))
  :parents (defmodules)
  :short "Load and simplify some modules."

  (b* (((mv loadresult state)
        (xf-cwtime (vl-load loadconfig)))

       ((vl-loadresult loadresult)
        (if (vl-simpconfig->compress-p simpconfig)
            (xf-cwtime (hons-copy loadresult))
          loadresult))

       ((mv good bad use-set-report)
        (xf-cwtime (vl-simplify loadresult.design simpconfig)))

       (mods     (vl-design->mods good))
       (failmods (vl-design->mods bad))
       (walist   (vl-origname-modwarningalist
                  (append-without-guard mods failmods)))
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

       (result (make-vl-translation :good          good
                                    :bad           bad
                                    :orig          loadresult.design
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





; ESIM Symbolic Hardware Simulator
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
(include-book "translation")
(include-book "vltoe/top")
(include-book "occform/top")
(include-book "centaur/vl2014/loader/top" :dir :system)
(include-book "centaur/vl2014/lint/portcheck" :dir :system)
(include-book "centaur/vl2014/mlib/comment-writer" :dir :system)
(include-book "centaur/vl2014/transforms/annotate/top" :dir :system)
(include-book "centaur/vl2014/transforms/always/top" :dir :system)
(include-book "centaur/vl2014/transforms/unparam/top" :dir :system)
(include-book "centaur/vl2014/transforms/cn-hooks" :dir :system)
(include-book "centaur/vl2014/transforms/addinstnames" :dir :system)
(include-book "centaur/vl2014/transforms/assign-trunc" :dir :system)
(include-book "centaur/vl2014/transforms/blankargs" :dir :system)
(include-book "centaur/vl2014/transforms/clean-params" :dir :system)
(include-book "centaur/vl2014/transforms/delayredux" :dir :system)
(include-book "centaur/vl2014/transforms/drop-blankports" :dir :system)
(include-book "centaur/vl2014/transforms/elim-supply" :dir :system)
(include-book "centaur/vl2014/transforms/expand-functions" :dir :system)
(include-book "centaur/vl2014/transforms/expr-split" :dir :system)
(include-book "centaur/vl2014/transforms/gatesplit" :dir :system)
(include-book "centaur/vl2014/transforms/gate-elim" :dir :system)
(include-book "centaur/vl2014/transforms/oprewrite" :dir :system)
(include-book "centaur/vl2014/transforms/optimize-rw" :dir :system)
(include-book "centaur/vl2014/transforms/problem-mods" :dir :system)
(include-book "centaur/vl2014/transforms/replicate-insts" :dir :system)
(include-book "centaur/vl2014/transforms/resolve-ranges" :dir :system)
(include-book "centaur/vl2014/transforms/selresolve" :dir :system)
(include-book "centaur/vl2014/transforms/sizing" :dir :system)
(include-book "centaur/vl2014/transforms/unused-vars" :dir :system)
(include-book "centaur/vl2014/transforms/weirdint-elim" :dir :system)
(include-book "centaur/vl2014/transforms/wildeq" :dir :system)
(include-book "centaur/vl2014/util/clean-alist" :dir :system)
(include-book "centaur/vl2014/simpconfig" :dir :system)
(include-book "centaur/vl2014/wf-reasonable-p" :dir :system)
(include-book "centaur/misc/sneaky-load" :dir :system)
(local (include-book "centaur/vl2014/mlib/modname-sets" :dir :system))
(local (include-book "centaur/vl2014/mlib/design-meta" :dir :system))
(local (include-book "centaur/vl2014/util/arithmetic" :dir :system))
(local (include-book "centaur/vl2014/util/osets" :dir :system))
(local (include-book "system/f-put-global" :dir :system))
(local (in-theory (disable put-global)))

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

(define vl-simplify-main
  :parents (vl-simplify)
  :short "Core transformation sequence for using VL to generate E modules."
  ((design vl-design-p)
   (config vl-simpconfig-p))
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

       ;; We eliminate functions before cleaning params, since we don't want to
       ;; allow function parameters to overlap with module parameters.
       (good          (xf-cwtime (vl-design-expand-functions good)))
       (good          (vl-simplify-maybe-clean-params good config))

       (good          (xf-cwtime (vl-design-lvaluecheck good)))
       (good          (xf-cwtime (vl-design-check-reasonable good)))
       (good          (xf-cwtime (vl-design-check-complete good)))
       ;; (good          (xf-cwtime (vl-design-check-good-paramdecls good)))
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

       (good           (xf-cwtime (vl-design-wildelim good)))
       (good           (xf-cwtime (vl-design-always-backend good)))
       ((mv good bad)  (xf-cwtime (vl-design-propagate-errors* good bad)))

       (good           (xf-cwtime (vl-design-elim-unused-vars good)))
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

       ((mv good bad) (xf-cwtime (vl-design-to-e good bad)))
       ((mv good bad) (xf-cwtime (vl-design-propagate-errors* good bad)))

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


(define vl-simplify
  :parents (defmodules)
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
            vl-design-p))
  (mbe :logic
       (b* (((mv good bad)
             (vl-simplify-main (vl-annotate-design design) config)))
         (mv good bad))
       :exec
       (b* (((vl-simpconfig config) config)
            (design (vl-annotate-design design))
            (design (if config.compress-p
                        (xf-cwtime (hons-copy design))
                      design))
            ((mv good bad)
             (vl-simplify-main design config))
            (good (if config.compress-p
                      (xf-cwtime (hons-copy good))
                    good))
            (bad  (if config.compress-p
                      (xf-cwtime (hons-copy bad))
                    bad)))
         (vl-gc)
         (mv good bad))))


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

       ((mv good bad)
        (xf-cwtime (vl-simplify loadresult.design simpconfig)))

       (reportcard (vl-design-origname-reportcard good))
       (- (vl-cw-ps-seq
           (vl-cw "Successfully simplified ~x0 module~s1.~%"
                  (len (vl-design->mods good))
                  (if (vl-plural-p (vl-design->mods good)) "s" ""))
           (vl-println "")
           (vl-println "Warnings for successful modules:")
           (vl-print-reportcard reportcard)
           (vl-println "")))
       (- (fast-alist-free reportcard))

       (reportcard (vl-design-origname-reportcard bad))
       (failmods   (vl-design->mods bad))
       (- (vl-cw-ps-seq
           (if (atom failmods)
               ps
             (vl-ps-seq
              (vl-cw "Failed to simplify ~x0 module~s1: "
                     (len failmods)
                     (if (vl-plural-p failmods) "s" ""))
              (vl-print-strings-with-commas (vl-modulelist->names failmods) 4)
              (vl-println "")
              (vl-println "Warnings for failed descriptions:")
              (vl-print-reportcard reportcard)
              (vl-println "")))))
       (- (fast-alist-free reportcard))

       (result (make-vl-translation :good          good
                                    :bad           bad
                                    :orig          loadresult.design
                                    :filemap       loadresult.filemap
                                    :defines       loadresult.defines)))
    (mv result state)))


(defsection defmodules
  :parents (esim)
  :short "High level command to load Verilog files, transform them, and
generate the corresponding E modules."

  :long "<p>Note: if you are new to VL and are trying to load some Verilog
modules, you might want to start with the <i>ESIM Hardware Verification
Tutorial</i> located in @({ books/centaur/esim/tutorial/intro.lisp }), which
shows some examples of using @('defmodules') and working with the resulting
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







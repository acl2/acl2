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

#||
;before LDing this file:

;; name of directory that spec.sv and input/output.data are in
(defconst *testname* "gates")

(with-redef (defconst vl::*vl-shadowcheck-debug* t))

(trace$ #!VL (vl-shadowcheck-genelement
              :entry (list 'vl-shadowcheck-genelement
                           (with-local-ps (vl-pp-genelement x)))
              :exit (list 'vl-shadowcheck-genelement)))

(trace$ #!VL (vl-shadowcheck-genblock
              :entry (list 'vl-shadowcheck-genblock
                           :condnestp (vl-genblock->condnestp x)
                           :block (with-local-ps (vl-pp-genblock x)))
              :exit (list 'vl-shadowcheck-genblock)))


(trace$ #!VL
        (vl-genelement-make-implicit-wires
         :entry (list 'vl-genelement-make-implicit-wires
                      (with-local-ps (vl-pp-genelement x))
                      :imp (vl-vardecllist->names impitems))
         :exit (list 'vl-genelement-make-implicit-wires
                     (b* (((list ?new-warnings ?st ?new-x ?new-impitems) values))
                       (list (with-local-ps (vl-pp-genelement new-x))
                             :imp (vl-vardecllist->names new-impitems))))))

(vl::vl-trace-warnings)


(trace$ (vl-design-argresolve
         :entry (list 'vl-design-argresolve (with-local-ps (vl-pp-design x)))
         :exit (list 'vl-design-argresolve (with-local-ps (vl-pp-design x)))))

(trace$ (vl-unhierarchicalize-interfaceport
         :entry (list 'vl-unhierarchicalize-interfaceport
                      :arg (with-local-ps (vl-pp-plainarg arg))
                      :port (with-local-ps (vl-pp-port port))
                      :inst (with-local-ps (vl-pp-modinst inst nil)))
         :exit (b* (((list ?warnings new-arg) values))
                 (list 'vl-unhierarchicalize-interfaceport
                       (with-local-ps (vl-pp-plainarg new-arg))))))

||#

(in-package "SV")


(b* ((constval (fgetprop '*testname* 'acl2::const nil (w state)))
     ;; When testname is already bound don't do anything.
     ((when constval) (value 'testname-already-set))
     ;; When running non-interactively we read the cosim name from the
     ;; environment.  In this case, try to set up some sanity checking.  Note:
     ;; This used to be inside a defconsts form, which didn't work because
     ;; settings of ld-error-action made during make-event expansion don't
     ;; stick.  Fortunately this doesn't need to be a certifiable book so we
     ;; can do these outside make-event expansion.
     ((mv & & state) (acl2::set-ld-error-action '(:exit 1) state))
     ((mv & & state) (acl2::set-slow-alist-action :break)))
  (ld
   '((defconsts (*testname* state)
       (b* (((mv er val state) (getenv$ "COSIM_TESTDIR" state))
            (- (or val (raise "Empty COSIM_TESTDIR")))
            (- (and er (raise "Failed: ~@0" er))))
         (mv val state))))))

(defconsts (*svex-design* *orig-design* state)
  #!vl
  (vl-load-svex "spec"
                (make-vl-loadconfig
                 :start-files (list (cat sv::*testname* "/spec.sv"))
                 ;; See the Makefile, we provide +test_is_testname to support
                 ;; $test$plusargs testing.
                 :plusargs (list (cat "test_is_" sv::*testname*))
                 :defines
                 (b* (((mv warnings defines)
                       (vl-parse-cmdline-defines (list "test_define=3")
                                                 *vl-fakeloc*
                                                 t)))
                   (or (not warnings)
                       (raise "Oops, warnings in parsing cmdline defines?"))
                   defines))
                :simpconfig
                ;; for things like bigcase, work hard at unrolling loops
                (change-vl-simpconfig *vl-default-simpconfig*
                                      :sc-limit 20000)))

(assert! *svex-design*)

(defconsts (*input-lines* state)
  (b* ((twovalued-file (cat *testname* "/twovalued"))
       ((mv err twovaluedp state)
        (oslib::path-exists-p twovalued-file))
       (- (or (not err) (raise "~@0" err)))
       ((when twovaluedp)
        (acl2::read-file-lines "twovalued.data" state))
       (threevalued-file (cat *testname* "/threevalued"))
       ((mv err threevaluedp state)
        (oslib::path-exists-p threevalued-file))
       (- (or (not err) (raise "~@0" err)))
       ((when threevaluedp)
        (acl2::read-file-lines "threevalued.data" state)))
    (acl2::read-file-lines "fourvalued.data" state)))

(define skip-sv-implementation-p (ctx (fname stringp) (envname stringp) &optional (state 'state))
  (b* (((mv err exists state) (oslib::regular-file-p (str::cat *testname* "/" fname)))
       ((when err)
        (er hard? ctx "~@0~%" err)
        (mv t state))
       ((when exists) (mv t state))
       ((mv err val state) (getenv$ envname state))
       ((when err)
        (er hard? ctx "~@0~%" err)
        (mv nil state))
       ((when (Equal val "1"))
        (mv t state)))
    (mv nil state)))



(defconsts (*output-lines-ncv* state)
  (b* (((mv skip state) (skip-sv-implementation-p 'output-lines-ncv "no_ncv" "NO_NCV"))
       ((when skip) (mv nil state))
       ((mv lines state)
        (acl2::read-file-lines (str::cat *testname* "/outputs.ncv.data") state))
       ((when (stringp lines))
        ;; indicates error
        (er hard? 'output-lines-ncv "~@0" lines)
        (mv nil state))
       ((unless (eql (len lines) (len *input-lines*)))
        (er hard? 'output-lines-ncv "Wrong number of lines read: ~x0, expecting ~x1"
            (len lines) (len *input-lines*))
        (mv nil state)))
    (mv lines state)))
        

(defconsts (*output-lines-vcs* state)
  (b* (((mv skip state) (skip-sv-implementation-p 'output-lines-vcs "no_vcs" "NO_VCS"))
       ((when skip) (mv nil state))
       ((mv lines state)
        (acl2::read-file-lines (str::cat *testname* "/outputs.vcs.data") state))
       ((when (stringp lines))
        ;; indicates error
        (er hard? 'output-lines-vcs "~@0" lines)
        (mv nil state))
       ((unless (eql (len lines) (len *input-lines*)))
        (er hard? 'output-lines-vcs "Wrong number of lines read: ~x0, expecting ~x1"
            (len lines) (len *input-lines*))
        (mv nil state)))
    (mv lines state)))

(defun drop-comment-lines (lines)
  (if (atom lines)
      lines
    (if (equal (search "//" (car lines)) 0)
        (drop-comment-lines (cdr lines))
      (cons (car lines) (drop-comment-lines (cdr lines))))))

(defconsts (*output-lines-iv* state)
  (b* (((mv skip state) (skip-sv-implementation-p 'output-lines-iv "no_iv" "NO_IV"))
       ((when skip) (mv nil state))
       ((mv lines state)
        (acl2::read-file-lines (str::cat *testname* "/outputs.iv.data")
                               state))
       ((when (stringp lines))
        ;; indicates error -- but allow for now since iverilog is a new/optional feature
        ;; (er hard? 'output-lines-iv "~@0" lines)
        (mv nil state))
       (lines (drop-comment-lines lines))
       ((unless (eql (len lines) (len *input-lines*)))
        (er hard? 'output-lines-iv "Wrong number of lines read: ~x0, expecting ~x1"
            (len lines) (len *input-lines*))
        (mv nil state)))
    (mv lines state)))

(defconsts (*err* *updates* *nextstates* *constraints* *assigns* *delays* *flat-constraints* moddb aliases)
  (svex-design-compile *svex-design*))

(make-event
 (if *err*
     (raise "Error compiling: ~x0~%" *err*)
   '(value-triple :ok)))

;; (defstv impl-stv
;;   :mod *svex-design*
;;   :inputs `(("in" input))
;;   :outputs `(("out" output)))

(defconsts (*exactp* state)
  (b* (((mv err exists state) (oslib::regular-file-p (str::cat *testname* "/inexact")))
       ((when err)
        (er hard? 'exactp "~@0~%" err)
        (mv nil state)))
    (mv (not exists) state)))

(assert! (or (not *output-lines-ncv*)
             (cosims-compare *input-lines* *output-lines-ncv* *exactp* *updates* *nextstates*)))
(assert! (or (not *output-lines-vcs*)
             (cosims-compare *input-lines* *output-lines-vcs* *exactp* *updates* *nextstates*)))
(assert! (or (not *output-lines-iv*)
             (cosims-compare *input-lines* *output-lines-iv*  *exactp* *updates* *nextstates*)))

;; (assert! (or (not *output-lines-ncv*)
;;              (cosims-compare-stv *input-lines* *output-lines-ncv* *exactp* (impl-stv))))
;; (assert! (or (not *output-lines-vcs*)
;;              (cosims-compare-stv *input-lines* *output-lines-vcs* *exactp* (impl-stv))))



#||


(define vl::vl-cw-warning ((warning vl::vl-warning-p))
  (vl::with-local-ps
    (vl::vl-print-warning warning)))


(defmacro trace-parser (name)
  `(trace! (,(intern-in-package-of-symbol
              (cat (symbol-name name) "-FN") 'vl::vl-package)
            :entry (list ',name
                         (vl::vl-tokenlist->string-with-spaces
                          (take 5 (vl::vl-tokstream->tokens))))
            :exit (cons ',name
                        (let ((rest (vl::vl-tokenlist->string-with-spaces
                                     (take 5 (vl::vl-tokstream->tokens)))))
                          (if (car values)
                              (list (vl::vl-cw-warning (car values)) rest)
                            (list rest)))))))

#!VL
(trace$ (vl-design-elaborate
         :entry (with-local-ps (vl-pp-design x))
         :exit (with-local-ps (vl-pp-design value))))


#!VL
(trace$ (vl-inside-expr-case-to-svex
         :entry (list 'vl-inside-expr-case-to-svex
                      :elem elem
                      :elem-selfsize elem-selfsize
                      :elem-type elem-type
                      :range range)
         :exit (list 'vl-inside-expr-case-to-svex
                     (second values))))

#!VL
(trace$ (vl-inside-expr-cases-to-svex
         :entry (list 'vl-inside-expr-case-to-svex
                      :elem elem
                      :elem-selfsize elem-selfsize
                      :elem-type elem-type
                      :set set)
         :exit (list 'vl-inside-expr-case-to-svex
                     (second values))))

#!VL
(trace$ (vl-expr-to-svex-opaque
         :entry (list 'vl-expr-to-svex-opaque x)
         :exit (list 'vl-expr-to-svex-opaque (second values))))



||#

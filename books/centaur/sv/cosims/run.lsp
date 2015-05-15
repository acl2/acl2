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



||#

(in-package "SV")

(defconsts (*testname* state)
  (b* ((constval (fgetprop '*testname* 'acl2::const nil (w state)))
       ((when constval)
        ;; Make this event redundant if testname is already bound :)
        (mv (acl2::unquote constval) state))
       ((mv er val state) (getenv$ "COSIM_TESTDIR" state)))
    (and er (raise "Failed: ~@0" er))
    (mv val state)))


(defconsts (*svex-design* *orig-design* state)
  #!vl
  (vl-load-svex "spec"
                (make-vl-loadconfig
                 :start-files (list (cat sv::*testname* "/spec.sv")))))

(assert! *svex-design*)

(defconsts (*input-lines* state)
  (acl2::read-file-lines (str::cat *testname* "/inputs.data") state))

(defconsts (*output-lines-ncv* state)
  (b* (((mv err exists state) (oslib::regular-file-p (str::cat *testname* "/no_ncv")))
       ((when err)
        (er hard? 'output-lines-ncv "~@0~%" err)
        (mv nil state))
       ((when exists) (mv nil state)))
    (acl2::read-file-lines (str::cat *testname* "/outputs.ncv.data") state)))

(defconsts (*output-lines-vcs* state)
  (b* (((mv err exists state) (oslib::regular-file-p (str::cat *testname* "/no_vcs")))
       ((when err)
        (er hard? 'output-lines-vcs "~@0~%" err)
        (mv nil state))
       ((when exists) (mv nil state)))
    (acl2::read-file-lines (str::cat *testname* "/outputs.vcs.data") state)))

(defstv impl-stv
  :mod *svex-design*
  :inputs `(("in" input))
  :outputs `(("out" output)))

(defconsts (*exactp* state)
  (b* (((mv err exists state) (oslib::regular-file-p (str::cat *testname* "/inexact")))
       ((when err)
        (er hard? 'exactp "~@0~%" err)
        (mv nil state)))
    (mv (not exists) state)))

(assert! (or (not *output-lines-ncv*)
             (cosims-compare-stv *input-lines* *output-lines-ncv* *exactp* (impl-stv))))
(assert! (or (not *output-lines-vcs*)
             (cosims-compare-stv *input-lines* *output-lines-vcs* *exactp* (impl-stv))))



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

||#

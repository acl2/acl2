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
; Original author: Jared Davis <jared@centtech.com>


;; Debugging:
#||
$ fvq ../cosims/cosim-core

(in-package "VL")
(acl2::set-ld-error-action :continue state)
(defconst *testname* "inc1")              ;; Set up test name
(defconst *edition* :system-verilog-2012)
;; (defconst *edition* :verilog-2005)
||#

;; Else, not debugging:

(in-package "VL")
(acl2::set-ld-error-action '(:exit 1) state)
(defconsts (*testname* *edition* state)
  ;; Read testname/edition from environment, unless they've been defined above
  ;; for debugging.
  (b* ((testname (fgetprop '*testname* 'acl2::const nil (w state)))
       ((mv testname state)
        (b* (((when testname)
              (mv (acl2::unquote testname) state))
             ((mv er testname state) (getenv$ "TESTNAME" state))
             (- (or (not er) (raise "Failed: ~@0" er))))
          (mv testname state)))
       (- (or (stringp testname)
              (raise "Testname not a string? ~x0~%" testname)))

       (edition (fgetprop '*edition* 'acl2::const nil (w state)))
       ((mv edition state)
        (b* (((when edition)
              (mv (acl2::unquote edition) state))
             ((mv er edition state) (getenv$ "EDITION" state))
             (- (or (not er) (raise "Failed: ~@0" er)))
             (- (or (stringp edition) (raise "Edition not a string? ~x0~%" edition))))
          (mv (intern$ edition "KEYWORD") state)))
       (- (or (vl::vl-edition-p edition)
              (raise "Invalid verilog edition: ~x0~%" edition))))
    (mv testname edition state)))

(define write-passed-file ((testname stringp)
                           (edition  vl-edition-p)
                           &key
                           (state 'state))
  :returns state
  (b* ((suffix (case edition
                 (:verilog-2005        "vok")
                 (:system-verilog-2012 "svok")
                 (otherwise            (progn$ (impossible) "v??ok"))))
       (filename (cat testname "." suffix)))
    (cw "Writing OK file: ~x0~%" filename)
    (with-ps-file filename
      (vl-cw "Test ~x0 successfully marked as failure.~%" testname))))

(define vl-do-failtest ((testname stringp)
                        (edition vl-edition-p)
                        &key
                        (state 'state))
  :returns (mv (okp booleanp)
               (good vl-design-p)
               (bad  vl-design-p)
               state)
  (b* ((loadconfig (make-vl-loadconfig
                    :start-files (list (cat testname ".v"))
                    :edition edition))
       ((mv loadresult state) (vl-load loadconfig))
       (design (vl-loadresult->design loadresult))
       ((mv err ?svex-design good bad)
        (vl-design->svex-design "top" design *vl-default-simpconfig*))
       (- (cw "Module names (good): ~x0~%" (vl-modulelist->names (vl-design->mods good))))
       (- (cw "Module names (bad): ~x0~%" (vl-modulelist->names (vl-design->mods bad))))
       (- (cw "Reportcard for good mods:~%"))
       (- (cw-unformatted (vl-reportcard-to-string (vl-design-reportcard good))))
       (- (cw "Reportcard for bad mods:~%"))
       (- (cw-unformatted (vl-reportcard-to-string (vl-design-reportcard bad))))
       ((when err)
        (cw "~%+++Status: GOOD: Successfully failed with clear error+++~%")
        (cw "~@0~%~%" err)
        (let ((state (write-passed-file testname edition)))
          (mv t good bad state)))
       ;; For some warnings (like bind errors) it's probably necessary to check for
       ;; fatal floating warnings.
       ((when (or (vl-some-warning-fatalp (vl-design->warnings good) nil)
                  (vl-some-warning-fatalp (vl-design->warnings bad) nil)))
        (cw "~%+++Status: GOOD: No clear error but design has fatal floating warnings. +++~%~%")
        (let ((state (write-passed-file testname edition)))
          (mv t good bad state)))
       ;; Otherwise let's check to make sure that at least there is a fatal warning
       ;; in the top module.
       (mod (vl-find-module "top" (vl-design->mods good)))
       ((unless mod)
        (cw "~%+++Status: WEIRD: No clear error but didn't find top in good or bad? +++~%~%")
        (mv nil good bad state))
       (fatalp (vl-some-warning-fatalp (vl-module->warnings mod) nil))
       ((when fatalp)
        (cw "~%+++Status: GOOD: No clear error but top has fatal warnings. +++~%~%")
        (let ((state (write-passed-file testname edition)))
          (mv t good bad state))))
    (cw "~%+++Status: BAD: Failed to fail!  No clear error, top has no fatal warnings.+++~%~%")
    (mv nil good bad state)))

(defconsts (*passedp* *good* *bad* state)
  (vl-do-failtest *testname* *edition*))

(if *passedp*
    (exit 0)
  (exit 1))


#||
;; For debugging:

(defconst *top*
  (vl-find-module "top" (vl-design->mods *good*)))

(vl-module->warnings *top*)

(vl-design-reportcard *good*)

||#

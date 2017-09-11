; XDOC Documentation System for ACL2
; Copyright (C) 2009-2015 Centaur Technology
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

(in-package "ACL2")

(defun unsound-eval-fn (sexpr state)
  (unless (live-state-p state)
    ;; I think we don't want to trap this one; if we get called in logic mode
    ;; on a fake state, we really should cause an error.
    (error "Unsound-eval requires a live state."))
  (handler-case
   (b* (#+lispworks
        ;; (Mod by Matt K., 12/2013:)
        ;; LispWorks 6.1.1 has a bug that can prevent catching stack overflow
        ;; errors when system::*stack-overflow-behaviour* is nil, as it is in
        ;; ACL2.  We work around that bug as follows.
        (system::*stack-overflow-behaviour* t)
        ((mv err val state)
         ;; This with-guard-checking form seems necessary because otherwise, it
         ;; seems, trans-eval will just do whatever the default guard checking
         ;; mode is.  And, in some make-events, it appears that guard checking
         ;; gets disabled somehow.
         (with-guard-checking-error-triple
          t

; Matt K. mod, 9/8/2017: replacing trans-eval by the trans-eval-no-warning, to
; avoid the new "User-stobjs-modified" warnings.  Suppressing such warnings
; seems in the spirit of unsound-eval.

          (trans-eval-no-warning sexpr 'unsound-eval state t)))
        ((when err)
         (mv (msg "Failed to evaluate ~x0; trans eval failed? ~x1." sexpr err)
             nil state))
        ((unless (and (consp val)
                      (true-listp (car val))))
         (mv (msg "Failed to evaluate ~x0; trans-eval returned unexpected value ~x1." sexpr val)
             nil state))
        (stobjs-out  (car val))
        (num-returns (length stobjs-out))
        ((unless (posp num-returns))
         (mv (msg "Failed to evaluate ~x0; trans-eval returned malformed stobjs-out ~x1."
                  sexpr stobjs-out)
             nil state))
        ;; Trans-eval has a really weird interface.  In the singleton return
        ;; value case, it doesn't seem to wrap the return values in a list...
        (return-vals (if (eql num-returns 1)
                         (list (cdr val))
                       (cdr val)))
        ((unless (equal (len return-vals)
                        (len stobjs-out)))
         (mv (msg "Failed to evaluate ~x0; trans-eval returned incoherent return values ~x1."
                  (list :stobjs-out stobjs-out
                        :return-vals return-vals))
             nil state)))
     (mv nil (unsound-eval-elide stobjs-out return-vals) state))
   (error
    (condition)
    (let ((condition-str (format nil "~S" condition)))
      (mv (msg "Failed to evaluate ~x0; ~s1" sexpr condition-str)
          nil state)))
   (storage-condition
    (condition)
    (let ((condition-str (format nil "~S" condition)))
      (mv (msg "Failed to evaluate ~x0; ~s1" sexpr condition-str)
          nil state)))))

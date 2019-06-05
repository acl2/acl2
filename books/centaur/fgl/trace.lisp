; GL - A Symbolic Simulation Framework for ACL2
; Copyright (C) 2019 Centaur Technology
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

(in-package "FGL")

(include-book "interp-st")




(encapsulate
  (((gl-rewrite-try-rule-trace * * * * interp-st state) => interp-st
    :formals (status rule fn args interp-st state)
    :guard t))

  (set-ignore-ok t)
  (set-irrelevant-formals-ok t)
  (local (defun gl-rewrite-try-rule-trace (status rule fn args interp-st state)
           (declare (xargs :stobjs (interp-st state)))
           interp-st))

  (defthm interp-st-get-of-gl-rewrite-try-rule-trace
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key (gl-rewrite-try-rule-trace status rule fn args interp-st state))
                    (interp-st-get key interp-st)))))

(define gl-rewrite-try-rule-trace-wrapper (trace status rule fn args interp-st state)
  :inline t
  (if trace
      (gl-rewrite-try-rule-trace status rule fn args interp-st state)
    interp-st)
  ///
  (defthm interp-st-get-of-gl-rewrite-try-rule-trace-wrapper
    (implies (not (equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key (gl-rewrite-try-rule-trace-wrapper
                                        trace status rule fn args interp-st state))
                    (interp-st-get key interp-st)))))


(define gl-rewrite-rule-try-trace-default (status rule fn args interp-st state)
  :returns new-interp-st
  (b* ((rule-alist (and (boundp-global :fgl-trace-rule-alist state)
                        (@ :fgl-trace-rule-alist)))
       ((unless (and (consp rule)
                     (consp (cdr rule))
                     (alistp rule-alist)))
        ;; needed to access the rune
        (prog2$ (cw "bad rule~%")
                interp-st))
       (rune (cadr rule))
       (look (assoc-equal rune rule-alist))
       ((unless look)
        interp-st)
       (depth (nfix (interp-st->trace-scratch interp-st)))
       (evisc-tuple (and (boundp-global :fgl-trace-evisc-tuple state)
                         (@ :fgl-trace-evisc-tuple))))
    (case-match status
      (':start
       (prog2$ (fmt-to-comment-window
                "~t0~x1> ~x2 ~x3~%"
                (pairlis2 acl2::*base-10-chars* (list depth depth rune (cons fn args)))
                0 evisc-tuple nil)
               (update-interp-st->trace-scratch (1+ depth) interp-st)))
      ((':hyps . failed-hyp)
       (b* ((errmsg (interp-st->errmsg interp-st))
            ((when errmsg)
             (fmt-to-comment-window
              "~t0<~x1 ~x2 failed (error in hyps: ~@3)~%"
              (pairlis2 acl2::*base-10-chars* (list (1- depth) (1- depth) rune
                                                    (if (msgp errmsg)
                                                        errmsg
                                                      (msg "~x0" errmsg))))
              0 evisc-tuple nil)
             (update-interp-st->trace-scratch (1- depth) interp-st))
            ((when failed-hyp)
             (fmt-to-comment-window
              "~t0<~x1 ~x2 failed (hyp ~x3)~%"
              (pairlis2 acl2::*base-10-chars* (list (1- depth) depth rune failed-hyp))
              0 evisc-tuple nil)
             (update-interp-st->trace-scratch (1- depth) interp-st)))
         interp-st))
      ((':finish . val)
       (b* ((errmsg (interp-st->errmsg interp-st))
            ((when errmsg)
             (fmt-to-comment-window
              "~t0<~x1 ~x2 failed (error: ~@3)~%"
              (pairlis2 acl2::*base-10-chars* (list (1- depth) (1- depth) rune
                                                    (if (msgp errmsg)
                                                        errmsg
                                                      (msg "~x0" errmsg))))
              0 evisc-tuple nil)
             (update-interp-st->trace-scratch (1- depth) interp-st)))
         (fmt-to-comment-window
          "~t0<~x1 ~x2 success: ~x3~%"
          (pairlis2 acl2::*base-10-chars* (list (1- depth) (1- depth) rune val))
          0 evisc-tuple nil)
         (update-interp-st->trace-scratch (1- depth) interp-st)))
      (& (prog2$ (cw "bad status: ~x0~%" status)
                 interp-st))))
  ///
  (defret interp-st-get-of-<fn>
    (implies (not (Equal (interp-st-field-fix key) :trace-scratch))
             (equal (interp-st-get key new-interp-st)
                    (interp-st-get key interp-st)))))

(defattach gl-rewrite-try-rule-trace gl-rewrite-rule-try-trace-default)

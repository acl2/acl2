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

(in-package "SV")
(include-book "rewrite-base")
(include-book "centaur/misc/sneaky-load" :dir :system)

;; We make this a separate book since sneaky-load requires ttags.

(define svex-rewrite-trace-rule (rule mask args localp rhs subst)
  :parents (rewriter-tracing)
  :short "Trace individual rewrite rules, printing to @(see cw)."
  :long "@({
 (defattach svex-rewrite-trace svex-rewrite-trace-rule)    ;; turn on tracing
 (defattach svex-rewrite-trace svex-rewrite-trace-default) ;; turn off tracing
 })"
  :ignore-ok t
  :irrelevant-formals-ok t
  (cw "Rule: ~x0~%" rule))

(define svex-sneaky-prof-mutator ((val consp) (name-localp consp))
  :parents (svex-rewrite-trace-profile)
  :short "<p>A @(see acl2::sneaky) mutator for profiling.</p>"
  (b* ((val (car val))
       ((mv nonloc loc) (if (consp val) (mv (car val) (cdr val)) (mv nil nil))))
    (list (cons (car name-localp)
                (if (cdr name-localp)
                    (cons nonloc (+ 1 (fix loc)))
                  (cons (+ 1 (fix nonloc)) loc))))))

(define svex-rewrite-trace-profile (rule mask args localp rhs subst)
  :parents (rewriter-tracing)
  :short "Profile the number of applications of rewrite rules."
  :long "<p>This is incredibly primitive; you can surely do better if you spend
any time to improve it.</p>

@({
     (defattach svex-rewrite-trace svex-rewrite-trace-profile)
     ;; do rewriting
     (sneaky-alist state)  ;; see results
     (sneaky-clear)        ;; clear data

     (defattach svex-rewrite-trace svex-rewrite-trace-default) ;; stop profiling
})"

  :ignore-ok t
  :irrelevant-formals-ok t
  (acl2::sneaky-mutate 'svex-sneaky-prof-mutator (list rule) (cons rule localp)))

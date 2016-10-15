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
(include-book "svex")
(local (include-book "clause-processors/just-expand" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (std::add-default-post-define-hook :fix))

;; A context-alist maps svexes to contexts in which they occur.  A context is
;; either :top or a pair consisting of the function and arglist of an svex call and an
;; argument number.

(fty::deftagsum svex-context
  :short "An object that describes a reference to a particular svex subexpression."
  (:call ((argnum natp)
          (fn fnsym-p)
          (args svexlist-p))
   :layout :tree
   :short "Represents a use of a subexpression in a call.  Contains the
function and arguments of the call, and the argument number of the particular
subexpression in question.")
  (:top  nil
   :short "Represents a use of a particular subexpression as a primary output,
or something top-level."))

(fty::deflist svex-contextlist :elt-type svex-context)

(fty::defalist svex-context-alist :key-type svex :val-type svex-contextlist)

;; Make a context alist for an svex.
(defines svex-make-context-alist
  (define svex-make-context-alist ((x svex-p)
                                   (ctx svex-context-p)
                                   (acc svex-context-alist-p))
    :returns (alist svex-context-alist-p)
    :measure (svex-count x)
    :verify-guards nil
    (b* ((acc (svex-context-alist-fix acc))
         (x (svex-fix x))
         (look (cdr (hons-get x acc)))
         (new-val (cons (svex-context-fix ctx) look))
         (acc (hons-acons x new-val acc))
         ((when (consp look))
          ;; already traversed x -- done.
          acc))
      (svex-case x
        :call (svex-args-make-context-alist x.args 0 x.fn x.args acc)
        :otherwise acc)))
  (define svex-args-make-context-alist ((x svexlist-p)
                                        (argnum natp)
                                        (fn fnsym-p)
                                        (args svexlist-p)
                                        (acc svex-context-alist-p))
    :returns (alist svex-context-alist-p)
    :measure (svexlist-count x)
    (b* (((when (atom x)) (svex-context-alist-fix acc))
         (acc (svex-make-context-alist (car x)
                                       (make-svex-context-call
                                        :argnum argnum
                                        :fn fn
                                        :args args)
                                       acc)))
      (svex-args-make-context-alist (cdr x) (1+ (lnfix argnum)) fn args acc)))
  ///
  (verify-guards svex-make-context-alist :guard-debug t)
  (deffixequiv-mutual svex-make-context-alist))

(define svexlist-make-top-context-alist ((x svexlist-p)
                                         (acc svex-context-alist-p))
  :returns (alist svex-context-alist-p)
  :prepwork ((local (in-theory (enable fast-alist-clean)))
             (local (defthm atom-of-cdr-last
                      (not (consp (cdr (last x)))))))
  (if (atom x)
      (fast-alist-clean (svex-context-alist-fix acc))
    (svexlist-make-top-context-alist
     (cdr x) (svex-make-context-alist (car x) (make-svex-context-top) acc))))



; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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

(in-package "VL")
(include-book "../mlib/modnamespace")
(include-book "../mlib/expr-tools")
(local (include-book "../util/arithmetic"))

(defsection portcheck
  :parents (lint)
  :short "Trivial check to make sure that each module's ports agree with its
  port declarations.")

(local (xdoc::set-default-parents portcheck))

(define vl-collect-regular-ports-exec ((x vl-portlist-p) nrev)
  :parents (vl-collect-regular-ports)
  (b* (((when (atom x))
        (nrev-fix nrev))
       (x1 (vl-port-fix (car x)))
       ((when (eq (tag x1) :vl-regularport))
        (b* ((nrev (nrev-push x1 nrev)))
          (vl-collect-regular-ports-exec (cdr x) nrev))))
    (vl-collect-regular-ports-exec (cdr x) nrev)))

(define vl-collect-regular-ports
  :parents (vl-portlist-p)
  :short "Filter a @(see vl-portlist-p) to collect only the regular ports."
  ((x vl-portlist-p))
  :returns (ifports (and (vl-portlist-p ifports)
                         (vl-regularportlist-p ifports)))
  :verify-guards nil
  (mbe :logic
       (b* (((when (atom x))
             nil)
            (x1 (vl-port-fix (car x)))
            ((when (eq (tag x1) :vl-regularport))
             (cons x1 (vl-collect-regular-ports (cdr x)))))
         (vl-collect-regular-ports (cdr x)))
       :exec
       (with-local-nrev
         (vl-collect-regular-ports-exec x nrev)))
  ///
  (defthm vl-collect-regular-ports-exec-removal
    (equal (vl-collect-regular-ports-exec x nrev)
           (append nrev (vl-collect-regular-ports x)))
    :hints(("Goal" :in-theory (enable vl-collect-regular-ports-exec))))

  (verify-guards vl-collect-regular-ports)

  (defthm vl-collect-regular-ports-when-atom
    (implies (atom x)
             (equal (vl-collect-regular-ports x)
                    nil)))

  (defthm vl-collect-regular-ports-of-cons
    (equal (vl-collect-regular-ports (cons a x))
           (if (eq (tag (vl-port-fix a)) :vl-regularport)
               (cons (vl-port-fix a)
                     (vl-collect-regular-ports x))
             (vl-collect-regular-ports x)))))

(defprojection vl-regularportlist->exprs ((x vl-regularportlist-p))
  :parents (vl-portlist-p)
  :nil-preservingp t
  (vl-regularport->expr x)
  ///
  (defthm vl-exprlist-p-of-vl-regularportlist->exprs
    (equal (vl-exprlist-p (vl-regularportlist->exprs x))
           (not (member nil (vl-regularportlist->exprs x)))))

  (defthm vl-exprlist-p-of-remove-equal-of-vl-regularportlist->exprs
    (vl-exprlist-p (remove-equal nil (vl-regularportlist->exprs x)))))


(define vl-module-portcheck ((x vl-module-p))
  :returns (new-x vl-module-p :hyp :fguard
                  "New version of @('x'), with at most some added warnings.")
  (b* (((vl-module x) x)
       (decl-names (mergesort (vl-portdecllist->names x.portdecls)))
       (port-names (mergesort
                    (vl-exprlist-names
                     (remove nil
                             (vl-regularportlist->exprs
                              (vl-collect-regular-ports x.ports))))))
       ((unless (subset decl-names port-names))
        (b* ((w (make-vl-warning
                 :type :vl-port-mismatch
                 :msg "Port declarations for non-ports: ~&0."
                 :args (list (difference decl-names port-names))
                 :fatalp t
                 :fn 'vl-check-ports-agree-with-portdecls)))
          (change-vl-module x :warnings (cons w x.warnings))))

       ((unless (subset port-names decl-names))
        (b* ((w (make-vl-warning
                 :type :vl-port-mismatch
                 :msg "Missing port declarations for ~&0."
                 :args (list (difference port-names decl-names))
                 :fatalp t
                 :fn 'vl-check-ports-agree-with-portdecls)))
          (change-vl-module x :warnings (cons w x.warnings)))))
    x))

(defprojection vl-modulelist-portcheck (x)
  (vl-module-portcheck x)
  :parents (portcheck)
  :guard (vl-modulelist-p x)
  :result-type vl-modulelist-p)

(define vl-design-portcheck
  :short "Top-level @(see portcheck) check."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* ((x (vl-design-fix x))
       ((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-portcheck x.mods))))


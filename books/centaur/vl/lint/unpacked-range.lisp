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
(include-book "../mlib/ctxexprs")
(include-book "../../sv/vl/expr")
(local (include-book "../util/arithmetic"))


(defsection unpacked-range-check
  :parents (vl-lint)
  :short "Warn about partselects on unpacked arrays."

  :long "<p>Some tools don't deal well with idioms like the following:</p>

@({
 logic [width-1:0] to [height];
 logic [width-1:0] from [height+4];
 
 assign to = from[2+=height];
 })

<p>That is, they don't handle partselects across unpacked arrays. This warns
about expressions that contain such constructs.</p>")



(define vl-indexexpr-unpacked-range-check ((x vl-expr-p)
                                           (ss vl-scopestack-p)
                                           (scopes vl-elabscopes-p))
  :guard (vl-expr-case x :vl-index)
  :returns (warnings (and (vl-warninglist-p warnings)
                          (true-listp warnings)))
  (b* (((vl-index x))
       ((when (vl-partselect-case x.part :none)) nil)
       ((mv err opinfo) (vl-index-expr-typetrace x ss scopes))
       ((when err) nil)
       ((vl-operandinfo opinfo))
       ((unless (consp (vl-datatype->udims opinfo.type)))))
    (list (make-vl-warning :type :vl-unpacked-range
                           :msg "The expression ~a0 is a partselect across an ~
                                 unpacked array, which is not supported by ~
                                 some tools."
                           :args (list x)))))
    

(defines vl-expr-unpacked-range-check-rec
  (define vl-expr-unpacked-range-check-rec ((x vl-expr-p)
                                            (ss vl-scopestack-p)
                                            (scopes vl-elabscopes-p))
    :returns (warnings (and (vl-warninglist-p warnings)
                            (true-listp warnings)))
    :measure (vl-expr-count x)
    :verify-guards nil
    (append
     (vl-expr-case x
       :vl-index (vl-indexexpr-unpacked-range-check x ss scopes)
       :otherwise nil)
     (vl-exprlist-unpacked-range-check-rec (vl-expr->subexprs x) ss scopes)))
  (define vl-exprlist-unpacked-range-check-rec ((x vl-exprlist-p)
                                                (ss vl-scopestack-p)
                                                (scopes vl-elabscopes-p))
    :returns (warnings (and (vl-warninglist-p warnings)
                            (true-listp warnings)))
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (append (vl-expr-unpacked-range-check-rec (car x) ss scopes)
              (vl-exprlist-unpacked-range-check-rec (cdr x) ss scopes))))
  ///
  (verify-guards vl-expr-unpacked-range-check-rec))

(define vl-expr-unpacked-range-check ((x vl-expr-p)
                                      (ss vl-scopestack-p))
    :returns (warnings (and (vl-warninglist-p warnings)
                            (true-listp warnings)))
  (vl-expr-unpacked-range-check-rec
   x ss (vl-elabscopes-init-ss ss)))

(def-expr-check unpacked-range-check)


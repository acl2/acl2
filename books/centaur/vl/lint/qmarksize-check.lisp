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
(include-book "../mlib/selfsize")
(local (include-book "../util/arithmetic"))

(defsection qmarksize-check
  :parents (vl-lint)
  :short "Check the sizes of conditional expression tests."

  :long "<p>This is a heuristic for generating warnings.</p>

<p>We think it would be strange to see an expression like @('A ? B : C') where
@('A') is not one bit wide.  It found a few minor things that we were able to
clean up, but nothing that was really a bug.</p>

<p>Since the @('?:') operator has the lowest precedence, expressions like @('A
& B ? C : D') are parsed as @('(A & B) ? C : D'), which might not be what is
intended.  In some cases, an actual precedence problem might be revealed by
seeing that the size of the test expression isn't 1.</p>")

(local (xdoc::set-default-parents qmarksize-check))

(define vl-expr-qmarksize-test-trivial ((x  vl-expr-p)
                                        (ss vl-scopestack-p))
  :short "Recognize test expressions that are too trivial to warn about."
  (b* ((x (vl-expr-fix x)))
    (vl-expr-case x
      :vl-literal
      (vl-value-case x.val
        :vl-constint
        (or
         ;; A (sized or unsized) constant 0 or 1 is a little unusual, but it
         ;; shouldn't provoke a size error.
         (eql x.val.value 1)
         (eql x.val.value 0))
        :otherwise
        nil)

      :vl-index
      ;; Module parameters are often untyped, so if we see something like a
      ;; very vanilla `parameter foo = 1; wire w = foo ? a : b`, then we
      ;; will treat this as trivial and not warn.
      (b* (((unless (and (atom x.indices)
                         (vl-partselect-case x.part :none)))
            ;; Something complex, don't suppress warnings
            nil)
           ((mv err trace ?context ?tail) (vl-follow-scopeexpr x.scope ss))
           ((when err)
            nil)
           (target (vl-hidstep->item (car trace)))
           ((unless (eq (tag target) :vl-paramdecl))
            nil)
           ((vl-paramdecl target))
           (plain-p
            ;; It seems that we convert implicit to explicit before running
            ;; qmarksize, so treat either implicit or explicit integer
            ;; parameters as OK here.
            (vl-paramtype-case target.type
              :vl-implicitvalueparam
              (and (not target.type.range)
                   (not target.type.sign))
              :vl-explicitvalueparam
              (vl-datatype-case target.type.type
                :vl-coretype (and (vl-coretypename-equiv target.type.type.name :vl-integer)
                                  (atom target.type.type.pdims)
                                  (atom target.type.type.udims))
                ;; For any more complex type, go ahead and warn.
                :otherwise nil)
              :vl-typeparam
              nil)))
        plain-p)

      :otherwise
      nil)))

(define vl-expr-qmarksize-check-aux ((x  vl-expr-p)
                                     (ss vl-scopestack-p))
  :short "Warn if the top level of x is a @('?:') expression with a wide test."
  :returns (warnings vl-warninglist-p)
  (vl-expr-case x
    :vl-qmark (b* (((mv warnings test-size)
                    (vl-expr-selfsize x.test ss (vl-elabscopes-init-ss ss)))
                   ((unless test-size)
                    ;; Presumably we already warned about being unable to size it.
                    warnings)
                   ((unless (or (eql test-size 1)
                                (vl-expr-qmarksize-test-trivial x.test ss)))
                    (warn :type :vl-warn-qmark-width
                          :msg "~x1-bit wide \"test\" expression for ?: operator, ~a2."
                          :args (list nil test-size x.test))))
                warnings)
    :otherwise nil))

(defines vl-expr-qmarksize-check
  :short "Look throughout an expression for any @('?:') expressions that have
wide tests."

  :long "<p>We look through the expression @('x') for any @('?:')
sub-expressions with wide tests, and produce a warning whenever we find one.
The @('ctx') is a @(see vl-context-p) that says where @('x') occurs, and is
just used to generate more meaningful error messages.</p>"

  (define vl-expr-qmarksize-check ((x   vl-expr-p)
                                   (ss vl-scopestack-p))
    :returns (warnings (and (vl-warninglist-p warnings)
                            (true-listp warnings)))
    :measure (vl-expr-count x)
    :verify-guards nil
    (append-without-guard
     (vl-expr-qmarksize-check-aux x ss)
     (vl-exprlist-qmarksize-check (vl-expr->subexprs x) ss)))

  (define vl-exprlist-qmarksize-check ((x vl-exprlist-p)
                                       (ss vl-scopestack-p))
    :returns (warnings vl-warninglist-p)
    :measure (vl-exprlist-count x)
    (if (atom x)
        nil
      (append
       (vl-expr-qmarksize-check (car x) ss)
       (vl-exprlist-qmarksize-check (cdr x) ss))))
  ///
  (verify-guards vl-expr-qmarksize-check))

(def-expr-check qmarksize-check)


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
(include-book "../parsetree")
(include-book "../mlib/lvalues")
(include-book "../mlib/stmt-tools")
(include-book "centaur/fty/visitor" :dir :system)
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc lvaluecheck
  :parents (vl-lint lvalues)
  :short "Checks to ensure that expressions used in lvalue positions are valid
in the sense of @(see vl-expr-net-lvalue-p) or @(see
vl-expr-variable-lvalue-p), depending on the context."

  :long "<p>Throughout our representation of Verilog/SystemVerilog @(see
syntax), we just use ordinary expressions to represent @(see lvalues).  In many
cases our @(see parser) is more restrictive than this suggests.  For instance,
the parser will not accept syntax such as</p>

@({
     assign a + b = c;
})

<p>However, there are other places where a proper lvalue probably ought to be
expected that we may not understand at parse time.  For instance, the arguments
to the output ports of a module instance probably ought to be good lvalues.
That is, if you have:</p>

@({
     module myadder(output [3:0] out, input [3:0] a, input [3:0] b);
})

<p>Then you should probably never try to write something like:</p>

@({
     myadder adder1 (a + b, foo, bar);
})

<p>Because then you're trying to connect the adder's output to @('a + b'),
which is a lot like writing @('assign a + b = c').</p>

<p>So, in this simple @(see vl-lint) check we simply walk over the design and
look for places where it seems like non-lvalues are being used where lvalues
are probably expected.  This is purely heuristic so the warnings we generate
are never fatal.</p>

<p>We assume that at least @(see argresolve) has been run.</p>")

(local (xdoc::set-default-parents lvaluecheck))

(define vl-assign-lvaluecheck ((x        vl-assign-p)
                               (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  ;; Probably it shouldn't be possible to get a bad lvalue here because our
  ;; parser should explicitly check for good lvalues.  On the other hand, maybe
  ;; some transform could introduce a bad lvalue, and it's easy enough to check
  ;; it just in case.
  (b* (((vl-assign x))
       ((when (vl-expr-variable-lvalue-p x.lvalue))
        (ok)))
    (warn :type :vl-bad-lvalue
          :msg "~a0: assignment to bad lvalue ~a1."
          :args (list x.loc x.lvalue))))

(define vl-plainarg-lvaluecheck ((x        vl-plainarg-p)
                                 (loc      vl-location-p)
                                 (instname maybe-stringp)
                                 (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  ;; This isn't correct in general because we should be looking at the ports
  ;; instead of just their .dir annotation.  On the other hand, this is just a
  ;; warnings heuristic, and just looking at the .dir is probably pretty good
  ;; in general.
  (b* (((vl-plainarg x))
       ((unless x.expr)
        ;; Nothing to check.
        (ok))
       ((unless x.dir)
        ;; NOTE: We used to warn about this, but now if there are interface
        ;; ports it's correct for argresolve to leave the direction blank.
        (ok))
       ((when (vl-direction-equiv x.dir :vl-input))
        ;; Input to the submodule need not be an lvalue, nothing to check.
        (ok))
       ((when (vl-expr-variable-lvalue-p x.expr))
        ;; Looks like a plausibly good lvalue, looks good.
        (ok)))
    (warn :type :vl-bad-lvalue
          :msg "~a0: expression for ~s1 port ~s2 of instance ~w3 is not a ~
                valid lvalue: ~a4.~%"
          :args (list (vl-location-fix loc)
                      (case x.dir
                        (:vl-inout "inout")
                        (:vl-output "output"))
                      x.portname
                      (maybe-string-fix instname)
                      x.expr))))

(define vl-plainarglist-lvaluecheck ((x        vl-plainarglist-p)
                                     (loc      vl-location-p)
                                     (instname maybe-stringp)
                                     (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (warnings (vl-plainarg-lvaluecheck (car x) loc instname warnings)))
    (vl-plainarglist-lvaluecheck (cdr x) loc instname warnings)))

(define vl-arguments-lvaluecheck ((x        vl-arguments-p)
                                  (loc      vl-location-p)
                                  (instname maybe-stringp)
                                  (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (vl-arguments-case x
    (:vl-arguments-named
     ;; Arguments not resolved?  Then we're too stupid to say anything useful,
     ;; so don't try to issue any warnings.
     ;; (warn :type :vl-programming-error
     ;;       :msg "~l0: expected arguments of instance ~s1 to be resolved, but ~
     ;;              args are still named."
     ;;        :args (list loc instname))
     (ok))
    (:vl-arguments-plain
     (vl-plainarglist-lvaluecheck x.args loc instname warnings))))

(define vl-modinst-lvaluecheck ((x        vl-modinst-p)
                                (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((vl-modinst x)))
    (vl-arguments-lvaluecheck x.portargs x.loc x.instname warnings)))

(define vl-gateinst-lvaluecheck ((x        vl-gateinst-p)
                                 (warnings vl-warninglist-p))
  :returns (warnings vl-warninglist-p)
  (b* (((vl-gateinst x)))
    (vl-plainarglist-lvaluecheck x.args x.loc x.name warnings)))

(fty::defvisitor-template lvaluecheck ((x :object)
                                       (warnings vl-warninglist-p "Warnings accumulator."))
  :returns (warnings (:acc warnings :fix (vl-warninglist-fix warnings))
                     vl-warninglist-p)
  :type-fns ((vl-assign   vl-assign-lvaluecheck)
             (vl-modinst  vl-modinst-lvaluecheck)
             (vl-gateinst vl-gateinst-lvaluecheck))
  :renames ((vl-module vl-module-lvaluecheck-aux))
  :fnname-template <type>-lvaluecheck)

; Added by Matt K. 2/20/2016, pending possible mod by Sol to defvisitor.
(set-bogus-measure-ok t)

(fty::defvisitor vl-stmt-lvaluecheck
  :template lvaluecheck
  :type statements
  :renames ((vl-stmt vl-stmt-lvaluecheck-aux))
  :type-fns ((vl-stmt vl-stmt-lvaluecheck))
  :measure (two-nats-measure :count 0)

  (define vl-stmt-lvaluecheck ((x vl-stmt-p)
                               (warnings vl-warninglist-p))
    :returns (warnings vl-warninglist-p)
    :measure (two-nats-measure (vl-stmt-count x) 1)
    (b* ((warnings (vl-stmt-lvaluecheck-aux x warnings)))
      (vl-stmt-case x
        :vl-assignstmt
        (if (vl-expr-variable-lvalue-p x.lvalue)
            (ok)
          (warn :type :vl-bad-lvalue
                :msg "~l0: assignment to bad lvalue, ~a1."
                :args (list x.loc x.lvalue)))
        :vl-deassignstmt
        (if (vl-expr-variable-lvalue-p x.lvalue)
            (ok)
          (warn :type :vl-bad-lvalue
                ;; BOZO add locations to deassign statements
                :msg "Deassignment to bad lvalue, ~a0."
                :args (list x.lvalue)))
        :otherwise
        (ok)))))

(fty::defvisitors lvaluecheck
  :types (vl-module)
  :template lvaluecheck)

(define vl-module-lvaluecheck ((x vl-module-p))
  :returns (new-x vl-module-p)
  (change-vl-module x
                    :warnings (vl-module-lvaluecheck-aux x (vl-module->warnings x))))

(defprojection vl-modulelist-lvaluecheck ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-lvaluecheck x))

(define vl-design-lvaluecheck ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-lvaluecheck x.mods))))


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
(include-book "../mlib/scopestack")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defxdoc logicassign
  :parents (vl-lint)
  :short "Basic check for declaration-time assignments to @('logic') variables."

  :long "<p>SystemVerilog encourages logic designers to use @('logic')
variables to avoid having to distinguish between nets and regs.  But a
fundamental problem with this is that declaration-time assignments to regs and
nets are very different.  For instance,</p>

@({
    wire [3:0] foo1 = a + b;   // Continuous assignment to foo1
    reg [3:0] foo2 = a + b;    // One-time, initial assignment to foo2
})

<p>Since @('logic') variables act like regs here, a logic designer who
writes</p>

@({
    logic [3:0] foo3 = a + b;
})

<p>gets a one-time, initial value assignment to @('foo3'), which is quite
possibly not at all what they meant if they've been led to believe that
@('logic') is a new, wonderful replacement for both @('wire') or @('reg').</p>

<p>Here we just implement a completely stupid check to look for
declaration-time assignments of variables.  If we see an assignment to a
@('reg') variable we don't complain, but if we see an assignment to something
else we issue a warning.</p>")

(local (xdoc::set-default-parents logicassign))

(define vl-vardecl-logicassign ((x        vl-vardecl-p)
                                (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* (((vl-vardecl x) (vl-vardecl-fix x))
       ((unless x.initval)
        ;; No initial value, i.e., this is something like "wire foo;" or "logic
        ;; [3:0] bar;" with no declaration-time assignment.  No need to warn.
        (ok))
       (reg-p (vl-datatype-case x.type
                (:vl-coretype
                 (vl-coretypename-equiv x.type.name :vl-reg))
                (:otherwise
                 ;; Something else, a struct, union, or similar.  Not a
                 ;; register.
                 nil)))
       ((when reg-p)
        ;; We are going to assume folks understand that initial assignments to
        ;; regs are special, no warning in this case.
        (ok)))
    (warn :type :vl-warn-vardecl-assign
          :msg "~a0: declaration-time assignment to ~s1 will be treated ~
                like an 'initial' assignment, not a continuous assignment; ~
                is that what you meant?"
          :args (list x x.name))))

(define vl-vardecllist-logicassign ((x        vl-vardecllist-p)
                                    (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (warnings (vl-vardecl-logicassign (car x) warnings)))
    (vl-vardecllist-logicassign (cdr x) warnings)))

(define vl-module-logicassign ((x vl-module-p))
  :returns (new-x vl-module-p)
  (b* (((vl-module x))
       (warnings (vl-vardecllist-logicassign x.vardecls x.warnings)))
    (change-vl-module x
                      :warnings warnings)))

(defprojection vl-modulelist-logicassign ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-logicassign x))

(define vl-design-logicassign ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x)))
    (change-vl-design x
                      :mods (vl-modulelist-logicassign x.mods))))

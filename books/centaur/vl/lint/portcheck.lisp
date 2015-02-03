; VL Verilog Toolkit
; Copyright (C) 2008-2015 Centaur Technology
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
(include-book "../mlib/port-tools")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection portcheck
  :parents (lint)
  :short "Trivial check to make sure that each module's ports satisfy basic
well-formedness conditions and agree with its port declarations and to issue
style warnings for tricky ports."

  :long "<p>In this check, we try to identify cases like:</p>

@({
     module foo (o, a, b);              |   module bar (o, a, b);
       output o;                        |     output o;
       input a;                         |     input c;    // oops, no such port
       // oops, no declaration for b    |     ...
     endmodule                          |   endmodule
})

<p>This is mostly straightforward.  One complication is that ports can have
many names internally, for instance:</p>

@({
     module baz (o, a, .foo({b, c}), d) ;
       ...
     endmodule
})

<p>So, in general, we need to gather the names from the port expressions.</p>")

(local (xdoc::set-default-parents portcheck))

(define vl-port-check-wellformed ((x vl-port-p))
  :returns (warnings vl-warninglist-p)
  (b* ((x (vl-port-fix x))
       ((when (vl-port-wellformed-p x))
        nil))
    (fatal :type :vl-bad-port
           :msg "~a0: ill-formed port expression."
           :args (list x)
           :acc nil))
  ///
  (more-returns
   (warnings true-listp :rule-classes :type-prescription)
   (warnings (iff warnings (not (vl-port-wellformed-p x)))
             :name vl-port-check-wellformed-under-iff)))

(define vl-portlist-check-wellformed ((x vl-portlist-p))
  :returns (warnings vl-warninglist-p)
  (if (atom x)
      nil
    (append (vl-port-check-wellformed (car x))
            (vl-portlist-check-wellformed (cdr x))))
  ///
  (more-returns
   (warnings true-listp :rule-classes :type-prescription)
   (warnings (iff warnings (not (vl-portlist-wellformed-p x)))
             :name vl-portlist-check-wellformed-under-iff)))

(define vl-port-check-style ((x        vl-port-p)
                             (warnings vl-warninglist-p))
  :guard (vl-port-wellformed-p x)
  :returns (warnings vl-warninglist-p)
  (b* ((x (vl-port-fix x))
       ((when (eq (tag x) :vl-interfaceport))
        (ok))
       ((vl-regularport x))

       ((when (and x.name
                   x.expr
                   (vl-idexpr-p x.expr)
                   (equal (vl-idexpr->name x.expr) x.name)))
        ;; Ordinary, simple kind of port.  No worries.
        (ok))

       ((when (not x.expr))
        (if x.name
            ;; Fine, the port is blank but it has a name at least, so the
            ;; designer had to write something like .foo() to get this and it
            ;; seems like that really is what they want.
            (ok)
          (warn :type :vl-warn-port-style
                :msg "~a0: completely blank port without even a name.  Is ~
                      this an accidental extra comma?  If not, while blank ~
                      ports are legal, they will prevent you from ~
                      instantiating the module using named port connections.  ~
                      Consider giving this port a name using syntax like ~
                      \".myportname()\" instead to avoid this."
                :args (list x))))

       ((when (and (not x.name)
                   (not (vl-idexpr-p x.expr))
                   (vl-atomicportexpr-p x.expr)))
        ;; This can happen when a logic designer copies/pastes a submodule
        ;; instantiation to make the port list for a module.  That is, they end
        ;; up with `module foo (a, b[3:0], c[1:0], ...)` or similar.
        (warn :type :vl-warn-port-style
              :msg "~a0: the port expression ~a1 has a range.  This is legal, ~
                    but means you can't connect the port by name, etc.  It ~
                    would be better to move the range to the port's ~
                    input/output declaration, or (better yet) to use the more ~
                    modern \"ANSI\" syntax for combined port declarations."
              :args (list x x.expr))))

    ;; Otherwise something pretty fancy is going on.  We'll just recommend
    ;; against this out of general principle.
    (warn :type :vl-warn-port-style
          :msg "~a0: port has complex expression ~a1."
          :args (list x x.expr))))

(define vl-portlist-check-style ((x vl-portlist-p)
                                 (warnings vl-warninglist-p))
  :guard (vl-portlist-wellformed-p x)
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (warnings (vl-port-check-style (car x) warnings)))
    (vl-portlist-check-style (cdr x) warnings)))

(define vl-module-portcheck ((x vl-module-p))
  :returns (new-x vl-module-p "New version of @('x'), with at most some added warnings.")
  (b* (((vl-module x) x)

       (bad-warnings (vl-portlist-check-wellformed x.ports))
       ((when bad-warnings)
        ;; There are already fatal warnings with the ports.  We aren't going to
        ;; do any additional checking.
        (change-vl-module x :warnings (append bad-warnings x.warnings)))

       (warnings x.warnings)
       (warnings (vl-portlist-check-style x.ports warnings))

       (decl-names (mergesort (vl-portdecllist->names x.portdecls)))
       (port-names (mergesort (vl-portlist->internalnames x.ports)))

       (warnings (if (subset decl-names port-names)
                     warnings
                   (fatal :type :vl-port-mismatch
                          :msg "Port declarations for non-ports: ~&0."
                          :args (list (difference decl-names port-names)))))

       (warnings (if (subset port-names decl-names)
                     warnings
                   (fatal :type :vl-port-mismatch
                          :msg "Missing port declarations for ~&0."
                          :args (list (difference port-names decl-names))))))
    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-portcheck ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-portcheck x))

(define vl-design-portcheck ((x vl-design-p))
  :returns (new-x vl-design-p)
  :short "Top-level @(see portcheck) check."
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-portcheck x.mods))))


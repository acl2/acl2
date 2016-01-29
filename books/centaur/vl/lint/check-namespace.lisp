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
(include-book "../mlib/modnamespace")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))

(defxdoc check-namespace
  :parents (vl-lint)
  :short "A check for basic, incorrect constructs like name clashes."
  :long "<p>This does basic sanity checking to ensure that port and module item
names are not duplicated and that port declarations overlap with their
corresponding variable declarations in a sensible way.</p>")

(local (xdoc::set-default-parents check-namespace))

;; BOZO we should do similar checking for interfaces, etc.

(define vl-check-portdecl-and-moduleitem-compatible
  :short "Checking whether a port declaration, which overlaps with some module
item declaration, is a reasonable overlap."
  ((portdecl vl-portdecl-p)
   (item     vl-scopeitem-p))
  :returns (warning (iff (vl-warning-p warning) warning))

  :long "<p>For instance, we might have:</p>

@({
    input x;
    wire x;
})

<p>Which is fine, or we might have:</p>

@({
    input [3:0] x;
    wire [4:0] x;
})

<p>Which is definitely not okay.  See also @(see portdecl-sign).  We expect
that after parsing, the types will agree exactly.</p>"

  (b* ((portdecl (vl-portdecl-fix portdecl))
       (item     (vl-scopeitem-fix item))

       ((vl-portdecl portdecl) portdecl)
       ((unless (eq (tag item) :vl-vardecl))
        (make-vl-warning :type :vl-weird-port
                         :msg "~a0: port ~s1 is also declared to be a ~s2."
                         :args (list portdecl portdecl.name (tag item))
                         :fatalp t
                         :fn __function__))

       ((vl-vardecl item))
       ((unless (equal portdecl.type item.type))
        (make-vl-warning :type :vl-incompatible-port
                         :msg "~a0: the variable declaration for port ~s1 has ~
                               incompatible type: ~a1 vs. ~a2."
                         :args (list portdecl portdecl.type item.type)
                         :fatalp t
                         :fn __function__))

       ((unless (equal portdecl.nettype item.nettype))
        (make-vl-warning :type :vl-incompatible-port
                         :msg "~a0: the variable declaration for port ~s1 has ~
                               incompatible nettype: ~a1 vs. ~a2."
                         :args (list portdecl portdecl.nettype item.nettype)
                         :fatalp t
                         :fn __function__)))
    nil))

(define vl-check-portdecl-overlap-compatible ((portdecls vl-portdecllist-p)
                                              (ss        vl-scopestack-p))
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom portdecls))
        nil)
       (warnings (vl-check-portdecl-overlap-compatible (cdr portdecls) ss))
       ((vl-portdecl decl1) (vl-portdecl-fix (car portdecls)))
       (item1 (vl-scopestack-find-item decl1.name ss))
       ((unless item1)
        (fatal :type :vl-programming-error
               :msg "~a0: port ~s1 has no corresponding variable declaration. ~
                     Thought this should never happen."
               :args (list decl1 decl1.name))))
    warnings))

(define vl-module-check-namespace ((x vl-module-p))
  :returns (new-x vl-module-p "Perhaps extended with warnings.")
  (b* (((vl-module x) (vl-module-fix x))
       (warnings x.warnings)

       ;; Clashing external port names?
       (portdupes (duplicated-members (remove nil (vl-portlist->names x.ports))))
       (warnings
        (if portdupes
            (fatal :type :vl-bad-ports
                   :msg "Duplicate port names: ~&0."
                   :args (list portdupes))
          warnings))

       ;; Clashing port decls?
       (pdnames     (vl-portdecllist->names x.portdecls))
       (pdnames-s   (mergesort pdnames))
       (warnings
        (if (mbe :logic (no-duplicatesp-equal pdnames)
                 :exec (same-lengthp pdnames pdnames-s))
            warnings
          (fatal :type :vl-bad-portdecls
                 :msg "Duplicate port declaration names: ~&0."
                 :args (list (duplicated-members pdnames)))))

       ;; Clashing internal names?
       (namespace   (vl-module->modnamespace x))
       (namespace-s (mergesort namespace))
       (warnings
        (if (mbe :logic (no-duplicatesp-equal namespace)
                 :exec (same-lengthp namespace namespace-s))
            warnings
          (fatal :type :vl-namespace-error
                 :msg "Illegal redefinition of ~&0."
                 :args (list (duplicated-members namespace)))))

       (ss (vl-scopestack-push x (vl-scopestack-null)))
       (warnings
        (append-without-guard
         (vl-check-portdecl-overlap-compatible x.portdecls ss)
         warnings)))
    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-check-namespace ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-check-namespace x))

(define vl-design-check-namespace ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-check-namespace x.mods))))


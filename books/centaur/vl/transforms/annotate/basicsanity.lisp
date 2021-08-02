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
(include-book "../../mlib/port-tools")
(include-book "../../mlib/writer")
(local (include-book "../../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection basicsanity
  :parents (annotate)
  :short "Basic sanity checking of various constructs."

  :long "<p>This is a set of basic but rather ad-hoc sanity checks that don't
really fit into other places.  It is carried out as part of @(see annotate).
Some of the things we do here...</p>


<h5>Port sanity checking</h5>

<p>We check that ports satisfy basic well-formedness conditions and agree with
its port declarations and to issue style warnings for tricky ports.  This is
meant to identify cases such as:</p>

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
     module baz (o, a, .foo( {b, c} ), d) ;
       ...
     endmodule
})

<p>So, in general, we need to gather the names from the port expressions.
While we're at it we may issue various port style warnings.</p>


<h5>Port and modport name clashes</h5>

<p>Most name clash checking for real scopes is done by @(see shadowcheck), but
things like the external port names for a module, e.g., the @('a1') and @('a2')
in</p>

@({
     module foo (.a1(b1), .a2(b2)) ;
      ...
     endmodule
})

<p>aren't separate from other scopes, so we check them here.  We similarly
check the external names listed by modports.</p>


<h5>Interface instances</h5>

<p>SystemVerilog 25.3 (page 713) prohibits interfaces from instantiating
submodules, but interfaces <i>are</i> allowed to instantiate other interfaces.
Since we can't tell until after parsing whether a particular instance refers to
a module, interface, or user-defined primitive and use the same representation
for all of these, we check here that any such instances really do refer to
interfaces.</p>")

(local (xdoc::set-default-parents basicsanity))

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

(define vl-pps-expr-elided ((x vl-expr-p))
  :returns (str stringp :rule-classes :type-prescription)
  (b* ((str (vl-pps-expr x))
       ((when (<= (length str) 50))
        str))
    (cat (subseq str 0 50) "...")))

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
          ;; Some of these expressions are bigger than we want to see in
          ;; warning output, so we elide them.
          :msg "~a0: port has complex expression ~s1"
          :args (list x (vl-pps-expr-elided x.expr)))))

(define vl-portlist-check-style ((x vl-portlist-p)
                                 (warnings vl-warninglist-p))
  :guard (vl-portlist-wellformed-p x)
  :returns (warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (warnings (vl-port-check-style (car x) warnings)))
    (vl-portlist-check-style (cdr x) warnings)))

(define vl-module-basicsanity ((x vl-module-p))
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
                          :args (list (difference port-names decl-names)))))

       (external-names (vl-portlist->names x.ports))
       (dupes          (duplicated-members (remove nil external-names)))
       (warnings       (if (not dupes)
                           warnings
                         (fatal :type :vl-bad-ports
                                :msg "Duplicate port names: ~&0."
                                :args (list dupes)))))

    (change-vl-module x :warnings warnings)))

(defprojection vl-modulelist-basicsanity ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  :share-suffix t
  (vl-module-basicsanity x))


(defprojection vl-modport-portlist->names ((x vl-modport-portlist-p))
  :returns (names string-listp)
  (vl-modport-port->name x))

(define vl-modport-port-check-wellformed ((x             vl-modport-port-p)
                                          (ctx           vl-modport-p)
                                          (warnings      vl-warninglist-p)
                                          (internalnames string-listp))
  :returns (mv (warnings vl-warninglist-p)
               (internalnames string-listp))
  (b* ((internalnames (string-list-fix internalnames))
       ((vl-modport-port x) (vl-modport-port-fix x))
       ((unless x.expr)
        (mv (ok) internalnames))
       ((unless (vl-portexpr-p x.expr))
        (mv (fatal :type :vl-bad-port
                   :msg "~a0: ill-formed expression for modport port: ~a1."
                   :args (list (vl-modport-fix ctx) x))
            internalnames)))
    (mv (ok) (append (vl-portexpr->internalnames x.expr) internalnames))))

(define vl-modport-portlist-check-wellformed ((x             vl-modport-portlist-p)
                                              (ctx           vl-modport-p)
                                              (warnings      vl-warninglist-p)
                                              (internalnames string-listp))
  :returns (mv (warnings vl-warninglist-p)
               (internalnames string-listp))
  (b* (((when (atom x))
        (mv (ok) (string-list-fix internalnames)))
       ((mv warnings internalnames)
        (vl-modport-port-check-wellformed (car x) ctx warnings internalnames)))
    (vl-modport-portlist-check-wellformed (cdr x) ctx warnings internalnames)))

(define vl-modport-portcheck ((x        vl-modport-p)
                              (oknames  string-listp "Names of local wires, etc., that are OK in modport expressions.")
                              (warnings vl-warninglist-p))
  :guard (setp oknames)
  :returns (new-warnings vl-warninglist-p)
  (b* ((oknames (string-list-fix oknames))
       ((vl-modport x) (vl-modport-fix x))
       (external-names (vl-modport-portlist->names x.ports))
       (dupes (duplicated-members external-names))
       ((when dupes)
        (fatal :type :vl-bad-modport
               :msg "~a0: Duplicated modport port names: ~&1."
               :args (list x dupes)))
       ((mv warnings internalnames)
        (vl-modport-portlist-check-wellformed x.ports x warnings nil))
       (internalnames (mergesort internalnames))
       (badnames (difference internalnames oknames))
       ((when badnames)
        (fatal :type :vl-bad-modport
               :msg "~a0: Modport refers to unknown name~s1: ~&2."
               :args (list x
                           (if (vl-plural-p badnames) "s" "")
                           badnames))))
    (ok)))

(define vl-modportlist-portcheck ((x        vl-modportlist-p)
                                  (oknames  string-listp)
                                  (warnings vl-warninglist-p))
  :guard (setp oknames)
  :returns (new-warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (warnings (vl-modport-portcheck (car x) oknames warnings)))
    (vl-modportlist-portcheck (cdr x) oknames warnings)))


(define vl-interface-check-modinst-is-subinterface
  ((x        vl-modinst-p "Modinst to check, occurs within an interface.")
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* (((vl-modinst x) (vl-modinst-fix x))
       (def (vl-scopestack-find-definition x.modname ss))
       ((unless def)
        (fatal :type :vl-interface-instance-undefined
               :msg "~a0 refers to undefined interface ~m1."
               :args (list x x.modname)))
       ((unless (mbe :logic (vl-interface-p def)
                     :exec (eq (tag def) :vl-interface)))
        (fatal :type :vl-interface-instantiates-noninterface
               :msg "~a0: can't instantiate ~s1 within an interface ~
                     (interfaces can instantiate other interfaces, but can't ~
                     have ~s2 instances.)"
               :args (list x x.modname
                           (case (tag def)
                             (:vl-module    "submodule")
                             (:vl-udp       "primitive")
                             ;; bozo not sure this is not ok -- currently we
                             ;; don't really have any support for programs so
                             ;; let's just rule it out, too.
                             (:vl-program   "program")
                             (:vl-class     "class")
                             (otherwise (impossible)))))))
    ;; Else, looks like an interface, so that seems good.
    (ok))
  :prepwork ((local (in-theory (enable tag-reasoning)))

             (local (defthm l0
                      (implies (vl-scopedef-p x)
                               (or (equal (tag x) :vl-interface)
                                   (equal (tag x) :vl-module)
                                   (equal (tag x) :vl-udp)
                                   (equal (tag x) :vl-program)
                                   (equal (tag x) :vl-class)))
                      :rule-classes :forward-chaining
                      :hints(("Goal" :in-theory (enable vl-scopedef-p)))))

             (local (defthm l1
                      (let ((x (vl-scopestack-find-definition name ss)))
                        (implies x
                                 (or (equal (tag x) :vl-interface)
                                     (equal (tag x) :vl-module)
                                     (equal (tag x) :vl-udp)
                                     (equal (tag x) :vl-program)
                                     (equal (tag x) :vl-class))))
                      :rule-classes :forward-chaining
                      :hints(("goal" :use ((:instance l0 (x (vl-scopestack-find-definition name ss))))))))

             (local (defthm l2
                      (let ((x (vl-scopestack-find-definition name ss)))
                        (implies x
                                 (equal (vl-interface-p x)
                                        (eq (tag x) :vl-interface))))))))

(define vl-interface-check-modinsts-are-subinterfaces ((x        vl-modinstlist-p)
                                                       (ss       vl-scopestack-p)
                                                       (warnings vl-warninglist-p))
  :returns (new-warnings vl-warninglist-p)
  (b* (((when (atom x))
        (ok))
       (warnings (vl-interface-check-modinst-is-subinterface (car x) ss warnings)))
    (vl-interface-check-modinsts-are-subinterfaces (cdr x) ss warnings)))


(define vl-interface-basicsanity ((x vl-interface-p)
                                  (ss vl-scopestack-p))
  :returns (new-x vl-interface-p "New version of @('x'), with at most some added warnings.")
  (b* (((vl-interface x) (vl-interface-fix x))
       (ss (vl-scopestack-push x ss))

       (bad-warnings (vl-portlist-check-wellformed x.ports))
       ((when bad-warnings)
        ;; There are already fatal warnings with the ports.  We aren't going to
        ;; do any additional checking.
        (change-vl-interface x :warnings (append bad-warnings x.warnings)))

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
                          :args (list (difference port-names decl-names)))))

       (external-names (vl-portlist->names x.ports))
       (dupes          (duplicated-members (remove nil external-names)))
       (warnings       (if (not dupes)
                           warnings
                         (fatal :type :vl-bad-ports
                                :msg "Duplicate port names: ~&0."
                                :args (list dupes))))

       (oknames
        ;; VCS and NCVerilog both seem to let interface ports to be used in the
        ;; modport expressions.  But I don't think other local names (typedefs,
        ;; parameters, etc.) make any sense here.
        (mergesort (append (vl-portdecllist->names x.portdecls)
                           (vl-vardecllist->names x.vardecls))))

       (warnings (vl-modportlist-portcheck x.modports oknames warnings))
       (warnings (vl-interface-check-modinsts-are-subinterfaces x.modinsts ss warnings)))

    (change-vl-interface x :warnings warnings)))

(defprojection vl-interfacelist-basicsanity ((x  vl-interfacelist-p)
                                             (ss vl-scopestack-p))
  :returns (new-x vl-interfacelist-p)
  :share-suffix t
  (vl-interface-basicsanity x ss))

(define vl-design-basicsanity ((x vl-design-p))
  :returns (new-x vl-design-p)
  :short "Top-level @(see basicsanity) check."
  (b* (((vl-design x) x)
       (ss (vl-scopestack-init x))
       (new-x (change-vl-design x
                                :mods (vl-modulelist-basicsanity x.mods)
                                :interfaces (vl-interfacelist-basicsanity x.interfaces ss))))
    (vl-scopestacks-free)
    new-x))


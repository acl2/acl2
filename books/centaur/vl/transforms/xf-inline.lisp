; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "xf-subst")
(include-book "../mlib/namemangle")
(include-book "../mlib/relocate")
(include-book "../mlib/namefactory")
(include-book "../mlib/port-tools")
(include-book "../mlib/writer")
(include-book "../mlib/print-warnings")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(local (defthm vl-string-values-p-of-pairlis$
         (implies (and (force (same-lengthp x y))
                       (string-listp y))
                  (vl-string-values-p (pairlis$ x y)))
         :hints(("Goal" :in-theory (enable pairlis$)))))

(local (defthm vl-string-keys-p-of-pairlis$
         (implies (string-listp x)
                  (vl-string-keys-p (pairlis$ x y)))
         :hints(("Goal" :in-theory (enable pairlis$)))))


(defxdoc inline-mods
  :parents (transforms)
  :short "A transform for inlining basic modules."

  :long "<p>This transform can be used to inline modules as long as they are
very simple.  The modules being inlined can't have always blocks, registers,
and so forth; more specifically they must be accepted by @(see
vl-ok-to-inline-p).</p>

<p><b>WARNING</b>: We assume that the modules involved are \"sensible.\" That
is, we are not trying to defend against modules with incoherent namespaces,
divergent ports and portdecls, etc.</p>

<p><b>WARNING</b>: For this transform to be sound, the submodule must have its
ports properly declared as INPUT or OUTPUT ports.  We do NOT try to handle
inout ports.  Why?  Well, here is our basic strategy.  If we have a module
like:</p>

@({
    module mymod ( output o, input a, input b ) ; ... endmodule
})

<p>And we want to inline an instance such as:</p>

@({
    mymod myinst (w, 1'b1, c + d) ;
})

<p>Then the basic idea is to replace myinst with:</p>

@({
     assign w = mangled_o;
     assign mangled_a = 1'b1;
     assign mangled_b = c + d;
     [... mangled body of mymod ...]
})

<p>These assignment statements are unidirectional and if, for instance, you
incorrectly mark an output as an input, then the assignment will flow in the
wrong way.  This use of assignment statements is particularly simpleminded.  We
have considered doing something smarter to avoid temporaries, but it seems like
a very tricky problem in general so we think it's best not to get too
clever.</p>")

(defsection vl-ok-to-inline-p
  :parents (inline-mods)

  (defund vl-ok-to-inline-p (x)
    (declare (xargs :guard (vl-module-p x)))
    (b* (((vl-module x) x)
         (- (cw "Checking if we can inline ~s0..." x.name)))
      (and (or (not (vl-portdecls-with-dir :vl-inout x.portdecls))
               (cw "no: inout ports~%"))
           (or (not x.alwayses)
               (cw "no: always blocks~%"))
           (or (not x.regdecls)
               (cw "no: reg declarations~%"))
           (or (not x.vardecls)
               (cw "no: var declarations~%"))
           (or (not x.eventdecls)
               (cw "no: event declarations~%"))
           (or (not x.paramdecls)
               (cw "no: parameter declarations~%"))
           (or (not x.fundecls)
               (cw "no: function declarations~%"))
           (or (not x.taskdecls)
               (cw "no: task declarations~%"))
           (not (cw "yes~%"))))))

(deflist vl-ok-to-inline-list-p (x)
  (vl-ok-to-inline-p x)
  :guard (vl-modulelist-p x)
  :parents (inline-mods))




(defsection vl-make-inlining-assigns
  :parents (inline-mods)
  :short "Make assignments that hook up the superior module to the new, mangled
wires that have been derived from the module's ports."

  (defund vl-make-inlining-assigns (ports plainargs portdecls palist loc warnings)
    "Returns (MV SUCCESSP WARNINGS ASSIGNS)"
    (declare (xargs :guard (and (vl-portlist-p ports)
                                (vl-plainarglist-p plainargs)
                                (same-lengthp ports plainargs)
                                (vl-portdecllist-p portdecls)
                                (equal palist (vl-portdecl-alist portdecls))
                                (vl-location-p loc)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom ports))
          (mv t warnings nil))
         (port1   (car ports))
         (inside  (vl-port->expr port1))
         (outside (vl-plainarg->expr (car plainargs)))

         ((mv warnings dir)
          (vl-port-direction (car ports) portdecls palist nil))
         ((unless dir)
          ;; Already warned
          (mv nil warnings nil))

         ((when (eq dir :vl-inout))
          (b* ((w (make-vl-warning :type :vl-inline-fail
                                   :msg "Inout ports aren't supported for inlining."
                                   :args (list (car ports))
                                   :fn 'vl-make-inlining-assigns
                                   :fatalp nil)))
            (mv nil (cons w warnings) nil)))

         (assigns1
          ;; If the port's expression (inside) is blank (nil), we don't need
          ;; ANY assignments to cover this port:
          ;;
          ;;   - If the port is an input, it isn't used inside the submodule,
          ;;     so there's obviously no need to assign it to anything.
          ;;
          ;;   - If the port is an output, it isn't being driven by the
          ;;     submodule, so we don't need to drive whatever the superior
          ;;     module wants to connect it to.
          ;;
          ;; Similarly, if the actual expression (outside) is blank (nil), we
          ;; don't need any assignment:
          ;;
          ;;   - If the port is an input, then since the superior module isn't
          ;;     driving it, we don't need to assign anything to it.
          ;;
          ;;   - If the port is an output, then since it's not connected to
          ;;     anything in the superior module, there's obviously no need to
          ;;     assign it to anything.
          ;;
          ;; Otherwise, we'll need an assignment based on the direction of the
          ;; port.
          (cond ((or (not inside) (not outside))
                 nil)
                ((eq dir :vl-input)
                 (list (make-vl-assign :lvalue inside :expr outside :loc loc)))
                (t
                 (list (make-vl-assign :lvalue outside :expr inside :loc loc)))))

         ((mv okp warnings assigns2)
          (vl-make-inlining-assigns (cdr ports) (cdr plainargs)
                                    portdecls palist loc warnings)))
      (mv okp warnings (append assigns1 assigns2))))

  (local (in-theory (enable vl-make-inlining-assigns)))

  (defmvtypes vl-make-inlining-assigns
    (booleanp nil true-listp))

  (defthm vl-assignlist-p-of-vl-make-inlining-assigns
    (let ((ret (vl-make-inlining-assigns ports plainargs portdecls palist loc warnings)))
      (implies (and (force (vl-portlist-p ports))
                    (force (vl-plainarglist-p plainargs))
                    (force (same-lengthp ports plainargs))
                    (force (vl-portdecllist-p portdecls))
                    (force (equal palist (vl-portdecl-alist portdecls)))
                    (force (vl-location-p loc)))
               (vl-assignlist-p (mv-nth 2 ret)))))

  (defthm vl-warninglist-p-p-of-vl-make-inlining-assigns
    (let ((ret (vl-make-inlining-assigns ports plainargs portdecls palist loc warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 1 ret))))))



(defsection vl-inline-rename-portdecls
  :parents (inline-mods)
  :short "Rename portdecls using the renaming alist (which binds old names to
their new, mangled names)."

  (defund vl-inline-rename-portdecl (x alist)
    (declare (xargs :guard (and (vl-portdecl-p x)
                                (vl-string-keys-p alist)
                                (vl-string-values-p alist))))
    (b* ((new-name (or (cdr (hons-get (vl-portdecl->name x) alist))
                       (er hard? 'vl-inline-rename-portdecl "all portdecls should be bound")
                       (vl-portdecl->name x))))
      (change-vl-portdecl x :name new-name)))

  (defthm vl-portdecl-p-of-vl-inline-rename-portdecl
    (implies (and (vl-portdecl-p x)
                  (vl-string-keys-p alist)
                  (vl-string-values-p alist))
             (vl-portdecl-p (vl-inline-rename-portdecl x alist)))
    :hints(("Goal" :in-theory (enable vl-inline-rename-portdecl))))

  (defprojection vl-inline-rename-portdecls (x alist)
    (vl-inline-rename-portdecl x alist)
    :guard (and (vl-portdecllist-p x)
                (vl-string-keys-p alist)
                (vl-string-values-p alist))
    :result-type vl-portdecllist-p))



(defsection vl-inline-mod-in-modinst
  :parents (inline-mods)
  :short "Maybe replace a module instance with its inlined body."

  (defund vl-inline-mod-in-modinst (sub x nf warnings)
    "Returns (MV NF' MODINSTS' GATEINSTS' ASSIGNS' NETDECLS' WARNINGS')"
    (declare (xargs :guard (and (vl-module-p sub)
                                (vl-ok-to-inline-p sub)
                                (vl-modinst-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((vl-modinst x) x)
         ((vl-module sub) sub)

         ((unless (equal x.modname sub.name))
          ;; Not an instance of the desired module, do nothing to this instance.
          (mv nf (list x) nil nil nil warnings))

         ((when (vl-arguments->namedp x.portargs))
          (b* ((w (make-vl-warning :type :vl-inline-fail
                                   :msg "~a0: can't inline because args aren't resolved."
                                   :args (list x)
                                   :fn 'vl-inline-mod-in-modinst
                                   :fatalp t)))
            (mv nf (list x) nil nil nil (cons w warnings))))
         (plainargs (vl-arguments->args x.portargs))

         ((when (vl-arguments->args x.paramargs))
          (b* ((w (make-vl-warning :type :vl-inline-fail
                                   :msg "~a0: can't inline because of parameters."
                                   :args (list x)
                                   :fn 'vl-inline-mod-in-modinst
                                   :fatalp t)))
            (mv nf (list x) nil nil nil (cons w warnings))))

         ((unless (same-lengthp sub.ports plainargs))
          (b* ((w (make-vl-warning :type :vl-inline-fail
                                   :msg "~a0: can't inline due to improper arity."
                                   :args (list x)
                                   :fn 'vl-inline-mod-in-modinst
                                   :fatalp t)))
            (mv nf (list x) nil nil nil (cons w warnings))))

         ;; Mangle and relocate the submodule's guts so that they are all at the
         ;; location of the instance, all the names are fresh, and all the
         ;; expressions have been updated to the new names.
         (prefix           (or x.instname "inst"))
         ((mv netdecls nf) (vl-namemangle-netdecls prefix sub.netdecls nf))
         (netdecls         (vl-relocate-netdecls x.loc netdecls))
         (old-names        (vl-netdecllist->names sub.netdecls))
         (new-names        (vl-netdecllist->names netdecls))
         (new-exprs        (vl-make-idexpr-list new-names nil nil))
         (sigma            (pairlis$ old-names new-exprs))

         ((with-fast sigma))

         (modinsts (vl-modinstlist-subst sub.modinsts sigma))
         (modinsts (vl-relocate-modinsts x.loc modinsts))
         ((mv modinsts nf) (vl-namemangle-modinsts prefix modinsts nf))

         (gateinsts (vl-gateinstlist-subst sub.gateinsts sigma))
         (gateinsts (vl-relocate-gateinsts x.loc gateinsts))
         ((mv gateinsts nf) (vl-namemangle-gateinsts prefix gateinsts nf))

         (assigns (vl-assignlist-subst sub.assigns sigma))
         (assigns (vl-relocate-assigns x.loc assigns))

         ;; The only thing we're missing are the assignments to handle the port
         ;; connections.  This is a bit tricky.  We name mangle sub's ports which
         ;; rewrites the port expressions (the wires internal to sub) and also
         ;; rewrite the portdecls so that they are all in terms of the new wire
         ;; names.
         (ports          (vl-portlist-subst sub.ports sigma))
         (renaming-alist (pairlis$ old-names new-names))
         (portdecls      (with-fast-alist renaming-alist
                           (vl-inline-rename-portdecls sub.portdecls renaming-alist)))
         (palist         (vl-portdecl-alist portdecls))
         ((mv okp warnings port-assigns)
          (vl-make-inlining-assigns ports plainargs portdecls palist x.loc warnings))
         (- (fast-alist-free palist))
         ((unless okp)
          (b* ((w (make-vl-warning :type :vl-inline-fail
                                   :msg "~a0: problem with inlining port connections."
                                   :args (list x)
                                   :fn 'vl-inline-mod-in-modinst
                                   :fatalp t)))
            (mv nf (list x) nil nil nil (cons w warnings))))

         ;; If we get this far, then the port-assigns are already set and everything
         ;; else is looking good, too.
         )
      (mv nf modinsts gateinsts (append port-assigns assigns) netdecls warnings)))

  (local (in-theory (enable vl-inline-mod-in-modinst)))

  (defmvtypes vl-inline-mod-in-modinst (nil true-listp true-listp true-listp true-listp nil))

  (defthm vl-inline-mod-in-modinst-basics
    (let ((ret (vl-inline-mod-in-modinst sub x nf warnings)))
      (implies (and (force (vl-module-p sub))
                    (force (vl-modinst-p x))
                    (force (vl-namefactory-p nf)))
               (and (vl-namefactory-p (mv-nth 0 ret))
                    (vl-modinstlist-p (mv-nth 1 ret))
                    (vl-gateinstlist-p (mv-nth 2 ret))
                    (vl-assignlist-p (mv-nth 3 ret))
                    (vl-netdecllist-p (mv-nth 4 ret))))))

  (defthm vl-warninglist-p-of-vl-inline-mod-in-modinst
    (let ((ret (vl-inline-mod-in-modinst sub x nf warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 5 ret))))))



(defsection vl-inline-mod-in-modinsts
  :parents (inline-mods)
  :short "Replace any instance of a module with its inlined body."

  (defund vl-inline-mod-in-modinsts (sub x nf warnings)
    "Returns (MV NF' MODINSTS' GATEINSTS' ASSIGNS' NETDECLS' WARNINGS')"
    (declare (xargs :guard (and (vl-module-p sub)
                                (vl-ok-to-inline-p sub)
                                (vl-modinstlist-p x)
                                (vl-namefactory-p nf)
                                (vl-warninglist-p warnings))))
    (b* (((when (atom x))
          (mv nf nil nil nil nil warnings))
         ((mv nf modinsts1 gateinsts1 assigns1 netdecls1 warnings)
          (vl-inline-mod-in-modinst sub (car x) nf warnings))
         ((mv nf modinsts2 gateinsts2 assigns2 netdecls2 warnings)
          (vl-inline-mod-in-modinsts sub (cdr x) nf warnings)))
      (mv nf
          (append modinsts1 modinsts2)
          (append gateinsts1 gateinsts2)
          (append assigns1 assigns2)
          (append netdecls1 netdecls2)
          warnings)))

  (local (in-theory (enable vl-inline-mod-in-modinsts)))

  (defmvtypes vl-inline-mod-in-modinsts
    (nil true-listp true-listp true-listp true-listp nil))

  (defthm vl-inline-mod-in-modinsts-basics
    (let ((ret (vl-inline-mod-in-modinsts sub x nf warnings)))
      (implies (and (force (vl-module-p sub))
                    (force (vl-modinstlist-p x))
                    (force (vl-namefactory-p nf)))
               (and (vl-namefactory-p (mv-nth 0 ret))
                    (vl-modinstlist-p (mv-nth 1 ret))
                    (vl-gateinstlist-p (mv-nth 2 ret))
                    (vl-assignlist-p (mv-nth 3 ret))
                    (vl-netdecllist-p (mv-nth 4 ret))))))

  (defthm vl-warninglist-p-of-vl-inline-mod-in-modinsts
    (let ((ret (vl-inline-mod-in-modinsts sub x nf warnings)))
      (implies (force (vl-warninglist-p warnings))
               (vl-warninglist-p (mv-nth 5 ret))))))



(defsection vl-inline-mod-in-mod
  :parents (inline-mods)
  :short "Expand any instances of a submodule into its inlined body, throughout
a module."

  (defund vl-inline-mod-in-mod (sub x)
    (declare (xargs :guard (and (vl-module-p sub)
                                (vl-ok-to-inline-p sub)
                                (vl-module-p x))))
    (b* (((vl-module x) x)
         (nf (vl-starting-namefactory x))
         ((mv nf modinsts gateinsts assigns netdecls warnings)
          (vl-inline-mod-in-modinsts sub x.modinsts nf x.warnings)))
      (vl-free-namefactory nf)
      (change-vl-module x
                        :modinsts  modinsts
                        :gateinsts (append gateinsts x.gateinsts)
                        :assigns   (append assigns x.assigns)
                        :netdecls  (append netdecls x.netdecls)
                        :warnings  warnings)))

  (local (in-theory (enable vl-inline-mod-in-mod)))

  (defthm vl-module-p-of-vl-inline-mod-in-mod
    (implies (and (vl-module-p sub)
                  (vl-ok-to-inline-p sub)
                  (vl-module-p x))
             (vl-module-p (vl-inline-mod-in-mod sub x))))

  (defthm vl-module->name-of-vl-inline-mod-in-mod
    (equal (vl-module->name (vl-inline-mod-in-mod sub x))
           (vl-module->name x))))


(defprojection vl-inline-mod-in-mods-aux (sub x)
  (vl-inline-mod-in-mod sub x)
  :guard (and (vl-module-p sub)
              (vl-ok-to-inline-p sub)
              (vl-modulelist-p x))
  :result-type vl-modulelist-p
  :parents (inline-mods)
  :rest
  ((defthm vl-modulelist->names-of-vl-inline-mod-in-mods-aux
     (equal (vl-modulelist->names (vl-inline-mod-in-mods-aux sub x))
            (vl-modulelist->names x)))))



(defsection vl-inline-mods
  :parents (inline-mods)
  :short "@(call vl-inline-mods) inlines all modules in @('x') throughout
@('all-mods')."

  (defund vl-inline-mods (x all-mods)
    (declare (xargs :guard (and (vl-modulelist-p x)
                                (vl-ok-to-inline-list-p x)
                                (vl-modulelist-p all-mods))))
    (if (atom x)
        all-mods
      (b* ((all-mods (vl-inline-mod-in-mods-aux (car x) all-mods)))
        (vl-inline-mods (cdr x) all-mods))))

  (local (in-theory (enable vl-inline-mods)))

  (defthm vl-modulelist-p-of-vl-inline-mods
    (implies (and (force (vl-modulelist-p x))
                  (force (vl-ok-to-inline-list-p x))
                  (force (vl-modulelist-p all-mods)))
             (vl-modulelist-p (vl-inline-mods x all-mods))))

  (defthm vl-modulelist->names-of-vl-inline-mods
    (equal (vl-modulelist->names (vl-inline-mods x all-mods))
           (vl-modulelist->names all-mods))))





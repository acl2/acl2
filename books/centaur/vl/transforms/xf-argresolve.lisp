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
(include-book "../mlib/find-item")
(include-book "../mlib/port-tools")
(include-book "../mlib/find-module")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))


(defxdoc argresolve
  :parents (transforms)
  :short "Converts named argument lists into plain argument lists, and
annotates each plain argument with its direction."

  :long "<p>We prefer to use plain (or positional) argument lists as our
internal representation for module and gate instances.</p>

<p>We have little choice but to support plain argument lists internally,
because the are the only way to instantiate gates and are also the only way to
instantiate modules with ports like @('foo[3:0]') without external names.  But
it is basically straightforward to eliminate all named argument lists by
replacing them with their plain equivalents, reducing the number of syntactic
constructs that later transformations need to deal with.</p>

<p>In this transformation, we simplify module instances as follows:</p>

<ul>

<li>We try to get rid of all the named argument lists by replacing them with
plain argument lists; see @(see vl-convert-namedargs),</li>

<li>We try to annotate each @(see vl-plainarg-p) with its @('dir') and
@('portname') fields, so that the direction and name of many ports will be
available for use in error messages; see @(see vl-annotate-plainargs),</li>

<li>We check that each module instance has the proper arity, and</li>

<li>We check that any \"blank\" ports are connected only to blank arguments,
and vice-versa; see @(see vl-check-blankargs).</li>

</ul>

<p>We also simplify gate instances as follows:</p>

<ul>

<li>We check that the arity of each gate instance is acceptable and annotate
each @(see vl-plainarg-p) with its @('dir') field; see @(see
vl-gateinst-dirassign), and</li>

<li>We check that no \"blank\" arguments are given to gates, and issue a
warning if such a connection is made.  This is actually also done by @(see
vl-gateinst-dirassign), just because it is convenient.</li>

</ul>")


(define vl-find-namedarg ((name stringp)
                          (args vl-namedarglist-p))
  :parents (vl-convert-namedargs)
  :short "Look up an argument by name in a named argument list."
  :long "<p>We once used some fast-alist stuff here, but now I think that it
isn't worthwhile since most module instances either have relatively few
arguments or are instantiated infrequently.  It'd be easy enough to write an
version that uses fast-alists when there are many arguments if performance
becomes a problem.</p>"
  (cond ((atom args)
         nil)
        ((equal (vl-namedarg->name (car args)) name)
         (car args))
        (t
         (vl-find-namedarg name (cdr args))))
  ///
  (defthm vl-find-namedarg-under-iff
    (implies (force (vl-namedarglist-p args))
             (iff (vl-find-namedarg name args)
                  (member-equal name (vl-namedarglist->names args)))))

  (defthm vl-namedarg-p-of-vl-find-namedarg
    (implies (force (vl-namedarglist-p args))
             (equal (vl-namedarg-p (vl-find-namedarg name args))
                    (if (member-equal name (vl-namedarglist->names args))
                        t
                      nil)))))


(define vl-convert-namedargs-aux
  ((args  "Named arguments for some module instance" vl-namedarglist-p)
   (ports "Ports of the submodule"
          (and (vl-portlist-p ports)
               (vl-portlist-named-p ports))))
  :returns (new-args vl-plainarglist-p :hyp :fguard)
  :parents (vl-convert-namedargs)
  :short "Change a named argument list into an equivalent plain (positional)
argument list."
  :long "<p>We walk down the list of ports since they're in the \"right\"
order.  For each port, we look up the corresponding argument and build a
plainarg for it.</p>"

  (b* (((when (atom ports))
        nil)
       (namedarg (vl-find-namedarg (vl-port->name (car ports)) args))
       (plainarg (if namedarg
                     (make-vl-plainarg :expr (vl-namedarg->expr namedarg)
                                       :atts (vl-namedarg->atts namedarg))
                   ;; Otherwise, there's no argument corresponding to this
                   ;; port.  That's bad, but we've already warned about it (see
                   ;; below) and so we're just going to create a blank argument
                   ;; for it.
                   (make-vl-plainarg :expr nil
                                     :atts '(("VL_MISSING_CONNECTION"))))))
    (cons plainarg
          (vl-convert-namedargs-aux args (cdr ports))))
  ///
  (defthm len-of-vl-convert-namedargs-aux
    (equal (len (vl-convert-namedargs-aux args ports))
           (len ports))))


(define vl-convert-namedargs
  ((x        "arguments of a module instance, named or plain" vl-arguments-p)
   (ports    "ports of the submodule"                         vl-portlist-p)
   (warnings "warnings accumulator"                           vl-warninglist-p)
   (inst     "just a context for warnings"                    vl-modinst-p))
  :returns (mv successp
               (warnings vl-warninglist-p :hyp :fguard)
               (new-x    vl-arguments-p   :hyp :fguard))
  :short "Coerce arguments into plain (positional) style."

  :long "<p>We used to require that every port had a connection, and otherwise
caused a fatal warning.  This is no longer the case.</p>

<p>A missing port is obviously a concern and we should at least cause a
warning.  But the Verilog standard does not seem to say that it is an error,
and at least some other Verilog tools, like Verilog-XL and NCVerilog, merely
warn about the situation and then simply treat the port as unconnected.</p>

<p>To be able to handle designs that do this bad thing, we now also tolerate
named arguments with missing ports, and only issue non-fatal warnings.</p>"

  (b* (((vl-arguments x) x)
       ((vl-modinst inst) inst)

       ((unless x.namedp)
        ;; Already uses plain arguments, nothing to do.
        (mv t warnings x))

       (formal-names   (vl-portlist->names ports))
       (actual-names   (vl-namedarglist->names x.args))
       (sorted-formals (mergesort formal-names))
       (sorted-actuals (mergesort actual-names))

       ((unless (vl-portlist-named-p ports))
        ;; BOZO do other Verilog tools tolerate this and just supply Zs
        ;; instead?  Maybe we should tolerate this, too.
        (b* ((w (make-vl-warning
                 :type :vl-bad-instance
                 :msg "~a0 has named arguments, which is illegal since ~m1 ~
                       has unnamed ports."
                 :args (list inst inst.modname)
                 :fatalp t
                 :fn 'vl-convert-namedargs)))
          (mv nil (cons w warnings) x)))

       ((unless (mbe :logic (uniquep actual-names)
                     :exec (same-lengthp actual-names sorted-actuals)))
        (b* ((w (make-vl-warning
                 :type :vl-bad-instance
                 :msg "~a0 illegally has multiple connections for port~s1 ~&2."
                 :args (let ((dupes (duplicated-members actual-names)))
                         (list inst (if (vl-plural-p dupes) "s" "") dupes))
                 :fatalp t
                 :fn 'vl-convert-namedargs)))
          (mv nil (cons w warnings) x)))

       ((unless (subset sorted-actuals sorted-formals))
        ;; There are actuals that aren't formals, i.e., connections to "extra"
        ;; ports that don't exist in the module.  Seems like a pretty clear
        ;; error, and tools like Verilog-XL and NCVerilog reject it.
        (b* ((extra (difference sorted-actuals sorted-formals))
             (w     (make-vl-warning
                     :type :vl-bad-instance
                     :msg "~a0 illegally connects to the following ~s1 in ~
                           ~m2: ~&3"
                     :args (list inst
                                 (if (vl-plural-p extra)
                                     "ports, which do not exist"
                                   "port, which does not exist")
                                 inst.modname extra)
                     :fatalp t
                     :fn 'vl-convert-namedargs)))
          (mv nil (cons w warnings) x)))

       (warnings
        (if (subset sorted-formals sorted-actuals)
            ;; Every formal is connected, looking good...
            warnings
          ;; There are formals that aren't actuals, i.e., we don't have
          ;; connections to some ports.  Bad, bad.  But, we'll only issue a
          ;; NON-FATAL warning, because this is allowed by tools like
          ;; Verilog-XL and NCVerilog.
          (b* ((missing (difference sorted-formals sorted-actuals))
               (w       (make-vl-warning
                         :type :vl-bad-instance
                         :msg "~a0 omits the following ~s1 from ~m2: ~&3"
                         :args (list inst
                                     (if (vl-plural-p missing) "ports" "port")
                                     inst.modname missing)
                         :fatalp nil
                         :fn 'vl-convert-namedargs)))
            (cons w warnings))))

       (plainargs (vl-convert-namedargs-aux x.args ports))
       (new-x     (vl-arguments nil plainargs)))
    (mv t warnings new-x))

  ///
  (defthm vl-arguments->named-of-vl-convert-namedargs
    (implies (force (vl-arguments-p x))
             (b* (((mv successp ?warnings new-x)
                   (vl-convert-namedargs x ports warnings inst)))
               (equal (vl-arguments->namedp new-x)
                      (not successp))))))



(define vl-annotate-plainargs
  ((args "plainargs that typically have no @(':dir') or @(':portname')
         information; we want to annotate them."
         vl-plainarglist-p)
   (ports "corresponding ports for the submodule"
          (and (vl-portlist-p ports)
               (same-lengthp args ports)))
   (portdecls "port declarations for the submodule"
              vl-portdecllist-p)
   (palist "precomputed for fast lookups"
           (equal palist (vl-portdecl-alist portdecls))))
  :returns
  (annotated-args "annotated version of @('args'), semantically equivalent
                   but typically has @(':dir') and @(':portname') information."
                  vl-plainarglist-p :hyp :fguard)
  :parents (argresolve)
  :short "Annotates a plain argument list with port names and directions."
  :long "<p>This is a \"best-effort\" process which may fail to add annotations
to any or all arguments.  Such failures are expected, so we do not generate any
warnings or errors in response to them.</p>

<p>What causes these failures?</p>

<ul>
<li>Not all ports necessarily have a name, so we cannot add a @(':portname')
for every port.</li>
<li>The direction of a port may also not be apparent in some cases; see
@(see vl-port-direction) for details.</li>
</ul>"

  (b* (((when (atom args))
        nil)
       (name (vl-port->name (car ports)))
       (expr (vl-port->expr (car ports)))

       ((mv & dir)
        ;; Our direction inference is pretty sophisticated, and handles even
        ;; compound ports as long as their directions are all the same.  But it
        ;; could also fail and leave dir as NIL.
        (vl-port-direction (car ports) portdecls palist nil))

       ;; If we're dealing with a simple port (which is most of the time), we
       ;; try to propagate active high/low information from its declaration
       ;; back into the argument.  BOZO this stuff is all old and should be
       ;; removed.
       (maybe-decl (and name
                        expr
                        (vl-idexpr-p expr)
                        (equal (vl-idexpr->name expr) name)
                        (vl-find-portdecl name portdecls)))
       (decl-atts (and maybe-decl
                       (vl-portdecl->atts maybe-decl)))

       (arg-atts (vl-plainarg->atts (car args)))
       (arg-atts (if (assoc-equal "VL_ACTIVE_HIGH" decl-atts)
                     (acons "VL_ACTIVE_HIGH" nil arg-atts)
                   arg-atts))
       (arg-atts (if (assoc-equal "VL_ACTIVE_LOW" decl-atts)
                     (acons "VL_ACTIVE_LOW" nil arg-atts)
                   arg-atts))

       (arg-prime  (change-vl-plainarg (car args)
                                       :dir dir         ;; could be nil
                                       :portname name   ;; could be nil
                                       :atts arg-atts)))
    (cons arg-prime
          (vl-annotate-plainargs (cdr args) (cdr ports) portdecls palist))))

(define vl-check-blankargs
  ((args  "plainargs for a module instance" vl-plainarglist-p)
   (ports "corresponding ports for the submodule"
          (and (vl-portlist-p ports)
               (same-lengthp args ports)))
   (inst  "just a context for warnings" vl-modinst-p)
   (warnings "warnings accumulator" vl-warninglist-p))
  :returns (warnings vl-warninglist-p :hyp :fguard)
  :parents (argresolve)
  :short "Warn about expressions connected to blank ports and for blanks
connected to non-blank ports."
  :long "<p>Either of these situations is semantically well-formed and
relatively easy to handle; see @(see blankargs).  But they are also bizarre,
and at least would seem to indicate a situation that could be optimized.  So,
if we see either of these cases, we add a non-fatal warning explaining the
problem.</p>"
  (b* (((when (atom args))
        warnings)
       (portexpr (vl-port->expr (car ports)))
       (argexpr  (vl-plainarg->expr (car args)))
       (warnings
        (if (and argexpr (not portexpr))
            (cons (make-vl-warning
                   :type :vl-warn-blank
                   :msg "~a0 connects the expression ~a1 to the blank port at ~
                         ~l2."
                   :args (list inst argexpr (vl-port->loc (car ports)))
                   :fatalp nil
                   :fn 'vl-check-blankargs)
                  warnings)
          warnings))
       (warnings
        (if (and portexpr (not argexpr))
            (cons (make-vl-warning
                   :type :vl-warn-blank
                   ;; BOZO linking doesn't quite work here for the foreign port.
                   :msg "~a0 gives a blank expression for non-blank ~a1."
                   :args (list inst (car ports))
                   :fatalp nil
                   :fn 'vl-check-blankargs)
                  warnings)
          warnings)))
    (vl-check-blankargs (cdr args) (cdr ports) inst warnings)))


(define vl-arguments-argresolve
  ((x         "arguments of a module instance, named or plain" vl-arguments-p)
   (ports     "ports of the submodule" vl-portlist-p)
   (portdecls "portdecls of the submodule" vl-portdecllist-p)
   (palist    "precomputed for fast lookups"
              (equal palist (vl-portdecl-alist portdecls)))
   (warnings  "warnings accumulator" vl-warninglist-p)
   (inst      "just a context for error messages" vl-modinst-p))
  :returns
  (mv (warnings vl-warninglist-p :hyp :fguard)
      (new-x    vl-arguments-p   :hyp :fguard))
  :parents (argresolve)
  :short "Apply the @(see argresolve) transformation to some arguments."
  :long "<p>This wrapper is really the heart of the @(see argresolve)
transform.  We convert @('x') into a plain argument list, do basic arity/blank
checking, and add direction/name annotations.</p>"

  (b* (((mv successp warnings x)
        (vl-convert-namedargs x ports warnings inst))
       ((unless successp)
        (mv warnings x))
       (plainargs (vl-arguments->args x))

       ((unless (same-lengthp plainargs ports))
        (b* ((nports   (len ports))
             (nargs    (len plainargs))
             (w (make-vl-warning
                 :type :vl-bad-instance
                 ;; Wow this is hideous
                 :msg "~a0 ~s1 ~x2 ~s3, but module ~m4 ~s5 ~x6 ~s7."
                 :args (list inst
                             (if (< nargs nports) "only has" "has")
                             nargs
                             (if (= nargs 1) "argument" "arguments")
                             (vl-modinst->modname inst)
                             (if (< nargs nports) "has" "only has")
                             nports
                             (if (= nports 1) "port" "ports"))
                 :fatalp t
                 :fn 'vl-arguments-argresolve)))
          (mv (cons w warnings) x)))

       (warnings  (vl-check-blankargs plainargs ports inst warnings))
       (plainargs (vl-annotate-plainargs plainargs ports portdecls palist))
       (new-x     (vl-arguments nil plainargs)))
    (mv warnings new-x)))


(define vl-modulelist-portdecl-alists ((x vl-modulelist-p))
  :parents (argresolve)
  :short "Computes the @(see vl-portdecl-alist)s for a list of modules."
  :long "<p>@(call vl-modulelist-portdecl-alists) builds a fast alist
associating each module name to its corresponding @(see vl-portdecl-alist).</p>"

  (if (atom x)
      nil
    (hons-acons (vl-module->name (car x))
                (vl-portdecl-alist (vl-module->portdecls (car x)))
                (vl-modulelist-portdecl-alists (cdr x))))
  ///

  (defthm hons-assoc-equal-of-vl-modulelist-portdecl-alists
    (implies
     (force (vl-modulelist-p x))
     (equal (hons-assoc-equal name (vl-modulelist-portdecl-alists x))
            (let ((mod (vl-find-module name x)))
              (and mod
                   (cons name (vl-portdecl-alist (vl-module->portdecls mod)))))))))


(define vl-modinst-argresolve
  ((x        vl-modinst-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (mpalists (equal mpalists (vl-modulelist-portdecl-alists mods)))
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p :hyp :fguard)
      (new-x    vl-modinst-p     :hyp :fguard))
  :parents (argresolve)
  :short "Resolve arguments in a @(see vl-modinst-p)."

  (b* (((vl-modinst x) x)
       (submod (vl-fast-find-module x.modname mods modalist))
       ((unless submod)
        (b* ((w (make-vl-warning
                 :type :vl-bad-instance
                 :msg "~a0 refers to undefined module ~m1."
                 :args (list x x.modname)
                 :fatalp t
                 :fn 'vl-modinst-argresolve)))
          (mv (cons w warnings) x)))

       ((vl-module submod) submod)
       (palist    (cdr (hons-get x.modname mpalists)))
       ((mv warnings new-args)
        (vl-arguments-argresolve x.portargs submod.ports submod.portdecls
                                 palist warnings x))
       (new-x (change-vl-modinst x :portargs new-args)))
    (mv warnings new-x)))


(define vl-modinstlist-argresolve
  ((x        vl-modinstlist-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (mpalists (equal mpalists (vl-modulelist-portdecl-alists mods)))
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p :hyp :fguard)
      (new-x    vl-modinstlist-p :hyp :fguard))
  :parents (argresolve)
  :short "Resolve arguments in a @(see vl-modinstlist-p)."

  (b* (((when (atom x))
        (mv warnings nil))
       ((mv warnings car)
        (vl-modinst-argresolve (car x) mods modalist mpalists warnings))
       ((mv warnings cdr)
        (vl-modinstlist-argresolve (cdr x) mods modalist mpalists warnings)))
    (mv warnings (cons car cdr))))



(defsection vl-gateinst-dirassign
  :parents (argresolve)
  :short "Arity-checks a gate instance and annotates its arguments with their
directions."

  :long "<p><b>Signature:</b> @(call vl-gateinst-dirassign) returns @('(mv
warnings x-prime)').</p>

<p>We are given @('x'), a gate instance, and @('warnings'), an ordinary @(see
warnings) accumulator.  We return a new gate instance, @('x-prime'), which is
semantically equivalent to @('x').</p>

<p>If @('x') is a well-formed gate instance, then no fatal warnings will be
added and every argument of @('x-prime') will be given the correct @(':dir')
annotation, following the rules in Chapter 7 of the Verilog specification.</p>

<p>If @('x') is a not well-formed (i.e., it has an improper arity), then it
will be returned unchanged and a fatal warning will be added.</p>

<p>We also check for blank arguments in gates during this function.  BOZO this
is convenient but isn't necessarily a very sensible place to do this.</p>"

  (defund vl-plainarglist-assign-dir (dir x)
    "Assign DIR to every argument in the list X."
    (declare (xargs :guard (and (vl-direction-p dir)
                                (vl-plainarglist-p x))))
    (if (consp x)
        (cons (change-vl-plainarg (car x) :dir dir)
              (vl-plainarglist-assign-dir dir (cdr x)))
      nil))

  (defthm vl-plainarglist-p-of-vl-plainarglist-assign-dir
    (implies (and (force (vl-plainarglist-p x))
                  (force (vl-direction-p dir)))
             (vl-plainarglist-p (vl-plainarglist-assign-dir dir x)))
    :hints(("Goal" :in-theory (enable vl-plainarglist-assign-dir))))

  (defund vl-plainarglist-assign-last-dir (dir x)
    "Assign DIR to the last argument in the list X.
     Leave the other arguments unchanged."
    (declare (xargs :guard (and (vl-direction-p dir)
                                (vl-plainarglist-p x))))
    (cond ((atom x)
           nil)
          ((atom (cdr x))
           (list (change-vl-plainarg (car x) :dir dir)))
          (t
           (cons (car x)
                 (vl-plainarglist-assign-last-dir dir (cdr x))))))

  (defthm vl-plainarglist-p-of-vl-plainarglist-assign-last-dir
    (implies (and (force (vl-plainarglist-p x))
                  (force (vl-direction-p dir)))
             (vl-plainarglist-p (vl-plainarglist-assign-last-dir dir x)))
    :hints(("Goal" :in-theory (enable vl-plainarglist-assign-last-dir))))


  (defund vl-gateinst-dirassign (x warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-gateinst-p x)
                                (vl-warninglist-p warnings))
                    :verify-guards nil))

    (b* (((vl-gateinst x) x)
         (nargs (len x.args))

         (warnings
          (if (vl-plainarglist-blankfree-p x.args)
              warnings
            (cons (make-vl-warning
                   :type :vl-warn-blank-gateargs
                   :msg "~a0 has \"blank\" arguments; we treat these as ~
                         unconnected wires, but other tools like Cadence's ~
                         Verilog-XL simulator do not seem to support this."
                   :args (list x)
                   :fatalp nil
                   :fn 'vl-gateinst-dirassign)
                  warnings)))

         ((mv warnings args-prime)
          (case x.type

            ((:vl-and :vl-nand :vl-nor :vl-or :vl-xor :vl-xnor)
             ;; Per Section 7.2 (Page 80), the first terminal is the output and
             ;; the remaining terminals are inputs.
             (if (< nargs 2)
                 (mv (cons (make-vl-warning :type :vl-bad-gate
                                            :msg "~a0 has ~s1."
                                            :args (list x (if (= nargs 1)
                                                              "only one argument"
                                                            "no arguments"))
                                            :fatalp t
                                            :fn 'vl-gateinst-dirassign)
                           warnings)
                     x.args)
               (mv warnings
                   (cons (change-vl-plainarg (car x.args) :dir :vl-output)
                         (vl-plainarglist-assign-dir :vl-input (cdr x.args))))))


            ((:vl-buf :vl-not)
             ;; Per Section 7.3 (Page 81), the last terminal is the input and
             ;; every other terminal is an output.
             (if (< nargs 2)
                 (mv (cons (make-vl-warning :type :vl-bad-gate
                                            :msg "~a0 has ~s1."
                                            :args (list x (if (= nargs 1)
                                                              "only one argument"
                                                            "no arguments"))
                                            :fatalp t
                                            :fn 'vl-gateinst-dirassign)
                           warnings)
                     x.args)
               (mv warnings
                   (vl-plainarglist-assign-last-dir
                    :vl-input
                    (vl-plainarglist-assign-dir :vl-output x.args)))))


            ((:vl-bufif0 :vl-bufif1 :vl-notif0 :vl-notif1
                         :vl-nmos :vl-pmos :vl-rnmos :vl-rpmos)

             ;; Per Section 7.4 (page 82), bufif0..notif1 have exactly three terminals,
             ;; which are output, data in, control in.

             ;; Per Section 7.5 (page 84), nmos..rpmos also have exactly three terminals,
             ;; which are output, data in, and control in.

             (if (/= nargs 3)
                 (mv (cons (make-vl-warning
                            :type :vl-bad-gate
                            :msg "~a0 has ~x1 argument~s2, but must have exactly 3 ~
                                  arguments."
                            :args (list x nargs (if (= nargs 1) "s" ""))
                            :fatalp t
                            :fn 'vl-gateinst-dirassign)
                           warnings)
                     x.args)
               (mv warnings
                   (cons (change-vl-plainarg (car x.args) :dir :vl-output)
                         (vl-plainarglist-assign-dir :vl-input (cdr x.args))))))


            ((:vl-tranif1 :vl-tranif0 :vl-rtranif1 :vl-rtranif0)

             ;; Per Section 7.6 (page 85), tranif1..rtranif0 have three terminals.
             ;; the first two are inout, and the last is control in.

             (if (/= nargs 3)
                 (mv (cons (make-vl-warning
                            :type :vl-bad-gate
                            :msg "~a0 has ~x1 argument~s2, but must have exactly 3 ~
                                  arguments."
                            :args (list x nargs (if (= nargs 1) "s" ""))
                            :fatalp t
                            :fn 'vl-gateinst-dirassign)
                           warnings)
                     x.args)
               (mv warnings
                   (list (change-vl-plainarg (first x.args) :dir :vl-inout)
                         (change-vl-plainarg (second x.args) :dir :vl-inout)
                         (change-vl-plainarg (third x.args) :dir :vl-input)))))


            ((:vl-tran :vl-rtran)

             ;; Per Section 7.6 (page 85), tran and rtran have two terminals, both of
             ;; which are inouts.

             (if (/= nargs 2)
                 (mv (cons (make-vl-warning
                            :type :vl-bad-gate
                            :msg "~a0 has ~x1 argument~s2, but must have exactly 2 ~
                                  arguments."
                            :args (list x nargs (if (= nargs 1) "s" ""))
                            :fatalp t
                            :fn 'vl-gateinst-dirassign)
                           warnings)
                     x.args)
               (mv warnings
                   (list (change-vl-plainarg (first x.args) :dir :vl-inout)
                         (change-vl-plainarg (second x.args) :dir :vl-inout)))))


            ((:vl-cmos :vl-rcmos)

             ;; Per Section 7.7 (page 85), cmos and rcmos have four terminals:
             ;; data out, data in, n-channel control in, p-channel control in.
             ;; It's kind of weird that data-in and data-out aren't inouts.

             (if (/= nargs 4)
                 (mv (cons (make-vl-warning
                            :type :vl-bad-gate
                            :msg "~a0 has ~x1 argument~s2, but must have exactly 4 ~
                                  arguments."
                            :args (list x nargs (if (= nargs 1) "s" ""))
                            :fatalp t
                            :fn 'vl-gateinst-dirassign)
                           warnings)
                     x.args)
               (mv warnings
                   (list (change-vl-plainarg (first x.args) :dir :vl-output)
                         (change-vl-plainarg (second x.args) :dir :vl-input)
                         (change-vl-plainarg (third x.args) :dir :vl-input)
                         (change-vl-plainarg (fourth x.args) :dir :vl-input)))))


            ((:vl-pullup :vl-pulldown)

             ;; Per Section 7.8 (page 86), pullup and pulldown just emit 0/1
             ;; on any connected terminals.  I think this means all the terminals
             ;; are effectively outputs.

             (mv warnings (vl-plainarglist-assign-dir :vl-output x.args)))


            (otherwise
             (prog2$ (er hard 'vl-gateinst-dirassign "Impossible")
                     (mv warnings x.args)))))

         (x-prime (change-vl-gateinst x :args args-prime)))

        (mv warnings x-prime)))

  (local (in-theory (enable vl-gateinst-dirassign)))

  (verify-guards vl-gateinst-dirassign
                 :hints(("Goal"
                         :in-theory (e/d (vl-gatetype-p)
                                         (vl-gatetype-p-of-vl-gateinst->type))
                         :use ((:instance vl-gatetype-p-of-vl-gateinst->type)))))

  (defthm vl-warninglist-p-of-vl-gateinst-dirassign
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gateinst-dirassign x warnings))))
    :hints(("Goal" :in-theory (disable (force)))))

  (defthm vl-gateinst-p-of-vl-gateinst-dirassign
    (implies (force (vl-gateinst-p x))
             (vl-gateinst-p (mv-nth 1 (vl-gateinst-dirassign x warnings))))))



(defsection vl-gateinstlist-dirassign
  :parents (argresolve)
  :short "Projects @(see vl-gateinst-dirassign) across a list of @(see
vl-gateinst-p)s."

  (defund vl-gateinstlist-dirassign (x warnings)
    "Returns (MV WARNINGS-PRIME X-PRIME)"
    (declare (xargs :guard (and (vl-gateinstlist-p x)
                                (vl-warninglist-p warnings))))
    (if (atom x)
        (mv warnings nil)
      (b* (((mv warnings car-prime) (vl-gateinst-dirassign (car x) warnings))
           ((mv warnings cdr-prime) (vl-gateinstlist-dirassign (cdr x) warnings)))
          (mv warnings (cons car-prime cdr-prime)))))

  (local (in-theory (enable vl-gateinstlist-dirassign)))

  (defthm vl-warninglist-p-of-vl-gateinstlist-dirassign
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p (mv-nth 0 (vl-gateinstlist-dirassign x warnings)))))

  (defthm vl-gateinstlist-p-of-vl-gateinstlist-dirassign
    (implies (force (vl-gateinstlist-p x))
             (vl-gateinstlist-p (mv-nth 1 (vl-gateinstlist-dirassign x warnings))))))



(defsection vl-module-argresolve
  :parents (argresolve)
  :short "Apply the @(see argresolve) transformation to a @(see vl-module-p)."

  :long "<p><b>Signature:</b> @(call vl-module-argresolve) returns
@('x-prime').</p>

<p>This is just glue-code to apply @(see vl-modinst-argresolve) to all of the
module instances, and @(see vl-gateinst-dirassign) to all of the gate instances
in the module.</p>"

  (defund vl-module-argresolve (x mods modalist mpalists)
    (declare (xargs :guard (and (vl-module-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (equal mpalists (vl-modulelist-portdecl-alists mods)))))
    (b* (((when (vl-module->hands-offp x))
          x)
         (warnings (vl-module->warnings x))
         ((mv warnings modinsts)
          (vl-modinstlist-argresolve (vl-module->modinsts x) mods modalist mpalists warnings))
         ((mv warnings gateinsts)
          (vl-gateinstlist-dirassign (vl-module->gateinsts x) warnings)))
      (change-vl-module x
                        :warnings warnings
                        :modinsts modinsts
                        :gateinsts gateinsts)))

  (local (in-theory (enable vl-module-argresolve)))

  (defthm vl-module-p-of-vl-module-argresolve
    (implies (and (force (vl-module-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (equal mpalists (vl-modulelist-portdecl-alists mods))))
             (vl-module-p (vl-module-argresolve x mods modalist mpalists))))

  (defthm vl-module->name-of-vl-module-argresolve
    (equal (vl-module->name (vl-module-argresolve x mods modalist mpalists))
           (vl-module->name x))))



(defprojection vl-modulelist-argresolve-aux (x mods modalist mpalists)
  (vl-module-argresolve x mods modalist mpalists)
  :guard (and (vl-modulelist-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods))
              (equal mpalists (vl-modulelist-portdecl-alists mods)))
  :result-type vl-modulelist-p
  :parents (argresolve)
  :rest
  ((defthm vl-modulelist->names-of-vl-modulelist-argresolve-aux
     (equal (vl-modulelist->names
             (vl-modulelist-argresolve-aux x mods modalist mpalists))
            (vl-modulelist->names x)))))



(defsection vl-modulelist-argresolve
  :parents (argresolve)
  :short "Top-level @(see argresolve) transformation for a list of modules."

  :long "<p><b>Signature:</b> @(call vl-modulelist-argresolve) returns a module
list.</p>

<p>All of the real work is done by @(see vl-modulelist-argresolve-aux).  This
function is just a wrapper that builds a @(see vl-modalist) for fast module
lookups and also pre-compute the @(see vl-portdecl-alist)s for all modules
using @(see vl-modulelist-portdecl-alists).</p>"

  (defund vl-modulelist-argresolve (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (b* ((modalist (vl-modalist x))
         (mpalists (vl-modulelist-portdecl-alists x))
         (result   (vl-modulelist-argresolve-aux x x modalist mpalists)))
      (fast-alist-free modalist)
      (fast-alist-free mpalists)
      (fast-alist-free-each-alist-val mpalists)
      result))

  (local (in-theory (enable vl-modulelist-argresolve)))

  (defthm vl-modulelist-p-of-vl-modulelist-argresolve
    (implies (force (vl-modulelist-p x))
             (vl-modulelist-p (vl-modulelist-argresolve x))))

  (defthm vl-modulelist->names-of-vl-modulelist-argresolve
    (equal (vl-modulelist->names (vl-modulelist-argresolve x))
           (vl-modulelist->names x))))



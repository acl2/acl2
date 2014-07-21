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
(include-book "../mlib/find-item")
(include-book "../mlib/port-tools")
(include-book "../mlib/find-module")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))

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

(local (xdoc::set-default-parents argresolve))

(define vl-find-namedarg ((name stringp)
                          (args vl-namedarglist-p))
  :parents (vl-convert-namedargs)
  :short "Look up an argument by name in a named argument list."
  :long "<p>We once used some fast-alist stuff here, but now I think that it
isn't worthwhile since most module instances either have relatively few
arguments or are instantiated infrequently.  It'd be easy enough to write an
version that uses fast-alists when there are many arguments if performance
becomes a problem.</p>"
  :hooks ((:fix :args ((args vl-namedarglist-p))))
  (cond ((atom args)
         nil)
        ((equal (vl-namedarg->name (car args)) name)
         (vl-namedarg-fix (car args)))
        (t
         (vl-find-namedarg name (cdr args))))
  ///
  (defthm vl-find-namedarg-under-iff
    (iff (vl-find-namedarg name args)
         (member-equal name (vl-namedarglist->names args))))

  (defthm vl-namedarg-p-of-vl-find-namedarg
    (equal (vl-namedarg-p (vl-find-namedarg name args))
           (if (member-equal name (vl-namedarglist->names args))
               t
             nil))))


(define vl-convert-namedargs-aux
  ((args   vl-namedarglist-p "Named arguments for some module instance")
   (ports vl-portlist-p      "Ports of the submodule"))
  :guard (not (member nil (vl-portlist->names ports)))
  :returns (new-args vl-plainarglist-p)
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
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-arguments-p))
  :parents (argresolve)
  :short "Coerce arguments into plain (positional) style."

  :long "<p>We used to require that every port had a connection, and otherwise
caused a fatal warning.  This is no longer the case.</p>

<p>A missing port is obviously a concern and we should at least cause a
warning.  But the Verilog-2005 standard does not seem to say that it is an error,
and at least some other Verilog tools, like Verilog-XL and NCVerilog, merely
warn about the situation and then simply treat the port as unconnected.</p>

<p>To be able to handle designs that do this bad thing, we now also tolerate
named arguments with missing ports, and only issue non-fatal warnings.</p>"

  (b* ((x    (vl-arguments-fix x))
       (inst (vl-modinst-fix inst))
       ((vl-modinst inst) inst)

       ((when (eq (vl-arguments-kind x) :plain))
        ;; Already uses plain arguments, nothing to do.
        (mv t (ok) x))

       (x.args         (vl-arguments-named->args x))
       (formal-names   (vl-portlist->names ports))
       (actual-names   (vl-namedarglist->names x.args))
       (sorted-formals (mergesort formal-names))
       (sorted-actuals (mergesort actual-names))

       ((when (member nil (vl-portlist->names ports)))
        ;; BOZO do other Verilog tools tolerate this and just supply Zs
        ;; instead?  Maybe we should tolerate this, too.
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0 has named arguments, which is illegal since ~m1 ~
                         has unnamed ports."
                   :args (list inst inst.modname))
            x))

       ((unless (mbe :logic (uniquep actual-names)
                     :exec (same-lengthp actual-names sorted-actuals)))
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0 illegally has multiple connections for port~s1 ~
                         ~&2."
                   :args (let ((dupes (duplicated-members actual-names)))
                           (list inst (if (vl-plural-p dupes) "s" "") dupes)))
            x))

       ((unless (subset sorted-actuals sorted-formals))
        ;; There are actuals that aren't formals, i.e., connections to "extra"
        ;; ports that don't exist in the module.  Seems like a pretty clear
        ;; error, and tools like Verilog-XL and NCVerilog reject it.
        (b* ((extra (difference sorted-actuals sorted-formals)))
          (mv nil
              (fatal :type :vl-bad-instance
                     :msg "~a0 illegally connects to the following ~s1 in ~
                           ~m2: ~&3"
                     :args (list inst
                                 (if (vl-plural-p extra)
                                     "ports, which do not exist"
                                   "port, which does not exist")
                                 inst.modname extra))
              x)))

       (warnings
        (if (subset sorted-formals sorted-actuals)
            ;; Every formal is connected, looking good...
            (ok)
          ;; There are formals that aren't actuals, i.e., we don't have
          ;; connections to some ports.  Bad, bad.  But, we'll only issue a
          ;; NON-FATAL warning, because this is allowed by tools like
          ;; Verilog-XL and NCVerilog.
          (b* ((missing (difference sorted-formals sorted-actuals)))
            (warn :type :vl-bad-instance
                  :msg "~a0 omits the following ~s1 from ~m2: ~&3"
                  :args (list inst
                              (if (vl-plural-p missing) "ports" "port")
                              inst.modname missing)))))

       (plainargs (vl-convert-namedargs-aux x.args ports))
       (new-x     (make-vl-arguments-plain :args plainargs)))
    (mv t (ok) new-x))

  ///
  (defthm vl-arguments->named-of-vl-convert-namedargs
    (implies (force (vl-arguments-p x))
             (b* (((mv successp ?warnings new-x)
                   (vl-convert-namedargs x ports warnings inst)))
               (equal (vl-arguments-kind new-x)
                      (if successp
                          :plain
                        :named))))))


(define vl-annotate-plainargs
  ((args "plainargs that typically have no @(':dir') or @(':portname')
         information; we want to annotate them."
         vl-plainarglist-p)
   (ports "corresponding ports for the submodule"
          vl-portlist-p)
   (portdecls "port declarations for the submodule"
              vl-portdecllist-p)
   (palist "precomputed for fast lookups"
           (equal palist (vl-portdecl-alist portdecls))))
  :guard (same-lengthp args ports)
  :returns
  (annotated-args "annotated version of @('args'), semantically equivalent
                   but typically has @(':dir') and @(':portname') information."
                  vl-plainarglist-p)
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
  :short "Warn about expressions connected to blank ports and for blanks
connected to non-blank ports."
  ((args  "plainargs for a module instance" vl-plainarglist-p)
   (ports "corresponding ports for the submodule"
          vl-portlist-p)
   (inst  "just a context for warnings" vl-modinst-p)
   (warnings "warnings accumulator" vl-warninglist-p))
  :guard (same-lengthp args ports)
  :returns (warnings vl-warninglist-p)
  :long "<p>Either of these situations is semantically well-formed and
relatively easy to handle; see @(see blankargs).  But they are also bizarre,
and at least would seem to indicate a situation that could be optimized.  So,
if we see either of these cases, we add a non-fatal warning explaining the
problem.</p>"
  (b* (((when (atom args))
        (ok))
       (inst     (vl-modinst-fix inst))
       (port1    (vl-port-fix (car ports)))
       ((vl-port port1) port1)
       (argexpr  (vl-plainarg->expr (car args)))
       (warnings
        (if (and argexpr (not port1.expr))
            (warn :type :vl-warn-blank
                  :msg "~a0 connects the expression ~a1 to the blank port at ~
                        ~l2."
                  :args (list inst argexpr port1.loc))
          (ok)))
       (warnings
        (if (and port1.expr (not argexpr))
            (warn :type :vl-warn-blank
                  ;; BOZO linking doesn't quite work here for the foreign port.
                  :msg "~a0 gives a blank expression for non-blank ~a1."
                  :args (list inst port1))
          (ok))))
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
  (mv (warnings vl-warninglist-p)
      (new-x    vl-arguments-p))
  :short "Apply the @(see argresolve) transformation to some arguments."
  :long "<p>This wrapper is really the heart of the @(see argresolve)
transform.  We convert @('x') into a plain argument list, do basic arity/blank
checking, and add direction/name annotations.</p>"

  (b* (((mv successp warnings x)
        (vl-convert-namedargs x ports warnings inst))
       ((unless successp)
        (mv (ok) x))
       (inst      (vl-modinst-fix inst))
       (plainargs (vl-arguments-plain->args x))

       ((unless (same-lengthp plainargs ports))
        (b* ((nports   (len ports))
             (nargs    (len plainargs)))
          (mv (fatal :type :vl-bad-instance
                     ;; Wow this is hideous
                     :msg "~a0 ~s1 ~x2 ~s3, but module ~m4 ~s5 ~x6 ~s7."
                     :args (list inst
                                 (if (< nargs nports) "only has" "has")
                                 nargs
                                 (if (= nargs 1) "argument" "arguments")
                                 (vl-modinst->modname inst)
                                 (if (< nargs nports) "has" "only has")
                                 nports
                                 (if (= nports 1) "port" "ports")))
              x)))
       (warnings  (vl-check-blankargs plainargs ports inst warnings))
       (plainargs (vl-annotate-plainargs plainargs ports portdecls palist))
       (new-x     (make-vl-arguments-plain :args plainargs)))
    (mv (ok) new-x)))


(define vl-modulelist-portdecl-alists ((x vl-modulelist-p))
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
    (equal (hons-assoc-equal name (vl-modulelist-portdecl-alists x))
           (let ((mod (vl-find-module name x)))
             (and mod
                  (cons name (vl-portdecl-alist (vl-module->portdecls mod))))))))


(define vl-modinst-argresolve
  :short "Resolve arguments in a @(see vl-modinst-p)."
  ((x        vl-modinst-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (mpalists (equal mpalists (vl-modulelist-portdecl-alists mods)))
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-modinst-p))
  (b* ((x (vl-modinst-fix x))
       ((vl-modinst x) x)
       (submod (vl-fast-find-module x.modname mods modalist))
       ((unless submod)
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0 refers to undefined module ~m1."
                   :args (list x x.modname))
            x))
       ((vl-module submod) submod)
       (palist    (cdr (hons-get x.modname mpalists)))
       ((mv warnings new-args)
        (vl-arguments-argresolve x.portargs submod.ports submod.portdecls
                                 palist warnings x))
       (new-x (change-vl-modinst x :portargs new-args)))
    (mv (ok) new-x)))


(define vl-modinstlist-argresolve
  ((x        vl-modinstlist-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (mpalists (equal mpalists (vl-modulelist-portdecl-alists mods)))
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-modinstlist-p))
  :parents (argresolve)
  :short "Resolve arguments in a @(see vl-modinstlist-p)."
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings car)
        (vl-modinst-argresolve (car x) mods modalist mpalists warnings))
       ((mv warnings cdr)
        (vl-modinstlist-argresolve (cdr x) mods modalist mpalists warnings)))
    (mv warnings (cons car cdr))))


(define vl-plainarglist-assign-dir ((dir vl-direction-p)
                                    (x   vl-plainarglist-p))
  :parents (vl-gateinst-dirassign)
  :returns (new-x vl-plainarglist-p)
  :short "Assign DIR to every argument in the list X."
  (if (atom x)
      nil
    (cons (change-vl-plainarg (car x) :dir (vl-direction-fix dir))
          (vl-plainarglist-assign-dir dir (cdr x)))))

(define vl-plainarglist-assign-last-dir ((dir vl-direction-p)
                                         (x vl-plainarglist-p))
  :parents (vl-gateinst-dirassign)
  :returns (new-x vl-plainarglist-p)
  :short "Assign DIR to the last argument in the list X, leave the other
          arguments unchanged."
  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (list (change-vl-plainarg (car x) :dir (vl-direction-fix dir))))
        (t
         (cons (vl-plainarg-fix (car x))
               (vl-plainarglist-assign-last-dir dir (cdr x))))))

(define vl-gateinst-dirassign
  :short "Arity-checks a gate instance and annotates its arguments with their
          directions."
  ((x        vl-gateinst-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-gateinst-p "Semantically equivalent to @('x')."))

  :long "<p>If @('x') is a well-formed gate instance, then no fatal warnings
will be added and every argument of @('x-prime') will be given the correct
@(':dir') annotation, following the rules in Chapter 7 of the Verilog-2005
specification.</p>

<p>If @('x') is a not well-formed (i.e., it has an improper arity), then it
will be returned unchanged and a fatal warning will be added.</p>

<p>We also check for blank arguments in gates during this function.  BOZO this
is convenient but isn't necessarily a very sensible place to do this.</p>"

  :verify-guards nil

  (b* ((x (vl-gateinst-fix x))
       ((vl-gateinst x) x)
       (nargs (len x.args))

       (warnings
        (if (vl-plainarglist-blankfree-p x.args)
            (ok)
          (warn :type :vl-warn-blank-gateargs
                :msg "~a0 has \"blank\" arguments; we treat these as ~
                      unconnected wires, but other tools like Cadence's ~
                      Verilog-XL simulator do not seem to support this."
                :args (list x))))

       ((mv warnings args-prime)
        (case x.type

          ((:vl-and :vl-nand :vl-nor :vl-or :vl-xor :vl-xnor)
           ;; Per Section 7.2 (Page 80), the first terminal is the output and
           ;; the remaining terminals are inputs.
           (if (< nargs 2)
               (mv (fatal :type :vl-bad-gate
                          :msg "~a0 has ~s1."
                          :args (list x (if (= nargs 1)
                                            "only one argument"
                                          "no arguments")))
                   x.args)
             (mv (ok)
                 (cons (change-vl-plainarg (car x.args) :dir :vl-output)
                       (vl-plainarglist-assign-dir :vl-input (cdr x.args))))))

          ((:vl-buf :vl-not)
           ;; Per Section 7.3 (Page 81), the last terminal is the input and
           ;; every other terminal is an output.
           (if (< nargs 2)
               (mv (fatal :type :vl-bad-gate
                          :msg "~a0 has ~s1."
                          :args (list x (if (= nargs 1)
                                            "only one argument"
                                          "no arguments")))
                   x.args)
             (mv (ok)
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
               (mv (fatal :type :vl-bad-gate
                          :msg "~a0 has ~x1 argument~s2, but must have ~
                                exactly 3 arguments."
                          :args (list x nargs (if (= nargs 1) "s" "")))
                   x.args)
             (mv (ok)
                 (cons (change-vl-plainarg (car x.args) :dir :vl-output)
                       (vl-plainarglist-assign-dir :vl-input (cdr x.args))))))


          ((:vl-tranif1 :vl-tranif0 :vl-rtranif1 :vl-rtranif0)

           ;; Per Section 7.6 (page 85), tranif1..rtranif0 have three terminals.
           ;; the first two are inout, and the last is control in.

           (if (/= nargs 3)
               (mv (fatal :type :vl-bad-gate
                          :msg "~a0 has ~x1 argument~s2, but must have ~
                                exactly 3 arguments."
                          :args (list x nargs (if (= nargs 1) "s" "")))
                   x.args)
             (mv (ok)
                 (list (change-vl-plainarg (first x.args) :dir :vl-inout)
                       (change-vl-plainarg (second x.args) :dir :vl-inout)
                       (change-vl-plainarg (third x.args) :dir :vl-input)))))


          ((:vl-tran :vl-rtran)

           ;; Per Section 7.6 (page 85), tran and rtran have two terminals, both of
           ;; which are inouts.

           (if (/= nargs 2)
               (mv (fatal :type :vl-bad-gate
                          :msg "~a0 has ~x1 argument~s2, but must have ~
                                exactly 2 arguments."
                          :args (list x nargs (if (= nargs 1) "s" "")))
                   x.args)
             (mv (ok)
                 (list (change-vl-plainarg (first x.args) :dir :vl-inout)
                       (change-vl-plainarg (second x.args) :dir :vl-inout)))))


          ((:vl-cmos :vl-rcmos)

           ;; Per Section 7.7 (page 85), cmos and rcmos have four terminals:
           ;; data out, data in, n-channel control in, p-channel control in.
           ;; It's kind of weird that data-in and data-out aren't inouts.

           (if (/= nargs 4)
               (mv (fatal :type :vl-bad-gate
                          :msg "~a0 has ~x1 argument~s2, but must have ~
                                exactly 4 arguments."
                          :args (list x nargs (if (= nargs 1) "s" "")))
                   x.args)
             (mv (ok)
                 (list (change-vl-plainarg (first x.args) :dir :vl-output)
                       (change-vl-plainarg (second x.args) :dir :vl-input)
                       (change-vl-plainarg (third x.args) :dir :vl-input)
                       (change-vl-plainarg (fourth x.args) :dir :vl-input)))))


          ((:vl-pullup :vl-pulldown)

           ;; Per Section 7.8 (page 86), pullup and pulldown just emit 0/1
           ;; on any connected terminals.  I think this means all the terminals
           ;; are effectively outputs.

           (mv (ok) (vl-plainarglist-assign-dir :vl-output x.args)))


          (otherwise
           (progn$ (impossible)
                   (mv (ok) x.args)))))

       (x-prime (change-vl-gateinst x :args args-prime)))

    (mv (ok) x-prime))
  ///
  (verify-guards vl-gateinst-dirassign))

(define vl-gateinstlist-dirassign
  :short "Projects @(see vl-gateinst-dirassign) across a list of @(see
vl-gateinst-p)s."
  ((x        vl-gateinstlist-p)
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-x vl-gateinstlist-p))
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings car-prime) (vl-gateinst-dirassign (car x) warnings))
       ((mv warnings cdr-prime) (vl-gateinstlist-dirassign (cdr x) warnings)))
    (mv warnings (cons car-prime cdr-prime))))

(define vl-module-argresolve
  :short "Apply the @(see argresolve) transformation to a @(see vl-module-p)."
  :long "<p>This is just glue-code to apply @(see vl-modinst-argresolve) to all
of the module instances, and @(see vl-gateinst-dirassign) to all of the gate
instances in the module.</p>"
  ((x        vl-module-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   (mpalists (equal mpalists (vl-modulelist-portdecl-alists mods))))
  :returns (new-x vl-module-p)
  (b* (((when (vl-module->hands-offp x))
        (vl-module-fix x))
       (warnings (vl-module->warnings x))
       ((mv warnings modinsts)
        (vl-modinstlist-argresolve (vl-module->modinsts x) mods modalist mpalists warnings))
       ((mv warnings gateinsts)
        (vl-gateinstlist-dirassign (vl-module->gateinsts x) warnings)))
    (change-vl-module x
                      :warnings warnings
                      :modinsts modinsts
                      :gateinsts gateinsts)))

(defprojection vl-modulelist-argresolve-aux ((x    vl-modulelist-p)
                                             (mods vl-modulelist-p)
                                             (modalist (equal modalist (vl-modalist mods)))
                                             (mpalists (equal mpalists (vl-modulelist-portdecl-alists mods))))
  :returns (new-x vl-modulelist-p)
  (vl-module-argresolve x mods modalist mpalists))

(define vl-modulelist-argresolve
  :short "Apply @(see argresolve) to a list of modules."
  ((x vl-modulelist-p))
  :returns (new-x vl-modulelist-p)
  :long "<p>The real work is done by @(see vl-modulelist-argresolve-aux).  This
function is just a wrapper that builds a @(see vl-modalist) for fast module
lookups and also pre-compute the @(see vl-portdecl-alist)s for all modules
using @(see vl-modulelist-portdecl-alists).</p>"

  (b* ((modalist (vl-modalist x))
       (mpalists (vl-modulelist-portdecl-alists x))
       (result   (vl-modulelist-argresolve-aux x x modalist mpalists)))
    (fast-alist-free modalist)
    (fast-alist-free mpalists)
    (fast-alist-free-each-alist-val mpalists)
    result))

(define vl-design-argresolve
  :short "Top-level @(see argresolve) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x))
    (change-vl-design x :mods (vl-modulelist-argresolve x.mods))))

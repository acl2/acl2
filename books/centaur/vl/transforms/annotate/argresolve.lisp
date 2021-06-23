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
(include-book "../../mlib/port-tools")
(include-book "../../mlib/modnamespace")
(include-book "../../mlib/hid-tools")
(include-book "../../mlib/find")
(local (include-book "../../util/arithmetic"))
(local (include-book "../../util/osets"))
(local (std::add-default-post-define-hook :fix))

(local (in-theory (disable (tau-system))))

(defxdoc argresolve
  :parents (annotate)
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

<li>We try to expand out any SystemVerilog @('.*')-style port connections,</li>

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


; -----------------------------------------------------------------------------
;
;                            Gate Instances
;
; -----------------------------------------------------------------------------

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

(with-output
  :evisc (:gag-mode (evisc-tuple 5 10 nil nil))
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
    :prepwork ((local (in-theory (disable member-equal-when-member-equal-of-cdr-under-iff
                                          promote-member-equal-to-membership
                                          acl2::true-listp-member-equal
                                          double-containment
                                          vl-warninglist-p-when-not-consp
                                          subsetp-equal-when-first-two-same-yada-yada
                                          default-car default-cdr))))
    ///
    (verify-guards vl-gateinst-dirassign
      :hints((and stable-under-simplificationp
                  '(:in-theory (e/d (vl-gatetype-p)
                                    (vl-gatetype-p-of-vl-gateinst->type))
                    :use ((:instance vl-gatetype-p-of-vl-gateinst->type))))))))

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




; -----------------------------------------------------------------------------
;
;                            Module Instances
;
; -----------------------------------------------------------------------------


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

(FTY::DEFALIST VL-NAMEDARG-ALIST
  :KEY-TYPE STRINGP
  :VAL-TYPE VL-NAMEDARG-P
  :KEYP-OF-NIL NIL
  :VALP-OF-NIL NIL)

(DEFINE
  VL-NAMEDARGLIST-ALIST
  ((X VL-NAMEDARGLIST-P) ACC)
  :RETURNS
  (ALIST (EQUAL (VL-NAMEDARG-ALIST-P ALIST)
                (VL-NAMEDARG-ALIST-P ACC)))
  :SHORT
  (CAT "Extend an alist by binding the names of @(see VL-"
       (SYMBOL-NAME 'NAMEDARG)
       ")s to their definitions.")
  :LONG
  (CAT "<p>This can be used as an alternative to @(see "
       (SYMBOL-NAME 'VL-FIND-NAMEDARG)
       ") when you need to perform a lot of lookups.</p>")
  (IF (ATOM X)
      ACC
      (CONS (CONS (VL-NAMEDARG->NAME (CAR X))
                  (VL-NAMEDARG-FIX (CAR X)))
            (VL-NAMEDARGLIST-ALIST (CDR X) ACC)))
  ///
  (DEFTHM
    LOOKUP-IN-VL-NAMEDARGLIST-ALIST-ACC-ELIM
    (IMPLIES (SYNTAXP (NOT (EQUAL ACC ''NIL)))
             (EQUAL (HONS-ASSOC-EQUAL NAME (VL-NAMEDARGLIST-ALIST X ACC))
                    (OR (HONS-ASSOC-EQUAL NAME (VL-NAMEDARGLIST-ALIST X NIL))
                        (HONS-ASSOC-EQUAL NAME ACC)))))
  (DEFTHM
    LOOKUP-IN-VL-NAMEDARGLIST-ALIST-FAST
    (IMPLIES (STRINGP NAME)
             (EQUAL (HONS-ASSOC-EQUAL NAME (VL-NAMEDARGLIST-ALIST X NIL))
                    (LET ((VAL (VL-FIND-NAMEDARG NAME X)))
                         (AND VAL (CONS NAME VAL)))))
    :HINTS (("Goal" :IN-THEORY (DISABLE (:D VL-NAMEDARGLIST-ALIST))
             :INDUCT (VL-NAMEDARGLIST-ALIST X NIL)
             :EXPAND ((VL-NAMEDARGLIST-ALIST X NIL)
                      (VL-FIND-NAMEDARG NAME X))))))

(define vl-make-namedarg-alist ((x vl-namedarglist-p))
  :returns (palist vl-namedarg-alist-p :hyp :guard)
  :short "Build a fast alist associating the name of each port declaration with
the whole @(see vl-namedarg-p) object."
  (make-fast-alist (vl-namedarglist-alist x nil))
  ///
  (local (defthm l0
           (implies (alistp acc)
                    (alistp (vl-namedarglist-alist x acc)))
           :hints(("Goal" :in-theory (enable vl-namedarglist-alist)))))

  (defthm alistp-of-vl-make-namedarg-alist
    (alistp (vl-make-namedarg-alist x)))

  (defthm hons-assoc-equal-of-vl-make-namedarg-alist
    (implies (stringp k)
             (equal (hons-assoc-equal k (vl-make-namedarg-alist x))
                    (and (vl-find-namedarg k x)
                         (cons k (vl-find-namedarg k x)))))
    :hints(("Goal" :in-theory (e/d (vl-find-namedarg
                                    vl-namedarglist-alist)
                                   (vl-find-namedarg-under-iff))))))


(define vl-fast-find-namedarg
  ((name      stringp)
   (namedargs vl-namedarglist-p)
   (alist     (equal alist (vl-make-namedarg-alist namedargs))))
  :short "Faster version of @(see vl-find-namedarg), where the search is done
  as an fast-alist lookup rather than as string search."
  :enabled t
  :hooks nil
  (mbe :logic (vl-find-namedarg name namedargs)
       :exec (cdr (hons-get name alist))))

(define vl-convert-namedargs-aux
  ((args  vl-namedarglist-p "Named arguments for some module instance")
   (ports vl-portlist-p     "Ports of the submodule"))
  :guard (not (member nil (vl-portlist->names ports)))
  :returns (new-args vl-plainarglist-p)
  :parents (vl-convert-namedargs)
  :short "Change a named argument list into an equivalent plain (positional)
argument list."

  :long "<p>We walk down the list of ports since they're in the \"right\"
order.  For each port, we look up the corresponding argument and build a
plainarg for it.</p>

<p>Note: we assume here that @('.*') style ports have already been expanded,
i.e., if any port does is missing a corresponding argument, then there really
is no argument to that port and we're to infer a blank connection.</p>"

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



(define vl-convert-namedargs-aux-fal
  ((args  vl-namedarglist-p "Named arguments for some module instance")
   (alist (equal alist (vl-make-namedarg-alist args)))
   (ports vl-portlist-p     "Ports of the submodule"))
  :guard (not (member nil (vl-portlist->names ports)))
  :parents (vl-convert-namedargs)
  :enabled t
  :guard-hints (("goal" :in-theory (enable vl-convert-namedargs-aux)
                 :expand ((:Free (alist) (vl-convert-namedargs-aux-fal args alist (cdr ports))))))
  (mbe :logic (vl-convert-namedargs-aux args ports)
       :exec
       (b* (((when (atom ports))
             nil)
            (namedarg (vl-fast-find-namedarg (vl-port->name (car ports)) args alist))
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
               (vl-convert-namedargs-aux-fal args alist (cdr ports))))))

(define vl-create-namedarg-for-dotstar
  :parents (vl-expand-dotstar-arguments)
  :short "Create a single missing argument for a @('.*') connection."
  ((name     stringp           "Name of the submodule port that is implicitly connected by @('.*').")
   (ss       vl-scopestack-p   "Scopestack for the superior module.")
   (warnings vl-warninglist-p  "Warnings accumulator.")
   (inst     vl-modinst-p      "Context for warnings."))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-args vl-namedarglist-p))

  (b* ((name              (string-fix name))
       ((vl-modinst inst) (vl-modinst-fix inst))

       (look (vl-scopestack-find-item name ss))
       ((unless look)
        (mv nil
            (fatal :type :vl-bad-dotstar-connection
                   :msg "~a0: using .* syntax to instantiate ~m1, but there is ~
                         no declaration for port ~s2."
                   :args (list inst inst.modname name))
            nil))

       ((when (eq (tag look) :vl-vardecl))
        ;; We are supposed to check that, e.g., the variable has a compatible
        ;; type with the port.  I don't think we want to / can do this yet,
        ;; because we need to wait for unparameterization.  So at this point
        ;; I'm just going to call it good enough.
        ;;
        ;; We'll mark this as name-only, because name-only ports are supposed
        ;; to also have this datatype compatibility restriction.  So, if we
        ;; ever implement such a check downstream, it'll catch ports that were
        ;; literally .name, and also ports that were introduced by .*
        ;; connections.
        (b* ((new-arg (make-vl-namedarg :name       name
                                        :expr       (vl-idexpr name)
                                        :nameonly-p t
                                        :atts       nil)))
          (mv t (ok) (list new-arg))))

       ((when (eq (tag look) :vl-modinst))
        ;; Possibly an interface that needs to be connected to a compatible
        ;; interface port.  We definitely need to check somewhere that the
        ;; port type and the argument type are both of the same interface.
        ;;
        ;; However, I don't think this is the right place to do that, because
        ;; we're going to have to check it for interface compatibility for
        ;; other kinds of arguments like explicit .foo(foo) style arguments or
        ;; positional arguments somewhere else, anyway.
        ;;
        ;; So, all we'll require here is that the module instance is actually
        ;; an interface instead of something else (e.g., an actual submodule or
        ;; a UDP.)  The actual interface compatibility checking is done later;
        ;; see for instance VL-PLAINARG-EXPRSIZE and failure tests such as
        ;; failtests/port1.v.
        (b* (((vl-modinst look))
             (mod/if (vl-scopestack-find-definition look.modname ss))
             ((unless mod/if)
              (mv nil
                  (fatal :type :vl-bad-dotstar-connection
                         :msg "~a0: trying to resolve .* connection for ~
                               ~w1 (type ~m2): but ~m2 is not defined."
                         :args (list inst name look.modname))
                  nil))
             ((when (eq (tag mod/if) :vl-interface))
              ;; Good enough for now.  Again we'll mark it name-only.
              (b* ((new-arg (make-vl-namedarg :name       name
                                              :expr       (vl-idexpr name)
                                              :nameonly-p t
                                              :atts       nil)))
                (mv t (ok) (list new-arg)))))
          (mv nil
              (fatal :type :vl-bad-dotstar-connection
                     :msg "~a0: using .* syntax to instantiate ~m1 would ~
                           result in connecting port ~s2 to ~a3, which is ~
                           an instance of a ~x4."
                     :args (list inst inst.modname name look (tag mod/if)))
              nil)))

       ((when (eq (tag look) :vl-interfaceport))
        ;; As above in the modinst case, we aren't going to try to check any
        ;; kind of compatibility here.  We did at least find an interface,
        ;; and that's good enough.
        (b* ((new-arg (make-vl-namedarg :name       name
                                        :expr       (vl-idexpr name)
                                        :nameonly-p t
                                        :atts       nil)))
          (mv t (ok) (list new-arg)))))

    (mv nil
        (fatal :type :vl-bad-dotstar-connection
               :msg "~a0: using .* syntax to instantiate ~m1 would result in ~
                     connecting port ~s2 to ~a3, which has unsupported type ~
                     ~x4."
               :args (list inst inst.modname name look (tag look)))
        nil))
  ///
  (more-returns
   (new-args true-listp :rule-classes :type-prescription)))


(define vl-create-namedargs-for-dotstar
  :parents (vl-expand-dotstar-arguments)
  :short "Create the arguments that @('.*') expands to."
  ((missing  string-listp      "Names of submodule ports that aren't explicitly connected.")
   (ss       vl-scopestack-p   "Scopestack for the superior module.")
   (warnings vl-warninglist-p  "Warnings accumulator.")
   (inst     vl-modinst-p      "Context for warnings."))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-args vl-namedarglist-p))
  (b* (((when (atom missing))
        (mv t (ok) nil))
       ((mv okp1 warnings args1) (vl-create-namedarg-for-dotstar (car missing) ss warnings inst))
       ((mv okp2 warnings args2) (vl-create-namedargs-for-dotstar (cdr missing) ss warnings inst)))
    (mv (and okp1 okp2)
        warnings
        (append args1 args2)))
  ///
  (more-returns
   (new-args true-listp :rule-classes :type-prescription)))

(define vl-expand-dotstar-arguments
  :parents (vl-convert-namedargs)
  :short "Expand @('.*') style arguments into explicit .foo(foo) format."
  ((args     vl-namedarglist-p "The explicit arguments besides the @('.*'), i.e., @('.foo(1), .bar(2), ...').")
   (ss       vl-scopestack-p   "Scopestack for the superior module.")
   (ports    vl-portlist-p     "Ports of the submodule.")
   (warnings vl-warninglist-p  "Warnings accumulator.")
   (inst     vl-modinst-p      "Just a context for warnings."))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-args vl-namedarglist-p))
  (b* ((args              (vl-namedarglist-fix args))
       ((vl-modinst inst) (vl-modinst-fix inst))

       (portnames (vl-portlist->names ports))
       ((when (member nil portnames))
        (mv nil
            (fatal :type :vl-bad-instance
                   :msg "~a0 has named arguments, which is illegal since ~m1 ~
                         has unnamed ports."
                   :args (list inst inst.modname))
            args))

       (argnames (vl-namedarglist->names args))
       (missing  (difference (mergesort portnames) (mergesort argnames)))
       (warnings (if missing
                     warnings
                   (warn :type :vl-warn-empty-dotstar
                         :msg "~a0 mentions .*, but explicitly connects all of ~
                               the ports of ~m1, so the .* isn't doing anything."
                         :args (list inst inst.modname))))

       ((mv okp warnings inferred-args)
        (vl-create-namedargs-for-dotstar missing ss warnings inst))
       ((unless okp)
        ;; Already warned
        (mv nil warnings args))

       (new-args (append inferred-args args)))

    (mv t warnings new-args)))

(define vl-convert-namedargs
  ((x        "arguments of a module instance, named or plain" vl-arguments-p)
   (ss       "scope stack for the superior module"            vl-scopestack-p)
   (ports    "ports of the submodule"                         vl-portlist-p)
   (warnings "warnings accumulator"                           vl-warninglist-p)
   (inst     "just a context for warnings"                    vl-modinst-p))
  :returns (mv (successp booleanp :rule-classes :type-prescription)
               (warnings vl-warninglist-p)
               (new-x    vl-arguments-p))
  :short "Coerce arguments into plain (positional) style."

  :long "<p>We used to require that every port had a connection, and otherwise
caused a fatal warning.  This is no longer the case.</p>

<p>A missing port is obviously a concern and we should at least cause a
warning.  But the Verilog-2005 standard does not seem to say that it is an error,
and at least some other Verilog tools, like Verilog-XL and NCVerilog, merely
warn about the situation and then simply treat the port as unconnected.</p>

<p>To be able to handle designs that do this bad thing, we now also tolerate
named arguments with missing ports, and only issue non-fatal warnings.</p>"

  (declare (ignorable ss))

  (b* ((x    (vl-arguments-fix x))
       (inst (vl-modinst-fix inst))
       ((vl-modinst inst) inst)

       ;; If it's an empty plainarglist, treat it as an empty namedarglist,
       ;; because otherwise we get bad instance errors.
       (x (vl-arguments-case x
            :vl-arguments-plain (if (atom x.args)
                                    (make-vl-arguments-named :args nil :starp nil)
                                  x)
            :otherwise x))

       ((when (eq (vl-arguments-kind x) :vl-arguments-plain))
        ;; Already uses plain arguments, nothing to do.
        (mv t (ok) x))

       ((mv okp warnings args)
        ;; Expand out .* syntax into explicit arguments, if necessary
        (if (vl-arguments-named->starp x)
            (vl-expand-dotstar-arguments (vl-arguments-named->args x) ss ports warnings inst)
          ;; No .* is present, nothing to do
          (mv t (ok) (vl-arguments-named->args x))))
       ((unless okp)
        ;; Already warned.
        (mv nil warnings x))

       (formal-names   (vl-portlist->names ports))
       (actual-names   (vl-namedarglist->names args))
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

       (plainargs (mbe :logic (vl-convert-namedargs-aux args ports)
                       :exec (if (< (len args) 20)
                                 (vl-convert-namedargs-aux args ports)
                               (b* ((alist (vl-make-namedarg-alist args))
                                    (ans (vl-convert-namedargs-aux-fal args alist ports)))
                                 (fast-alist-free alist)
                                 ans))))
       (new-x     (make-vl-arguments-plain :args plainargs)))
    (mv t (ok) new-x))

  ///
  (more-returns
   (new-x (implies successp
                   (equal (vl-arguments-kind new-x) :vl-arguments-plain))
          :name vl-arguments-kind-of-vl-convert-namedargs)))


(define vl-annotate-plainargs
  ((args "plainargs that typically have no @(':dir') or @(':portname')
         information; we want to annotate them."
         vl-plainarglist-p)
   (ports "corresponding ports for the submodule"
          vl-portlist-p)
   (scope vl-scope-p))
  :guard (same-lengthp args ports)
  :returns
  (annotated-args "annotated version of @('args'), semantically equivalent
                   but typically has @(':dir') and @(':portname') information."
                  (and (vl-plainarglist-p annotated-args)
                       (equal (len annotated-args) (len args))))
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
       ((mv & dir)
        ;; Our direction inference is pretty sophisticated, and handles even
        ;; compound ports as long as their directions are all the same.  But it
        ;; could also fail and leave dir as NIL.
        (vl-port-direction (car ports) scope nil))

       (arg-prime  (change-vl-plainarg (car args)
                                       :dir dir         ;; could be nil
                                       :portname name   ;; could be nil
                                       )))
    (cons arg-prime
          (vl-annotate-plainargs (cdr args) (cdr ports) scope))))

(define vl-check-blankargs
  :short "Warn about expressions connected to blank ports and for blanks
connected to non-blank, non-output ports."
  ((args  "plainargs for a module instance, which should already be
           annotated with their directions"
          vl-plainarglist-p)
   (ports "corresponding ports for the submodule"
          vl-portlist-p)
   (inst  "just a context for warnings" vl-modinst-p)
   (warnings "warnings accumulator" vl-warninglist-p))
  :guard (same-lengthp args ports)
  :returns (warnings vl-warninglist-p)

  :long "<p>We historically warned about blank arguments connected to
<i>any</i> port.  However, it seems reasonably common that a module will
produce outputs you don't care about, and connecting a blank to such an output
seems like a very reasonable thing to do.  So, we no longer warn about blanks
that are connected to output ports.</p>

<p>Either of these situations is semantically well-formed and relatively easy
to handle, but they are also bizarre, and at least would seem to indicate a
situation that could be optimized.  So, if we see either of these cases, we add
a non-fatal warning explaining the problem.</p>"

  :hooks ((:fix :hints (("goal" :induct (vl-check-blankargs args ports inst warnings)
                         :in-theory (disable (:d vl-check-blankargs)))
                        (and stable-under-simplificationp
                             (flag::expand-calls-computed-hint
                              clause '(vl-check-blankargs))))))
  (b* (((when (atom args))
        (ok))
       (inst     (vl-modinst-fix inst))
       (port1    (vl-port-fix (car ports)))
       ((when (eq (tag port1) :vl-interfaceport))
        (vl-check-blankargs (cdr args) (cdr ports) inst warnings))
       ((vl-regularport port1) port1)
       ((vl-plainarg arg1) (car args))

       (warnings
        (if (and arg1.expr (not port1.expr))
            (warn :type :vl-warn-blank
                  :msg "~a0 connects the expression ~a1 to the blank port at ~
                        ~l2."
                  :args (list inst arg1.expr port1.loc))
          (ok)))
       (warnings
        (if (and port1.expr
                 (not arg1.expr)
                 (not (eq arg1.dir :vl-output)))
            (warn :type :vl-warn-blank
                  ;; BOZO linking doesn't quite work here for the foreign port.
                  :msg "~a0 gives a blank expression for non-blank port ~a1 (port direction: ~s2)."
                  :args (list inst port1 arg1.dir))
          (ok))))
    (vl-check-blankargs (cdr args) (cdr ports) inst warnings)))

;; BOZO implement automatic -case macros for transparent sums, so that we can
;; get things like vl-scopedef-case, vl-scopeitem-case, vl-port-case.  Tricky
;; for nested transsums, I guess.

(define vl-scopeitem-modinst-p ((x vl-scopeitem-p))
  :inline t
  :enabled t
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :hooks nil
  (mbe :logic (vl-modinst-p x)
       :exec (eq (tag x) :vl-modinst)))

(define vl-scopeitem-modport-p ((x vl-scopeitem-p))
  :inline t
  :enabled t
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :hooks nil
  (mbe :logic (vl-modport-p x)
       :exec (eq (tag x) :vl-modport)))

(define vl-scopeitem-interfaceport-p ((x vl-scopeitem-p))
  :inline t
  :enabled t
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :hooks nil
  (mbe :logic (vl-interfaceport-p x)
       :exec (eq (tag x) :vl-interfaceport)))

(define vl-port-interface-p ((x vl-port-p))
  :inline t
  :enabled t
  :prepwork ((local (in-theory (enable tag-reasoning))))
  :hooks nil
  (mbe :logic (vl-interfaceport-p x)
       :exec (eq (tag x) :vl-interfaceport)))

(define vl-hidexpr-split-right
  :parents (vl-unhierarchicalize-interfaceport)
  :short "Split off the rightmost part of a hierarchical identifier."
  ((x vl-hidexpr-p
      "Expression to split, say @('foo.bar') or @('elf.cow[3][4].horse')."))
  :returns
  (mv (successp booleanp
                "We fail if this is an atomic HID expression like @('foo')
                 since then there's nothing to split.  We also fail if we're
                 given a HID like @('$root.foo'), because @('$root') isn't a
                 valid @(see vl-hidexpr) by itself.")
      (prefix  vl-hidexpr-p
               "On success: everything up to the final indexing/name.  For instance,
                @('foo') or @('elf.cow') in the above examples.")
      (indices vl-exprlist-p
               "On success: any next-to-last indexing that is also chopped off.
                For instance, NIL and @('[3][4]') in the above examples.")
      (lastname stringp
                "On success: the final name that was chopped off, e.g.,
                 @('bar') or @('horse') in the above examples."))
  :verify-guards nil
  :measure (vl-hidexpr-count x)
  (let ((x (vl-hidexpr-fix x)))
    (vl-hidexpr-case x
      :end
      ;; Fail: this is atomic, there's nothing to split.
      (mv nil x nil "")
      :dot
      (vl-hidexpr-case x.rest
        :end
        (b* ((name1 (vl-hidindex->name x.first))
             ((unless (stringp name1))
              ;; Fail: trying to split $root.foo
              (mv nil x nil ""))
             (prefix (make-vl-hidexpr-end :name name1)))
          (mv t
              prefix
              (vl-hidindex->indices x.first)
              (vl-hidexpr-end->name x.rest)))
        :dot
        (b* (((mv rest-okp rest-prefix rest-indices rest-lastname)
              (vl-hidexpr-split-right x.rest))
             (prefix (change-vl-hidexpr-dot x :rest rest-prefix)))
          (mv rest-okp prefix rest-indices rest-lastname)))))
  ///
  (verify-guards vl-hidexpr-split-right))

(define vl-scopeexpr-split-right ((x vl-scopeexpr-p))
  :parents (vl-unhierarchicalize-interfaceport)
  :short "Split off the rightmost part of a hierarchical scope expression."
  :long "<p>This is a thin wrapper around @(see vl-hidexpr-split-right) that
         just sticks the scopes back on.</p>"
  :returns (mv (successp booleanp)
               (prefix   vl-scopeexpr-p)
               (indices  vl-exprlist-p)
               (lastname stringp))
  :measure (vl-scopeexpr-count x)
  :verify-guards nil
  (vl-scopeexpr-case x
    :end
    (b* (((mv okp new-hid indices lastname) (vl-hidexpr-split-right x.hid))
         (new-x (change-vl-scopeexpr-end x :hid new-hid)))
      (mv okp new-x indices lastname))
    :colon
    (b* (((mv okp new-rest indices lastname) (vl-scopeexpr-split-right x.rest))
         (new-x (change-vl-scopeexpr-colon x :rest new-rest)))
      (mv okp new-x indices lastname)))
  ///
  (verify-guards vl-scopeexpr-split-right))

(define vl-unhierarchicalize-interfaceport
  :short "Sanity check and normalize interface port arguments by dropping
hierarchical modinst name components, e.g., transform @('mypipe.producer') to
just @('mypipe')."

  :long "<p>See SystemVerilog-2012 Section 25.5, especially at the top of Page
718.  Suppose we have an interface called @('IPipe') with modports named
@('producer') and @('consumer').  The names of these modport declarations can
be used in two distinct places:</p>

@({
     module fooBuilder( IPipe.producer pipe ) ;  // <-- .producer used in the module's port
       ...
     endmodule

     module top ;
       IPipe mypipe;
       fooBuilder prod ( mypipe.producer );   // <-- .producer used in module instance
     endmodule
})

<p>Our goal here is to deal with the latter kind of usage.  The basic idea is
to reduce such an argument to just @('mypipe'), after checking that its
interface is compatible with the module's interface declaration.  This way,
later VL code for dealing with interface ports doesn't have to think about
hierarchical identifiers that point at modports.</p>"

  ((arg      vl-plainarg-p     "Actual for this port.")
   (port     vl-port-p         "Corresponding port; not necessarily an interface port.")
   (ss       vl-scopestack-p)
   (inst     vl-modinst-p      "The module instance itself, context for error messages.")
   (warnings vl-warninglist-p))
  :returns (mv (warnings vl-warninglist-p)
               (new-arg  vl-plainarg-p
                         "If @('arg') is of the form @('myinterface.myport')
                          and everything is OK, this will just be
                          @('myinterface').  In any other case, we just return
                          @('arg') unchanged."))
  :guard-debug t
  (b* ((port (vl-port-fix port))
       ((vl-plainarg arg) (vl-plainarg-fix arg))
       ((vl-modinst inst) (vl-modinst-fix inst))

       ((unless (vl-port-interface-p port))
        ;; Not an interface port, nothing to do.
        (mv (ok) arg))

       ((vl-interfaceport port))
       (expr (vl-plainarg->expr arg))
       ((unless expr)
        ;; Blank argument -- this doesn't seem to be allowed; see failtest/port5d.v
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: interface port ~s1 is blank."
                   :args (list inst port.name))
            arg))
       ((unless (vl-expr-case expr :vl-index))
        ;; Something like .myiface(3 + 4) or whatever.  failtest/iface14.v and
        ;; failtest/port5c.v
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: interface port argument isn't an interface: .~s1(~a2)"
                   :args (list inst port.name expr))
            arg))
       ((vl-index expr))

       ;; If we get here, we have a scope expression, so try to follow
       ;; it.  This is a bit limited.  Doing it here, instead of during
       ;; elaboration, means we won't be able to handle things like:
       ;;
       ;;   for(genvar i = 0; ...)
       ;;   begin : foo
       ;;       myinterface iface (...);
       ;;   end
       ;;
       ;;   mysubmod mysub ( .producer(foo[3].iface) );
       ;;
       ;; Because we can't follow the foo[3].iface into the generate array
       ;; until it's been elaborated.
       ;;
       ;; Fortunately, this seems to be too hard for commercial tools as well.
       ;; In particular failtest/iface23.v shows that neither of NCV and VCS
       ;; handle this, so we probably don't need to handle it either.
       ((mv err trace ?context tail)
        (vl-follow-scopeexpr expr.scope ss :strictp nil))
       ((when err)
        (mv (fatal :type :vl-bad-instance ;; failtest/iface18.v
                   :msg "~a0: error resolving interface port argument .~s1(~a2): ~@3"
                   :args (list inst port.name expr err))
            arg))

       ((vl-hidstep step1) (first trace))
       ((when (vl-scopeitem-modinst-p step1.item))
        (b* (((vl-modinst step1.item))
             (iface (vl-scopestack-find-definition step1.item.modname ss))
             ((unless (and iface (vl-scopedef-interface-p iface)))
              ;; Connecting .ifport(foo) where foo is a module/UDP instance
              ;; instead of an interface instance.  See also failtest/iface24.v
              ;; and failtest/iface25.v
              (mv (fatal :type :vl-bad-instance
                         :msg "~a0: interface port argument isn't an interface: .~s1(~a2)"
                         :args (list inst port.name expr))
                  arg))
             ((unless (equal step1.item.modname port.ifname))
              ;; See failtest/port1.v
              (mv (fatal :type :vl-bad-instance
                         :msg "~a0: type error: interface port ~s1 (type ~s2) ~
                               is connected to ~a3 (type ~s4)."
                         :args (list inst port.name port.ifname expr step1.item.modname))
                  arg)))
          (mv (ok) arg)))

       ((when (vl-scopeitem-interfaceport-p step1.item))
        (b* (((vl-interfaceport step1.item))
             ((unless (equal step1.item.ifname port.ifname))
              ;; See failtest/port1b.v
              (mv (fatal :type :vl-bad-instance
                         :msg "~a0: type error: interface port ~s1 (type ~s2) ~
                               is connected to ~a3 (type ~s4)."
                         :args (list inst port.name port.ifname expr step1.item.ifname))
                  arg)))
          (mv (ok) arg)))

       ;; The only other possibility is the very weird case where you can write
       ;; a modport name directly in the instantiation instead.  For instance
       ;; we might be instantiating
       ;;
       ;;    submodule sub (.pipe(foo.bar.mypipe.consumer));
       ;;
       ;; to sanity check that the "foo.bar.mypipe" part is a compatible
       ;; interface and that the "consumer" part is a valid modport name for
       ;; this interface.

       ((unless (vl-scopeitem-modport-p step1.item))
        ;; See also failtest/ifport2.v, 
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: interface port argument isn't an interface: .~s1(~a2)"
                   :args (list inst port.name expr))
            arg))
       ;; There shouldn't be any indices on the outside, because modports don't
       ;; come in arrays.
       ((when (or (consp expr.indices)
                  (not (vl-partselect-case expr.part :none))))
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: array indexing can't be applied to modport: .~s1(~a2)"
                   :args (list inst port.name expr))
            arg))
       ((vl-modport step1.item))
       ((unless (vl-hidexpr-case tail :end))
        ;; If there's stuff in the tail, there's additional indexing *through*
        ;; the modport?  That doesn't seem like it makes any sense.
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: error resolving interface port argument .~s1(~a2): ~
                         trying to index through modport ~s3 with ~a4."
                   :args (list inst port.name expr step1.item.name tail))
            arg))
       ((unless (consp (cdr trace)))
        ;; There are no more steps in the trace, so somehow this is a direct
        ;; reference to a modport?  Can this happen?  Maybe if we have an
        ;; interface like:
        ;;     interface foo ;
        ;;         modport consumer (...);
        ;;         otherinterface bar (consumer);
        ;;     endinterface
        ;; but that certainly makes no sense.
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: interface port argument isn't an interface: .~s1(~a2)"
                   :args (list inst port.name expr))
            arg))

       ((vl-hidstep step2) (second trace))
       ((unless (vl-scopeitem-modinst-p step2.item))
        ;; The expression is something like:
        ;;
        ;;    foo.bar.baz.mymodport
        ;;
        ;; but baz isn't an interface instance (a modinst)?  Can this make
        ;; any sense?  Maybe...
        ;;
        ;; See failtest/iface20: NCV allows, but VCS disallows using modport
        ;; connections when instantiating submodules with interface ports.
        ;; That is, assuming consumer is a modport of myinterface, VCS will
        ;; reject:
        ;;
        ;;     module foo (myinterface iface) ;
        ;;        submod bar (iface.consumer);
        ;;     endmodule
        ;;
        ;; For now we mimic VCS and only allow .modport connections when they
        ;; are used on explicit interface instances.  If we want to relax this
        ;; and allow them on interface ports, we'll need to add another case
        ;; here for step2.item being an interfaceport.
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: unsupported interface port argument .~s1(~a2). ~
                         We currently only support arguments with modport ~
                         specifiers for direct interface instantiations, but ~
                         modport ~s3 is found via ~a4."
                   :args (list inst port.name expr step1.item.name step2.item))
            arg))

       ((vl-modinst step2.item))
       (iface   (vl-scopestack-find-definition step2.item.modname ss))
       ((unless (and iface (vl-scopedef-interface-p iface)))
        ;; I don't think this should be possible unless we're not properly
        ;; prohibiting modports from occurring except in interfaces.
        ;; BOZO maybe this can happen if the modports are in a generate?
        (mv (fatal :type :vl-programming-error
                   :msg "~a0: unsupported interface port argument .~s1(~a2). ~
                         Expected the modport ~s3 to be inside an interface, ~
                         but found it inside ~s4 which is a ~a5.  Thought ~
                         that modports should only occur in interfaces."
                   :args (list inst port.name expr step1.item.name step2.name iface))
            arg))
       ((vl-interface iface))
       ((unless (equal iface.name port.ifname))
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: type error: interface port ~s1 (type ~s2) is ~
                         connected to ~a3 (type ~s4)."
                   :args (list inst port.name port.ifname expr iface.name))
            arg))
       ((unless (or (not port.modport)
                    (equal port.modport step1.item.name)))
        ;; SystemVerilog-2012 25.5, page 718: "If a port connection specifies a
        ;; modport list name in both the module instance and module header
        ;; declaration, then the two modport list names shall be identical."
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: modport clash for .~s1(~a2).  In submodule ~s3 ~
                         the port is declared as modport ~s4, so you can't ~
                         instantiate it with modport ~s5."
                   :args (list inst port.name expr inst.modname
                               port.modport step1.item.name))
            arg))

       ;; All sanity checks passed, this is an OK modport.  Now remove the
       ;; .modport part from the expression.
       ((mv chop-okp new-scopeexpr indices ?lastname)
        (vl-scopeexpr-split-right expr.scope))
       ((unless chop-okp)
        (mv (fatal :type :vl-programming-error
                   :msg "~a0: reducing interface port .~s1(~a2) by dropping ~
                         modport ~s3: somehow failed to split the modport?"
                   :args (list inst port.name expr step1.item.name))
            arg))
       ((when indices)
        ;; This probably won't be too hard to support: we'll need to somehow
        ;; move these indices into the new index expression we build.  I'm not
        ;; sure what that's going to look like, yet.
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0: reducing interface port .~s1(~a2) by dropping ~
                         modport ~s3: indices on pre-modport expression?  ~
                         BOZO we might need to support this for interface ~
                         arrays.")
            arg))
       ;; We'll make some attributes to record what we did.
       ;; Note: these attributes are used by Lucid!
       (modportname-as-expr   (make-vl-literal :val (make-vl-string :value step1.item.name)))
       (interfacename-as-expr (make-vl-literal :val (make-vl-string :value port.ifname)))
       (new-atts (list* (cons "VL_REMOVED_EXPLICIT_MODPORT" modportname-as-expr)
                        (cons "VL_INTERFACE_NAME" interfacename-as-expr)
                        arg.atts))
       (new-arg (change-vl-plainarg arg
                                    :expr (change-vl-index expr :scope new-scopeexpr)
                                    :atts new-atts)))
    (mv (ok) new-arg)))

(define vl-unhierarchicalize-interfaceports
  ((args     vl-plainarglist-p "plainargs to the instance")
   (ports    vl-portlist-p     "corresponding ports for the submodule")
   (ss       vl-scopestack-p)
   (inst     vl-modinst-p      "the module instance itself, context for error messages.")
   (warnings vl-warninglist-p))
  :guard (same-lengthp args ports)
  :returns (mv (warnings vl-warninglist-p)
               (new-args vl-plainarglist-p))
  (b* (((when (atom args))
        (mv (ok) nil))
       ((mv warnings first) (vl-unhierarchicalize-interfaceport (car args) (car ports) ss inst warnings))
       ((mv warnings rest) (vl-unhierarchicalize-interfaceports (cdr args) (cdr ports) ss inst warnings)))
    (mv warnings (cons first rest)))
  ///
  (defret len-of-vl-unhierarchicalize-interfaceports
    (equal (len new-args)
           (len args))))

;; [Jared] folded all of this into unhierarchicalize.

;; (define vl-typecheck-interfaceport
;;   :short "Check that interface ports are connected sensibly."
;;   ((arg      vl-plainarg-p     "Actual for this port.")
;;    (port     vl-port-p         "Corresponding port; not necessarily an interface port.")
;;    (ss       vl-scopestack-p)
;;    (inst     vl-modinst-p      "The module instance itself, context for error messages.")
;;    (warnings vl-warninglist-p))
;;   :returns (warnings vl-warninglist-p)
;;   :long "<p>See also @(see vl-unhierarchicalize-interfaceport), which
;; simplifies arguments of the form @('myiface.mymodport') to just @('myiface').
;; We assume that it has been run first.</p>"
;;   :prepwork ((local (in-theory (enable tag-reasoning))))
;;   (b* ((port (vl-port-fix port))
;;        ((vl-plainarg arg) (vl-plainarg-fix arg))
;;        ((vl-modinst inst) (vl-modinst-fix inst))

;;        ((unless (mbe :logic (vl-interfaceport-p port)
;;                      :exec (eq (tag port) :vl-interfaceport)))
;;         ;; Not an interface port, nothing to do.
;;         (ok))

;;        ((vl-interfaceport port))
;;        (expr        (vl-plainarg->expr arg))
;;        ((unless expr)
;;         ;; Blank argument -- this doesn't seem to be allowed; see failtest/port5d.v
;;         (fatal :type :vl-bad-instance
;;                :msg "~a0: interface port ~s1 is left blank."
;;                :args (list inst port.name)))

;;        ((unless (vl-idexpr-p expr))
;;         (fatal :type :vl-bad-instance
;;                :msg "~a0: interface port connected to non-identifier: .~s1(~a2)"
;;                :args (list inst port.name expr)))

;;        (varname (vl-idexpr->name expr))
;;        (item    (vl-scopestack-find-item varname ss))
;;        ((unless item)
;;         (fatal :type :vl-bad-instance
;;                :msg "~a0: interface port connected to undeclared identifier: .~s1(~s2)"
;;                :args (list inst port.name varname)))

;;        ((when (mbe :logic (vl-modinst-p item)
;;                    :exec (eq (tag item) :vl-modinst)))
;;         (b* (((vl-modinst item))
;;              (iface (vl-scopestack-find-definition item.modname ss))
;;              ((unless (and iface (vl-scopedef-interface-p iface)))
;;               ;; It's a module or UDP instance instead of an interface.  Report
;;               ;; it like any other non-interface things.
;;               (fatal :type :vl-bad-instance
;;                      :msg "~a0: interface port ~s1 is connected to non-interface: ~a2."
;;                      :args (list inst port.name item)))

;;              ((unless (equal item.modname port.ifname))
;;               (fatal :type :vl-bad-instance
;;                      :msg "~a0: type error: interface port ~s1 (type ~s2) is ~
;;                            connected to ~s3 (type ~s4)."
;;                      :args (list inst port.name port.ifname varname item.modname))))
;;           (ok)))

;;        ((when (mbe :logic (vl-interfaceport-p item)
;;                    :exec (eq (tag item) :vl-interfaceport)))
;;         (b* (((vl-interfaceport item))
;;              ((unless (equal item.ifname port.ifname))
;;               (fatal :type :vl-bad-instance
;;                      :msg "~a0: type error: interface port ~s1 (type ~s2) is ~
;;                            connected to ~s3 (type ~s4)."
;;                      :args (list inst port.name port.ifname varname item.ifname))))
;;           (ok))))

;;     ;; Anything else makes no sense.
;;     (fatal :type :vl-bad-instance
;;            :msg "~a0: interface port ~s1 is connected to non-interface: ~a2."
;;            :args (list inst port.name item))))

;; (define vl-typecheck-interfaceports
;;   ((args     vl-plainarglist-p "plainargs to the instance")
;;    (ports    vl-portlist-p     "corresponding ports for the submodule")
;;    (ss       vl-scopestack-p)
;;    (inst     vl-modinst-p      "the module instance itself, context for error messages.")
;;    (warnings vl-warninglist-p))
;;   :guard (same-lengthp args ports)
;;   :returns (warnings vl-warninglist-p)
;;   (b* (((when (atom args))
;;         (ok))
;;        (warnings (vl-typecheck-interfaceport (car args) (car ports) ss inst warnings)))
;;     (vl-typecheck-interfaceports (cdr args) (cdr ports) ss inst warnings)))


(define vl-arguments-argresolve
  ((x         "arguments of a module instance, named or plain" vl-arguments-p)
   (ss        vl-scopestack-p)
   (ports     "ports of the submodule" vl-portlist-p)
   (scope     "instantiated module or interface" vl-scope-p)
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
        (vl-convert-namedargs x ss ports warnings inst))
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
       ;; Note: must annotate before checking for blanks, because the checks
       ;; heuristically consider the directions of the ports.
       (plainargs (vl-annotate-plainargs plainargs ports scope))
       (warnings  (vl-check-blankargs plainargs ports inst warnings))
       ((mv warnings plainargs) (vl-unhierarchicalize-interfaceports plainargs ports ss inst warnings))
       ;; (warnings  (vl-typecheck-interfaceports plainargs ports ss inst warnings))
       (new-x     (make-vl-arguments-plain :args plainargs)))
    (mv (ok) new-x)))

(define vl-modinst-argresolve
  :short "Resolve arguments in a @(see vl-modinst-p)."
  ((x        vl-modinst-p)
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-modinst-p))
  :prepwork ((local (in-theory (disable std::tag-forward-to-consp)))
             (local (defthm vl-scope-p-when-vl-module-p-strong
                      (implies (or (vl-module-p x)
                                   (vl-interface-p x))
                               (vl-scope-p x)))))
  (b* ((x (vl-modinst-fix x))
       ((vl-modinst x) x)
       (submod (vl-scopestack-find-definition x.modname ss))
       ((unless (and submod
                     (or (eq (tag submod) :vl-module)
                         (eq (tag submod) :vl-interface))))
        (mv (fatal :type :vl-bad-instance
                   :msg "~a0 refers to undefined module ~m1."
                   :args (list x x.modname))
            x))
       (submod.ports (if (eq (tag submod) :vl-module)
                         (vl-module->ports submod)
                       (vl-interface->ports submod)))
       ((mv warnings new-args)
        (vl-arguments-argresolve x.portargs ss
                                 submod.ports submod warnings x))
       (new-x (change-vl-modinst x :portargs new-args)))
    (mv (ok) new-x)))

(define vl-modinst-maybe-argresolve
  :short "Resolve arguments in a @(see vl-modinst-p), if the flag is true."
  ((flag booleanp)
   (x vl-modinst-p)
   (ss vl-scopestack-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-modinst-p))
  (if flag
      (vl-modinst-argresolve x ss warnings)
    (mv (vl-warninglist-fix warnings) (vl-modinst-fix x))))

(define vl-modinstlist-argresolve
  ((x        vl-modinstlist-p)
   (ss       vl-scopestack-p)
   (warnings vl-warninglist-p))
  :returns
  (mv (warnings vl-warninglist-p)
      (new-x    vl-modinstlist-p))
  :short "Resolve arguments in a @(see vl-modinstlist-p)."
  (b* (((when (atom x))
        (mv (ok) nil))
       ((mv warnings car)
        (vl-modinst-argresolve (car x) ss warnings))
       ((mv warnings cdr)
        (vl-modinstlist-argresolve (cdr x) ss warnings)))
    (mv warnings (cons car cdr))))

(def-genblob-transform vl-genblob-argresolve ((ss       vl-scopestack-p)
                                              (warnings vl-warninglist-p))
  :returns ((warnings vl-warninglist-p))
  (b* (((vl-genblob x) (vl-genblob-fix x))
       (ss (vl-scopestack-push x ss))
       ((mv warnings modinsts)  (vl-modinstlist-argresolve x.modinsts ss warnings))
       ((mv warnings gateinsts) (vl-gateinstlist-dirassign x.gateinsts warnings))
       ((mv warnings generates) (vl-generates-argresolve x.generates ss warnings)))
    (mv warnings
        (change-vl-genblob x
                           :modinsts modinsts
                           :gateinsts gateinsts
                           :generates generates)))
  :apply-to-generates vl-generates-argresolve)

(define vl-module-argresolve
  :short "Apply the @(see argresolve) transformation to a @(see vl-module-p)."
  :long "<p>This is just glue-code to apply @(see vl-modinst-argresolve) to all
of the module instances, and @(see vl-gateinst-dirassign) to all of the gate
instances in the module.</p>"
  ((x  vl-module-p)
   (ss vl-scopestack-p))
  :returns (new-x vl-module-p)
  (b* (((when (vl-module->hands-offp x))
        (vl-module-fix x))
       ((mv warnings genblob)
        (vl-genblob-argresolve (vl-module->genblob x) ss (vl-module->warnings x)))
       (x-warn (change-vl-module x :warnings warnings)))
    (vl-genblob->module genblob x-warn)))

(defprojection vl-modulelist-argresolve ((x    vl-modulelist-p)
                                         (ss   vl-scopestack-p))
  :returns (new-x vl-modulelist-p)
  (vl-module-argresolve x ss))

(define vl-interface-argresolve
  :short "Apply the @(see argresolve) transformation to a @(see vl-interface-p)."
  :long "<p>This is just glue-code to apply @(see vl-modinst-argresolve) to all
of the interface instances, and @(see vl-gateinst-dirassign) to all of the gate
instances in the interface.</p>"
  ((x  vl-interface-p)
   (ss vl-scopestack-p))
  :returns (new-x vl-interface-p)
  (b* (((mv warnings genblob)
        (vl-genblob-argresolve (vl-interface->genblob x) ss (vl-interface->warnings x)))
       (x-warn (change-vl-interface x :warnings warnings)))
    (vl-genblob->interface genblob x-warn)))

(defprojection vl-interfacelist-argresolve ((x    vl-interfacelist-p)
                                            (ss   vl-scopestack-p))
  :returns (new-x vl-interfacelist-p)
  (vl-interface-argresolve x ss))

(define vl-design-argresolve
  :short "Top-level @(see argresolve) transform."
  ((x vl-design-p))
  :returns (new-x vl-design-p)
  (b* (((vl-design x) x)
       (ss         (vl-scopestack-init x))
       (mods       (vl-modulelist-argresolve x.mods ss))
       (interfaces (vl-interfacelist-argresolve x.interfaces ss)))
    (vl-scopestacks-free)
    (change-vl-design x
                      :mods mods
                      :interfaces interfaces)))

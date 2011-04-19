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
(include-book "../mlib/hierarchy")
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
instantiate modules with ports like <tt>foo[3:0]</tt> without external names.
But it is basically straightforward to eliminate all named argument lists by
replacing them with their plain equivalents, reducing the number of syntactic
constructs that later transformations need to deal with.</p>

<p>In this transformation, we simplify module instances as follows:</p>

<ul>

<li>We try to get rid of all the named argument lists by replacing them with
plain argument lists; see @(see vl-convert-namedargs),</li>

<li>We try to annotate each @(see vl-plainarg-p) with its <tt>dir</tt> and
<tt>portname</tt> fields, so that the direction and name of many ports will be
available for use in error messages; see @(see vl-annotate-plainargs),</li>

<li>We check that each module instance has the proper arity, and</li>

<li>We check that any \"blank\" ports are connected only to blank arguments,
and vice-versa; see @(see vl-check-blankargs).</li>

</ul>

<p>We also simplify gate instances as follows:</p>

<ul>

<li>We check that the arity of each gate instance is acceptable and annotate
each @(see vl-plainarg-p) with its <tt>dir</tt> field; see @(see
vl-gateinst-dirassign), and</li>

<li>We check that no \"blank\" arguments are given to gates, and issue a
warning if such a connection is made.  This is actually also done by @(see
vl-gateinst-dirassign), just because it is convenient.</li>

</ul>")


(defsection vl-find-namedarg
  :parents (vl-convert-namedargs)
  :short "@(call vl-find-namedarg) attempts to find a @(see vl-namedarg-p) of
the specified <tt>name</tt> among <tt>args</tt>, a @(see vl-namedarglist-p)."

  :long "<p>We once used some fast-alist stuff here, but now I think that it
isn't worthwhile since most module instances have relatively few arguments so
it isn't really worthwhile.  It'd be easy enough to write an version that uses
fast-alists when there are many arguments, but Jared doesn't expect performance
to be a problem.</p>"

  (defund vl-find-namedarg (name args)
    (declare (xargs :guard (and (stringp name)
                                (vl-namedarglist-p args))))
    (cond ((atom args)
           nil)
          ((equal (vl-namedarg->name (car args)) name)
           (car args))
          (t
           (vl-find-namedarg name (cdr args)))))

  (defthm vl-namedarg-p-of-vl-find-namedarg
    (implies (force (vl-namedarglist-p args))
             (equal (vl-namedarg-p (vl-find-namedarg name args))
                    (if (member-equal name (vl-namedarglist->names args))
                        t
                      nil)))
    :hints(("Goal" :in-theory (enable vl-find-namedarg)))))



(defsection vl-convert-namedargs
  :parents (argresolve)
  :short "Canonicalizes @(see vl-arguments-p) structures to use plain
arguments."

  :long "<p><b>Signature:</b> @(call vl-convert-namedargs) returns <tt>(mv
successp warnings x-prime)</tt>.</p>

<p>As inputs:</p>

<ul>

<li><tt>x</tt> is the @(see vl-arguments-p) structure that is the
<tt>:portargs</tt> field of a module instance,</li>

<li><tt>ports</tt> and <tt>portdecls</tt> are the lists of ports and port
declarations for the module being instanced, and <tt>palist</tt> is the @(see
vl-portdecl-alist) for <tt>portdecls</tt>, and</li>

<li><tt>warnings</tt> is an ordinary @(see warnings) accumulator which we may
extend with fatal warnings, and <tt>inst</tt> is the module instance we are
working with, which is semantically irrelevant and is used merely to provide
better error messages.</li>

</ul>

<p>We return a success flag, updated warnings, and <tt>x-prime</tt>, a new
@(see vl-arguments-p) structure which is always semantically equivalent to
<tt>x</tt> and, upon success, uses plain arguments.</p>

<p>The main function just does a few well-formedness checks, then calls the
auxiliary function to do the conversion.</p>

<p>The auxiliary function walks down the list of ports.  For each port, it
finds the corresponding argument and builds a new @(see vl-plainarg-p).  The
resulting list of plain arguments ends up being in the same order as the
ports.</p>"

  (defund vl-convert-namedargs-aux (args ports)
    "Returns a vl-plainarglist-p"
    (declare (xargs :guard (and (vl-portlist-p ports)
                                (vl-namedarglist-p args)
                                (vl-portlist-named-p ports)
                                (subsetp-equal (vl-portlist->names ports)
                                               (vl-namedarglist->names args)))))
    (if (atom ports)
        nil
      (let ((arg (vl-find-namedarg (vl-port->name (car ports)) args)))
        (cons (make-vl-plainarg :expr (vl-namedarg->expr arg)
                                :atts (vl-namedarg->atts arg))
              (vl-convert-namedargs-aux args (cdr ports))))))

  (local (in-theory (enable vl-convert-namedargs-aux)))

  (defthm vl-plainarglist-of-vl-convert-namedargs-aux
    (implies (and (force (vl-portlist-p ports))
                  (force (vl-namedarglist-p args))
                  (force (vl-portlist-named-p ports))
                  (force (subsetp-equal (vl-portlist->names ports)
                                        (vl-namedarglist->names args))))
             (vl-plainarglist-p (vl-convert-namedargs-aux args ports))))

  (defthm len-of-vl-convert-namedargs-aux
    (equal (len (vl-convert-namedargs-aux args ports))
           (len ports)))



  (defund vl-convert-namedargs (x ports warnings inst)
    "Returns (MV SUCCESSP WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-arguments-p x)
                                (vl-portlist-p ports)
                                (vl-warninglist-p warnings)
                                (vl-modinst-p inst))))
    (b* ((namedp (vl-arguments->namedp x))
         (args   (vl-arguments->args x))

         ((unless namedp)
          ;; Already uses plain arguments, nothing to do.
          (mv t warnings x))

         (modname        (vl-modinst->modname inst))

         (formal-names   (vl-portlist->names ports))
         (actual-names   (vl-namedarglist->names args))
         (sorted-formals (mergesort formal-names))
         (sorted-actuals (mergesort actual-names))

         ((unless (vl-portlist-named-p ports))
          ;; Illegal instance: uses named arguments but module has unnamed ports
          (b* ((nils (acl2::duplicity nil formal-names))
               (w    (make-vl-warning
                      :type :vl-bad-instance
                      :msg "~a0 has named arguments, which is illegal since ~
                            ~m1 has ~s2."
                      :args (list inst modname
                                  (if (vl-plural-p nils)
                                      "unnamed ports"
                                    "an unnamed port"))
                      :fatalp t
                      :fn 'vl-convert-namedargs)))
            (mv nil (cons w warnings) x)))

         ((unless (mbe :logic (uniquep actual-names)
                       :exec (same-lengthp actual-names sorted-actuals)))
          ;; Illegal instance: actual names are not unique.
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0 illegally has multiple connections for port~s1 ~&2."
                   :args (let ((dupes (duplicated-members actual-names)))
                           (list inst (if (vl-plural-p dupes) "s" "") dupes))
                   :fatalp t
                   :fn 'vl-convert-namedargs)))
            (mv nil (cons w warnings) x)))

         ((unless (equal sorted-formals sorted-actuals))
          ;; Illegal instance: actuals don't line up with formals.
          (b* ((missing (difference sorted-formals sorted-actuals))
               (extra   (difference sorted-actuals sorted-formals))
               (w1 (and extra
                        (make-vl-warning
                         :type :vl-bad-instance
                         :msg "~a0 illegally connects to the following ~s1 ~
                               in ~m2: ~&3"
                         :args (list inst
                                     (if (vl-plural-p extra)
                                         "ports, which do not exist"
                                       "port, which does not exist")
                                     extra)
                         :fatalp t
                         :fn 'vl-convert-namedargs)))
               (w2 (and missing
                        (make-vl-warning
                         :type :vl-bad-instance
                         :msg "~a0 illegally omits the following ~s1 from ~
                               ~m2: ~&3"
                         :args (list inst
                                     (if (vl-plural-p missing) "ports" "port")
                                     modname missing)
                         :fatalp t
                         :fn 'vl-convert-namedargs)))
               (warnings (cond ((and w1 w2) (list* w1 w2 warnings))
                               (w1          (cons w1 warnings))
                               (w2          (cons w2 warnings))
                               ;; Impossible case, but easier than proving it away.
                               (t           warnings))))
            (mv nil warnings x)))

         (plainargs (vl-convert-namedargs-aux args ports))
         (x-prime   (vl-arguments nil plainargs)))
      (mv t warnings x-prime)))

  (local (in-theory (enable vl-convert-namedargs)))

  (defthm vl-warninglist-p-of-vl-convert-namedargs
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-convert-namedargs x ports warnings inst)))))

  (defthm vl-arguments-p-of-vl-convert-namedargs
    (implies (and (force (vl-arguments-p x))
                  (force (vl-portlist-p ports)))
             (vl-arguments-p
              (mv-nth 2 (vl-convert-namedargs x ports warnings inst)))))

  (defthm vl-arguments->named-of-vl-convert-namedargs
    (implies (force (vl-arguments-p x))
             (let ((result (vl-convert-namedargs x ports warnings inst)))
               (equal (vl-arguments->namedp (mv-nth 2 result))
                      (not (mv-nth 0 result)))))))




(defsection vl-annotate-plainargs
  :parents (argresolve)
  :short "Annotates a plain argument list with port names and directions."

  :long "<p><b>Signature:</b> @(call vl-annotate-plainargs) returns
<tt>args-prime</tt>.</p>

<p>As inputs,</p>

<ul>

<li><tt>args</tt> is a list of @(see vl-plainarg-p) structures which typically
have no <tt>:dir</tt> or <tt>:portname</tt> information; our goal is to add
these annotations to <tt>x</tt>, and</li>

<li><tt>ports</tt> and <tt>portdecls</tt> are the lists of ports and port
declarations for the module being instanced, and <tt>palist</tt> is the @(see
vl-portdecl-alist) for <tt>portdecls</tt>.</li>

</ul>

<p>We return a new argument list, <tt>args-prime</tt>, which is semantically
equivalent to <tt>x</tt> but may have additional <tt>:portname</tt> and
<tt>:dir</tt> annotations.</p>

<p>This is a \"best-effort\" process which may fail to add annotations to any
or all arguments.  Such failures are expected, so we do not generate any
warnings or errors in response to them.  What causes these failures?  Not all
ports necessarily have a name, so we cannot add a <tt>:portname</tt> for every
port.  The direction of a port may also not be apparent in some cases; see
@(see vl-port-direction) for details.</p>"

  (defund vl-annotate-plainargs (args ports portdecls palist)
    "Returns a new plainarglist"
    (declare (xargs :guard (and (vl-plainarglist-p args)
                                (vl-portlist-p ports)
                                (same-lengthp args ports)
                                (vl-portdecllist-p portdecls)
                                (equal palist (vl-portdecl-alist portdecls)))))
    (b* (((when (atom args))
          nil)
         (name (vl-port->name (car ports)))
         (expr (vl-port->expr (car ports)))

         ;; Our direction inference is pretty sophisticated, and handles even
         ;; compound ports as long as their directions are all the same.  But
         ;; it could also fail and leave dir as NIL.
         ((mv & dir) (vl-port-direction (car ports) portdecls palist nil))

         ;; If we're dealing with a simple port (which is most of the time), we
         ;; try to propagate active high/low information from its declaration
         ;; back into the argument.
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
                                         :dir dir       ;; could be nil
                                         :portname name ;; could be nil
                                         :atts arg-atts
                                         )))
      (cons arg-prime
            (vl-annotate-plainargs (cdr args) (cdr ports) portdecls palist))))

  (local (in-theory (enable vl-annotate-plainargs)))

  (defthm vl-plainarglist-p-of-vl-annotate-plainargs
    (implies (and (force (vl-plainarglist-p args))
                  (force (vl-portlist-p ports))
                  (force (same-lengthp args ports))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls))))
             (vl-plainarglist-p (vl-annotate-plainargs args ports portdecls palist)))))




(defsection vl-check-blankargs
  :parents (argresolve)
  :short "Check for any expressions connected to blank ports, and for any
blanks connected to non-blank ports."

  :long "<p><b>Signature:</b> @(call vl-check-blankargs) returns an updated
@(see warnings) accumulator.</p>

<p>As inputs,</p>

<ul>

<li><tt>args</tt> is a list of @(see vl-plainarg-p) structures, and</li>

<li><tt>ports</tt> and <tt>portdecls</tt> are the lists of ports and port
declarations for the module being instanced, and <tt>palist</tt> is the @(see
vl-portdecl-alist) for <tt>portdecls</tt>.</li>

</ul>

<p>We compare the arguments and ports, looking for any \"blank\" ports that are
given non-blank arguments, and for any blank arguments that are given to
non-blank ports.</p>

<p>Either of these situations is semantically well-formed and relatively easy
to handle; see @(see blankargs).  But they are also bizarre, and at least would
seem to indicate a situation that could be optimized.  So, if we see either of
these cases, we add a non-fatal warning explaining the problem.</p>"

  (defund vl-check-blankargs (args ports inst warnings)
    (declare (xargs :guard (and (vl-plainarglist-p args)
                                (vl-portlist-p ports)
                                (same-lengthp args ports)
                                (vl-modinst-p inst)
                                (vl-warninglist-p warnings))))
    (if (atom args)
        warnings
      (b* ((portexpr (vl-port->expr (car ports)))
           (argexpr  (vl-plainarg->expr (car args)))
           (warnings
            (if (and argexpr (not portexpr))
                (cons (make-vl-warning
                       :type :vl-warn-blank
                       :msg "~a0 connects the expression ~a1 to the blank ~
                             port at ~l2."
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
        (vl-check-blankargs (cdr args) (cdr ports) inst warnings))))

  (local (in-theory (enable vl-check-blankargs)))

  (defthm vl-warninglist-p-of-vl-check-blankargs
    (implies (vl-warninglist-p warnings)
             (vl-warninglist-p (vl-check-blankargs args ports inst warnings)))))



(defsection vl-arguments-argresolve
  :parents (argresolve)
  :short "Apply the @(see argresolve) transformation to a @(see
vl-arguments-p)."

  :long "<p><b>Signature:</b> @(call vl-arguments-argresolve) returns
<tt>(mv warnings x-prime)</tt>.</p>

<p>This is just a basic wrapper that applies @(see vl-convert-namedargs), @(see
vl-annotate-plainargs), and @(see vl-check-blankargs), and checks that the
arguments have the proper arity.</p>"

  (defund vl-arguments-argresolve (x ports portdecls palist warnings inst)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-arguments-p x)
                                (vl-portlist-p ports)
                                (vl-portdecllist-p portdecls)
                                (equal palist (vl-portdecl-alist portdecls))
                                (vl-warninglist-p warnings)
                                (vl-modinst-p inst))))
    (b* (((mv successp warnings x)
          (vl-convert-namedargs x ports warnings inst))
         ((unless successp)
          (mv warnings x))
         (plainargs (vl-arguments->args x))

         ((unless (same-lengthp plainargs ports))
          (b* ((modname  (vl-modinst->modname inst))
               (nports   (len ports))
               (nargs    (len plainargs))
               (w (make-vl-warning
                   :type :vl-bad-instance
                   ;; Wow this is hideous
                   :msg "~a0 ~s1 ~x2 ~s3, but module ~m4 ~s5 ~x6 ~s7."
                   :args (list inst
                               (if (< nargs nports) "only has" "has")
                               nargs
                               (if (= nargs 1) "argument" "arguments")
                               modname
                               (if (< nargs nports) "has" "only has")
                               nports
                               (if (= nports 1) "port" "ports"))
                   :fatalp t
                   :fn 'vl-arguments-argresolve)))
            (mv (cons w warnings) x)))

         (warnings  (vl-check-blankargs plainargs ports inst warnings))
         (plainargs (vl-annotate-plainargs plainargs ports portdecls palist))
         (x-prime   (vl-arguments nil plainargs)))
      (mv warnings x-prime)))

  (local (in-theory (enable vl-arguments-argresolve)))

  (defthm vl-warninglist-p-of-vl-arguments-argresolve
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-arguments-argresolve x ports portdecls palist warnings inst)))))

  (defthm vl-arguments-p-of-vl-arguments-argresolve
    (implies (and (force (vl-arguments-p x))
                  (force (vl-portlist-p ports))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls))))
             (vl-arguments-p
              (mv-nth 1 (vl-arguments-argresolve x ports portdecls palist warnings inst))))))




(defsection vl-modulelist-portdecl-alists
  :parents (argresolve)
  :short "Computes the @(see vl-portdecl-alist)s for a list of modules."
  :long "<p>@(call vl-modulelist-portdecl-alists) builds a fast alist
associating each module name to its corresponding @(see vl-portdecl-alist).</p>"

  (defund vl-modulelist-portdecl-alists (x)
    (declare (xargs :guard (vl-modulelist-p x)))
    (if (atom x)
        nil
      (hons-acons (vl-module->name (car x))
                  (vl-portdecl-alist (vl-module->portdecls (car x)))
                  (vl-modulelist-portdecl-alists (cdr x)))))

  (defthm hons-assoc-equal-of-vl-modulelist-portdecl-alists
    (implies (force (vl-modulelist-p x))
             (equal (hons-assoc-equal name (vl-modulelist-portdecl-alists x))
                    (let ((mod (vl-find-module name x)))
                      (and mod
                           (cons name (vl-portdecl-alist (vl-module->portdecls mod)))))))
    :hints(("Goal" :in-theory (enable vl-modulelist-portdecl-alists)))))



(defsection vl-modinst-argresolve
  :parents (argresolve)
  :short "Apply the @(see argresolve) transformation to a @(see vl-modinst-p)."

  :long "<p><b>Signature:</b> @(call vl-modinst-argresolve) returns <tt>(mv
warnings x-prime)</tt>.</p>

<p>This is just a basic wrapper around @(see vl-arguments-argresolve).  We look
up the module being instantiated from the @(see vl-modalist) so that we can get
its ports and port declarations.  We also look up the corresponding @(see
vl-portdecl-alist) from the precomputed @(see vl-modulelist-portdecl-alists).
Finally we standardize the instance's arguments and return the updated
instance.</p>"

  (defund vl-modinst-argresolve (x mods modalist mpalists warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-modinst-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (equal mpalists (vl-modulelist-portdecl-alists mods))
                                (vl-warninglist-p warnings))
                    :guard-debug t))
    (b* ((modname (vl-modinst->modname x))
         (lookup  (vl-fast-find-module modname mods modalist))
         ((unless lookup)
          (b* ((w (make-vl-warning
                   :type :vl-bad-instance
                   :msg "~a0 refers to undefined module ~m1."
                   :args (list x modname)
                   :fatalp t
                   :fn 'vl-modinst-argresolve)))
            (mv (cons w warnings) x)))

         (ports     (vl-module->ports lookup))
         (portdecls (vl-module->portdecls lookup))
         (palist    (cdr (hons-get modname mpalists)))
         (args      (vl-modinst->portargs x))

         ((mv warnings args)
          (vl-arguments-argresolve args ports portdecls palist warnings x))
         (x-prime (change-vl-modinst x :portargs args)))

        (mv warnings x-prime)))

  (local (in-theory (enable vl-modinst-argresolve)))

  (defthm vl-warninglist-p-of-vl-modinst-argresolve
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-modinst-argresolve x mods modalist mpalists warnings)))))

  (defthm vl-modinst-p-of-vl-modinst-argresolve
    (implies (and (force (vl-modinst-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (equal mpalists (vl-modulelist-portdecl-alists mods))))
             (vl-modinst-p
              (mv-nth 1 (vl-modinst-argresolve x mods modalist mpalists warnings))))))



(defsection vl-modinstlist-argresolve
  :parents (argresolve)
  :short "Projects @(see vl-modinst-argresolve) across a list of @(see
vl-modinst-p)s."

  (defund vl-modinstlist-argresolve (x mods modalist mpalists warnings)
    "Returns (MV WARNINGS X-PRIME)"
    (declare (xargs :guard (and (vl-modinstlist-p x)
                                (vl-modulelist-p mods)
                                (equal modalist (vl-modalist mods))
                                (equal mpalists (vl-modulelist-portdecl-alists mods))
                                (vl-warninglist-p warnings))))
    (if (atom x)
        (mv warnings nil)
      (b* (((mv warnings car-prime)
            (vl-modinst-argresolve (car x) mods modalist mpalists warnings))
           ((mv warnings cdr-prime)
            (vl-modinstlist-argresolve (cdr x) mods modalist mpalists warnings)))
        (mv warnings (cons car-prime cdr-prime)))))

  (local (in-theory (enable vl-modinstlist-argresolve)))

  (defthm vl-warninglist-p-of-vl-modinstlist-argresolve
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-modinstlist-argresolve x mods modalist mpalists warnings)))))

  (defthm vl-modinstlist-p-of-vl-modinstlist-argresolve
    (implies (and (force (vl-modinstlist-p x))
                  (force (vl-modulelist-p mods))
                  (force (equal modalist (vl-modalist mods)))
                  (force (equal mpalists (vl-modulelist-portdecl-alists mods))))
             (vl-modinstlist-p
              (mv-nth 1 (vl-modinstlist-argresolve x mods modalist mpalists warnings))))))



(defsection vl-gateinst-dirassign
  :parents (argresolve)
  :short "Arity-checks a gate instance and annotates its arguments with their
directions."

  :long "<p><b>Signature:</b> @(call vl-gateinst-dirassign) returns <tt>(mv
warnings x-prime)</tt>.</p>

<p>We are given <tt>x</tt>, a gate instance, and <tt>warnings</tt>, an ordinary
@(see warnings) accumulator.  We return a new gate instance, <tt>x-prime</tt>,
which is semantically equivalent to <tt>x</tt>.</p>

<p>If <tt>x</tt> is a well-formed gate instance, then no fatal warnings will be
added and every argument of <tt>x-prime</tt> will be given the correct
<tt>:dir</tt> annotation, following the rules in Chapter 7 of the Verilog
specification.</p>

<p>If <tt>x</tt> is a not well-formed (i.e., it has an improper arity), then it
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
<tt>x-prime</tt>.</p>

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



(defsection vl-modulelist-argresolve-aux
  :parents (argresolve)
  :short "Projects @(see vl-module-argresolve) across a list of @(see vl-module-p)s."

  (defprojection vl-modulelist-argresolve-aux (x mods modalist mpalists)
    (vl-module-argresolve x mods modalist mpalists)
    :guard (and (vl-modulelist-p x)
                (vl-modulelist-p mods)
                (equal modalist (vl-modalist mods))
                (equal mpalists (vl-modulelist-portdecl-alists mods)))
    :result-type vl-modulelist-p)

  (local (in-theory (enable vl-modulelist-argresolve-aux)))

  (defthm vl-modulelist->names-of-vl-modulelist-argresolve-aux
    (equal (vl-modulelist->names (vl-modulelist-argresolve-aux x mods modalist mpalists))
           (vl-modulelist->names x))))



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



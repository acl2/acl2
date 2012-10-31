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
(include-book "expr-tools")
(include-book "range-tools")
(include-book "find-item")
(local (include-book "../util/arithmetic"))


; BOZO many things to document


(deflist vl-directionlist-p (x)
  (vl-direction-p x)
  :elementp-of-nil nil
  :guard t)


(defsection vl-portexpr-p
  :parents (vl-port-p)
  :short "Recognizer for well-formed port expressions."

  :long "<p>Our @(see vl-port-p) recognizer does not place any restrictions
upon a port's expression, except that it should satisfy @(see
vl-maybe-expr-p).</p>

<p>But from 12.3.2, \"the port reference for each port in the list of ports at
the top of each module declaration can be one of the following:</p>

<ul>
<li>A simple identifier or escaped identifier</li>
<li>A bit-select of a vector declared within the module</li>
<li>A part-select of a vector declared within the module</li>
<li>A concatenation of any of the above.\"</li>
</ul>

<p>Note that nested concatenations are not permitted under these rules, e.g.,
whereas @('.a({b,c,d})') is a valid port, @('.a({b,{c,d}})') is not.  Simple
tests suggest that indeed Cadence permits only one concatenation, not nested
concatenations.</p>

<p>We now introduce a recognizer that tolerates most of these expressions,
except that we make two additional restrictions:</p>

<ul>

<li>For any bit-select, @('w[i]'), the bit @('i') being selected must be a
resolved, constant integer, and</li>

<li>For any part-select, @('w[a,b]') the indexes @('a') and @('b') must be
resolved, constant integers, with @('a >= b').</li>

</ul>

<p>Note that Cadence seems to impose similar restrictions, e.g., it rejects
attempts to write @('w[width-1]') where @('width') is one of the module's
parameters.  On the other hand, Cadence does tolerate port expressions such as
@('w[3-1]').  I think the right way for VL to support these kinds of
expressions is to apply @(see vl-expr-selresolve) to the port expressions
before considering whether they are valid.</p>

<p>We call the first three kinds of expressions <em>basic</em> port expressions
and recognize them with @(call vl-basic-portexpr-p).  We then introduce @(call
vl-portexpr-p), which tolerates basic port expressions or concatenations of
basic port expressions.</p>"

  (defund vl-basic-portexpr-p (x)
    (declare (xargs :guard (vl-maybe-expr-p x)))
    (b* (((unless x)
          t)
         ((when (vl-fast-atom-p x))
          (vl-idexpr-p x))
         (op (vl-nonatom->op x))
         (args (vl-nonatom->args x))
         ((when (eq op :vl-bitselect))
          (let ((from (first args))
                (bit  (second args)))
            (and (vl-idexpr-p from)
                 (vl-expr-resolved-p bit)
                 (natp (vl-resolved->val bit)))))
         ((when (eq op :vl-partselect-colon))
          (let ((from (first args))
                (high (second args))
                (low  (third args)))
            (and (vl-idexpr-p from)
                 (vl-expr-resolved-p high)
                 (vl-expr-resolved-p low)
                 (natp (vl-resolved->val high))
                 (natp (vl-resolved->val low))
                 (>= (vl-resolved->val high)
                     (vl-resolved->val low))))))
      nil))

  (defthm vl-basic-portexpr-p-when-degenerate
    (implies (and (not (vl-atom-p x))
                  (not (vl-nonatom-p x))
                  (vl-maybe-expr-p x))
             (equal (vl-basic-portexpr-p x)
                    (not x)))
    :hints(("Goal" :in-theory (enable vl-basic-portexpr-p))))

  (deflist vl-basic-portexprlist-p (x)
    (vl-basic-portexpr-p x)
    :guard (vl-exprlist-p x))

  (defund vl-portexpr-p (x)
    (declare (xargs :guard (vl-maybe-expr-p x)))
    (b* (((when (vl-basic-portexpr-p x))
          t)
         ((when (vl-fast-atom-p x))
          nil)
         (op   (vl-nonatom->op x))
         (args (vl-nonatom->args x)))
      (and (eq op :vl-concat)
           (vl-basic-portexprlist-p args)))))





(defund vl-port-wellformed-p (x)
  (declare (xargs :guard (vl-port-p x)))
  (vl-portexpr-p (vl-port->expr x)))

(defthm vl-portexpr-p-of-vl-port->expr
  (implies (force (vl-port-wellformed-p x))
           (vl-portexpr-p (vl-port->expr x)))
  :hints(("Goal" :in-theory (enable vl-port-wellformed-p))))

(deflist vl-portlist-wellformed-p (x)
  (vl-port-wellformed-p x)
  :guard (vl-portlist-p x)
  :elementp-of-nil t)


(defund vl-port-named-p (x)
  (declare (xargs :guard (vl-port-p x)))
  (if (vl-port->name x)
      t
    nil))

(defthm stringp-of-vl-port->name-when-vl-port-named-p
  (implies (and (vl-port-named-p x)
                (force (vl-port-p x)))
           (stringp (vl-port->name x)))
  :rule-classes ((:rewrite)
                 (:type-prescription)
                 (:rewrite :corollary
                           (implies (and (vl-port-named-p x)
                                         (force (vl-port-p x)))
                                    (vl-port->name x))))
  :hints(("Goal" :in-theory (e/d (vl-port-named-p)))))

(deflist vl-portlist-named-p (x)
  (vl-port-named-p x)
  :guard (vl-portlist-p x)
  :elementp-of-nil nil)

(defthm string-listp-of-vl-portlist->names
  (implies (and (vl-portlist-named-p x)
                (force (vl-portlist-p x)))
           (string-listp (vl-portlist->names x)))
  :hints(("Goal" :induct (len x))))



(defsection vl-flatten-portexpr
  :parents (vl-port-p)
  :short "Flatten a @(see vl-portexpr-p) into a list of @(see
vl-basic-portexpr-p)s."

  :long "<p>This function just allows us to treat any port expression as a list
of basic port expressions, so that we can process them in a uniform way.</p>"

  (defund vl-flatten-portexpr (x)
    (declare (xargs :guard (and (vl-maybe-expr-p x)
                                (vl-portexpr-p x))))
    (cond ((not x)
           nil)
          ((vl-fast-atom-p x)
           (list x))
          ((eq (vl-nonatom->op x) :vl-concat)
           (vl-nonatom->args x))
          (t
           (list x))))

  (local (in-theory (enable vl-flatten-portexpr
                            vl-portexpr-p
                            vl-basic-portexpr-p)))

  (defthm vl-exprlist-p-of-vl-flatten-portexpr
    (implies (and (force (vl-maybe-expr-p x))
                  (force (vl-portexpr-p x)))
             (vl-exprlist-p (vl-flatten-portexpr x))))

  (defthm vl-basic-portexprlist-p-of-vl-flatten-portexpr
    (implies (and (force (vl-maybe-expr-p x))
                  (force (vl-portexpr-p x)))
             (vl-basic-portexprlist-p (vl-flatten-portexpr x)))))




(defsection vl-port-internal-wirenames
  :parents (vl-port-p)
  :short "Collect the names of any internal wires that are connected to a
well-formed port and return them as a list of strings."

  :long "<p><b>Signature:</b> @(call vl-port-internal-wirenames) returns a string
list.</p>

<p>Given a well-formed port (see @(see vl-port-wellformed-p), we just collect
the names of the internal wires that are connected to the port.  For instance,
in the following module,</p>

@({
module mod (a, .b(foo), .c({bar[2], baz})) ;
  ...
endmodule
})

<p>the internal wires for the first port are @('(\"a\")'), the second port to
@('(\"foo\")'), and for the third port to @('(\"bar\" \"baz\")').</p>

<p>We ignore any bit- or part-selects involved in the port expression and just
return a list of strings.</p>"

  (defund vl-basic-portexpr-internal-wirename (x)
    (declare (xargs :guard (and (vl-expr-p x)
                                (vl-basic-portexpr-p x))
                    :guard-hints (("Goal" :in-theory (enable vl-basic-portexpr-p)))))
    (if (vl-fast-atom-p x)
        (vl-idexpr->name x)
      (vl-idexpr->name (first (vl-nonatom->args x)))))

  (defprojection vl-basic-portexprlist-internal-wirenames (x)
    (vl-basic-portexpr-internal-wirename x)
    :guard (and (vl-exprlist-p x)
                (vl-basic-portexprlist-p x)))

  (defthm string-listp-of-vl-basic-portexprlist-internal-wirenames
    (string-listp (vl-basic-portexprlist-internal-wirenames x))
    :hints(("Goal" :induct (len x))))

  (defund vl-port-internal-wirenames (x)
    (declare (xargs :guard (and (vl-port-p x)
                                (vl-port-wellformed-p x))))
    (vl-basic-portexprlist-internal-wirenames
     (vl-flatten-portexpr
      (vl-port->expr x))))

  (defthm string-listp-of-vl-port-internal-wirenames
    (string-listp (vl-port-internal-wirenames x))
    :hints(("Goal" :in-theory (enable vl-port-internal-wirenames)))))



(defsection vl-port-direction
  :parents (vl-port-p)
  :short "Attempt to determine the direction for a port."

  :long "<p><b>Signature:</b> @(call vl-port-direction) returns @('(mv warnings
maybe-dir)').</p>

<p>As inputs:</p>

<ul>

<li>@('port') is the @(see vl-port-p) whose direction is being decided,</li>

<li>@('portdecls') should be the list of all @(see vl-portdecl-p)s for this
module,</li>

<li>@('palist') is the @(see vl-portdecl-alist) that provides fast lookups for
these portdecls, and</li>

<li>@('warnings') is an ordinary warnings accumulator, which we may extend with
non-fatal warnings.</li>

</ul>

<p>We attempt to determine the direction of this port and return it.</p>

<p>This function can fail if the port is not well-formed or if there is no port
declaration corresponding to this port.  In this case we return @('nil') as the
@('maybe-dir'), and add a non-fatal warning describing the problem.</p>

<p>Non-fatal warnings can also be added if a complex port has conflicting
directions, e.g., imagine a port such as @('.foo({bar,baz})'), where @('bar')
is an input and @('baz') is an output.  We regard such a port as an @('inout'),
and add a warning that this case is very unusual.</p>"

  (defund vl-port-direction-aux (names portdecls palist warnings port)
    "Returns (MV SUCCESSP WARNINGS DIRECTIONS)"
    (declare (xargs :guard (and (string-listp names)
                                (vl-portdecllist-p portdecls)
                                (equal palist (vl-portdecl-alist portdecls))
                                (vl-warninglist-p warnings)
                                (vl-port-p port))))
    (b* (((when (atom names))
          (mv t warnings nil))
         (decl (vl-fast-find-portdecl (car names) portdecls palist))
         ((mv successp warnings directions)
          (vl-port-direction-aux (cdr names) portdecls palist warnings port))
         ((when decl)
          (mv successp warnings (cons (vl-portdecl->dir decl) directions)))
         (w (make-vl-warning
             :type :vl-bad-port
             :msg "~a0 refers to ~w1, but there is no port declaration for ~w1."
             :args (list port (car names))
             :fn 'vl-port-direction-aux)))
      (mv nil (cons w warnings) directions)))

  (defmvtypes vl-port-direction-aux (booleanp nil true-listp))

  (defthm vl-warninglist-p-of-vl-port-direction-aux
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 1 (vl-port-direction-aux names portdecls palist warnings port))))
    :hints(("Goal" :in-theory (e/d (vl-port-direction-aux)
                                   ((force))))))

  (defthm vl-directionlist-p-of-vl-port-direction-aux
    (implies (and (force (string-listp names))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls)))
                  (force (vl-port-p port)))
             (vl-directionlist-p
              (mv-nth 2 (vl-port-direction-aux names portdecls palist warnings port))))
    :hints(("Goal" :in-theory (enable vl-port-direction-aux))))



  (defund vl-port-direction (port portdecls palist warnings)
    "Returns (MV WARNINGS MAYBE-DIR)"
    (declare (xargs :guard (and (vl-port-p port)
                                (vl-portdecllist-p portdecls)
                                (equal palist (vl-portdecl-alist portdecls))
                                (vl-warninglist-p warnings))))
    (b* (((unless (vl-port-wellformed-p port))
          (b* ((w (make-vl-warning :type :vl-bad-port
                                   :msg "~a0 is not well-formed."
                                   :args (list port)
                                   :fn 'vl-port-direction)))
            (mv (cons w warnings) nil)))

         (names (vl-port-internal-wirenames port))
         ((mv successp warnings dirs)
          (vl-port-direction-aux names portdecls palist warnings port))
         ((unless successp)
          (mv warnings nil))

         ((when (or (atom (cdr dirs))
                    (all-equalp :vl-input dirs)
                    (all-equalp :vl-output dirs)
                    (all-equalp :vl-inout dirs)))
          (mv warnings (car dirs)))

         (w (make-vl-warning
             :type :vl-bad-port
             :msg "~a0 refers to ~&1, which do not all agree upon a direction.  ~
                   We do not support this. Directions: ~&2."
             :args (list port names (mergesort dirs))
             :fn 'vl-port-direction)))
      (mv (cons w warnings) nil)))

  (local (in-theory (enable vl-port-direction)))

  (defthm vl-warninglist-p-of-vl-port-direction
    (implies (force (vl-warninglist-p warnings))
             (vl-warninglist-p
              (mv-nth 0 (vl-port-direction port portdecls palist warnings)))))

  (defthm vl-maybe-direction-p-of-vl-port-direction
    (implies (and (force (vl-port-p port))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls))))
             (vl-maybe-direction-p
              (mv-nth 1 (vl-port-direction port portdecls palist warnings))))
    :hints(("Goal" :in-theory (enable vl-maybe-direction-p))))

  (defthm vl-direction-p-of-vl-port-direction
    (implies (and (force (vl-port-p port))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls))))
             (equal (vl-direction-p
                     (mv-nth 1 (vl-port-direction port portdecls palist warnings)))
                    (if (mv-nth 1 (vl-port-direction port portdecls palist warnings))
                        t
                      nil)))))





(definlined vl-plainarg-blankfree-p (x)
  (declare (xargs :guard (vl-plainarg-p x)))
  (if (vl-plainarg->expr x)
      t
    nil))

(deflist vl-plainarglist-blankfree-p (x)
  (vl-plainarg-blankfree-p x)
  :guard (vl-plainarglist-p x))

(definlined vl-namedarg-blankfree-p (x)
  (declare (xargs :guard (vl-namedarg-p x)))
  (if (vl-namedarg->expr x)
      t
    nil))

(deflist vl-namedarglist-blankfree-p (x)
  (vl-namedarg-blankfree-p x)
  :guard (vl-namedarglist-p x))

(definlined vl-arguments-blankfree-p (x)
  (declare (xargs :guard (vl-arguments-p x)))
  (if (vl-arguments->namedp x)
      (vl-namedarglist-blankfree-p (vl-arguments->args x))
    (vl-plainarglist-blankfree-p (vl-arguments->args x))))

(definlined vl-modinst-blankfree-p (x)
  (declare (xargs :guard (vl-modinst-p x)))
  (vl-arguments-blankfree-p (vl-modinst->portargs x)))

(deflist vl-modinstlist-blankfree-p (x)
  (vl-modinst-blankfree-p x)
  :guard (vl-modinstlist-p x))



(defund vl-ports-from-portdecls (x)
  (declare (xargs :guard (vl-portdecllist-p x)))
  (if (atom x)
      nil
    (b* ((name (vl-portdecl->name (car x)))
         (loc  (vl-portdecl->loc (car x)))
         (guts (make-vl-id :name name))
         (expr (make-vl-atom :guts guts)))
      (cons (make-vl-port :name name :expr expr :loc loc)
            (vl-ports-from-portdecls (cdr x))))))

(defthm vl-portlist-p-of-vl-ports-from-portdecls
  (implies (vl-portdecllist-p x)
           (vl-portlist-p (vl-ports-from-portdecls x)))
  :hints(("Goal" :in-theory (enable vl-ports-from-portdecls))))



(defsection vl-portdecls-with-dir

  (defund vl-portdecls-with-dir (dir x)
    (declare (xargs :guard (and (vl-direction-p dir)
                                (vl-portdecllist-p x))))
    (cond ((atom x)
           nil)
          ((eq dir (vl-portdecl->dir (car x)))
           (cons (car x) (vl-portdecls-with-dir dir (cdr x))))
          (t
           (vl-portdecls-with-dir dir (cdr x)))))

  (local (in-theory (enable vl-portdecls-with-dir)))

  (defthm vl-portdecllist-p-of-vl-portdecls-with-dir
    (implies (vl-portdecllist-p x)
             (vl-portdecllist-p (vl-portdecls-with-dir dir x)))))

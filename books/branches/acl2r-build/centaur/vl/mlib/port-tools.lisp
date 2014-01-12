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


(defsection port-tools
  :parents (mlib vl-port-p vl-portdecl-p)
  :short "Basic functions for working with ports.")

(local (xdoc::set-default-parents port-tools))

(deflist vl-directionlist-p (x)
  (vl-direction-p x)
  :elementp-of-nil nil
  :guard t)

(define vl-basic-portexpr-p ((x vl-maybe-expr-p))
  :parents (vl-portexpr-p)
  :returns (okp booleanp :rule-classes :type-prescription)
  :short "Non-concatenations that can occur in port expressions."
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
    nil)
  ///
  (defthm vl-basic-portexpr-p-when-degenerate
    (implies (and (not (vl-atom-p x))
                  (not (vl-nonatom-p x))
                  (vl-maybe-expr-p x))
             (equal (vl-basic-portexpr-p x)
                    (not x)))
    :hints(("Goal" :in-theory (enable vl-basic-portexpr-p)))))

(deflist vl-basic-portexprlist-p (x)
  (vl-basic-portexpr-p x)
  :guard (vl-exprlist-p x)
  :parents (vl-portexpr-p))

(define vl-portexpr-p
  :short "Recognizer for well-formed port expressions."
  ((x vl-maybe-expr-p))
  :returns (okp booleanp :rule-classes :type-prescription)
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

  (b* (((when (vl-basic-portexpr-p x))
        t)
       ((when (vl-fast-atom-p x))
        nil)
       (op   (vl-nonatom->op x))
       (args (vl-nonatom->args x)))
    (and (eq op :vl-concat)
         (vl-basic-portexprlist-p args))))


(define vl-port-wellformed-p ((x vl-port-p))
  :short "Recognizer for ports whose expressions are well-formed."
  (vl-portexpr-p (vl-port->expr x))
  ///
  (defthm vl-portexpr-p-of-vl-port->expr
    (implies (force (vl-port-wellformed-p x))
             (vl-portexpr-p (vl-port->expr x)))
    :hints(("Goal" :in-theory (enable vl-port-wellformed-p)))))

(deflist vl-portlist-wellformed-p (x)
  (vl-port-wellformed-p x)
  :guard (vl-portlist-p x)
  :elementp-of-nil t)


(define vl-port-named-p ((x vl-port-p))
  :short "Recognizer for ports that have a non-blank name."
  (if (vl-port->name x)
      t
    nil)
  ///
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
    :hints(("Goal" :in-theory (e/d (vl-port-named-p))))))

(deflist vl-portlist-named-p (x)
  (vl-port-named-p x)
  :guard (vl-portlist-p x)
  :elementp-of-nil nil
  :rest
  ((defthm string-listp-of-vl-portlist->names
     (implies (and (vl-portlist-named-p x)
                   (force (vl-portlist-p x)))
              (string-listp (vl-portlist->names x))))))


(define vl-flatten-portexpr ((x (and (vl-maybe-expr-p x)
                                     (vl-portexpr-p x))))
  :returns (exprs (and (vl-exprlist-p exprs)
                       (vl-basic-portexprlist-p exprs))
                  :hyp :fguard)
  :short "Flatten a @(see vl-portexpr-p) into a list of @(see
vl-basic-portexpr-p)s."

  :long "<p>This function just allows us to treat any port expression as a list
of basic port expressions, so that we can process them in a uniform way.</p>"

  (cond ((not x)
         nil)
        ((vl-fast-atom-p x)
         (list x))
        ((eq (vl-nonatom->op x) :vl-concat)
         (vl-nonatom->args x))
        (t
         (list x)))

  :prepwork
  ((local (in-theory (enable vl-portexpr-p
                             vl-basic-portexpr-p)))))


(define vl-basic-portexpr-internal-wirename ((x (and (vl-expr-p x)
                                                     (vl-basic-portexpr-p x))))
  :guard-hints (("Goal" :in-theory (enable vl-basic-portexpr-p)))
  :parents (vl-port-internal-wirenames)
  (if (vl-fast-atom-p x)
      (vl-idexpr->name x)
    (vl-idexpr->name (first (vl-nonatom->args x)))))

(defprojection vl-basic-portexprlist-internal-wirenames (x)
  (vl-basic-portexpr-internal-wirename x)
  :guard (and (vl-exprlist-p x)
              (vl-basic-portexprlist-p x))
  :parents (vl-port-internal-wirenames)
  ///
  (defthm string-listp-of-vl-basic-portexprlist-internal-wirenames
    (string-listp (vl-basic-portexprlist-internal-wirenames x))))

(define vl-port-internal-wirenames ((x (and (vl-port-p x)
                                            (vl-port-wellformed-p x))))
  :returns (names string-listp)
  :short "Collect the names of any internal wires that are connected to a
well-formed port and return them as a list of strings."

  :long "<p>Given a well-formed port, we just collect the names of the internal
wires that are connected to the port.  For instance, in the following
module,</p>

@({
module mod (a, .b(foo), .c( {bar[2], baz} )) ;
  ...
endmodule
})

<p>the internal wires for the first port are @('(\"a\")'), the second port to
@('(\"foo\")'), and for the third port to @('(\"bar\" \"baz\")').</p>

<p>We ignore any bit- or part-selects involved in the port expression and just
return a list of strings.</p>"

  (vl-basic-portexprlist-internal-wirenames
   (vl-flatten-portexpr
    (vl-port->expr x))))


(define vl-port-direction-aux
  :parents (vl-port-direction)
  ((names     string-listp)
   (portdecls vl-portdecllist-p)
   (palist    (equal palist (vl-portdecl-alist portdecls)))
   (warnings  vl-warninglist-p)
   (port      vl-port-p))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p
                :hyp (force (vl-warninglist-p warnings)))
      (directions true-listp :rule-classes :type-prescription))
  (b* (((when (atom names))
        (mv t warnings nil))
       (decl (vl-fast-find-portdecl (car names) portdecls palist))
       ((mv successp warnings directions)
        (vl-port-direction-aux (cdr names) portdecls palist warnings port))
       ((when decl)
        (mv successp warnings (cons (vl-portdecl->dir decl) directions))))
    (mv nil
        (warn :type :vl-bad-port
              :msg "~a0 refers to ~w1, but there is no port declaration for ~
                      ~w1."
              :args (list port (car names)))
        directions))
  ///
  (defthm vl-directionlist-p-of-vl-port-direction-aux
    (implies (and (force (string-listp names))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls)))
                  (force (vl-port-p port)))
             (vl-directionlist-p
              (mv-nth 2 (vl-port-direction-aux names portdecls palist warnings port))))
    :hints(("Goal" :in-theory (enable vl-port-direction-aux)))))

(define vl-port-direction
  :short "Attempt to determine the direction for a port."
  ((port      "The port whose direction is being decided."
              vl-port-p)
   (portdecls "The list of all portdecls for this module."
              vl-portdecllist-p)
   (palist    "Precomputed fast alist for these portdecls."
              (equal palist (vl-portdecl-alist portdecls)))
   (warnings  "Ordinary warnings accumulator, may be extended with non-fatal
               warnings."
              vl-warninglist-p))
  :returns
  (mv (warnings  vl-warninglist-p
                 :hyp (force (vl-warninglist-p warnings)))
      (maybe-dir "The direction for this port, or @('nil') on failure."
                 vl-maybe-direction-p
                 :hints(("Goal" :in-theory (enable vl-maybe-direction-p)))
                 :hyp
                 (and (force (vl-port-p port))
                      (force (vl-portdecllist-p portdecls))
                      (force (equal palist (vl-portdecl-alist portdecls))))))

  :long "<p>We attempt to determine the direction of this port and return it.
We can fail if the port is not well-formed or if there is no port declaration
corresponding to this port.  In this case we return @('nil') as the
@('maybe-dir'), and add a non-fatal warning describing the problem.</p>

<p>Non-fatal warnings can also be added if a complex port has conflicting
directions, e.g., imagine a port such as @('.foo({bar,baz})'), where @('bar')
is an input and @('baz') is an output.  We regard such a port as an @('inout'),
and add a warning that this case is very unusual.</p>"

  (b* (((unless (vl-port-wellformed-p port))
        (mv (warn :type :vl-bad-port
                  :msg "~a0 is not well-formed."
                  :args (list port))
            nil))

       (names (vl-port-internal-wirenames port))
       ((mv successp warnings dirs)
        (vl-port-direction-aux names portdecls palist warnings port))
       ((unless successp)
        (mv warnings nil))

       ((when (or (atom (cdr dirs))
                  (all-equalp :vl-input dirs)
                  (all-equalp :vl-output dirs)
                  (all-equalp :vl-inout dirs)))
        (mv warnings (car dirs))))
    (mv (warn :type :vl-bad-port
              :msg "~a0 refers to ~&1, which do not all agree upon a ~
                      direction.  We do not support this. Directions: ~&2."
              :args (list port names (mergesort dirs)))
        nil))
  ///
  (defthm vl-direction-p-of-vl-port-direction
    (implies (and (force (vl-port-p port))
                  (force (vl-portdecllist-p portdecls))
                  (force (equal palist (vl-portdecl-alist portdecls))))
             (equal (vl-direction-p
                     (mv-nth 1 (vl-port-direction port portdecls palist warnings)))
                    (if (mv-nth 1 (vl-port-direction port portdecls palist warnings))
                        t
                      nil)))))


(define vl-plainarg-blankfree-p ((x vl-plainarg-p))
  :inline t
  (if (vl-plainarg->expr x)
      t
    nil))

(deflist vl-plainarglist-blankfree-p (x)
  (vl-plainarg-blankfree-p x)
  :guard (vl-plainarglist-p x))

(define vl-namedarg-blankfree-p ((x vl-namedarg-p))
  :inline t
  (if (vl-namedarg->expr x)
      t
    nil))

(deflist vl-namedarglist-blankfree-p (x)
  (vl-namedarg-blankfree-p x)
  :guard (vl-namedarglist-p x))

(define vl-arguments-blankfree-p ((x vl-arguments-p))
  (if (vl-arguments->namedp x)
      (vl-namedarglist-blankfree-p (vl-arguments->args x))
    (vl-plainarglist-blankfree-p (vl-arguments->args x))))

(define vl-modinst-blankfree-p ((x vl-modinst-p))
  :inline t
  (vl-arguments-blankfree-p (vl-modinst->portargs x)))

(deflist vl-modinstlist-blankfree-p (x)
  (vl-modinst-blankfree-p x)
  :guard (vl-modinstlist-p x))



(define vl-ports-from-portdecls ((x vl-portdecllist-p))
  :short "Construct basic ports corresponding to a list of portdecls."
  :returns (ports vl-portlist-p :hyp :guard)
  (b* (((when (atom x))
        nil)
       (name (vl-portdecl->name (car x)))
       (loc  (vl-portdecl->loc (car x)))
       (guts (make-vl-id :name name))
       (expr (make-vl-atom :guts guts)))
    (cons (make-vl-port :name name :expr expr :loc loc)
          (vl-ports-from-portdecls (cdr x)))))

(define vl-portdecls-with-dir ((dir vl-direction-p)
                               (x   vl-portdecllist-p))
  :short "Filter port declarations by direction."
  :returns (sub-x vl-portdecllist-p :hyp (vl-portdecllist-p x))
  (cond ((atom x)
         nil)
        ((eq dir (vl-portdecl->dir (car x)))
         (cons (car x) (vl-portdecls-with-dir dir (cdr x))))
        (t
         (vl-portdecls-with-dir dir (cdr x)))))

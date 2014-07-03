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
(include-book "expr-tools")
(include-book "range-tools")
(include-book "find-item")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(defsection port-tools
  :parents (mlib vl-port-p vl-portdecl-p)
  :short "Basic functions for working with arguments and ports.")

(local (xdoc::set-default-parents port-tools))



(define vl-exprlist-to-plainarglist
  ((x    vl-exprlist-p        "list to convert")
   &key
   (dir  vl-maybe-direction-p "direction for each new plainarg")
   (atts vl-atts-p            "attributes for each new plainarg"))
  :returns (ans vl-plainarglist-p)
  :parents (expr-tools)
  :short "Convert expressions into @(see vl-plainarg-p)s."
  (if (consp x)
      (cons (make-vl-plainarg :expr (vl-expr-fix (car x))
                              :dir dir
                              :atts atts)
            (vl-exprlist-to-plainarglist-fn (cdr x) dir atts))
    nil)
  ///
  (defthm vl-exprlist-to-plainarglist-under-iff
    (iff (vl-exprlist-to-plainarglist x :dir dir :atts atts)
         (consp x)))

  (defthm len-of-vl-exprlist-to-plainarglist
    (equal (len (vl-exprlist-to-plainarglist x :dir dir :atts atts))
           (len x))))

(define vl-partition-plainargs
  :parents (vl-plainarglist-p)
  ;; BOZO find this a better home
  ((x      vl-plainarglist-p "list to filter")
   ;; bozo make these optional
   (inputs   vl-plainarglist-p "accumulator for args with :dir :vl-input")
   (outputs  vl-plainarglist-p "accumulator for args with :dir :vl-output")
   (inouts   vl-plainarglist-p "accumulator for args with :dir :vl-inout")
   (unknowns vl-plainarglist-p "accumulator for args with :dir nil"))
  :returns (mv (inputs   vl-plainarglist-p)
               (outputs  vl-plainarglist-p)
               (inouts   vl-plainarglist-p)
               (unknowns vl-plainarglist-p))
  (b* (((when (atom x))
        (mv (vl-plainarglist-fix inputs)
            (vl-plainarglist-fix outputs)
            (vl-plainarglist-fix inouts)
            (vl-plainarglist-fix unknowns)))
       (x1  (vl-plainarg-fix (car x)))
       (dir (vl-plainarg->dir x1))
       ((when (eq dir :vl-input))
        (vl-partition-plainargs (cdr x) (cons x1 inputs) outputs inouts unknowns))
       ((when (eq dir :vl-output))
        (vl-partition-plainargs (cdr x) inputs (cons x1 outputs) inouts unknowns))
       ((when (eq dir :vl-inout))
        (vl-partition-plainargs (cdr x) inputs outputs (cons x1 inouts) unknowns)))
    (vl-partition-plainargs (cdr x) inputs outputs inouts (cons x1 unknowns))))



(fty::deflist vl-directionlist
  :elt-type vl-direction-p)

(deflist vl-directionlist-p (x)
  (vl-direction-p x)
  :elementp-of-nil nil)

(define vl-basic-portexpr-p ((x vl-maybe-expr-p))
  :returns (okp booleanp :rule-classes :type-prescription)
  :short "Recognize non-concatenations that can occur in port expressions."
  (b* ((x (vl-maybe-expr-fix x))
       ((unless x)
        t)
       ((when (vl-fast-atom-p x))
        (vl-idexpr-p x))
       (op (vl-nonatom->op x))
       (args (vl-nonatom->args x))
       ((when (eq op :vl-bitselect))
        (let ((from (first args))
              (bit  (second args)))
          (and (vl-idexpr-p from)
               (vl-expr-resolved-p bit))))
       ((when (eq op :vl-partselect-colon))
        (let ((from (first args))
              (high (second args))
              (low  (third args)))
          (and (vl-idexpr-p from)
               (vl-expr-resolved-p high)
               (vl-expr-resolved-p low)
               (>= (vl-resolved->val high)
                   (vl-resolved->val low))))))
    nil)
  ///
  ;; BOZO not sure what to do about this.
  ;; (defthm vl-basic-portexpr-p-when-degenerate
  ;;   (implies (and (not (vl-atom-p x))
  ;;                 (not (vl-nonatom-p x))
  ;;                 (vl-maybe-expr-p x))
  ;;            (equal (vl-basic-portexpr-p x)
  ;;                   (not x)))
  ;;   :hints(("Goal" :in-theory (enable vl-basic-portexpr-p))))
  )

(deflist vl-basic-portexprlist-p (x)
  (vl-basic-portexpr-p x)
  :guard (vl-exprlist-p x))


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
    (implies (vl-port-wellformed-p x)
             (vl-portexpr-p (vl-port->expr x)))))

(deflist vl-portlist-wellformed-p (x)
  (vl-port-wellformed-p x)
  :guard (vl-portlist-p x)
  :elementp-of-nil t
  ///
  (deffixequiv vl-portlist-wellformed-p :args ((x vl-portlist-p))))



(define vl-flatten-portexpr ((x vl-maybe-expr-p))
  :guard (vl-portexpr-p x)
  :returns (exprs (and (vl-exprlist-p exprs)
                       (vl-basic-portexprlist-p exprs))
                  :hyp :fguard)
  :hooks nil
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


(define vl-basic-portexpr-internal-wirename ((x vl-expr-p))
  :guard (vl-basic-portexpr-p x)
  :guard-hints (("Goal" :in-theory (enable vl-basic-portexpr-p)))
  :parents (vl-port-internal-wirenames)
  (if (vl-fast-atom-p x)
      (vl-idexpr->name x)
    (vl-idexpr->name (first (vl-nonatom->args x)))))

(defprojection vl-basic-portexprlist-internal-wirenames ((x vl-exprlist-p))
  (vl-basic-portexpr-internal-wirename x)
  :guard (vl-basic-portexprlist-p x)
  :parents (vl-port-internal-wirenames)
  :returns (wirenames string-listp))

(define vl-port-internal-wirenames ((x vl-port-p))
  :guard (vl-port-wellformed-p x)
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
      (warnings vl-warninglist-p)
      (directions vl-directionlist-p))
  :verbosep t
  (b* (((when (atom names))
        (mv t (ok) nil))
       (name1 (string-fix (car names)))
       (decl (vl-fast-find-portdecl name1 portdecls palist))
       ((mv successp warnings directions)
        (vl-port-direction-aux (cdr names) portdecls palist warnings port))
       ((when decl)
        (mv successp warnings (cons (vl-portdecl->dir decl) directions))))
    (mv nil
        (warn :type :vl-bad-port
              :msg "~a0 refers to ~w1, but there is no port declaration for ~
                      ~w1."
              :args (list (vl-port-fix port) name1))
        directions))
  ///
  (defmvtypes vl-port-direction-aux (nil nil true-listp)))

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
  ;:hooks nil
  :verbosep t
  :returns
  (mv (warnings  vl-warninglist-p)
      (maybe-dir "The direction for this port, or @('nil') on failure."
                 vl-maybe-direction-p
                 :hints(("Goal" :in-theory (enable vl-maybe-direction-p)))))

  :long "<p>We attempt to determine the direction of this port and return it.
We can fail if the port is not well-formed or if there is no port declaration
corresponding to this port.  In this case we return @('nil') as the
@('maybe-dir'), and add a non-fatal warning describing the problem.</p>

<p>Non-fatal warnings can also be added if a complex port has conflicting
directions, e.g., imagine a port such as @('.foo({bar,baz})'), where @('bar')
is an input and @('baz') is an output.  We regard such a port as an @('inout'),
and add a warning that this case is very unusual.</p>"

  (b* ((port (vl-port-fix port))
       ((unless (vl-port-wellformed-p port))
        (mv (warn :type :vl-bad-port
                  :msg "~a0 is not well-formed."
                  :args (list port))
            nil))

       (names (vl-port-internal-wirenames port))
       ((mv successp warnings dirs)
        (vl-port-direction-aux names portdecls palist warnings port))
       ((unless successp)
        (mv (ok) nil))

       ((when (or (atom (cdr dirs))
                  (all-equalp :vl-input dirs)
                  (all-equalp :vl-output dirs)
                  (all-equalp :vl-inout dirs)))
        (mv (ok) (car dirs))))
    (mv (warn :type :vl-bad-port
              :msg "~a0 refers to ~&1, which do not all agree upon a ~
                      direction.  We do not support this. Directions: ~&2."
              :args (list port names (mergesort dirs)))
        nil))
  ///
  (defthm vl-direction-p-of-vl-port-direction
    (equal (vl-direction-p
            (mv-nth 1 (vl-port-direction port portdecls palist warnings)))
           (if (mv-nth 1 (vl-port-direction port portdecls palist warnings))
               t
             nil))))


(define vl-plainarg-blankfree-p ((x vl-plainarg-p))
  :inline t
  (if (vl-plainarg->expr x)
      t
    nil))

(deflist vl-plainarglist-blankfree-p (x)
  (vl-plainarg-blankfree-p x)
  :guard (vl-plainarglist-p x)
  ///
  (deffixequiv vl-plainarglist-blankfree-p :args ((x vl-plainarglist-p))))

(define vl-namedarg-blankfree-p ((x vl-namedarg-p))
  :inline t
  (if (vl-namedarg->expr x)
      t
    nil))

(deflist vl-namedarglist-blankfree-p (x)
  (vl-namedarg-blankfree-p x)
  :guard (vl-namedarglist-p x)
  ///
  (deffixequiv vl-namedarglist-blankfree-p :args ((x vl-namedarglist-p))))

(define vl-arguments-blankfree-p ((x vl-arguments-p))
  (vl-arguments-case x
    :named (vl-namedarglist-blankfree-p x.args)
    :plain (vl-plainarglist-blankfree-p x.args)))

(define vl-modinst-blankfree-p ((x vl-modinst-p))
  :inline t
  (vl-arguments-blankfree-p (vl-modinst->portargs x)))

(deflist vl-modinstlist-blankfree-p (x)
  (vl-modinst-blankfree-p x)
  :guard (vl-modinstlist-p x)
  ///
  (deffixequiv vl-modinstlist-blankfree-p :args ((x vl-modinstlist-p))))



(define vl-ports-from-portdecls ((x vl-portdecllist-p))
  :short "Construct basic ports corresponding to a list of portdecls."
  :returns (ports vl-portlist-p)
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
  :returns (sub-x vl-portdecllist-p)
  (cond ((atom x)
         nil)
        ((eq (vl-direction-fix dir) (vl-portdecl->dir (car x)))
         (cons (vl-portdecl-fix (car x))
               (vl-portdecls-with-dir dir (cdr x))))
        (t
         (vl-portdecls-with-dir dir (cdr x)))))

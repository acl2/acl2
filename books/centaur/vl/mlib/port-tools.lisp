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
(include-book "scopestack")
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



(defxdoc port-expressions
  :short "Recognizers and functions for working with well-formed port
expressions."

  :long "<p>Our @(see vl-port-p) recognizer doesn't place any restrictions on a
port's expression, except that it should satisfy @(see vl-maybe-expr-p).</p>

<p>However, per Verilog-2005, Section 12.3.2, \"the port reference for each
port in the list of ports at the top of each module declaration can be one of
the following:</p>

<ul>
<li>A simple identifier or escaped identifier</li>
<li>A bit-select of a vector declared within the module</li>
<li>A part-select of a vector declared within the module</li>
<li>A concatenation of any of the above.</li>
</ul>

<p>SystemVerilog-2012 presents identical rules in Section 23.2.2.1.</p>

<p>Note that nested concatenations are not permitted under these rules, e.g.,
whereas @('.a({b,c,d})') is a valid port, @('.a({b,{c,d}})') is not.  Simple
tests suggest that indeed none of Verilog-XL, NCVerilog, or VCS permits any
nested concatenations here; see for instance @('failtest/port13.v').</p>

<p>We now introduce recognizers for the accepted expressions.</p>

<p><u>Portexprs</u>.  We recognize the set of expressions described above with
@(see vl-portexpr-p).  Note that this function only checks the basic shape of
its argument&mdash;it doesn't check that the names are unique or valid or that
indices are sensible or anything like that.</p>

<p><u>Well-formed ports</u>.  We extend the idea of portexprs to check whole
ports in @(see vl-port-wellformed-p).  This function accepts any interface
ports or blank ports without complaint.  However, for any regular ports with
regular expressions, it insists that the expression is a portexpr.</p>

<p><u>Internalnames.</u> Given a valid portexpr, we can easily collect up the
identifiers that occur within it.  The main function to do this for a portexpr
is @(see vl-portexpr->internalnames).</p>")

(local (xdoc::set-default-parents port-expressions))

(define vl-atomicportexpr-p ((x vl-expr-p))
  :returns (okp booleanp :rule-classes :type-prescription)
  :short "Recognize non-concatenations that can occur in port expressions."
  (vl-expr-case x
    :vl-index (vl-scopeexpr-case x.scope
                :end (vl-hidexpr-case x.scope.hid :end)
                :otherwise nil)
    :otherwise nil))

(deflist vl-atomicportexprlist-p (x)
  :guard (vl-exprlist-p x)
  (vl-atomicportexpr-p x))

(define vl-portexpr-p ((x vl-expr-p))
  :returns (okp booleanp :rule-classes :type-prescription)
  :short "Recognizes all expressions that can validly occur in a (non-blank) port."
  (or (vl-atomicportexpr-p x)
      (vl-expr-case x
        :vl-concat (vl-atomicportexprlist-p x.parts)
        :otherwise nil)))

(define vl-maybe-portexpr-p ((x vl-maybe-expr-p))
  :short "Recognizes all expressions that can validly occur in a (possibly blank) port."
  :returns (okp booleanp :rule-classes :type-prescription)
  (b* ((x (vl-maybe-expr-fix x)))
    (or (not x)
        (vl-portexpr-p x)))
  ///
  (defthm vl-maybe-portexpr-p-when-nonnil
    (implies x
             (equal (vl-maybe-portexpr-p x)
                    (vl-portexpr-p x)))))

(define vl-port-wellformed-p ((x vl-port-p))
  :short "Recognizer for ports whose expressions are well-formed."
  (b* ((x (vl-port-fix x)))
    (or (eq (tag x) :vl-interfaceport)
        (vl-maybe-portexpr-p (vl-regularport->expr x)))))

(deflist vl-portlist-wellformed-p (x)
  :short "Recognizer for port lists whose expressions are well-formed."
  (vl-port-wellformed-p x)
  :guard (vl-portlist-p x)
  :elementp-of-nil t
  ///
  (deffixequiv vl-portlist-wellformed-p :args ((x vl-portlist-p))))

(define vl-atomicportexpr->internalname ((x vl-expr-p))
  :guard (vl-atomicportexpr-p x)
  :returns (name stringp :rule-classes :type-prescription)
  :guard-hints (("Goal" :in-theory (enable vl-atomicportexpr-p)))
  (vl-hidexpr-end->name (vl-scopeexpr-end->hid (vl-index->scope x))))

(defprojection vl-atomicportexprlist->internalnames ((x vl-exprlist-p))
  :guard (vl-atomicportexprlist-p x)
  :returns (names string-listp)
  (vl-atomicportexpr->internalname x))

(define vl-portexpr->internalnames ((x vl-expr-p))
  :short "Collect the names of any internal wires that are connected to a
well-formed port and return them as a list of strings."

  :long "<p>We just collect the names of the internal wires that are connected
to the port.  For instance, in the following module,</p>

@({
    module mod (a, .b(foo), .c( {bar[2], baz[width-1:0] } )) ;
      ...
    endmodule
})

<p>the internalnames for the first port are @('(\"a\")'), the second port to
@('(\"foo\")'), and for the third port to @('(\"bar\" \"baz\")').</p>

<p>Note that we omit any names that occur in index expressions, i.e., notice
how we omit @('width') in the third port.</p>"

  :guard (vl-portexpr-p x)
  :returns (names string-listp)
  :guard-hints(("Goal" :in-theory (enable vl-portexpr-p)))
  (if (vl-atomicportexpr-p x)
      (list (vl-atomicportexpr->internalname x))
    (vl-atomicportexprlist->internalnames (vl-concat->parts x))))

(define vl-port->internalnames ((x vl-port-p))
  :guard (vl-port-wellformed-p x)
  :guard-hints(("Goal" :in-theory (enable vl-port-wellformed-p)))
  :returns (names string-listp)
  (b* ((x (vl-port-fix x))
       ((when (eq (tag x) :vl-interfaceport))
        nil)
       (expr (vl-regularport->expr x))
       ((unless expr)
        nil))
    (vl-portexpr->internalnames expr)))

(defmapappend vl-portlist->internalnames (x)
  (vl-port->internalnames x)
  :guard (and (vl-portlist-p x)
              (vl-portlist-wellformed-p x))
  ///
  (defthm string-listp-of-vl-portlist->internalnames
    (string-listp (vl-portlist->internalnames x)))
  (deffixequiv vl-portlist->internalnames :args ((x vl-portlist-p))))


(define vl-port-direction-aux
  :parents (vl-port-direction)
  ((names     string-listp)
   (scope     vl-scope-p)
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
       (decl (vl-scope-find-portdecl-fast name1 scope))
       ((mv successp warnings directions)
        (vl-port-direction-aux (cdr names) scope warnings port))
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
   (scope     "The module or interface containing the port."
              vl-scope-p)
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

       ((when (eq (tag port) :vl-interfaceport))
        ;; No simple direction for interface port.
        (mv (ok) nil))

       (names (vl-port->internalnames port))
       ((mv successp warnings dirs)
        (vl-port-direction-aux names scope warnings port))
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
            (mv-nth 1 (vl-port-direction port scope warnings)))
           (if (mv-nth 1 (vl-port-direction port scope warnings))
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
    :vl-arguments-named (vl-namedarglist-blankfree-p x.args)
    :vl-arguments-plain (vl-plainarglist-blankfree-p x.args)))

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
       (expr (vl-idexpr name)))
    (cons (make-vl-regularport :name name :expr expr :loc loc)
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


(define vl-portdecllist-names-by-direction
  ((x vl-portdecllist-p)
   (in string-listp)
   (out string-listp)
   (inout string-listp))
  :parents (vl-portdecllist-p)
  :returns (mv (in string-listp)
               (out string-listp)
               (inout string-listp))
  (b* (((when (atom x))
        (mv (string-list-fix in)
            (string-list-fix out)
            (string-list-fix inout)))
       (decl (car x))
       (name (vl-portdecl->name decl))
       (dir  (vl-portdecl->dir decl)))
    (case dir
      (:vl-input  (vl-portdecllist-names-by-direction (cdr x) (cons name in) out inout))
      (:vl-output (vl-portdecllist-names-by-direction (cdr x) in (cons name out) inout))
      (:vl-inout  (vl-portdecllist-names-by-direction (cdr x) in out (cons name inout)))
      (otherwise  (progn$ (raise "Impossible")
                          (mv nil nil nil))))))

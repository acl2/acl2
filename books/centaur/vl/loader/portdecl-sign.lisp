; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "../mlib/range-tools")
(include-book "../mlib/find-item")
(include-book "../mlib/filter")
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (std::add-default-post-define-hook :fix))

(defxdoc portdecl-sign
  :parents (loader)
  :short "Fix up type information between port and variable declarations."

  :long "<p>Port and variable declarations have a strange overlap which has
various subtleties.</p>

<p>In some cases, the port declaration is \"complete\" and also gives rise to a
net declaration.  For instance, the declaration of @('a') below introduces both
a port declaration and a net declaration:</p>

@({
    module mymod (a, b, c, ...) ;

      input wire [3:0] a;   // <-- combined port and net declaration
                            //     illegal to subsequently declare wire [3:0] a.

    endmodule
})

<p>In other cases, the port declaration is \"incomplete,\" and it is legal
to subsequently declare the same name as a net or variable.  For instance,
the following is valid even though it looks like @('b') is declared twice:</p>

@({
    module mymod (a, b, c, ...) ;

      input [3:0] b;   // <-- port declaration
      wire [3:0] b;    // <-- corresponding net declaration

    endmodule
})

<p>But incomplete port declarations do not require that an corresponding net
declaration be explicitly present.  For instance, if we simply omit the @('wire
[3:0] b') part from the above example, we implicitly get an equivalent net
declaration.</p>

<p>A particularly subtle part of this is that signedness information can be
given in either the port or the net declaration.  For instance:</p>

@({
    module mymod (a, b, c, d, ...) ;

      input [3:0] c;          //  c becomes signed because the
      wire signed [3:0] c;    //  net declaration says so

      input signed [3:0] d;   //  d becomes signed because the
      wire [3:0] d;           //  port declaration says so

    endmodule
})

<p>To cope with this, after introducing implicit wires, we cross-propagate type
information between incomplete port declarations and their corresponding net
declarations.  The general goal is to ensure that the types of the ports and
nets agree and are correct by the time actual modules are produced.</p>")

(local (xdoc::set-default-parents portdecl-sign))

(define vl-portdecl-sign-adjust-type ((vardecl vl-vardecl-p)
                                      (final-signedp booleanp)
                                      (final-range   vl-maybe-range-p))
  :guard (vl-simplevar-p vardecl)
  :returns (new-type vl-datatype-p)
  :prepwork ((local (in-theory (enable vl-simplevar-p
                                       vl-simplenet-p
                                       vl-simplereg-p))))
  :hooks nil
  (b* ((type (vl-vardecl->type vardecl))
       ((when (eq (vl-datatype-kind type) :vl-nettype))
        (change-vl-nettype type
                           :signedp final-signedp
                           :range   final-range)))
    (change-vl-coretype type
                        :signedp final-signedp
                        :dims    (and final-range
                                      (list final-range)))))


(local (defthm vl-atts-p-of-delete-assoc-equal
         (implies (vl-atts-p atts)
                  (vl-atts-p (delete-assoc-equal name atts)))
         :hints(("Goal" :in-theory (enable delete-assoc-equal)))))

(define vl-portdecl-sign-1
  ((port     vl-portdecl-p)
   (var      vl-vardecl-p  "Corresponding variable declaration")
   (warnings vl-warninglist-p))
  :guard (equal (vl-portdecl->name port) (vl-vardecl->name var))
  :returns
  (mv (successp booleanp :rule-classes :type-prescription)
      (warnings vl-warninglist-p)
      (new-port vl-portdecl-p)
      (new-var  vl-vardecl-p))
  (b* (((vl-portdecl port) (vl-portdecl-fix port))
       ((vl-vardecl var)   (vl-vardecl-fix var))

       ((unless (assoc-equal "VL_INCOMPLETE_DECLARATION" port.atts))
        ;; The port was completely declared, so the types for the port and
        ;; variable should just be in total agreement.
        (if (equal port.type var.type)
            (mv t (ok) port var)
          (mv nil
              (fatal :type :vl-programming-error
                     :msg "~a0: mismatching types between complete port ~
                           declaration and its corresponding variable ~
                           declaration.  Port type: ~a1, variable type: ~a2."
                     :args (list port port.type var.type))
              port var)))

       ;; See vl-parse-basic-port-declaration-tail.  The port declaration is
       ;; not complete.  It may be marked as signed, and it may have a range.
       ;; But we don't know the proper type beyond that.
       ((unless (and (eq (vl-datatype-kind port.type) :vl-nettype)
                     (eq (vl-nettype->name port.type) :vl-wire)))
        ;; Just basic sanity checking.  Should never fail unless there are ways
        ;; to create port declarations that I don't understand.
        (mv nil
            (fatal :type :vl-programming-error
                   :msg "~a0: expected basic wire types for incomplete ~
                         declaration, but found ~a1."
                   :args (list port port.type))
            port var))

       (port-signedp (vl-nettype->signedp port.type))
       (port-range   (vl-nettype->range port.type))

       ((unless (vl-simplevar-p var))
        ;; The corresponding net/variable is something complicated.  I don't
        ;; think we need to allow this?  (Maybe we'll want to relax this and
        ;; allow things like bit or shortint or whatever, but we should
        ;; experiment with what Verilog simulators allow.)
        (mv nil
            (fatal :type :vl-port/var-disagree
                   :msg "~a0: the variable's type is too complex to merge ~
                         with the corresponding, incomplete port.  Type: ~a1."
                   :args (list var var.type))
            port var))

       (var-signedp (vl-simplevar->signedp var))
       (var-range   (vl-simplevar->range var))

       ((unless (or (not port-range)
                    (not var-range)
                    (equal port-range var-range)))
        (mv nil
            (fatal :type :vl-port/var-disagree
                   :msg "~a0: the given range, ~a1, disagrees with the range ~
                         for the corresponding net, ~a2."
                   :args (list port port-range var-range))
            port var))

       (final-signedp (or var-signedp port-signedp))
       (final-range   (or port-range var-range))
       (final-type    (vl-portdecl-sign-adjust-type var final-signedp final-range))

       (new-port (change-vl-portdecl port
                                     :atts (delete-assoc-equal "VL_INCOMPLETE_DECLARATION" port.atts)
                                     :type final-type))
       (new-var  (change-vl-vardecl var
                                    ;; Mark the net as port implicit so that it won't get pretty-printed.
                                    :atts (acons "VL_PORT_IMPLICIT" nil
                                                 (delete-assoc-equal "VL_INCOMPLETE_DECLARATION" var.atts))
                                    :type final-type)))
    (mv t (ok) new-port new-var)))


(define vl-portdecl-sign-list
  ((portdecls vl-portdecllist-p "Port declarations to process, which we recur through.")
   (vardecls  vl-vardecllist-p  "Exactly the corresponding variable declarations.")
   (warnings  vl-warninglist-p))
  :guard (equal (vl-portdecllist->names portdecls)
                (vl-vardecllist->names vardecls))
  :returns
  (mv (successp  booleanp :rule-classes :type-prescription)
      (warnings  vl-warninglist-p)
      (new-ports vl-portdecllist-p)
      (new-vars  vl-vardecllist-p))
  (b* (((when (atom portdecls))
        (mv t (ok) nil nil))
       ((mv okp1 warnings port1 var1)
        (vl-portdecl-sign-1 (car portdecls) (car vardecls) warnings))
       ((mv okp2 warnings ports2 vars2)
        (vl-portdecl-sign-list (cdr portdecls) (cdr vardecls) warnings)))
    (mv (and okp1 okp2)
        warnings
        (cons port1 ports2)
        (cons var1 vars2)))
  ///
  (more-returns
   (new-ports true-listp :rule-classes :type-prescription)
   (new-vars  true-listp :rule-classes :type-prescription)))


(define vl-find-vardecls-exec ((names    string-listp)
                               (vardecls vl-vardecllist-p)
                               (alist    (equal alist (vl-vardecllist-alist vardecls))))
  :parents (vl-find-vardecls)
  :hooks nil
  (if (atom names)
      nil
    (cons (cdr (hons-get (car names) alist))
          (vl-find-vardecls-exec (cdr names) vardecls alist))))

(define vl-find-vardecls
  :short "Collect variable declarations, by name, in order."
  ((names    string-listp     "Names of variables to collect.")
   (vardecls vl-vardecllist-p "List of all variable declarations to collect from."))
  :returns (named-vardecls)

  :long "<p>This is much like @(see vl-keep-vardecls), but it returns the
results in a different order.  That is:</p>

<ul>

<li>@('(vl-keep-vardecls names decls)') returns the named declarations in the
same order as they are listed in @('decls'), whereas</li>

<li>@('(vl-find-vardecls names decls)') returns the named declarations in the
same order as they are listed in @('names').</li>

</ul>

<p>Keeping the exact name order is useful for, e.g., collecting the variables
that correspond to port declarations.</p>"

  :hooks nil
  :verify-guards nil
  (mbe :logic
       (if (atom names)
           nil
         (cons (vl-find-vardecl (car names) vardecls)
               (vl-find-vardecls (cdr names) vardecls)))
       :exec
       (b* ((alist (vl-vardecllist-alist vardecls))
            (ans   (vl-find-vardecls-exec names vardecls alist)))
         (fast-alist-free alist)
         ans))
  ///
  (defthm vl-find-vardecls-exec-removal
    (implies (equal alist (vl-vardecllist-alist vardecls))
             (equal (vl-find-vardecls-exec names vardecls alist)
                    (vl-find-vardecls names vardecls)))
    :hints(("Goal" :in-theory (enable vl-find-vardecls-exec))))

  (verify-guards vl-find-vardecls)

  (defthm vl-vardecllist-p-of-vl-find-vardecls-unless-nil
    (let ((found (vl-find-vardecls names vardecls)))
      (implies (not (member nil found))
               (vl-vardecllist-p found))))

  (defthm vl-vardecllist-p-of-remove-nil-from-vl-find-vardecls
    (vl-vardecllist-p
     (remove-equal nil (vl-find-vardecls names vardecls))))

  (defthm nil-in-vl-find-vardecls
    (iff (member nil (vl-find-vardecls names vardecls))
         (not (subsetp-equal names (vl-vardecllist->names vardecls)))))

  (defthm vl-vardecllist-p-of-vl-find-vardecls-when-subset
    (implies (subsetp-equal names (vl-vardecllist->names vardecls))
             (vl-vardecllist-p (vl-find-vardecls names vardecls))))

  (local (defthm l0
           (implies (and (member a (vl-find-vardecls names vardecls))
                         (vl-vardecllist-p vardecls)
                         a)
                    (member a vardecls))))

  (defthm subsetp-of-vl-find-vardecls
    (implies (and (subsetp-equal names (vl-vardecllist->names vardecls))
                  (force (vl-vardecllist-p vardecls)))
             (subsetp-equal (vl-find-vardecls names vardecls) vardecls)))

  (defthm vl-vardecllist->names-of-vl-find-vardecls
    (implies (subsetp-equal names (vl-vardecllist->names vardecls))
             (equal (vl-vardecllist->names (vl-find-vardecls names vardecls))
                    (string-list-fix names)))))


(define vl-portdecl-sign
  ((portdecls vl-portdecllist-p)
   (vardecls  vl-vardecllist-p)
   (warnings  vl-warninglist-p))
  :returns
  (mv (warnings      vl-warninglist-p)
      (new-portdecls vl-portdecllist-p)
      (new-vardecls  vl-vardecllist-p))
  (b* ((portdecls (vl-portdecllist-fix portdecls))
       (vardecls  (vl-vardecllist-fix vardecls))

       (pnames (vl-portdecllist->names portdecls))
       (vnames (vl-vardecllist->names vardecls))

       (missing (difference (mergesort pnames) (mergesort vnames)))
       ((when missing)
        (mv (fatal :type :vl-bad-ports
                   :msg "Found ports without corresponding variable ~
                         declarations: ~&0."
                   :args (list missing))
            portdecls vardecls))

       (port-vars     (vl-find-vardecls pnames vardecls))
       (non-port-vars (vl-delete-vardecls pnames vardecls))

       ((mv ?okp warnings new-portdecls new-port-vars)
        (vl-portdecl-sign-list portdecls port-vars warnings))

       (new-vardecls  (append new-port-vars non-port-vars)))
    (mv (ok) new-portdecls new-vardecls)))

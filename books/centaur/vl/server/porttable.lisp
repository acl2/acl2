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
(include-book "../mlib/writer")
(include-book "../mlib/expr-tools")
(include-book "../mlib/port-tools")
(local (include-book "../util/arithmetic"))

; BOZO this is very old code.  It would be better to build a JSON
; representation of the ports that we just sent to the browser, and let it
; handle the details of how to render it into an HTML table.

(define vl-pp-porttable-in-decl (x &key (ps 'ps))
  :guard (vl-portdecl-p x)
  (b* (((vl-portdecl x) x))
    (vl-ps-seq
     (vl-print-markup "<tr><td align=\"right\"><nobr>")
     (vl-pp-datatype x.type)
     (vl-print " ")
     (vl-print-wirename x.name)
     (vl-println-markup "</nobr></td>")
     (vl-print-markup "<td width=\"41\"><img src=\"images/browser_arrow.png\"/></td>")
     (vl-println-markup "</tr>"))))

(define vl-pp-porttable-in-decls-aux (x &key (ps 'ps))
  :guard (vl-portdecllist-p x)
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-porttable-in-decl (car x))
               (vl-pp-porttable-in-decls-aux (cdr x)))))

(define vl-pp-porttable-in-decls (x &key (ps 'ps))
  :guard (vl-portdecllist-p x)
  (vl-ps-seq (vl-println-markup "<table class=\"portsignals\" cellspacing=\"0\" colspacing=\"15\">")
             (vl-pp-porttable-in-decls-aux x)
             (vl-println-markup "</table>")))


(define vl-pp-porttable-out-decl (x &key (ps 'ps))
  :guard (vl-portdecl-p x)
  (b* (((vl-portdecl x) x))
    (vl-ps-seq
     (vl-print-markup "<tr>")
     (vl-print-markup "<td width=\"41\"><img src=\"images/browser_arrow.png\"/></td>")
     (vl-print-markup "<td><nobr>")
     (vl-print-wirename x.name)
     (vl-print " ")
     (vl-pp-datatype x.type)
     (vl-println-markup "</nobr></td></tr>"))))

(define vl-pp-porttable-out-decls-aux (x &key (ps 'ps))
  :guard (vl-portdecllist-p x)
  (if (atom x)
      ps
    (vl-ps-seq (vl-pp-porttable-out-decl (car x))
               (vl-pp-porttable-out-decls-aux (cdr x)))))

(define vl-pp-porttable-out-decls (x &key (ps 'ps))
  :guard (vl-portdecllist-p x)
  (vl-ps-seq (vl-println-markup "<table class=\"portsignals\" cellspacing=\"15\">")
             (vl-pp-porttable-out-decls-aux x)
             (vl-println-markup "</table>")))


(define vl-portdecl-< ((x vl-portdecl-p)
                       (y vl-portdecl-p))
  (str::strnat< (vl-portdecl->name x)
                (vl-portdecl->name y))
  ///
  (defthm vl-portdecl-<-transitive
    (implies (and (vl-portdecl-< x y)
                  (vl-portdecl-< y z))
             (vl-portdecl-< x z))))

(acl2::defsort vl-portdecl-sort
  :weak t
  :comparablep vl-portdecl-p
  :compare< vl-portdecl-<
  :comparable-listp vl-portdecllist-p)

(define vl-pp-porttable (x &key (ps 'ps))
  :guard (vl-module-p x)
  (b* (((vl-module x) x)
       (inputs  (vl-portdecls-with-dir :vl-input x.portdecls))
       (outputs (vl-portdecls-with-dir :vl-output x.portdecls))
       (inouts  (vl-portdecls-with-dir :vl-inout x.portdecls))
       (ps      (if (not inouts)
                    ps
                  (vl-println-markup "<p>Note: inout ports not shown!</p>")))
       (ps      (if (atom (vl-module->ifports x))
                    ps
                  (vl-println-markup "<p>Note: interface ports not shown!</p>"))))
    (vl-ps-seq
     (vl-println-markup "<table width=\"100%\" height=\"100%\">")
     (vl-println-markup "<tr>")
     (vl-println-markup "")

     (vl-println-markup "<td class=\"porttable_ins\" width=\"10%\" align=\"right\">")
     (vl-pp-porttable-in-decls (vl-portdecl-sort inputs))
     (vl-println-markup "</td>")
     (vl-println-markup "")

     (vl-println-markup "<td class=\"porttable_mod\" width=\"80%\" valign=\"top\" align=\"center\">")
     (vl-print x.name)
     (vl-println-markup "</td>")
     (vl-println-markup "")

     (vl-println-markup "<td class=\"porttable_outs\" width=\"10%\">")
     (vl-pp-porttable-out-decls (vl-portdecl-sort outputs))
     (vl-println-markup "</td>")
     (vl-println-markup "")

     (vl-println-markup "</tr>")
     (vl-println-markup "</table>"))))



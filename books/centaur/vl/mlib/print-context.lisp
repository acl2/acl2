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
(include-book "writer")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (xdoc::set-default-parents vl-context))

(define vl-pp-ctxelement-summary
  :short "Print a short, human-friendly description of a @(see vl-ctxelement-p)."
  ((x vl-ctxelement-p)
   &key
   ((withloc "Ensure that a location is printed.  By default we generally hide
              location numbers and simply say things like, \"Assignment to foo.\"
              However, in some cases it's useful to ensure that a location gets
              printed, e.g., for multidrive warnings.") 'nil)
   (ps 'ps))
  (b* ((x (vl-ctxelement-fix x)))
    (case (tag x)
      (:vl-regularport
       (let* ((name (vl-regularport->name x)))
         (if name
             (vl-ps-seq (vl-print "Port ")
                        (vl-print-wirename name)
                        (if withloc
                            (vl-ps-seq (vl-print " at ")
                                       (vl-print-loc (vl-port->loc x)))
                          ps))
           (vl-ps-seq (vl-print "Unnamed port at ")
                      (vl-print-loc (vl-port->loc x))))))
      (:vl-interfaceport
       (let* ((name (vl-interfaceport->name x)))
         (vl-ps-seq (vl-print "Interface port ")
                    (vl-print-wirename name)
                    (if withloc
                        (vl-ps-seq (vl-print " at ")
                                   (vl-print-loc (vl-interfaceport->loc x)))
                      ps))))

      (:vl-portdecl
       (vl-ps-seq (vl-print "Port declaration of ")
                  (vl-print-wirename (vl-portdecl->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-portdecl->loc x)))
                    ps)))

      (:vl-assign
       ;; As a dumb hack, we say if the lvalue is less than 40 characters long
       ;; when printed in text mode, we'll just print the whole thing using our
       ;; real pretty-printer.  But to avoid really long output, we elide lvalues
       ;; that are longer than this (and just print their text version).
       (let* ((orig (vl-pps-origexpr (vl-assign->lvalue x))))
         (vl-ps-seq (vl-print "Assignment to ")
                    (if (< (length orig) 40)
                        (vl-ps-seq (vl-pp-origexpr (vl-assign->lvalue x))
                                   (if withloc
                                       (vl-ps-seq (vl-print " at ")
                                                  (vl-print-loc (vl-assign->loc x)))
                                     ps))
                      (vl-ps-seq
                       (vl-print (subseq orig 0 40))
                       ;; To reduce the amount of line numbers we see in error
                       ;; messages we now prefer to print the location only if
                       ;; the name is elided.
                       (vl-print "... at ")
                       (vl-print-loc (vl-assign->loc x)))))))

      (:vl-vardecl
       (vl-ps-seq (vl-print "Declaration of ")
                  (vl-print-wirename (vl-vardecl->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-vardecl->loc x)))
                    ps)))

      (:vl-paramdecl
       (vl-ps-seq (vl-print "Param declaration of ")
                  (vl-print-wirename (vl-paramdecl->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-paramdecl->loc x)))
                    ps)))

      (:vl-fundecl
       (vl-ps-seq (vl-print "Function ")
                  (vl-print-wirename (vl-fundecl->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-fundecl->loc x)))
                    ps)))

      (:vl-taskdecl
       (vl-ps-seq (vl-print "Task ")
                  (vl-print-wirename (vl-taskdecl->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-taskdecl->loc x)))
                    ps)))

      (:vl-modinst
       (let* ((instname (vl-modinst->instname x))
              (modname  (vl-modinst->modname x)))
         (if instname
             (vl-ps-seq (vl-print "Instance ")
                        (vl-print-wirename instname)
                        (vl-print " of ")
                        (vl-print-modname modname)
                        (if withloc
                            (vl-ps-seq (vl-print " at ")
                                       (vl-print-loc (vl-modinst->loc x)))
                          ps))
           (vl-ps-seq (vl-print "Unnamed instance of ")
                      (vl-print-modname modname)
                      (vl-print " at ")
                      (vl-print-loc (vl-modinst->loc x))))))

      (:vl-gateinst
       (b* ((name  (vl-gateinst->name x))
            (type  (vl-gatetype-string (vl-gateinst->type x))))
         (if name
             (vl-ps-seq (vl-print-str (str::upcase-first type))
                        (vl-print " gate ")
                        (vl-print-wirename name)
                        (if withloc
                            (vl-ps-seq (vl-print " at ")
                                       (vl-print-loc (vl-gateinst->loc x)))
                          ps))
           (vl-ps-seq (vl-print "Unnamed ")
                      (vl-print-str type)
                      (vl-print " gate at ")
                      (vl-print-loc (vl-gateinst->loc x))))))

      (:vl-always
       (vl-ps-seq (vl-print "Always statement at ")
                  (vl-print-loc (vl-always->loc x))))

      (:vl-initial
       (vl-ps-seq (vl-print "Initial statement at ")
                  (vl-print-loc (vl-initial->loc x))))

      (:vl-final
       (vl-ps-seq (vl-print "Final statement at ")
                  (vl-print-loc (vl-final->loc x))))

      (:vl-typedef
       (vl-ps-seq (vl-print "Typedef of ")
                  (vl-print-wirename (vl-typedef->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-typedef->loc x)))
                    ps)))

      (:vl-fwdtypedef
       (vl-ps-seq (vl-print "Fwdtypedef at ")
                  (vl-print-loc (vl-fwdtypedef->loc x))))

      (:vl-modport
       (vl-ps-seq (vl-print "Modport at ")
                  (vl-print-loc (vl-modport->loc x))))

      (:vl-alias
       (vl-ps-seq (vl-print "Alias at ")
                  (vl-print-loc (vl-alias->loc x))))

      (:vl-import
       ;; These are simple enough to just print.
       (vl-pp-import x))

      (:vl-property
       (vl-ps-seq (vl-print "Property ")
                  (vl-print-str (vl-property->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-property->loc x)))
                    ps)))

      (:vl-sequence
       (vl-ps-seq (vl-print "Sequence ")
                  (vl-print-str (vl-sequence->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-sequence->loc x)))
                    ps)))

      (:vl-clkdecl
       (vl-ps-seq (if (vl-clkdecl->name x)
                      (vl-ps-seq (vl-print "Clocking block ")
                                 (vl-print-str (vl-clkdecl->name x))
                                 (if withloc
                                     (vl-ps-seq (vl-print " at ")
                                                (vl-print-loc (vl-clkdecl->loc x)))
                                   ps))
                    (vl-ps-seq (vl-print "Clocking block at ")
                               (vl-print-loc (vl-clkdecl->loc x))))))

      (:vl-gclkdecl
       (vl-ps-seq (if (vl-gclkdecl->name x)
                      (vl-ps-seq (vl-print "Global clocking block ")
                                 (vl-print-str (vl-gclkdecl->name x))
                                 (if withloc
                                     (vl-ps-seq (vl-print " at ")
                                                (vl-print-loc (vl-gclkdecl->loc x)))
                                   ps))
                    (vl-ps-seq (vl-print "Global clocking block at ")
                               (vl-print-loc (vl-gclkdecl->loc x))))))

      (:vl-defaultdisable
       (vl-ps-seq (vl-print "Default disable statement at ")
                  (vl-print-loc (vl-defaultdisable->loc x))))

      (:vl-assertion
       (vl-ps-seq (vl-print "Assertion ")
                  (vl-print-str (or (vl-assertion->name x) ""))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-assertion->loc x)))
                    ps)))

      (:vl-cassertion
       (vl-ps-seq (vl-print "Assertion ")
                  (vl-print-str (or (vl-cassertion->name x) ""))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-cassertion->loc x)))
                    ps)))

      (:vl-dpiimport
       (vl-ps-seq (vl-print "DPI import of ")
                  (vl-print-str (vl-dpiimport->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-dpiimport->loc x)))
                    ps)))

      (:vl-dpiexport
       (vl-ps-seq (vl-print "DPI export of ")
                  (vl-print-str (vl-dpiexport->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-dpiexport->loc x)))
                    ps)))

      (:vl-bind
       (vl-ps-seq (vl-print "Bind construct at ")
                  (vl-print-loc (vl-bind->loc x))))

      (:vl-class
       (vl-ps-seq (vl-print "Class ")
                  (vl-print-str (vl-class->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-class->loc x)))
                    ps)))

      (:vl-covergroup
       (vl-ps-seq (vl-print "Covergroup ")
                  (vl-print-str (vl-covergroup->name x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-covergroup->loc x)))
                    ps)))

      (:vl-elabtask
       (vl-ps-seq (vl-print "Elaboration system task ")
                  (vl-pp-stmt (vl-elabtask->stmt x))
                  (if withloc
                      (vl-ps-seq (vl-print " at ")
                                 (vl-print-loc (vl-elabtask->loc x)))
                    ps)))

      ((:vl-genif :vl-genloop :vl-gencase :vl-genbegin :vl-genarray :vl-genbase)
       (vl-ps-seq (vl-print "Generate block at ")
                  (vl-print-loc (vl-genelement->loc x))))

      (otherwise
       (prog2$ (impossible) ps)))))

(define vl-ctxelement-summary
  :short "Get a short, human-friendly string describing a @(see vl-ctxelement-p)."
  ((x vl-ctxelement-p) &key (withloc 'nil))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-ctxelement-summary x :withloc withloc)))

(define vl-pp-context-summary ((x vl-context1-p) &key (withloc 'nil) (ps 'ps))
  :short "Print a short, human-friendly string describing a @(see vl-context-p)."
  (b* (((vl-context1 x) x))
    (vl-ps-seq (vl-print "In ")
               (vl-print-modname x.mod)
               (vl-println? ", ")
               (vl-pp-ctxelement-summary x.elem :withloc withloc))))

(define vl-context-summary
  :short "Get a short, human-friendly string describing a @(see vl-context-p)."
  ((x vl-context1-p) &key (withloc 'nil))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-context-summary x :withloc withloc)))

(define vl-pp-ctxelement-full
  :short "Pretty-print a full @(see vl-ctxelement-p)."
  ((x vl-ctxelement-p) &key (ps 'ps))
  :long "<p>This sometimes produces output that is too big.  If you just want a
quick summary instead, see @(see vl-pp-ctxelement-summary).</p>"
  (b* ((x (vl-ctxelement-fix x)))
    (case (tag x)
      (:vl-regularport   (vl-pp-regularport x))
      (:vl-interfaceport (vl-pp-interfaceport x))
      (:vl-portdecl      (vl-pp-portdecl x))
      (:vl-assign        (vl-pp-assign x))
      (:vl-vardecl       (vl-pp-vardecl x))
      (:vl-paramdecl     (vl-pp-paramdecl x))
      (:vl-fundecl       (vl-pp-fundecl x))
      (:vl-taskdecl      (vl-pp-taskdecl x))
      (:vl-modinst       (vl-pp-modinst x nil))
      (:vl-gateinst      (vl-pp-gateinst x))
      (:vl-always        (vl-pp-always x))
      (:vl-initial       (vl-pp-initial x))
      (:vl-final         (vl-pp-final x))
      (:vl-alias         (vl-pp-alias x))
      (:vl-typedef       (vl-pp-typedef x))
      (:vl-fwdtypedef    (vl-pp-fwdtypedef x))
      (:vl-modport       (vl-pp-modport x))
      (:vl-import        (vl-pp-import x))
      (:vl-property      (vl-pp-property x))
      (:vl-sequence      (vl-pp-sequence x))
      (:vl-clkdecl       (vl-pp-clkdecl x))
      (:vl-gclkdecl      (vl-pp-gclkdecl x))
      (:vl-defaultdisable (vl-pp-defaultdisable x))
      (:vl-dpiimport     (vl-pp-dpiimport x))
      (:vl-dpiexport     (vl-pp-dpiexport x))
      (:vl-bind          (vl-pp-bind x nil))
      (:vl-class         (vl-pp-class x))
      (:vl-covergroup    (vl-pp-covergroup x))
      (:vl-elabtask      (vl-pp-elabtask x))
      (:vl-assertion     (vl-pp-assertion x :include-name t))
      (:vl-cassertion    (vl-pp-cassertion x :include-name t))
      ((:vl-genif :vl-genloop :vl-gencase :vl-genbegin :vl-genarray :vl-genbase)
       (vl-pp-genelement x))
      (otherwise (prog2$ (impossible) ps)))))

(define vl-pp-context-full ((x vl-context1-p) &key (ps 'ps))
  :short "Pretty-print a full @(see vl-context-p)."
  (b* (((vl-context1 x) x))
      (vl-ps-seq (vl-print "In module ")
                 (vl-print-modname x.mod)
                 (vl-println ",")
                 (vl-pp-ctxelement-full x.elem)
                 (vl-println ""))))

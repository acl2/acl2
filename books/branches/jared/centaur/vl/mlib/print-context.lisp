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
(include-book "context")
(include-book "writer")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))

(local (xdoc::set-default-parents context))

(define vl-pp-modelement-summary
  :short "Print a short, human-friendly description of a @(see vl-modelement-p)."
  ((x vl-modelement-p) &key (ps 'ps))
  (b* ((x (vl-modelement-fix x)))
    (case (tag x)
      (:vl-port
       (let* ((name (vl-port->name x)))
         (if name
             (vl-ps-seq (vl-basic-cw "Port ")
                        (vl-print-wirename name))
           (vl-ps-seq (vl-basic-cw "Unnamed port at ")
                      (vl-print-loc (vl-port->loc x))))))

      (:vl-portdecl
       (vl-ps-seq (vl-basic-cw "Port declaration of ")
                  (vl-print-wirename (vl-portdecl->name x))))

      (:vl-assign
       ;; As a dumb hack, we say if the lvalue is less than 40 characters long
       ;; when printed in text mode, we'll just print the whole thing using our
       ;; real pretty-printer.  But to avoid really long output, we elide lvalues
       ;; that are longer than this (and just print their text version).
       (let* ((orig (vl-pps-origexpr (vl-assign->lvalue x))))
         (vl-ps-seq (vl-basic-cw "Assignment to ")
                    (if (< (length orig) 40)
                        (vl-pp-origexpr (vl-assign->lvalue x))
                      (vl-ps-seq
                       (vl-print (subseq orig 0 40))
                       ;; To reduce the amount of line numbers we see in error
                       ;; messages we now prefer to print the location only if
                       ;; the name is elided.
                       (vl-print "... at ")
                       (vl-print-loc (vl-assign->loc x)))))))

      (:vl-netdecl
       (vl-ps-seq (vl-basic-cw "Net declaration of ")
                  (vl-print-wirename (vl-netdecl->name x))))

      (:vl-vardecl
       (vl-ps-seq (vl-basic-cw "Var declaration of ")
                  (vl-print-wirename (vl-vardecl->name x))))

      (:vl-paramdecl
       (vl-ps-seq (vl-basic-cw "Param declaration of ")
                  (vl-print-wirename (vl-paramdecl->name x))))

      (:vl-fundecl
       (vl-ps-seq (vl-basic-cw "Function ")
                  (vl-print-wirename (vl-fundecl->name x))))

      (:vl-taskdecl
       (vl-ps-seq (vl-basic-cw "Task ")
                  (vl-print-wirename (vl-taskdecl->name x))))

      (:vl-modinst
       (let* ((instname (vl-modinst->instname x))
              (modname  (vl-modinst->modname x)))
         (if instname
             (vl-ps-seq (vl-basic-cw "Instance ")
                        (vl-print-wirename instname)
                        (vl-basic-cw " of ")
                        (vl-print-modname modname))
           (vl-ps-seq (vl-basic-cw "Unnamed instance of ")
                      (vl-print-modname modname)
                      (vl-basic-cw " at ")
                      (vl-print-loc (vl-modinst->loc x))))))

      (:vl-gateinst
       (b* ((name  (vl-gateinst->name x))
            (type  (vl-gatetype-string (vl-gateinst->type x))))
         (if name
             (vl-ps-seq (vl-basic-cw "Gate ")
                        (vl-print-wirename name)
                        (vl-basic-cw (cat " of type " type)))
           (vl-ps-seq (vl-basic-cw (cat "Unnamed gate of type " type " at "))
                      (vl-print-loc (vl-gateinst->loc x))))))

      (:vl-always
       (vl-ps-seq (vl-basic-cw "Always statement at ")
                  (vl-print-loc (vl-always->loc x))))

      (:vl-initial
       (vl-ps-seq (vl-basic-cw "Initial statement at ")
                  (vl-print-loc (vl-initial->loc x))))

      (otherwise
       (prog2$ (impossible) ps)))))

(define vl-modelement-summary
  :short "Get a short, human-friendly string describing a @(see vl-modelement-p)."
  ((x vl-modelement-p))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-modelement-summary x)))

(define vl-pp-context-summary ((x vl-context-p) &key (ps 'ps))
  :short "Print a short, human-friendly string describing a @(see vl-context-p)."
  (b* (((vl-context x) x))
    (vl-ps-seq (vl-print "In ")
               (vl-print-modname x.mod)
               (vl-println? ", ")
               (vl-pp-modelement-summary x.elem))))

(define vl-context-summary
  :short "Get a short, human-friendly string describing a @(see vl-context-p)."
  ((x vl-context-p))
  :returns (str stringp :rule-classes :type-prescription)
  (with-local-ps (vl-pp-context-summary x)))

(define vl-pp-modelement-full
  :short "Pretty-print a full @(see vl-modelement-p)."
  ((x vl-modelement-p) &key (ps 'ps))
  :long "<p>This sometimes produces output that is too big.  If you just want a
quick summary instead, see @(see vl-pp-modelement-summary).</p>"
  (b* ((x (vl-modelement-fix x)))
    (case (tag x)
      (:vl-port      (vl-pp-port x))
      (:vl-portdecl  (vl-pp-portdecl x))
      (:vl-assign    (vl-pp-assign x))
      (:vl-netdecl   (vl-pp-netdecl x))
      (:vl-vardecl   (vl-pp-vardecl x))
      (:vl-eventdecl (vl-print "// BOZO implement vl-pp-eventdecl in vl-pp-modelement-full"))
      (:vl-paramdecl (vl-pp-paramdecl x))
      (:vl-fundecl   (vl-pp-fundecl x))
      (:vl-taskdecl  (vl-pp-taskdecl x))
      (:vl-modinst   (vl-pp-modinst x nil nil))
      (:vl-gateinst  (vl-pp-gateinst x))
      (:vl-always    (vl-pp-always x))
      (:vl-initial   (vl-pp-initial x))
      (otherwise (prog2$ (impossible) ps)))))

(define vl-pp-context-full ((x vl-context-p) &key (ps 'ps))
  :short "Pretty-print a full @(see vl-context-p)."
  (b* (((vl-context x) x))
      (vl-ps-seq (vl-print "In module ")
                 (vl-print-modname x.mod)
                 (vl-println ",")
                 (vl-pp-modelement-full x.elem)
                 (vl-println ""))))

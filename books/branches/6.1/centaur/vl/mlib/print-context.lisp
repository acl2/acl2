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
(include-book "context")
(include-book "writer")
(local (include-book "../util/arithmetic"))


(defpp vl-pp-modelement-summary (x)
  :guard (vl-modelement-p x)
  :body
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

    (:vl-regdecl
     (vl-ps-seq (vl-basic-cw "Reg declaration of ")
                (vl-print-wirename (vl-regdecl->name x))))
    (:vl-eventdecl
     (vl-ps-seq (vl-basic-cw "Event declaration of ")
                (vl-print-wirename (vl-eventdecl->name x))))

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
     (prog2$ (er hard 'vl-pp-modelement-summary "Impossible")
             ps))))


(defsection vl-modelement-summary
  :parents (vl-modelement-p)
  :short "Produce a short, human-friendly description of a @(see vl-modelement-p)."
  :long "@(thm stringp-of-vl-modelement-summary)
@(def vl-modelement-summary)"

  (defund vl-modelement-summary (x)
    (declare (xargs :guard (vl-modelement-p x)))
    (with-local-ps (vl-pp-modelement-summary x)))

  (local (in-theory (enable vl-modelement-summary)))

  (defthm stringp-of-vl-modelement-summary
    (stringp (vl-modelement-summary x))
    :rule-classes :type-prescription))



(defpp vl-pp-context-summary (x)
  :guard (vl-context-p x)
  :body
  (b* (((vl-context x) x))
    (vl-ps-seq (vl-print "In ")
               (vl-print-modname x.mod)
               (vl-println? ", ")
               (vl-pp-modelement-summary x.elem))))

(defsection vl-context-summary
  :parents (vl-context-p)
  :short "Produce a short, human-friendly description of a @(see vl-context-p)."
  :long "<p>See also @(see vl-modelement-summary) and @(see
vl-pp-context-full).</p>"

  (defund vl-context-summary (x)
    (declare (xargs :guard (vl-context-p x)))
    (with-local-ps (vl-pp-context-summary x)))

  (local (in-theory (enable vl-context-summary)))

  (defthm stringp-of-vl-context-summary
    (stringp (vl-context-summary x))
    :rule-classes :type-prescription))


(defpp vl-pp-modelement-full (x)
  :parents (vl-modelement-p)
  :short "Pretty-print a full @(see vl-modelement-p)"
  :guard (vl-modelement-p x)
  :body
  (case (tag x)
    (:vl-port      (vl-pp-port x))
    (:vl-portdecl  (vl-pp-portdecl x))
    (:vl-assign    (vl-pp-assign x))
    (:vl-netdecl   (vl-pp-netdecl x))
    (:vl-vardecl   (vl-pp-vardecl x))
    (:vl-regdecl   (vl-pp-regdecl x))
    (:vl-eventdecl (vl-print "// BOZO implement vl-pp-eventdecl in vl-pp-modelement-full"))
    (:vl-paramdecl (vl-pp-paramdecl x))
    (:vl-fundecl   (vl-pp-fundecl x))
    (:vl-taskdecl  (vl-pp-taskdecl x))
    (:vl-modinst   (vl-pp-modinst x nil nil))
    (:vl-gateinst  (vl-pp-gateinst x))
    (:vl-always    (vl-pp-always x))
    (:vl-initial   (vl-pp-initial x))
    (otherwise
     (prog2$ (er hard 'vl-pp-modelement "Impossible")
             ps))))

(defpp vl-pp-context-full (x)
  :parents (vl-context-p)
  :short "Pretty-print a longer description of where a @(see vl-context-p) occurs."
  :guard (vl-context-p x)
  :body
  (b* (((vl-context x) x))
      (vl-ps-seq
       (vl-print "In module ")
       (vl-print-modname x.mod)
       (vl-println ",")
       (vl-pp-modelement-full x.elem)
       (vl-println ""))))

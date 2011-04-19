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
(include-book "writer")
(include-book "../util/cwtime")
(include-book "../loader/inject-comments") ; BOZO why is this in the loader?
(local (include-book "../util/arithmetic"))


;                             COMMENT INJECTION
;
; The above routines only print the parse-tree part of a module.  We now write
; our main routine for merging the comments in and printing the module back out
; in a reasonable order.
;
; The comment map is an alist of (location . string) pairs.  Since each module
; item has a location, and we can now pretty-print each kind of module item
; into a string, we will just create another one of these alists for the the
; module items.  Then, we just need to merge the two alists in order to put the
; comments back into place.
;
; To generate the PPMAP, we could use with-local-ps to print each module item
; in a local pstate.  But to avoid the overhead of creating and reconfiguring
; many ps objects, we instead just pass in the pstate to use but clear its
; rchars and column before printing each module item.  This is just a dumb hack
; to allow us to configure the pstate once, then never worry about its
; configuration again.


(defthm alistp-when-vl-commentmap-p
  (implies (vl-commentmap-p x)
           (alistp x))
  :hints(("Goal" :induct (len x))))


(defmacro with-semilocal-ps (&rest args)
  `(let ((ps (vl-ps-seq
              (vl-ps-update-rchars nil)
              (vl-ps-update-col 0)
              ,@args)))
     (mv (vl-ps->string) ps)))



(defund vl-portdecllist-ppmap (x alist ps)
  (declare (xargs :guard (and (vl-portdecllist-p x)
                              (vl-commentmap-p alist)
                              (vl-pstate-p ps))
                  :stobjs ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
            (with-semilocal-ps (vl-pp-portdecl (car x)))
            (vl-portdecllist-ppmap (cdr x)
                                   (acons (vl-portdecl->loc (car x)) str alist)
                                   ps))))

(defthm vl-commentmap-p-of-vl-portdecllist-ppmap
  (implies (and (force (vl-portdecllist-p x))
                (force (vl-commentmap-p alist))
                (force (vl-pstate-p ps)))
           (vl-commentmap-p (mv-nth 0 (vl-portdecllist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-portdecllist-ppmap))))

(defthm vl-pstate-p-of-vl-portdecllist-ppmap
  (implies (and (force (vl-portdecllist-p x))
                (force (vl-pstate-p ps)))
           (vl-pstate-p (mv-nth 1 (vl-portdecllist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-portdecllist-ppmap))))



(defund vl-assignlist-ppmap (x alist ps)
  (declare (xargs :guard (and (vl-assignlist-p x)
                              (vl-commentmap-p alist)
                              (vl-pstate-p ps))
                  :stobjs ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
            (with-semilocal-ps (vl-pp-assign (car x)))
            (vl-assignlist-ppmap (cdr x)
                                 (acons (vl-assign->loc (car x)) str alist)
                                 ps))))

(defthm vl-commentmap-p-of-vl-assignlist-ppmap
  (implies (and (force (vl-assignlist-p x))
                (force (vl-commentmap-p alist))
                (force (vl-pstate-p ps)))
           (vl-commentmap-p (mv-nth 0 (vl-assignlist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-assignlist-ppmap))))

(defthm vl-pstate-p-of-vl-assignlist-ppmap
  (implies (and (force (vl-assignlist-p x))
                (force (vl-pstate-p ps)))
           (vl-pstate-p (mv-nth 1 (vl-assignlist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-assignlist-ppmap))))



(defund vl-netdecllist-ppmap (x alist ps)
  (declare (xargs :guard (and (vl-netdecllist-p x)
                              (vl-commentmap-p alist)
                              (vl-pstate-p ps))
                  :stobjs ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
            (with-semilocal-ps (vl-pp-netdecl (car x)))
            (vl-netdecllist-ppmap (cdr x)
                                  (acons (vl-netdecl->loc (car x)) str alist)
                                  ps))))

(defthm vl-commentmap-p-of-vl-netdecllist-ppmap
  (implies (and (force (vl-netdecllist-p x))
                (force (vl-commentmap-p alist))
                (force (vl-pstate-p ps)))
           (vl-commentmap-p (mv-nth 0 (vl-netdecllist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-netdecllist-ppmap))))

(defthm vl-pstate-p-of-vl-netdecllist-ppmap
  (implies (and (force (vl-netdecllist-p x))
                (force (vl-pstate-p ps)))
           (vl-pstate-p (mv-nth 1 (vl-netdecllist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-netdecllist-ppmap))))




(defund vl-regdecllist-ppmap (x alist ps)
  (declare (xargs :guard (and (vl-regdecllist-p x)
                              (vl-commentmap-p alist)
                              (vl-pstate-p ps))
                  :stobjs ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
            (with-semilocal-ps (vl-pp-regdecl (car x)))
            (vl-regdecllist-ppmap (cdr x)
                                  (acons (vl-regdecl->loc (car x)) str alist)
                                  ps))))

(defthm vl-commentmap-p-of-vl-regdecllist-ppmap
  (implies (and (force (vl-regdecllist-p x))
                (force (vl-commentmap-p alist))
                (force (vl-pstate-p ps)))
           (vl-commentmap-p (mv-nth 0 (vl-regdecllist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-regdecllist-ppmap))))

(defthm vl-pstate-p-of-vl-regdecllist-ppmap
  (implies (and (force (vl-regdecllist-p x))
                (force (vl-pstate-p ps)))
           (vl-pstate-p (mv-nth 1 (vl-regdecllist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-regdecllist-ppmap))))



(defund vl-vardecllist-ppmap (x alist ps)
  (declare (xargs :guard (and (vl-vardecllist-p x)
                              (vl-commentmap-p alist)
                              (vl-pstate-p ps))
                  :stobjs ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
            (with-semilocal-ps (vl-pp-vardecl (car x)))
            (vl-vardecllist-ppmap (cdr x)
                                  (acons (vl-vardecl->loc (car x)) str alist)
                                  ps))))

(defthm vl-commentmap-p-of-vl-vardecllist-ppmap
  (implies (and (force (vl-vardecllist-p x))
                (force (vl-commentmap-p alist))
                (force (vl-pstate-p ps)))
           (vl-commentmap-p (mv-nth 0 (vl-vardecllist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-vardecllist-ppmap))))

(defthm vl-pstate-p-of-vl-vardecllist-ppmap
  (implies (and (force (vl-vardecllist-p x))
                (force (vl-pstate-p ps)))
           (vl-pstate-p (mv-nth 1 (vl-vardecllist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-vardecllist-ppmap))))




(defund vl-modinstlist-ppmap (x mods modalist alist ps)
  (declare (xargs :guard (and (vl-modinstlist-p x)
                              (vl-modulelist-p mods)
                              (equal modalist (vl-modalist mods))
                              (vl-commentmap-p alist)
                              (vl-pstate-p ps))
                  :stobjs ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
            (with-semilocal-ps (vl-pp-modinst (car x) mods modalist))
            (vl-modinstlist-ppmap (cdr x) mods modalist
                                  (acons (vl-modinst->loc (car x)) str alist)
                                  ps))))

(defthm vl-commentmap-p-of-vl-modinstlist-ppmap
  (implies (and (force (vl-modinstlist-p x))
                (force (vl-modulelist-p mods))
                (force (equal modalist (vl-modalist mods)))
                (force (vl-commentmap-p alist))
                (force (vl-pstate-p ps)))
           (vl-commentmap-p (mv-nth 0 (vl-modinstlist-ppmap x mods modalist alist ps))))
  :hints(("Goal" :in-theory (enable vl-modinstlist-ppmap))))

(defthm vl-pstate-p-of-vl-modinstlist-ppmap
  (implies (and (force (vl-modinstlist-p x))
                (force (vl-pstate-p ps))
                (force (vl-modulelist-p mods))
                (force (equal modalist (vl-modalist mods))))
           (vl-pstate-p (mv-nth 1 (vl-modinstlist-ppmap x mods modalist alist ps))))
  :hints(("Goal" :in-theory (enable vl-modinstlist-ppmap))))



(defund vl-gateinstlist-ppmap (x alist ps)
  (declare (xargs :guard (and (vl-gateinstlist-p x)
                              (vl-commentmap-p alist)
                              (vl-pstate-p ps))
                  :stobjs ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
            (with-semilocal-ps (vl-pp-gateinst (car x)))
            (vl-gateinstlist-ppmap (cdr x)
                                   (acons (vl-gateinst->loc (car x)) str alist)
                                   ps))))

(defthm vl-commentmap-p-of-vl-gateinstlist-ppmap
  (implies (and (force (vl-gateinstlist-p x))
                (force (vl-commentmap-p alist))
                (force (vl-pstate-p ps)))
           (vl-commentmap-p (mv-nth 0 (vl-gateinstlist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-gateinstlist-ppmap))))

(defthm vl-pstate-p-of-vl-gateinstlist-ppmap
  (implies (and (force (vl-gateinstlist-p x))
                (force (vl-pstate-p ps)))
           (vl-pstate-p (mv-nth 1 (vl-gateinstlist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-gateinstlist-ppmap))))




(defund vl-alwayslist-ppmap (x alist ps)
  (declare (xargs :guard (and (vl-alwayslist-p x)
                              (vl-commentmap-p alist)
                              (vl-pstate-p ps))
                  :stobjs ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
            (with-semilocal-ps (vl-pp-always (car x)))
            (vl-alwayslist-ppmap (cdr x)
                                 (acons (vl-always->loc (car x)) str alist)
                                 ps))))

(defthm vl-commentmap-p-of-vl-alwayslist-ppmap
  (implies (and (force (vl-alwayslist-p x))
                (force (vl-commentmap-p alist))
                (force (vl-pstate-p ps)))
           (vl-commentmap-p (mv-nth 0 (vl-alwayslist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-alwayslist-ppmap))))

(defthm vl-pstate-p-of-vl-alwayslist-ppmap
  (implies (and (force (vl-alwayslist-p x))
                (force (vl-pstate-p ps)))
           (vl-pstate-p (mv-nth 1 (vl-alwayslist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-alwayslist-ppmap))))




(defund vl-initiallist-ppmap (x alist ps)
  (declare (xargs :guard (and (vl-initiallist-p x)
                              (vl-commentmap-p alist)
                              (vl-pstate-p ps))
                  :stobjs ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
            (with-semilocal-ps (vl-pp-initial (car x)))
            (vl-initiallist-ppmap (cdr x)
                                  (acons (vl-initial->loc (car x)) str alist)
                                  ps))))

(defthm vl-commentmap-p-of-vl-initiallist-ppmap
  (implies (and (force (vl-initiallist-p x))
                (force (vl-commentmap-p alist))
                (force (vl-pstate-p ps)))
           (vl-commentmap-p (mv-nth 0 (vl-initiallist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-initiallist-ppmap))))

(defthm vl-pstate-p-of-vl-initiallist-ppmap
  (implies (and (force (vl-initiallist-p x))
                (force (vl-pstate-p ps)))
           (vl-pstate-p (mv-nth 1 (vl-initiallist-ppmap x alist ps))))
  :hints(("Goal" :in-theory (enable vl-initiallist-ppmap))))




(defund vl-html-encode-commentmap (x tabsize)
  (declare (xargs :guard (and (vl-commentmap-p x)
                              (posp tabsize))))
  ; BOZO inefficient, potentially bad!
  (if (atom x)
      nil
    (let* ((str    (cdar x))
           (len    (length str))
           (blockp (and (< 2 len) (eql (char str 1) #\*))))
      (acons (caar x)
             (str::cat "<span class=\"vl_cmt\">"
                       (vl-html-encode-string (cdar x) tabsize)
                       "</span>"
                       (if blockp
                           (coerce '(#\Newline) 'string)
                         ""))
             (vl-html-encode-commentmap (cdr x) tabsize)))))

(defthm vl-commentmap-p-of-vl-html-encode-commentmap
  (implies (force (vl-commentmap-p x))
           (vl-commentmap-p (vl-html-encode-commentmap x tabsize)))
  :hints(("Goal" :in-theory (enable vl-html-encode-commentmap))))



(defpp vl-pp-encoded-commentmap (x)

; The use of vl-print-markup throughout this function is somewhat subtle.  When
; we prepare the module items for printing by calling our regular functions, we
; end up with comment map entries whose values may contain HTML code, e.g.,
; color codes, etc.  So, we do not want to print these entries with vl-print,
; but instead we want to be sure to use vl-print-markup to avoid any
; re-encoding of the encoding.

  :guard (vl-commentmap-p x)
  :body  (cond ((atom x)
                ps)
               ((atom (cdr x))
                (vl-print-markup (cdr (first x))))
               ((atom (cddr x))
                (vl-ps-seq (vl-print-markup (cdr (first x)))
                           (vl-print-markup (cdr (second x)))))
               (t
                (let ((first  (first x))
                      (second (second x))
                      (third  (third x)))
                  (if (and (equal (car first) (car second))
                           (not (equal (car first) (car third))))
                      ;; To make our output nicer, we insert a newline if there
                      ;; are multiple elements at the same location after
                      ;; printing those elements.
                      (vl-ps-seq (vl-print-markup (cdr (first x)))
                                 (vl-print-markup (cdr (second x)))
                                 (vl-println "")
                                 (vl-pp-encoded-commentmap (cddr x)))
                    ;; Otherwise, first and second are unrelated or part of the
                    ;; same group as third, so don't insert a newline.
                    (vl-ps-seq (vl-print-markup (cdr (first x)))
                               (vl-pp-encoded-commentmap (cdr x))))))))

(defpp vl-ppc-module (x mods modalist)

; Pretty-print a module, with comments.

  :guard (and (vl-module-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods)))

  :body  (b* ((name       (vl-module->name x))
              (ports      (vl-module->ports x))
              (portdecls  (vl-module->portdecls x))
              (assigns    (vl-module->assigns x))
              (netdecls   (vl-module->netdecls x))
              (vardecls   (vl-module->vardecls x))
              (regdecls   (vl-module->regdecls x))
              (eventdecls (vl-module->eventdecls x))
              (paramdecls (vl-module->paramdecls x))
              (modinsts   (vl-module->modinsts x))
              (gateinsts  (vl-module->gateinsts x))
              (alwayses   (vl-module->alwayses x))
              (initials   (vl-module->initials x))
              (atts       (vl-module->atts x))
              (comments   (vl-module->comments x))

; We begin by assembling a (location . string) map of all the module items.
; For efficiency, our ppmap functions destroy the current contents of the
; printer's state, so we are going to go ahead and save them before we generate
; the ppmap.

              (rchars (vl-ps->rchars))
              (col    (vl-ps->col))
              (ps     (vl-pp-set-portnames portdecls))

              (imap nil)
              ((mv imap ps) (vl-portdecllist-ppmap portdecls imap ps))
              ((mv imap ps) (vl-regdecllist-ppmap regdecls imap ps))
              ((mv imap ps) (vl-vardecllist-ppmap vardecls imap ps))
              ((mv imap ps) (vl-netdecllist-ppmap netdecls imap ps))
              ((mv imap ps) (vl-assignlist-ppmap assigns imap ps))
              ((mv imap ps) (vl-modinstlist-ppmap modinsts mods modalist imap ps))
              ((mv imap ps) (vl-gateinstlist-ppmap gateinsts imap ps))
              ((mv imap ps) (vl-alwayslist-ppmap alwayses imap ps))
              ((mv imap ps) (vl-initiallist-ppmap initials imap ps))
              (ps (if (not eventdecls)
                      ps
                    (vl-println "// BOZO implement eventdecl printing")))
              (ps (if (not paramdecls)
                      ps
                    (vl-println "// BOZO Implement paramdecl printing")))

; Now that we are done generating the ppmap, we can restore the rchars and col
; from the pstate.  This whole approach is nothing more than a trick to avoid
; having to create new vl-pstate objects and reconfigure them for each module
; item.

              (ps   (vl-ps-update-rchars rchars))
              (ps   (vl-ps-update-col col))

; With the map of all module items in hand, we add in the comment map and sort
; by location order.  Why are we reversing the imap when we're going to sort it
; anyway?  I think the answer is that since our sort is stable, we want to have
; the printed elements in the proper order.

              (imap     (reverse imap))
              (comments (if (vl-ps->htmlp)
                            (vl-html-encode-commentmap comments (vl-ps->tabsize))
                          comments))
              (guts     (cwtime (vl-commentmap-entry-sort (append comments imap))
                                :mintime 1/2
                                :name vl-commentmap-entry-sort)))

             (vl-ps-seq (vl-when-html (vl-println-markup "<div class=\"vl_src\">"))
                        (vl-pp-atts atts)
                        (vl-ps-span "vl_key" (vl-print "module "))
                        (vl-print-modname name)
                        (vl-print " (")
                        (vl-pp-portlist ports)
                        (vl-println ");")
                        (vl-pp-encoded-commentmap guts)
                        (vl-ps-span "vl_key" (vl-println "endmodule"))
                        (vl-println "")
                        (vl-when-html (vl-println-markup "</div>")))))

(defpp vl-ppc-modulelist (x mods modalist)
  :guard (and (vl-modulelist-p x)
              (vl-modulelist-p mods)
              (equal modalist (vl-modalist mods)))
  :body (if (consp x)
            (vl-ps-seq (vl-ppc-module (car x) mods modalist)
                       (vl-ppc-modulelist (cdr x) mods modalist))
          ps))

(defund vl-ppcs-module (x)
  (declare (xargs :guard (vl-module-p x)))
  (with-local-ps (vl-ppc-module x nil nil)))

(defund vl-ppcs-modulelist (x)
  (declare (xargs :guard (vl-modulelist-p x)))
  (with-local-ps (vl-ppc-modulelist x nil nil)))



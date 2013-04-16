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

(defthm alistp-when-vl-commentmap-p
  (implies (vl-commentmap-p x)
           (alistp x))
  :hints(("Goal" :induct (len x))))


(defmacro with-semilocal-ps (&rest args)

; To generate the PPMAP, we could use with-local-ps to print each module item
; in a local pstate.  But to avoid the overhead of creating and reconfiguring
; many ps objects, we instead just pass in the pstate to use but clear its
; rchars and column before printing each module item.  This is just a dumb hack
; to allow us to configure the pstate once, then never worry about its
; configuration again.

  `(let ((ps (vl-ps-seq
              (vl-ps-update-rchars nil)
              (vl-ps-update-col 0)
              ,@args)))
     (mv (vl-ps->string) ps)))

(define vl-portdecllist-ppmap ((x     vl-portdecllist-p)
                               (alist vl-commentmap-p)
                               &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-portdecllist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-portdecl (car x)))
      (vl-portdecllist-ppmap (cdr x)
                             (acons (vl-portdecl->loc (car x)) str alist)))))

(define vl-assignlist-ppmap ((x     vl-assignlist-p)
                             (alist vl-commentmap-p)
                             &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-assignlist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-assign (car x)))
      (vl-assignlist-ppmap (cdr x)
                           (acons (vl-assign->loc (car x)) str alist)))))

(define vl-netdecllist-ppmap ((x     vl-netdecllist-p)
                              (alist vl-commentmap-p)
                              &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-netdecllist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-netdecl (car x)))
      (vl-netdecllist-ppmap (cdr x)
                            (acons (vl-netdecl->loc (car x)) str alist)))))

(define vl-regdecllist-ppmap ((x     vl-regdecllist-p)
                              (alist vl-commentmap-p)
                              &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-regdecllist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-regdecl (car x)))
      (vl-regdecllist-ppmap (cdr x)
                            (acons (vl-regdecl->loc (car x)) str alist)))))

(define vl-vardecllist-ppmap ((x     vl-vardecllist-p)
                              (alist vl-commentmap-p)
                              &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-vardecllist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-vardecl (car x)))
      (vl-vardecllist-ppmap (cdr x)
                            (acons (vl-vardecl->loc (car x)) str alist)))))

(define vl-modinstlist-ppmap ((x        vl-modinstlist-p)
                              (mods     vl-modulelist-p)
                              (modalist (equal modalist (vl-modalist mods)))
                              (alist    vl-commentmap-p)
                              &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-modinstlist-p x))
                                (force (vl-modulelist-p mods))
                                (force (equal modalist (vl-modalist mods)))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-modinst (car x) mods modalist))
      (vl-modinstlist-ppmap (cdr x) mods modalist
                            (acons (vl-modinst->loc (car x)) str alist)))))

(define vl-gateinstlist-ppmap ((x     vl-gateinstlist-p)
                               (alist vl-commentmap-p)
                               &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-gateinstlist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-gateinst (car x)))
      (vl-gateinstlist-ppmap (cdr x)
                             (acons (vl-gateinst->loc (car x)) str alist)))))

(define vl-alwayslist-ppmap ((x     vl-alwayslist-p)
                             (alist vl-commentmap-p)
                             &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-alwayslist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-always (car x)))
      (vl-alwayslist-ppmap (cdr x)
                           (acons (vl-always->loc (car x)) str alist)))))

(define vl-initiallist-ppmap ((x     vl-initiallist-p)
                              (alist vl-commentmap-p)
                              &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-initiallist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-initial (car x)))
      (vl-initiallist-ppmap (cdr x)
                            (acons (vl-initial->loc (car x)) str alist)))))

(define vl-paramdecllist-ppmap ((x     vl-paramdecllist-p)
                                (alist vl-commentmap-p)
                                &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-paramdecllist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-paramdecl (car x)))
      (vl-paramdecllist-ppmap (cdr x)
                              (acons (vl-paramdecl->loc (car x)) str alist)))))

(define vl-fundecllist-ppmap ((x     vl-fundecllist-p)
                              (alist vl-commentmap-p)
                              &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-fundecllist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-fundecl (car x)))
      (vl-fundecllist-ppmap (cdr x)
                            (acons (vl-fundecl->loc (car x)) str alist)))))

(define vl-taskdecllist-ppmap ((x     vl-taskdecllist-p)
                               (alist vl-commentmap-p)
                               &key (ps 'ps))
  :returns (mv (alist vl-commentmap-p
                      :hyp (and (force (vl-taskdecllist-p x))
                                (force (vl-commentmap-p alist))))
               (ps))
  (if (atom x)
      (mv alist ps)
    (mv-let (str ps)
      (with-semilocal-ps (vl-pp-taskdecl (car x)))
      (vl-taskdecllist-ppmap (cdr x)
                             (acons (vl-taskdecl->loc (car x)) str alist)))))

(define vl-add-newlines-after-block-comments ((x vl-commentmap-p))
  :returns (new-x vl-commentmap-p :hyp :fguard)
  (b* (((when (atom x))
        nil)
       (loc1 (caar x))
       (str1 (cdar x))
       ((when (and (> (length str1) 2)
                   (eql (char str1 1) #\*)))
        (cons (cons loc1 (cat str1 *nls*))
              (vl-add-newlines-after-block-comments (cdr x)))))
    (cons (car x)
          (vl-add-newlines-after-block-comments (cdr x)))))

(define vl-html-encode-commentmap ((x vl-commentmap-p)
                                   (tabsize posp))
  :returns (new-x vl-commentmap-p :hyp (force (vl-commentmap-p x)))
  ;; BOZO inefficient, potentially bad!
  (b* (((when (atom x))
        nil)
       (loc1 (caar x))
       (str1 (cdar x)))
    (cons (cons loc1
                (cat "<span class=\"vl_cmt\">"
                     (vl-html-encode-string str1 tabsize)
                     "</span>"))
          (vl-html-encode-commentmap (cdr x) tabsize))))

(define vl-pp-encoded-commentmap ((x vl-commentmap-p) &key (ps 'ps))

; The use of vl-print-markup throughout this function is somewhat subtle.  When
; we prepare the module items for printing by calling our regular functions, we
; end up with comment map entries whose values may contain HTML code, e.g.,
; color codes, etc.  So, we do not want to print these entries with vl-print,
; but instead we want to be sure to use vl-print-markup to avoid any
; re-encoding of the encoding.

  (cond ((atom x)
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
               ;; To make our output nicer, we insert a newline if there are
               ;; multiple elements at the same location after printing those
               ;; elements.
               (vl-ps-seq (vl-print-markup (cdr (first x)))
                          (vl-print-markup (cdr (second x)))
                          (vl-println "")
                          (vl-pp-encoded-commentmap (cddr x)))
             ;; Otherwise, first and second are unrelated or part of the same
             ;; group as third, so don't insert a newline.
             (vl-ps-seq (vl-print-markup (cdr (first x)))
                        (vl-pp-encoded-commentmap (cdr x))))))))

(define vl-make-item-map-for-ppc-module
  ((x        vl-module-p)
   (mods     vl-modulelist-p)
   (modalist (equal modalist (vl-modalist mods)))
   &key (ps 'ps))
  :returns (mv (map vl-commentmap-p
                    :hyp (and (force (vl-module-p x))
                              (force (vl-modulelist-p mods))
                              (force (equal modalist (vl-modalist mods)))))
               (ps))
  :parents (vl-ppc-module)
  :short "Build a commentmap that has the encoded items for a module."
  (b* (((vl-module x) x)

       ;; For efficiency, our ppmap functions destroy the current contents of
       ;; the printer's state, so we are going to go ahead and save them before
       ;; we generate the ppmap.
       (rchars (vl-ps->rchars))
       (col    (vl-ps->col))
       (misc   (vl-ps->misc))

       (ps     (vl-pp-set-portnames x.portdecls)) ;; modifies ps->misc

       (imap nil)

       ;; Note: portdecls need to come before netdecls, so that after stable
       ;; sorting any implicit portdecls are still listed before their
       ;; correspondign netdecl; Verilog-XL won't tolerate it the other way;
       ;; see make-implicit-wires for more details.  The netdecls should come
       ;; before any instances/assignments, so that things are declared before
       ;; use.
       ((mv imap ps) (vl-paramdecllist-ppmap x.paramdecls imap))
       ((mv imap ps) (vl-portdecllist-ppmap x.portdecls imap))
       ((mv imap ps) (vl-regdecllist-ppmap x.regdecls imap))
       ((mv imap ps) (vl-vardecllist-ppmap x.vardecls imap))
       ((mv imap ps) (vl-netdecllist-ppmap x.netdecls imap))
       ((mv imap ps) (vl-fundecllist-ppmap x.fundecls imap))
       ((mv imap ps) (vl-taskdecllist-ppmap x.taskdecls imap))
       ((mv imap ps) (vl-assignlist-ppmap x.assigns imap))
       ((mv imap ps) (vl-modinstlist-ppmap x.modinsts mods modalist imap))
       ((mv imap ps) (vl-gateinstlist-ppmap x.gateinsts imap))
       ((mv imap ps) (vl-alwayslist-ppmap x.alwayses imap))
       ((mv imap ps) (vl-initiallist-ppmap x.initials imap))

       ;; Why are we reversing the imap when we're going to sort it anyway?  I
       ;; think the answer is that some module elements may share a location,
       ;; and since our sort is stable we want to preserve their original order
       ;; in the lists above, if possible.
       (imap (reverse imap))

       ;; Now that we are done generating the ppmap, restore the previous state
       ;; of the ps.
       (ps   (vl-ps-update-rchars rchars))
       (ps   (vl-ps-update-col col))
       (ps   (vl-ps-update-misc misc)))
    (mv imap ps)))

(define vl-ppc-module ((x        vl-module-p)
                       (mods     vl-modulelist-p)
                       (modalist (equal modalist (vl-modalist mods)))
                       &key (ps 'ps))
  :parents (verilog-printing vl-module-p)
  :short "Pretty print a module with comments to @(see ps)."

  :long "<p>@(call vl-ppc-module) extends @(see ps) with a pretty-printed
representation of the module @('x').</p>

<p>For interactive use you may prefer @(see vl-ppcs-module) which writes
to a string instead of @(see ps).</p>

<p>The @('mods') here should be the list of all modules and @('modalist') is
its @(see vl-modalist); these arguments are only needed for hyperlinking to
submodules in HTML mode.</p>"

  (b* (((vl-module x) x)

       ;; The item map binds module item locations to their printed
       ;; representations.
       ((mv imap ps) (vl-make-item-map-for-ppc-module x mods modalist))

       (comments (vl-add-newlines-after-block-comments x.comments))
       (comments (if (vl-ps->htmlp)
                     (vl-html-encode-commentmap comments (vl-ps->tabsize))
                   comments))
       (guts     (cwtime (vl-commentmap-entry-sort (append comments imap))
                         :mintime 1/2
                         :name vl-commentmap-entry-sort)))

    (vl-ps-seq (vl-when-html (vl-println-markup "<div class=\"vl_src\">"))
               (vl-pp-atts x.atts)
               (vl-ps-span "vl_key" (vl-print "module "))
               (vl-print-modname x.name)
               (vl-print " (")
               (vl-pp-portlist x.ports)
               (vl-println ");")

               (if (not x.eventdecls)
                   ps
                 (vl-println "// BOZO implement eventdecl printing"))

               (vl-pp-encoded-commentmap guts)
               (vl-ps-span "vl_key" (vl-println "endmodule"))
               (vl-println "")
               (vl-when-html (vl-println-markup "</div>")))))

(define vl-ppc-modulelist ((x        vl-modulelist-p)
                           (mods     vl-modulelist-p)
                           (modalist (equal modalist (vl-modalist mods)))
                           &key (ps 'ps))
  :parents (verilog-printing)
  :short "Pretty print a list of modules with comments to @(see ps)."
  :long "<p>This just calls @(see vl-ppc-module) on each module.</p>"
  (if (atom x)
      ps
    (vl-ps-seq (vl-ppc-module (car x) mods modalist)
               (vl-ppc-modulelist (cdr x) mods modalist))))

(define vl-ppcs-module ((x vl-module-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (verilog-printing vl-module-p)
  :short "Pretty-print a module with comments to a plain-text string."
  :long "<p>@(call vl-ppcs-module) pretty-prints the @(see vl-module-p) @('x')
into a plain-text string.  See also @(see vl-ppc-module).</p>"
  (with-local-ps (vl-ppc-module x nil nil)))

(define vl-ppcs-modulelist ((x vl-modulelist-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (verilog-printing)
  :short "Pretty-print a list of modules with comments to a plain-text string."
  :long "<p>See also @(see vl-ppc-modulelist).</p>"
  (with-local-ps (vl-ppc-modulelist x nil nil)))



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
(include-book "../util/cwtime")
(local (include-book "../util/arithmetic"))
(local (std::add-default-post-define-hook :fix))


; Pretty-Printing Modules with Comments
;
; Our ordinary pretty-printing functions only print out the parse-tree part of
; a module.  We now write our main routine for merging the comments back in and
; printing the module back out in a reasonable order.
;
; Recall that:
;  - The comment map is an alist of (location . string) pairs.
;  - Meanwhile, each module item has a location
;
; The basic way we're going to do this is:
;   - Pretty-print each kind of module item into a string
;   - Associate the location of each module item with its pretty-printed string
;     (the result looks like a comment map!)
;   - Merge the resulting module element map with the actual comment map
;     (this is just ordinary comment-map sorting)
;
; The result is a location-sorted mixed list with module elements (already
; printed) and the comments interspersed in the right places.  Merging the
; strings gives us a pretty-printed version of the module with the comments
; injected in.

(defsection vl-commentmap-entry-sort
  :parents (vl-commentmap-p)
  :short "A basic sort for comment maps."

  :long "<p>Our pretty-printer uses the following routine in a funny way to get
the comments put inline with the module elements.</p>

<p>The sort is introduced with defsort, so it is a stable mergesort.  Note that
we ignore file names.</p>"

  (defund vl-commentmap-entry-p (x)
    (declare (xargs :guard t))
    (and (consp x)
         (vl-location-p (car x))
         (stringp (cdr x))))

  (defund vl-commentmap-entry-< (x y)
    (declare (xargs :guard (and (vl-commentmap-entry-p x)
                                (vl-commentmap-entry-p y))
                    :guard-hints (("Goal" :in-theory (enable vl-commentmap-entry-p)))))
    (let ((line-x (vl-location->line (car x)))
          (line-y (vl-location->line (car y))))
      (or (< line-x line-y)
          (and (= line-x line-y)
               (< (vl-location->col (car x))
                  (vl-location->col (car y)))))))

  (defthm transitivity-of-vl-commentmap-entry-<
    (implies (and (vl-commentmap-entry-< x y)
                  (vl-commentmap-entry-< y z))
             (vl-commentmap-entry-< x z))
    :hints(("Goal" :in-theory (enable vl-commentmap-entry-<))))

  (ACL2::defsort :comparablep vl-commentmap-entry-p
                 :compare< vl-commentmap-entry-<
                 :prefix vl-commentmap-entry)

  (defthm vl-commentmap-entry-list-p-elim
    (equal (vl-commentmap-entry-list-p x)
           (vl-commentmap-p (list-fix x)))
    :hints(("Goal"
            :in-theory (enable vl-commentmap-entry-p
                               vl-commentmap-entry-list-p))))

  (defthm vl-commentmap-p-of-vl-commentmap-entry-sort
    (implies (vl-commentmap-p x)
             (vl-commentmap-p (vl-commentmap-entry-sort x)))
    :hints(("goal" :use ((:instance vl-commentmap-entry-sort-creates-comparable-listp
                                    (acl2::x x)))))))


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

(defmacro def-vl-ppmap (&key list elem)
  (b* ((mksym-package-symbol (pkg-witness "VL"))
       (fn        (mksym 'vl- list '-ppmap))
       (list-p    (mksym 'vl- list '-p))
       (pp-elem   (mksym 'vl-pp- elem))
       (elem->loc (mksym 'vl- elem '->loc)))
    `(define ,fn ((x        ,list-p)
                  (item-map vl-commentmap-p)
                  &key (ps 'ps))
       :returns (mv (item-map vl-commentmap-p) ps)
       :verbosep t
       (b* (((when (atom x))
             (mv (vl-commentmap-fix item-map) ps))
            ((mv str ps)
             (with-semilocal-ps (,pp-elem (car x))))
            (item-map (cons (cons (,elem->loc (car x)) str) item-map)))
         (,fn (cdr x) item-map)))))

(def-vl-ppmap :list portdecllist :elem portdecl)
(def-vl-ppmap :list assignlist :elem assign)
(def-vl-ppmap :list vardecllist :elem vardecl)
(def-vl-ppmap :list gateinstlist :elem gateinst)
(def-vl-ppmap :list alwayslist :elem always)
(def-vl-ppmap :list initiallist :elem initial)
(def-vl-ppmap :list finallist :elem final)
(def-vl-ppmap :list paramdecllist :elem paramdecl)
(def-vl-ppmap :list fundecllist :elem fundecl)
(def-vl-ppmap :list taskdecllist :elem taskdecl)
(def-vl-ppmap :list modportlist :elem modport)
(def-vl-ppmap :list typedeflist :elem typedef)
(def-vl-ppmap :list propertylist :elem property)
(def-vl-ppmap :list sequencelist :elem sequence)
(def-vl-ppmap :list assertionlist :elem assertion)
(def-vl-ppmap :list cassertionlist :elem cassertion)


(local (defthm vl-genelementlist-fix-when-atom
         ;; bozo ??? why do we need this?
         (implies (atom x)
                  (equal (vl-genelementlist-fix x)
                         nil))))

(def-vl-ppmap :list genelementlist :elem genelement)


;; This one's a bit different because it takes a scopestack
(define vl-modinstlist-ppmap ((x  vl-modinstlist-p)
                              (ss vl-scopestack-p)
                              (item-map vl-commentmap-p)
                              &key (ps 'ps))
  :returns (mv (item-map vl-commentmap-p) ps)
  (b* (((when (atom x))
        (mv (vl-commentmap-fix item-map) ps))
       ((mv str ps)
        (with-semilocal-ps (vl-pp-modinst (car x) ss)))
       (item-map (cons (cons (vl-modinst->loc (car x)) str) item-map)))
    (vl-modinstlist-ppmap (cdr x) ss item-map)))

(define vl-add-newlines-after-block-comments ((x vl-commentmap-p))
  :returns (new-x vl-commentmap-p :hyp :fguard)
  :hooks nil
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
  :hooks nil
  ;; BOZO inefficient, potentially bad!
  (b* (((when (atom x))
        nil)
       (loc1 (caar x))
       (str1 (cdar x)))
    (cons (cons loc1
                (cat "<span class=\"vl_cmt\">"
                     (str::html-encode-string str1 tabsize)
                     "</span>"))
          (vl-html-encode-commentmap (cdr x) tabsize))))

(define vl-remove-empty-commentmap-entries-exec ((x vl-commentmap-p)
                                                 (nrev))
  :measure (len (vl-commentmap-fix x))
  (b* ((x (vl-commentmap-fix x))
       ((when (atom x))
        (nrev-fix nrev))
       ((cons ?loc guts) (car x))
       ((when (equal guts ""))
        (vl-remove-empty-commentmap-entries-exec (cdr x) nrev))
       (nrev (nrev-push (car x) nrev)))
    (vl-remove-empty-commentmap-entries-exec (cdr x) nrev)))

(define vl-remove-empty-commentmap-entries ((x vl-commentmap-p))
  ;; Removing empty entries helps with the newline insertion stuff below,
  ;; especially in the case of port declarations where we sometimes don't print
  ;; a net declaration because it's got a corresponding port.
  :returns (new-x vl-commentmap-p)
  :measure (len (vl-commentmap-fix x))
  :verify-guards nil
  (mbe :logic
       (b* ((x (vl-commentmap-fix x))
            ((when (atom x))
             nil)
            ((cons ?loc guts) (car x))
            ((when (equal guts ""))
             (vl-remove-empty-commentmap-entries (cdr x))))
         (cons (car x)
               (vl-remove-empty-commentmap-entries (cdr x))))
       :exec
       (if (atom x)
           nil
         (with-local-nrev
           (vl-remove-empty-commentmap-entries-exec x nrev))))
  ///
  (defthm vl-remove-empty-commentmap-entries-exec-removal
    (equal (vl-remove-empty-commentmap-entries-exec x nrev)
           (append nrev
                   (vl-remove-empty-commentmap-entries x)))
    :hints(("Goal" :in-theory (enable vl-remove-empty-commentmap-entries-exec))))
  (verify-guards vl-remove-empty-commentmap-entries))

(define vl-pp-encoded-commentmap ((x vl-commentmap-p) &key (ps 'ps))

; The use of vl-print-markup throughout this function is somewhat subtle.  When
; we prepare the module items for printing by calling our regular functions, we
; end up with comment map entries whose values may contain HTML code, e.g.,
; color codes, etc.  So, we do not want to print these entries with vl-print,
; but instead we want to be sure to use vl-print-markup to avoid any
; re-encoding of the encoding.
  :hooks nil

  (b* (((when (atom x))
        ps)

       ;; Print item 1.
       (ps (vl-print-markup (cdr (first x))))
       ((when (atom (cdr x)))
        ps)

       ;; Maybe insert a newline between item1 and item2.
       ;;
       ;; The idea here: if the original source code had a gap of more
       ;; than 2 lines, then we will insert an extra gap.  If the
       ;; user's code is on contiguous lines, say:
       ;;
       ;;    wire w1;
       ;;    wire w2;
       ;;
       ;; then we don't want to add an extra newline because they are
       ;; likely grouping up related logic.  But, if the user wrote
       ;; something like:
       ;;
       ;;    wire w1;
       ;;
       ;;    wire w2;
       ;;
       ;; Then they probably had some reason for wanting this gap, so
       ;; we will try to preserve it.
       ((list* first second rest) x)
       ((vl-location loc1) (car first))
       ((vl-location loc2) (car second))
       (ps (if (or (not (equal loc1.filename loc2.filename))
                   (< (+ 1 loc1.line) loc2.line))
               (vl-println "")
             ps))

       ;; If there is no item3, just print item2 and we're done.
       ((when (atom rest))
        (vl-print-markup (cdr second)))

       ;; Maybe insert an extra newline between item2 and item3.
       ;;
       ;; The idea here: If there are multiple elements at the same line, then
       ;; we will insert a newline after printing them.  This causes input
       ;; source like
       ;;
       ;;    wire a, b, c;
       ;;    wire d;
       ;;
       ;; to be printed as a block like:
       ;;
       ;;    wire a;
       ;;    wire b;
       ;;    wire c;
       ;;
       ;;    wire d;
       ;;
       ;; Which at least preserves the sort of major groupings of things.

       (third (car rest))
       (loc3 (car third))
       ((when (and (equal loc1 loc2)
                   (not (equal loc1 loc3))))
        (vl-ps-seq (vl-print-markup (cdr second))
                   (vl-println "")
                   (vl-pp-encoded-commentmap rest))))

    ;; Otherwise, first and second are unrelated or part of the same group as
    ;; third, so don't insert a newline, just print items 2...  as normal.
    (vl-pp-encoded-commentmap (cdr x))))




(define vl-genblob-populate-item-map ((x    vl-genblob-p)
                                      (ss   vl-scopestack-p)
                                      (imap vl-commentmap-p)
                                      &key (ps 'ps))
  :returns (mv (imap vl-commentmap-p)
               ps)
  (b* (((vl-genblob x))

       ;; For efficiency, our ppmap functions destroy the current contents of
       ;; the printer's state, so we are going to go ahead and save them before
       ;; we generate the ppmap.
       (rchars (vl-ps->rchars))
       (col    (vl-ps->col))
       (misc   (vl-ps->misc))

       ;; Note: portdecls need to come before vardecls, so that after stable
       ;; sorting any implicit portdecls are still listed before their
       ;; correspondign vardecl; Verilog-XL won't tolerate it the other way;
       ;; see make-implicit-wires for more details.  The vardecls should come
       ;; before any instances/assignments, so that things are declared before
       ;; use.

       ;; BOZO check this for completeness
       (ps (vl-progindent-block-start))
       ((mv imap ps) (vl-paramdecllist-ppmap x.paramdecls imap))
       ((mv imap ps) (vl-portdecllist-ppmap x.portdecls imap))
       ((mv imap ps) (vl-typedeflist-ppmap x.typedefs imap))
       ((mv imap ps) (vl-vardecllist-ppmap x.vardecls imap))
       ((mv imap ps) (vl-fundecllist-ppmap x.fundecls imap))
       ((mv imap ps) (vl-taskdecllist-ppmap x.taskdecls imap))
       ((mv imap ps) (vl-assignlist-ppmap x.assigns imap))
       ((mv imap ps) (vl-modinstlist-ppmap x.modinsts ss imap))
       ((mv imap ps) (vl-gateinstlist-ppmap x.gateinsts imap))
       ((mv imap ps) (vl-alwayslist-ppmap x.alwayses imap))
       ((mv imap ps) (vl-initiallist-ppmap x.initials imap))
       ((mv imap ps) (vl-finallist-ppmap x.finals imap))
       ((mv imap ps) (vl-propertylist-ppmap x.properties imap))
       ((mv imap ps) (vl-sequencelist-ppmap x.sequences imap))
       ((mv imap ps) (vl-assertionlist-ppmap x.assertions imap))
       ((mv imap ps) (vl-cassertionlist-ppmap x.cassertions imap))
       ((mv imap ps) (vl-modportlist-ppmap x.modports imap))
       ((mv imap ps) (vl-genelementlist-ppmap x.generates imap))
       (ps (vl-progindent-block-end))

       ;; Now that we are done generating the ppmap, restore the previous state
       ;; of the ps.

       (ps (vl-ps-update-rchars rchars))
       (ps (vl-ps-update-col col))
       (ps (vl-ps-update-misc misc)))
    (mv imap ps)))

(define vl-ppc-module ((x  vl-module-p)
                       (ss vl-scopestack-p)
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

  (b* (((vl-module x) (vl-module-fix x))
       (ss (vl-scopestack-push x ss))
       (ps (vl-pp-set-portnames x.portdecls)) ;; modifies ps->misc

       ;; The item map binds module item locations to their printed
       ;; representations.

       (imap nil)
       ((mv imap ps) (vl-genblob-populate-item-map (vl-module->genblob x) ss imap))
       (imap
        ;; Note: why are we reversing the imap when we're going to sort it
        ;; anyway?  I think the answer is that some module elements may share a
        ;; location, and since our sort is stable we want to preserve their
        ;; original order in the lists above, if possible.
        (rev imap))

       (comments (vl-add-newlines-after-block-comments x.comments))
       (comments (if (vl-ps->htmlp)
                     (vl-html-encode-commentmap comments (vl-ps->tabsize))
                   comments))
       (guts     (cwtime (vl-commentmap-entry-sort (append comments imap))
                         :mintime 1/2
                         :name vl-commentmap-entry-sort))
       (guts     (vl-remove-empty-commentmap-entries guts)))

    (vl-ps-seq (vl-when-html (vl-println-markup "<div class=\"vl_src\">"))
               (if x.atts (vl-pp-atts x.atts) ps)
               (vl-ps-span "vl_key" (vl-print "module "))
               (vl-print-modname x.name)
               (vl-print " (")
               (vl-pp-portlist x.ports)
               (vl-println ");")
               (vl-progindent-block (vl-pp-encoded-commentmap guts))
               (vl-ps-span "vl_key" (vl-println "endmodule"))
               (vl-println "")
               (vl-when-html (vl-println-markup "</div>")))))

(define vl-ppc-modulelist ((x  vl-modulelist-p)
                           (ss vl-scopestack-p)
                           &key (ps 'ps))
  :parents (verilog-printing)
  :short "Pretty print a list of modules with comments to @(see ps)."
  :long "<p>This just calls @(see vl-ppc-module) on each module.</p>"
  (if (atom x)
      ps
    (vl-ps-seq (vl-ppc-module (car x) ss)
               (vl-ppc-modulelist (cdr x) ss))))

(define vl-ppcs-module ((x vl-module-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (verilog-printing vl-module-p)
  :short "Pretty-print a module with comments to a plain-text string."
  :long "<p>@(call vl-ppcs-module) pretty-prints the @(see vl-module-p) @('x')
into a plain-text string.  See also @(see vl-ppc-module).</p>"
  (with-local-ps (vl-ppc-module x nil)))

(define vl-ppcs-modulelist ((x vl-modulelist-p))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (verilog-printing)
  :short "Pretty-print a list of modules with comments to a plain-text string."
  :long "<p>See also @(see vl-ppc-modulelist).</p>"
  (with-local-ps (vl-ppc-modulelist x nil)))




(define vl-ppc-interface ((x vl-interface-p) (ss vl-scopestack-p)  &key (ps 'ps))
  (b* (((vl-interface x) (vl-interface-fix x))
       (ss (vl-scopestack-push x ss))
       (ps (vl-pp-set-portnames x.portdecls)) ;; modifies ps->misc

       ;; The item map binds module item locations to their printed
       ;; representations.

       (imap nil)
       ((mv imap ps) (vl-genblob-populate-item-map (vl-interface->genblob x) ss imap))
       (imap
        ;; Note: why are we reversing the imap when we're going to sort it
        ;; anyway?  I think the answer is that some module elements may share a
        ;; location, and since our sort is stable we want to preserve their
        ;; original order in the lists above, if possible.
        (rev imap))

       (comments     (vl-add-newlines-after-block-comments x.comments))
       (comments     (if (vl-ps->htmlp)
                         (vl-html-encode-commentmap comments (vl-ps->tabsize))
                       comments))
       (guts         (cwtime (vl-commentmap-entry-sort (append comments imap))
                             :mintime 1/2
                             :name vl-commentmap-entry-sort)))


    (vl-ps-seq (if x.atts
                   (vl-ps-seq (vl-pp-atts x.atts)
                              (vl-print " "))
                 ps)
               (vl-ps-span "vl_key"
                           (vl-print "interface "))
               (vl-print-modname x.name)
               (vl-print " (")
               (vl-pp-portlist x.ports)
               (vl-println ");")
               (vl-pp-encoded-commentmap guts)
               (vl-ps-span "vl_key" (vl-println "endinterface"))
               (vl-println ""))))

(define vl-ppc-interfacelist ((x vl-interfacelist-p) (ss vl-scopestack-p) &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq (vl-ppc-interface (car x) ss)
               (vl-ppc-interfacelist (cdr x) ss))))

(define vl-ppc-package ((x vl-package-p) (ss vl-scopestack-p) &key (ps 'ps))
  (b* (((vl-package x) (vl-package-fix x))
       (ss (vl-scopestack-push x ss))
       (ps (vl-pp-set-portnames nil))

       (imap nil)
       ((mv imap ps) (vl-genblob-populate-item-map (vl-package->genblob x) ss imap))
       (imap (rev imap))

       (comments     (vl-add-newlines-after-block-comments x.comments))
       (comments     (if (vl-ps->htmlp)
                         (vl-html-encode-commentmap comments (vl-ps->tabsize))
                       comments))
       (guts         (cwtime (vl-commentmap-entry-sort (append comments imap))
                             :mintime 1/2
                             :name vl-commentmap-entry-sort)))
    (vl-ps-seq
     (if x.atts
         (vl-ps-seq (vl-pp-atts x.atts)
                    (vl-print " "))
       ps)
     (vl-ps-span "vl_key"
                 (vl-print "package "))
     (vl-print-modname x.name)
     (vl-println ";")
     (vl-pp-encoded-commentmap guts)
     (vl-println "")
     (vl-ps-span "vl_key" (vl-println "endpackage")))))

(define vl-ppc-program ((x vl-program-p) &key (ps 'ps))
  (b* (((vl-program x)))
    (vl-ps-seq
     (if x.atts
         (vl-ps-seq (vl-pp-atts x.atts)
                    (vl-print " "))
       ps)
     (vl-ps-span "vl_key"
                 (vl-print "program "))
     (vl-print-modname x.name)
     (vl-println "")
     (vl-print "BOZO implement printing of programs!\n")
     (vl-println "")
     (vl-ps-span "vl_key" (vl-println "endprogram")))))

(define vl-ppc-class ((x vl-class-p) &key (ps 'ps))
  (b* (((vl-class x)))
    (vl-ps-seq
     (if x.atts
         (vl-ps-seq (vl-pp-atts x.atts)
                    (vl-print " "))
       ps)
     (if x.virtualp (vl-ps-span "vl_key" (vl-print "virtual ")) ps)
     (vl-ps-span "vl_key"
                 (vl-print "class "))
     (vl-pp-lifetime x.lifetime)
     (vl-print-modname x.name)
     (vl-println "")
     (vl-print "BOZO implement printing of classes!\n")
     (vl-println "")
     (vl-ps-span "vl_key" (vl-println "endclass")))))

(define vl-ppc-config ((x vl-config-p) &key (ps 'ps))
  (b* (((vl-config x)))
    (vl-ps-seq
     (if x.atts
         (vl-ps-seq (vl-pp-atts x.atts)
                    (vl-print " "))
       ps)
     (vl-ps-span "vl_key"
                 (vl-print "config "))
     (vl-print-modname x.name)
     (vl-println "")
     (vl-print "BOZO implement printing of configs!\n")
     (vl-println "")
     (vl-ps-span "vl_key" (vl-println "endconfig")))))


(define vl-ppc-udp ((x vl-udp-p) &key (ps 'ps))
  (b* (((vl-udp x)))
    (vl-ps-seq
     (if x.atts
         (vl-ps-seq (vl-pp-atts x.atts)
                    (vl-print " "))
       ps)
     (vl-ps-span "vl_key"
                 (vl-print "primitive "))
     (vl-print-modname x.name)
     (vl-println "")
     (vl-print "BOZO implement printing of user-defined primitives!\n")
     (vl-println "")
     (vl-ps-span "vl_key" (vl-println "endprimitive")))))

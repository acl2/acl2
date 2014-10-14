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
(include-book "data")
(include-book "describe")
(include-book "porttable")
(include-book "showloc")
(include-book "file-layout")
(include-book "../transforms/xf-annotate-mods")
(include-book "../mlib/comment-writer")
(include-book "std/io/unsound-read" :dir :system)
(include-book "centaur/quicklisp/hunchentoot" :dir :system)
(include-book "centaur/quicklisp/bordeaux" :dir :system)
(include-book "centaur/quicklisp/bt-semaphore" :dir :system)
(include-book "centaur/bridge/to-json" :dir :system)
(include-book "xdoc/defxdoc-raw" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (in-theory (enable tag-reasoning)))
(set-state-ok t)

; cert_param: (ccl-only)

(local (defthm vl-descriptionlist-p-of-alist-vals-when-vl-descalist-p
         (implies (vl-descalist-p x)
                  (vl-descriptionlist-p (alist-vals x)))
         :hints(("Goal" :induct (len x)))))

(local (defthm vl-description-p-of-cdr-of-hons-assoc-equal
         (implies (vl-descalist-p x)
                  (equal (vl-description-p (cdr (hons-assoc-equal name x)))
                         (if (cdr (hons-assoc-equal name x))
                             t
                           nil)))))

(defttag :browser)

(defconsts *browser-dir* (cbd))

(define start (&key (port       maybe-natp)
                    (public-dir maybe-stringp "Path to @('public/') directory."))
  (declare (ignorable port
                      public-dir))
  (raise "Under the hood definition not installed."))

(define stop ()
  (raise "Under the hood definition not installed."))

(define vls-data-from-translation ((trans vl-translation-p))
  :returns (data vls-data-p :hyp :guard)
  :prepwork ((local (in-theory (enable vl-depalist-okp
                                       vl-descalist-okp))))
  (b* (((vl-translation trans) trans)
       (orig           (cwtime (hons-copy (cwtime (vl-annotate-design trans.orig)))))
       (orig-depalist  (fast-alist-free (vl-depalist (vl-design->mods orig))))
       (orig-descalist (fast-alist-free (vl-descalist (vl-design-descriptions orig)))))
    (make-vls-data
     :good           trans.good
     :bad            trans.bad
     :orig           orig
     :orig-depalist  orig-depalist
     :orig-descalist orig-descalist
     :filemap        trans.filemap
     :defs           trans.defines
     :use-set-report trans.useset-report)))

(define vl-find-description-insensitive ((name stringp)
                                         (descalist vl-descalist-p))
  :returns (desc (iff (vl-description-p desc) desc))
  (b* (((when (atom descalist))
        nil)
       ((cons name1 desc1) (car descalist))
       ((when (str::istreqv name name1))
        (vl-description-fix desc1)))
    (vl-find-description-insensitive name (cdr descalist))))

(define vl-ppc-description ((x vl-description-p)
                            (ss vl-scopestack-p)
                            &key (ps 'ps))
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module    (vl-ppc-module    x ss))
      (:vl-udp       (vl-ppc-udp       x))
      (:vl-interface (vl-ppc-interface x))
      (:vl-package   (vl-ppc-package   x))
      (:vl-program   (vl-ppc-program   x))
      (:vl-config    (vl-ppc-config    x))

      ;; items without comments
      (:vl-taskdecl   (vl-pp-taskdecl   x))
      (:vl-fundecl    (vl-pp-fundecl    x))
      (:vl-paramdecl  (vl-pp-paramdecl  x))
      (:vl-import     (vl-pp-import     x))
      (:vl-fwdtypedef (vl-pp-fwdtypedef x))
      (otherwise      (vl-pp-typedef    x)))))

(define vl-description-summary ((x vl-description-p))
  (b* ((type   (tag x))
       (name   (vl-description->name x))
       (minloc (vl-description->minloc x)))
    (list (cons :name name)
          (cons :type type)
          (cons :file (vl-location->filename minloc))
          (cons :line (vl-location->line minloc))
          (cons :col  (vl-location->col minloc)))))

(defprojection vl-descriptionlist-summaries ((x vl-descriptionlist-p))
  (vl-description-summary x))

(define vls-get-summary ((origname stringp     "Special: case insensitive.")
                         (data     vls-data-p))
  (b* (((vls-data data))
       ;; Special: case insensitive to support jump-to box.
       (desc (or (cdr (hons-assoc-equal origname data.orig-descalist))
                 (vl-find-description-insensitive origname data.orig-descalist)))
       ((unless desc)
        nil))
    (vl-description-summary desc)))

(define vls-get-origsrc ((origname stringp)
                         (data     vls-data-p))
  (b* (((vls-data data))
       (desc (cdr (hons-assoc-equal origname data.orig-descalist)))
       ((unless desc)
        (cat "Error: " origname " not found."))

       (ss       (vl-scopestack-init data.orig))
       (ans      (with-local-ps
                   (vl-ps-update-htmlp t)
                   (vl-ppc-description desc ss))))
    ans))

(define vls-get-plainsrc ((origname stringp)
                          (data     vls-data-p))
  (b* (((vls-data data))
       (desc (cdr (hons-assoc-equal origname data.orig-descalist)))
       ((unless desc)
        (cat "Error: " origname " not found."))

       (minloc   (vl-description->minloc desc))
       (maxloc   (vl-description->maxloc desc))

       ;; BOZO this is hideous.  The maxloc points at the start of the
       ;; endmodule keyword, not at the end of it.  Fix it in the worst
       ;; possible way.  Eventually rework vl-string-between-locs to be able to
       ;; just get the next line and not worry about overflows...
       (maxloc   (change-vl-location maxloc
                                     :col (nfix (+ (vl-location->col maxloc)
                                                   (case (tag desc)
                                                     (:vl-module    (length "endmodule"))
                                                     (:vl-udp       (length "endprimitive"))
                                                     (:vl-interface (length "endinterface"))
                                                     (:vl-package   (length "endpackage"))
                                                     (:vl-program   (length "endprogram"))
                                                     (:vl-config    (length "endconfig"))
                                                     (otherwise     0))))))

       (filename (vl-location->filename minloc))
       ((unless (equal filename (vl-location->filename maxloc)))
        (cat "Error: " origname " starts/ends in different files?"))
       (filemap  (vls-data->filemap data))
       (lookup   (hons-assoc-equal filename filemap))
       ((unless lookup)
        (cat "Error: " origname " not found in the filemap."))
       (result (vl-string-between-locs (cdr lookup) minloc maxloc))
       ((unless result)
        (cat "Error: invalid locations for " origname)))
    result))

(define vl-descalist->descriptions/types ((x vl-descalist-p))
  (b* (((when (atom x))
        nil)
       ((cons name description) (car x)))
    (cons (cons name (tag description))
          (vl-descalist->descriptions/types (cdr x)))))

(define vls-data->descriptions/types ((x vls-data-p))
  (vl-descalist->descriptions/types (vls-data->orig-descalist x)))


(define vls-describe ((data     vls-data-p)
                      (origname stringp)
                      (what     stringp))
  (b* (((vls-data data))
       (desc (cdr (hons-assoc-equal origname data.orig-descalist)))
       ((unless desc)
        (cat "<p>Error: " origname " not found.</p>"))
       ((unless (mbe :logic (vl-module-p desc)
                     :exec (eq (tag desc) :vl-module)))
        (cat "<p>BOZO implement describe page for " (ec-call (symbol-name (tag desc))) "</p>")))
    (with-local-ps
      (vl-ps-update-htmlp t)
      (vl-pp-describe what desc))))

(define vls-showloc ((data vls-data-p)
                     (file stringp)
                     (line posp)
                     (col  natp))
  (cwtime
   (b* (((vls-data data))
        (loc      (make-vl-location :filename file :line line :col col))
        (contents (cdr (hons-assoc-equal file data.filemap)))
        ((unless contents) (cat "No filemap binding for " file))
        (desc     (vl-find-description-for-loc loc (alist-vals (vls-data->orig-descalist data))))
        ((unless desc) (cat "No description found for location ~x0."))
        (min (vl-location->line (vl-description->minloc desc)))
        (max (vl-location->line (vl-description->maxloc desc))))
     (with-local-ps
       (vl-ps-seq
        (vl-ps-update-htmlp t)
        (vls-showloc-print contents min max line col))))
   :name vls-showloc))

(define vls-port-table ((data       vls-data-p)
                        (modname    stringp))
  (b* (((vls-data data))
       (look   (cdr (hons-assoc-equal modname data.orig-descalist)))
       ((unless look)
        (cat "Error: no such module " modname))
       ((unless (mbe :logic (vl-module-p look)
                     :exec (eq (tag look) :vl-module)))
        (cat "Error: expected a module but " modname " is a " (ec-call (symbol-name (tag look))))))
    (with-local-ps
      (vl-ps-seq
       (vl-ps-update-htmlp t)
       (vl-pp-porttable look)))))

(define vls-get-parents ((origname stringp     "Should be the name of a module.")
                         (data     vls-data-p))
  (b* (((vls-data data))
       (depalist data.orig-depalist))
    (cdr (hons-assoc-equal origname depalist))))

(define vls-get-children ((origname stringp     "Should be the name of a module.")
                          (data     vls-data-p))
  (b* (((vls-data data))
       (mods (vl-design->mods data.orig))
       (mod  (vl-find-module origname mods))
       ((unless mod)
        nil))
    (set::mergesort (vl-modinstlist->modnames (vl-module->modinsts mod)))))


; (depends-on "server-raw.lsp")
(acl2::include-raw "server-raw.lsp"
                   :host-readtable t)


#||
(in-package "VL")
(set-vls-root "/n/fv2/translations")
(start)
||#

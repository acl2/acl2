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
(include-book "command")
(include-book "../transforms/annotate/top")
(include-book "../mlib/comment-writer")
(include-book "../mlib/json")
(include-book "oslib/file-types-logic" :dir :system)
(include-book "std/io/unsound-read" :dir :system)
(include-book "quicklisp/hunchentoot" :dir :system)
(include-book "quicklisp/bordeaux" :dir :system)
(include-book "quicklisp/bt-semaphore" :dir :system)
(include-book "quicklisp/html-template" :dir :system)
(include-book "centaur/bridge/to-json" :dir :system)
(include-book "xdoc/defxdoc-raw" :dir :system)
(include-book "centaur/misc/memory-mgmt" :dir :system)
(local (include-book "../util/arithmetic"))
(local (include-book "../util/osets"))
(local (in-theory (enable tag-reasoning)))
(set-state-ok t)

(local (xdoc::set-default-parents vl-server))

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
                    (public-dir maybe-stringp "Path to @('public/') directory.")
                    (root-dir   stringp       "Path to the data directory."))
  (declare (ignorable port public-dir root-dir))
  (raise "Under the hood definition not installed."))

(define stop ()
  (raise "Under the hood definition not installed."))


(define vls-data-from-zip ((zip vl-zipfile-p))
  :returns (data vls-data-p)
  :prepwork ((local (in-theory (enable vl-descalist-okp))))
  (b* (((vl-zipfile zip))
       (orig           (cwtime (hons-copy (cwtime (vl-annotate-design zip.design *vl-default-simpconfig*)))))
       (orig-descalist (fast-alist-free (vl-make-descalist (vl-design-descriptions orig)))))
    (make-vls-data
     :name           zip.name
     :date           zip.date
     :ltime          zip.ltime
     :orig           orig
     :orig-descalist orig-descalist
     :filemap        zip.filemap
     :defs           zip.defines)))

(defalist vls-scannedalist-p (x)
  :key (stringp x) ;; Short file name
  :val (vl-zipinfo-p x))

(defalist vls-loadedalist-p (x)
  :key (stringp x) ;; Short file name
  :val (vls-data-p x))

(local (defthm string-listp-of-alist-keys-when-vls-scannedalist-p
         (implies (vls-scannedalist-p x)
                  (string-listp (alist-keys x)))
         :hints(("Goal" :induct (len x)))))

(local (defthm string-listp-of-alist-keys-when-vls-loadedalist-p
         (implies (vls-loadedalist-p x)
                  (string-listp (alist-keys x)))
         :hints(("Goal" :induct (len x)))))

(define vls-scannedalist-to-json ((x vls-scannedalist-p))
  (b* (((when (atom x))
        nil)
       ((cons name (vl-zipinfo info)) (car x))
       (entry (list (cons "name"     info.name)
                    (cons "date"     info.date)
                    (cons "ltime"    info.ltime)
                    (cons "compat"   (equal info.syntax *vl-current-syntax-version*)))))
    (cons (cons name entry)
          (vls-scannedalist-to-json (cdr x)))))

(define vls-loadedalist-to-json ((x vls-loadedalist-p))
  (b* (((when (atom x))
        nil)
       ((cons name (vls-data data)) (car x))
       (entry (list (cons "name"    data.name)
                    (cons "date"    data.date)
                    (cons "ltime"   data.ltime)
                    (cons "compat"  t))))
    (cons (cons name entry)
          (vls-loadedalist-to-json (cdr x)))))

(define vls-remove-from-scannedalist ((names string-listp)
                                      (x     vls-scannedalist-p))
  :returns (new-x vls-scannedalist-p :hyp (vls-scannedalist-p x))
  (cond ((atom x)
         nil)
        ((member-equal (caar x) names)
         (vls-remove-from-scannedalist names (cdr x)))
        (t
         (cons (car x)
               (vls-remove-from-scannedalist names (cdr x))))))

(define vls-make-scannedalist ((x vl-zipinfolist-p))
  :returns (alist vls-scannedalist-p)
  (if (atom x)
      nil
    (cons (cons (vl-zipinfo->filename (car x))
                (vl-zipinfo-fix (car x)))
          (vls-make-scannedalist (cdr x)))))

(define vls-get-unloaded-json ((scanned vls-scannedalist-p)
                               (loaded  vls-loadedalist-p))
  (vls-scannedalist-to-json
   (vls-remove-from-scannedalist (alist-keys loaded) scanned)))


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
      (:vl-interface (vl-ppc-interface x ss))
      (:vl-package   (vl-ppc-package   x ss))
      (:vl-program   (vl-ppc-program   x))
      (:vl-class     (vl-ppc-class     x))
      (:vl-config    (vl-ppc-config    x))

      ;; items without comments
      (:vl-taskdecl   (vl-pp-taskdecl   x))
      (:vl-fundecl    (vl-pp-fundecl    x))
      (:vl-paramdecl  (vl-pp-paramdecl  x))
      (:vl-import     (vl-pp-import     x))
      (:vl-fwdtypedef (vl-pp-fwdtypedef x))
      (:vl-vardecl    (vl-pp-vardecl    x))
      (:vl-dpiimport  (vl-pp-dpiimport  x))
      (:vl-dpiexport  (vl-pp-dpiexport  x))
      (:vl-bind       (vl-pp-bind       x ss))
      (:vl-property   (vl-pp-property   x))
      (:vl-sequence   (vl-pp-sequence   x))
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

(define-vls-json vls-get-summary (origname data)
  ;; Special command: the origname is case insensitive to support jump-to box.
  (b* (((vls-data data))
       ;; (- (raise "Testing out how errors work."))
       (desc (or (cdr (hons-assoc-equal origname data.orig-descalist))
                 (vl-find-description-insensitive origname data.orig-descalist)))
       ((unless desc)
        (vls-success :json (bridge::json-encode "NIL"))))
    (vls-success :json (bridge::json-encode (vl-description-summary desc)))))

(defprojection vl-descriptionlist-summaries ((x vl-descriptionlist-p))
  (vl-description-summary x))

(define-vls-json vls-get-summaries (data)
  (b* (((vls-data data))
       (descriptions (alist-vals data.orig-descalist))
       (summaries    (vl-descriptionlist-summaries descriptions)))
    (vls-success :json (bridge::json-encode summaries))))

(define-vls-html vls-get-origsrc (origname data)
  (b* (((vls-data data))
       (desc (cdr (hons-assoc-equal origname data.orig-descalist)))
       ((unless desc)
        (cat "Error: " origname " not found."))
       (ss  (vl-scopestack-init data.orig))
       (ans (with-local-ps
              (vl-ps-update-htmlp t)
              (vl-ppc-description desc ss))))
    ans))

(define-vls-html vls-get-plainsrc (origname data)
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
                                                     (:vl-class     (length "endclass"))
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

(define-vls-json vls-get-desctypes (data)
  (b* ((desctypes (vl-descalist->descriptions/types (vls-data->orig-descalist data))))
    (vls-success :json (bridge::json-encode desctypes))))

(local (defthm vl-module-p-by-tag-when-vl-description-p-unlimited
         (implies (and (vl-description-p x)
                       (eq (tag x) :vl-module))
                  (vl-module-p x))))

(local (defthm vl-interface-p-by-tag-when-vl-description-p-unlimited
         (implies (and (vl-description-p x)
                       (eq (tag x) :vl-interface))
                  (vl-interface-p x))))

(local (defthm vl-package-p-by-tag-when-vl-description-p-unlimited
         (implies (and (vl-description-p x)
                       (eq (tag x) :vl-package))
                  (vl-package-p x))))

(local (in-theory (disable (force))))

(define-vls-html vls-describe (origname what data)
  (b* (((vls-data data))
       (desc (cdr (hons-assoc-equal origname data.orig-descalist)))
       ; (- (raise "Testing error handling"))
       ((unless desc)
        (cat "Error: " origname " not found."))
       ;; ((unless (mbe :logic (vl-module-p desc)
       ;;               :exec (eq (tag desc) :vl-module)))
       ;;  (cat "BOZO implement describe page for " (ec-call (symbol-name (tag desc)))))
       (ss (vl-scopestack-init data.orig))
       (blob
        (case (tag desc)
          (:vl-module (vl-module->genblob desc))
          (:vl-interface (vl-interface->genblob desc))
          (:vl-package    (vl-package->genblob desc))
          (otherwise (make-vl-genblob :id origname :scopetype :vl-anonymous-scope)))))
    (with-local-ps
      (vl-ps-update-htmlp t)
      (vl-pp-describe what blob ss))))

(define-vls-html vls-showloc (file line col data)
  (b* (((vls-data data))
       (line     (str::strval line))
       (col      (str::strval col))
       ((unless (posp line))
        "Error: Invalid line number")
       ((unless (natp col))
        "Error: Invalid column number")
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
       (vls-showloc-print contents min max line col)))))

(define-vls-html vls-port-table (origname data)
  (b* (((vls-data data))
       (look   (cdr (hons-assoc-equal origname data.orig-descalist)))
       ((unless look)
        (cat "Error: no such module " origname))
       ((unless (mbe :logic (vl-module-p look)
                     :exec (eq (tag look) :vl-module)))
        (cat "Error: expected a module but " origname " is a " (ec-call (symbol-name (tag look))))))
    (with-local-ps
      (vl-ps-seq
       (vl-ps-update-htmlp t)
       (vl-pp-porttable look)))))

(define-vls-json vls-get-parents (origname data)
  (b* (((vls-data data))
       (parents (vl-dependent-elements-direct (list origname) data.orig)))
    (vls-success :json (bridge::json-encode parents))))

(define-vls-json vls-get-children (origname data)
  (b* (((vls-data data))
       (children (vl-necessary-elements-direct (list origname) data.orig)))
    (vls-success :json (bridge::json-encode children))))


(define vl-description->warnings ((x vl-description-p))
  :short "Get the warnings from most descriptions, or @('nil') if this
description doesn't have any warnings (e.g., an @('import') statement, function
declaration, ...)."
  :returns (warnings vl-warninglist-p)
  (b* ((x (vl-description-fix x)))
    (case (tag x)
      (:vl-module     (vl-module->warnings x))
      (:vl-udp        (vl-udp->warnings x))
      (:vl-interface  (vl-interface->warnings x))
      (:vl-package    (vl-package->warnings x))
      (:vl-program    (vl-program->warnings x))
      (:vl-class      (vl-class->warnings x))
      (:vl-config     (vl-config->warnings x))
      (:vl-taskdecl   nil)
      (:vl-fundecl    nil)
      (:vl-paramdecl  nil)
      (:vl-import     nil)
      (:vl-fwdtypedef nil)
      (:vl-typedef    nil)
      (:vl-vardecl    nil)
      (:vl-dpiimport  nil)
      (:vl-dpiexport  nil)
      (:vl-bind       nil)
      (:vl-property   nil)
      (:vl-sequence   nil)
      (otherwise      (impossible)))))

(define vls-data-origname-reportcard ((data vls-data-p))
  :returns (reportcard vl-reportcard-p)
  (b* (((vls-data data))
       (acc nil)
       (acc (vl-design-origname-reportcard-aux data.orig acc))
       ;; Previously this merged the reportcards for good and bad, i.e.,
       ;; (acc (vl-design-origname-reportcard-aux data.bad acc))... but we
       ;; don't do that anymore...
       (ret (vl-clean-reportcard acc)))
    (fast-alist-free acc)
    ret))

(memoize 'vls-data-origname-reportcard)

(define-vls-json vls-get-warnings (origname data)
  (b* (((vls-data data))
       (look (hons-assoc-equal origname data.orig-descalist))
       ((unless look)
        (vls-fail "No such description: ~s0~%" origname))

       (reportcard (vls-data-origname-reportcard data))
       (warnings   (cdr (hons-assoc-equal origname reportcard)))
       (json       (with-local-ps
                     (vl-jp-warninglist warnings))))
    (vls-success :json json)))

; (depends-on "server-raw.lsp")
(acl2::include-raw "server-raw.lsp"
                   :host-readtable t)

#||
(include-book
 "server")

(b* ((- (acl2::set-max-mem (* 12 (expt 2 30))))
     ((mv ?err port state)
      (getenv$ "FVQ_PORT" state))
     (- (cw "Port is ~x0.~%" port)))
  (start :port (or (str::strval port) 9999)
         :root-dir "./zips")
  state)

||#

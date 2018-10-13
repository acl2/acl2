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
(include-book "../parsetree")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "std/io/read-file-characters" :dir :system)
(include-book "oslib/ls-logic" :dir :system)
(include-book "../kit/zipfile")
(local (include-book "centaur/vl/util/arithmetic" :dir :system))

(defsection file-layout
  :parents (vl-server)
  :short "Where we look for translation data."

  :long "<p>The VL server looks in a particular root directory for its
translation data.  This directory should contain @('.vlzip') files created by
the @('vl zip') command.  See the @(see kit) for more details.  Each
@('.vlzip') file knows its name and has a date stamp associated with it.  We
occasionally rescan this directory to look for new translations.</p>")

(local (xdoc::set-default-parents file-layout))

(defprod vl-zipinfo
  :tag :vl-zipinfo
  :short "Meta information about .vlzip files we find."
  ((filename stringp :rule-classes :type-prescription
             "Short filename of the vlzip file.")
   (name     stringp :rule-classes :type-prescription
             "Project name extracted from the vlzip file.")
   (syntax   stringp :rule-classes :type-prescription
             "Syntax version of this vlzip file.")
   (date     stringp :rule-classes :type-prescription
             "Human-friendly date stamp for this vlzip file.")
   (ltime    natp    :rule-classes :type-prescription
             "Lisp time stamp (seconds since 1900) of this vlzip file.")))

(fty::deflist vl-zipinfolist :elt-type vl-zipinfo)

;; (define vl-zipinfo-order ((x vl-zipinfo-p)
;;                           (y vl-zipinfo-p))
;;   :short "We order .vlzip files so that the newest files come first (and then
;;           arbitrarily after that)."
;;   (b* (((vl-zipinfo x))
;;        ((vl-zipinfo y)))
;;     (or (> x.ltime y.ltime)
;;         (and (eql x.ltime y.ltime)
;;              ;; Completely arbitrary, total order.
;;              (<< x y))))
;;   ///
;;   (defthm vl-zipinfo-order-irreflexive
;;     (not (vl-zipinfo-order x x)))
;;   (defthm vl-zipinfo-order-antisymmetric
;;     (implies (vl-zipinfo-order x y)
;;              (not (vl-zipinfo-order y x))))
;;   (defthm vl-zipinfo-order-transitive
;;     (implies (and (vl-zipinfo-order x y)
;;                   (vl-zipinfo-order y z))
;;              (vl-zipinfo-order x z))))

;; (acl2::defsort vl-zipinfolist-sort (x)
;;   :compare< vl-zipinfo-order
;;   :comparablep vl-zipinfo-p
;;   :comparable-listp vl-zipinfolist-p
;;   :true-listp nil
;;   :weak t ;; BOZO why do I need weak here?
;;   )

(define vl-scan-for-zipinfos-aux ((dir   stringp)
                                  (files string-listp)
                                  &key (state 'state))
  :returns (mv (infos vl-zipinfolist-p)
               (state state-p1 :hyp (state-p1 state)))
  (b* (((when (atom files))
        (mv nil state))
       ((mv rest state) (vl-scan-for-zipinfos-aux dir (cdr files)))
       ((unless (str::strsuffixp ".vlzip" (car files)))
        ;; Not even a .vlzip file, don't consider it.
        (mv rest state))
       (shortname  (car files))
       (fullpath   (oslib::catpath dir shortname))
       ((ret head) (vl-read-zip-header fullpath))
       ((unless (and head.name head.syntax head.date head.ltime))
        (cw "; Note: vlzip header problem in ~s0.~%" fullpath)
        (mv rest state))
       (info (make-vl-zipinfo :filename shortname
                              :name head.name
                              :syntax head.syntax
                              :date head.date
                              :ltime head.ltime)))
    (mv (cons info rest) state)))

(define vl-scan-for-zipinfos ((dir stringp) &key (state 'state))
  :returns (mv (infos vl-zipinfolist-p)
               (state state-p1 :hyp (state-p1 state)))
  (b* (((mv err files state)
        (oslib::ls-files dir))
       ((when err)
        (cw "; NOTE: Error listing ~x0: ~@1~%" dir err)
        (mv nil state))
       ((mv infos state)
        (vl-scan-for-zipinfos-aux dir files)))
    (mv infos state)))

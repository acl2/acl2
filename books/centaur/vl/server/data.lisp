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
(include-book "../mlib/hierarchy")
(include-book "../loader/filemap")
(include-book "../loader/preprocessor/defines")
(include-book "../loader/descriptions")
(local (include-book "../util/arithmetic"))


;; (define vl-depalist-okp ((mods vl-modulelist-p)
;;                          depalist)
;;   (equal depalist (vl-depalist mods)))

(define vl-descalist-okp ((design vl-design-p)
                          descalist)
  (equal descalist (vl-make-descalist (vl-design-descriptions design)))
  ///
  (defthm vl-descalist-p-when-vl-descalist-okp
    (implies (vl-descalist-okp design descalist)
             (vl-descalist-p descalist))))

(defaggregate vls-data
  :parents (vl-server)
  :short "Data that is available to @(see vls-commands)."
  :tag :vls-data
  ((orig vl-design-p
         "The original design, as seen very shortly after parsing.")

   (name  stringp :rule-classes :type-prescription
          "Project name for this design.")

   (date  stringp :rule-classes :type-prescription
          "Date stamp for this zip file.")

   (ltime natp :rule-classes :type-prescription
          "Lisp time stamp for this zip file.")

   ;; (orig-depalist (vl-depalist-okp (vl-design->mods orig) orig-depalist)
   ;;                "A @(see vl-depalist) for the original modules.")

   (orig-descalist (vl-descalist-okp orig orig-descalist)
                   "A @(see vl-descalist-p) binding every description in the
                    original design to its definition.")

   (filemap vl-filemap-p
            "Map of all files that were loaded for this translation, for jumping
             to particular locations.")

   (defs vl-defines-p
     "Summary of all @('`define')s encountered while parsing."))

  :long "<p>A @('vls-data-p') structure just aggregates a bunch of data that is
produced when we run the translator.</p>

<p>These structures are typically produced by the @(see vl-server) as part of
its translation-loading scheme.</p>")

;; (defthm vls-data->orig-depalist-elim
;;   (implies (force (vls-data-p x))
;;            (equal (vls-data->orig-depalist x)
;;                   (vl-depalist (vl-design->mods (vls-data->orig x)))))
;;   :hints(("Goal"
;;           :use ((:instance return-type-of-vls-data->orig-depalist))
;;           :in-theory (e/d (vl-depalist-okp)
;;                           (return-type-of-vls-data->orig-depalist)))))

(defthm vls-data->orig-descalist-elim
  (implies (force (vls-data-p x))
           (equal (vls-data->orig-descalist x)
                  (vl-make-descalist (vl-design-descriptions (vls-data->orig x)))))
  :hints(("Goal"
          :use ((:instance return-type-of-vls-data->orig-descalist))
          :in-theory (e/d (vl-descalist-okp)
                          (return-type-of-vls-data->orig-descalist)))))



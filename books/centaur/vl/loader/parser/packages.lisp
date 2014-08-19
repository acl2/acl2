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
(include-book "utils")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))

;; package_declaration ::=
;; { attribute_instance } package [ lifetime ] package_identifier ;
;; [ timeunits_declaration ] { { attribute_instance } package_item }
;; endpackage [ : package_identifier ]

;; package_item ::=
;; package_or_generate_item_declaration
;; | anonymous_program
;; | package_export_declaration
;; | timeunits_declaration

;; package_or_generate_item_declaration ::=
;; net_declaration
;; | data_declaration
;; | task_declaration
;; | function_declaration
;; | checker_declaration
;; | dpi_import_export
;; | extern_constraint_declaration
;; | class_declaration
;; | class_constructor_declaration
;; | local_parameter_declaration ;
;; | parameter_declaration ;
;; | covergroup_declaration
;; | overload_declaration
;; | assertion_item_declaration
;; | ;

;; anonymous_program ::= program ; { anonymous_program_item } endprogram

;; anonymous_program_item ::=
;; task_declaration
;; | function_declaration
;; | class_declaration
;; | covergroup_declaration
;; | class_constructor_declaration
;; | ;

;; anonymous_program_item ::=
;; task_declaration
;; | function_declaration
;; | class_declaration
;; | covergroup_declaration
;; | class_constructor_declaration
;; | ;

(defparser vl-parse-package-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; Similar to UDPs, but we don't have to check for Verilog-2005 because
  ;; packages only exist in SystemVerilog-2012.
  (seqw tokens warnings
        (unless (vl-is-token? :vl-kwd-endpackage)
          (:s= (vl-match-any))
          (info := (vl-parse-package-declaration-aux))
          (return info))
        (end := (vl-match))
        (unless (vl-is-token? :vl-colon)
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-package-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-package-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-package))
        (name := (vl-match-token :vl-idtoken))
        (endinfo := (vl-parse-package-declaration-aux))
        (when (and (vl-endinfo->name endinfo)
                   (not (equal (vl-idtoken->name name)
                               (vl-endinfo->name endinfo))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched package/endpackage pair: expected "
                 (vl-idtoken->name name) " but found "
                 (vl-endinfo->name endinfo)))))
        (return
         (make-vl-package
          :name (vl-idtoken->name name)
          :atts atts
          :warnings (fatal :type :vl-warn-package
                           :msg "Packages are not supported."
                           :args nil
                           :acc nil)
          :minloc (vl-token->loc name)
          :maxloc (vl-endinfo->loc endinfo)))))



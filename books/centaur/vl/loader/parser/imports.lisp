; VL Verilog Toolkit
; Copyright (C) 2008-2014 Centaur Technology
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
(include-book "utils")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))

; -----------------------------------------------------------------------------
;
;                             Package Imports
;
; -----------------------------------------------------------------------------

; package_import_item ::= identifier '::' identifier
;                       | identifier '::' '*'

(defparser vl-parse-package-import-item (atts)
  :guard (vl-atts-p atts)
  :result (vl-import-p val)
  :resultp-of-nil nil
  :fails :gracefully
  :count :strong
  (seqw tokens warnings
        (pkgid := (vl-match-token :vl-idtoken))
        (:=       (vl-match-token :vl-scope))
        (when (vl-is-token? :vl-times)
          (:= (vl-match))
          (return (make-vl-import :pkg (vl-idtoken->name pkgid)
                                  :part :vl-import*
                                  :loc (vl-token->loc pkgid)
                                  :atts atts)))
        (what := (vl-match-token :vl-idtoken))
        (return (make-vl-import :pkg (vl-idtoken->name pkgid)
                                :part (vl-idtoken->name what)
                                :loc (vl-token->loc pkgid)
                                :atts atts))))

; package_import_declaration ::=
;    'import' package_import_item { ',' package_import_item } ';'

(defparser vl-parse-1+-package-import-items-separated-by-commas (atts)
  :guard (vl-atts-p atts)
  :result (vl-importlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails :gracefully
  :count :strong
  (seqw tokens warnings
        (first := (vl-parse-package-import-item atts))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-1+-package-import-items-separated-by-commas atts)))
        (return (cons first rest))))

(defparser vl-parse-package-import-declaration (atts)
  :guard (and (vl-is-token? :vl-kwd-import)
              (vl-atts-p atts))
  :result (vl-importlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails :gracefully
  :count :strong
  (seqw tokens warnings
        (:= (vl-match))
        (elems := (vl-parse-1+-package-import-items-separated-by-commas atts))
        (:= (vl-match-token :vl-semi))
        (return elems)))

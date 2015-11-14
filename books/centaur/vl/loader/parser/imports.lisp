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
  (seq tokstream
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
  (seq tokstream
        (first := (vl-parse-package-import-item atts))
        (when (vl-is-token? :vl-comma)
          (:= (vl-match))
          (rest := (vl-parse-1+-package-import-items-separated-by-commas atts)))
        (return (cons first rest))))

(define vl-plausible-start-of-package-import-p (&key (tokstream 'tokstream))
  :enabled t
  ;; Note that every package_import_item begins with an idtoken.  We check for
  ;; this idtoken, in addition to the import keyword, to rule out any possible
  ;; confusion between a package import and a DPI function import.
  (and (vl-is-token? :vl-kwd-import)
       (vl-lookahead-is-token? :vl-idtoken (cdr (vl-tokstream->tokens)))))

(defparser vl-parse-package-import-declaration (atts)
  :guard (and (vl-plausible-start-of-package-import-p)
              (vl-atts-p atts))
  :result (vl-importlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails :gracefully
  :count :strong
  (seq tokstream
       (:= (vl-match)) ;; eat the import keyword
       (elems := (vl-parse-1+-package-import-items-separated-by-commas atts))
       (:= (vl-match-token :vl-semi))
       (return elems)))

(defparser vl-parse-0+-package-import-declarations ()
  :result (vl-importlist-p val)
  :resultp-of-nil t
  :true-listp t
  :fails :gracefully
  :count :weak
  (seq tokstream
       (unless (vl-plausible-start-of-package-import-p)
         (return nil))
       (first := (vl-parse-package-import-declaration nil))
       (rest := (vl-parse-0+-package-import-declarations))
       (return (append first rest))))

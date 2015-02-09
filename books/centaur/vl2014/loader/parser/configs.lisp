; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
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

(in-package "VL2014")
(include-book "utils")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))

; Configurations
;
; Syntax in Verilog-2005:
;
; config_declaration ::=
;    'config' identifier ';'
;       design_statement
;       { config_rule_statement }
;    'endconfig'
;
; Syntax in SystemVerilog-2012:
;
; config_declaration ::=
;    'config' identifier ';'
;       { local_parameter_declaration ';' }
;       design_statement
;       { config_rule_statement }
;    'endconfig' [':' identifier]

(defparser vl-parse-config-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (unless (vl-is-token? :vl-kwd-endconfig)
          (:s= (vl-match-any))
          (info := (vl-parse-config-declaration-aux))
          (return info))
        (end := (vl-match))
        (when (or (eq (vl-loadconfig->edition config) :verilog-2005)
                  (not (vl-is-token? :vl-colon)))
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-config-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-config-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (:= (vl-match-token :vl-kwd-config))
        (name := (vl-match-token :vl-idtoken))
        (endinfo := (vl-parse-config-declaration-aux))
        (when (and (vl-endinfo->name endinfo)
                   (not (equal (vl-idtoken->name name)
                               (vl-endinfo->name endinfo))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched config/endconfig pair: expected "
                 (vl-idtoken->name name) " but found "
                 (vl-endinfo->name endinfo)))))
        (return
         (make-vl-config
          :name (vl-idtoken->name name)
          :atts atts
          :warnings (fatal :type :vl-warn-config
                           :msg "Configs are not supported."
                           :args nil
                           :acc nil)
          :minloc (vl-token->loc name)
          :maxloc (vl-endinfo->loc endinfo)))))

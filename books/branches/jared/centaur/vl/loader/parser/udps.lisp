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

; BOZO this is really not implemented.  We basically just read until
; endprimitive, throwing away any tokens we encounter until then.

; Verilog-2005 Syntax:
;
; udp_declaration ::=
;
;    {attribute_instance} 'primitive' udp_identifier '(' udp_port_list ')' ';'
;       udp_port_declaration { udp_port_declaration }
;       udp_body
;       'endprimitive'
;
;    {attribute_instance} 'primitive' udp_identifier '(' udp_declaration_port_list ')' ';'
;       udp_body
;       'endprimitive'
;
;
; SystemVerilog-2012 Syntax:
;
;   -- There is a bit more to it, but minimally it adds [ ':' identifier ] after
;      the endprimitive keyword.


(defparser vl-parse-udp-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (unless (vl-is-token? :vl-kwd-endprimitive)
          (:s= (vl-match-any))
          (info := (vl-parse-udp-declaration-aux))
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

(defparser vl-parse-udp-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-udp-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-kwd-primitive))
        (name := (vl-match-token :vl-idtoken))
        (endinfo := (vl-parse-udp-declaration-aux))
        (when (and (vl-endinfo->name endinfo)
                   (not (equal (vl-idtoken->name name)
                               (vl-endinfo->name endinfo))))
          (return-raw
           (vl-parse-error
            (cat "Mismatched primitive/endprimitive pair: expected "
                 (vl-idtoken->name name) " but found "
                 (vl-endinfo->name endinfo)))))
        (return
         (make-vl-udp
          :name (vl-idtoken->name name)
          :atts atts
          :warnings (fatal :type :vl-warn-primitive
                           :msg "User-defined primitives are not supported."
                           :args nil
                           :acc nil)
          :minloc (vl-token->loc name)
          :maxloc (vl-endinfo->loc endinfo)))))


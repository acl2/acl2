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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "VL")
(include-book "utils")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))

(defparser vl-maybe-parse-lifetime ()
  :parents (parser)
  :short "Match an optional @('lifetime') for SystemVerilog-2012."
  :long "<p>Grammar:</p>
         @({
              lifetime ::= 'static' | 'automatic'
         })"
  :result (vl-lifetime-p val)
  :resultp-of-nil t
  :fails gracefully
  :count strong-on-value
  (seq tokstream
        (when (vl-is-token? :vl-kwd-static)
          (:= (vl-match))
          (return :vl-static))
        (when (vl-is-token? :vl-kwd-automatic)
          (:= (vl-match))
          (return :vl-automatic))
        (return nil)))

(defparser vl-parse-class-declaration-aux ()
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  ;; Similar to UDPs, but we don't have to check for Verilog-2005 because
  ;; classes only exist in SystemVerilog-2012.
  (seq tokstream
        (unless (vl-is-token? :vl-kwd-endclass)
          (:s= (vl-match-any))
          (info := (vl-parse-class-declaration-aux))
          (return info))
        (end := (vl-match))
        (unless (vl-is-token? :vl-colon)
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-class-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-class-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (virtual := (vl-maybe-match-token :vl-kwd-virtual))
       (:= (vl-match-token :vl-kwd-class))
       (lifetime := (vl-maybe-parse-lifetime))
       (name := (vl-match-token :vl-idtoken))
       (endinfo := (vl-parse-class-declaration-aux))
       (when (and (vl-endinfo->name endinfo)
                  (not (equal (vl-idtoken->name name)
                              (vl-endinfo->name endinfo))))
         (return-raw
          (vl-parse-error
           (cat "Mismatched class/endclass pair: expected "
                (vl-idtoken->name name) " but found "
                (vl-endinfo->name endinfo)))))
       (return
        (make-vl-class
         :name (vl-idtoken->name name)
         :atts atts
         :virtualp (and virtual t)
         :lifetime lifetime
         :warnings (fatal :type :vl-warn-class
                          :msg "Classes are not supported."
                          :args nil
                          :acc nil)
         :minloc (vl-token->loc name)
         :maxloc (vl-endinfo->loc endinfo)))))

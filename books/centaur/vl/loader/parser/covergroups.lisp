; VL Verilog Toolkit, Covergroup Parsing
; Copyright (C) 2017 Apple, Inc.
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

(in-package "VL")
(include-book "utils")
(include-book "../../parsetree")
(local (include-book "../../util/arithmetic"))

(defparser vl-parse-covergroup-declaration-aux ()
  ;; Just read everything through endgroup and ignore it
  :result (vl-endinfo-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
        (unless (vl-is-token? :vl-kwd-endgroup)
          (:s= (vl-match-any))
          (info := (vl-parse-covergroup-declaration-aux))
          (return info))
        (end := (vl-match))
        (unless (vl-is-token? :vl-colon)
          (return (make-vl-endinfo :name nil
                                   :loc (vl-token->loc end))))
        (:= (vl-match))
        (id := (vl-match-token :vl-idtoken))
        (return (make-vl-endinfo :name (vl-idtoken->name id)
                                 :loc (vl-token->loc id)))))

(defparser vl-parse-covergroup-declaration (atts)
  :guard (vl-atts-p atts)
  :result (vl-covergroup-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-kwd-covergroup))
       (name := (vl-match-token :vl-idtoken))
       (endinfo := (vl-parse-covergroup-declaration-aux))
       (when (and (vl-endinfo->name endinfo)
                  (not (equal (vl-idtoken->name name)
                              (vl-endinfo->name endinfo))))
         (return-raw
          (vl-parse-error
           (cat "Mismatched covergroup/endgroup pair: expected "
                (vl-idtoken->name name) " but found "
                (vl-endinfo->name endinfo)))))
       (return
        (make-vl-covergroup :name (vl-idtoken->name name)
                            :atts atts
                            :loc  (vl-token->loc name)))))



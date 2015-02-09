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

(defsection parse-strengths
  :parents (parser)
  :short "Functions for parsing drive/charge strengths."

  :long "<p>From Verilog-2005:</p>

@({
    drive_strength ::=
       '(' strength0 ',' strength1 ')'
     | '(' strength1 ',' strength0 ')'
     | '(' strength0 ',' 'highz1' ')'
     | '(' strength1 ',' 'highz0' ')'
     | '(' 'highz0'  ',' strength1 ')'
     | '(' 'highz1'  ',' strength0 ')'

    strength0 ::= 'supply0' | 'strong0' | 'pull0' | 'weak0'
    strength1 ::= 'supply1' | 'strong1' | 'pull1' | 'weak1'

    charge_strength ::= '(' ['small'|'medium'|'large'] ')'
})")

(local (xdoc::set-default-parents parse-strengths))

(defval *vl-strength0-alist*
  :showval t
  '((:vl-kwd-supply0 . :vl-supply)
    (:vl-kwd-strong0 . :vl-strong)
    (:vl-kwd-pull0   . :vl-pull)
    (:vl-kwd-weak0   . :vl-weak)))

(defval *vl-strength1-alist*
  :showval t
  '((:vl-kwd-supply1 . :vl-supply)
    (:vl-kwd-strong1 . :vl-strong)
    (:vl-kwd-pull1   . :vl-pull)
    (:vl-kwd-weak1   . :vl-weak)))

(defval *vl-ds0-alist*

  :showval t
  (cons '(:vl-kwd-highz0 . :vl-highz) *vl-strength0-alist*))

(defval *vl-ds1-alist*
  :showval t
  (cons '(:vl-kwd-highz1 . :vl-highz) *vl-strength1-alist*))

(defval *vl-ds0-keywords*
  :showval t
  (strip-cars *vl-ds0-alist*))

(defval *vl-ds1-keywords*
  :showval t
  (strip-cars *vl-ds1-alist*))

(defval *vl-ds0/1-keywords*
  :showval t
  (append *vl-ds0-keywords* *vl-ds1-keywords*))


(defparser vl-parse-drive-strength ()
  :short "Match @('drive_strength'), return a @(see vl-gatestrength-p)."
  :result (vl-gatestrength-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-lparen))
       (first := (vl-match-some-token *vl-ds0/1-keywords*))
       (:= (vl-match-token :vl-comma))
       (second := (vl-match-some-token *vl-ds0/1-keywords*))
       (:= (vl-match-token :vl-rparen))
       (return-raw
        (b* (((mv s-zero s-one)
              ;; Sort them so that we know which is the strength0.
              (if (member-eq (vl-token->type first) *vl-ds0-keywords*)
                  (mv (vl-token->type first)
                      (vl-token->type second))
                (mv (vl-token->type second)
                    (vl-token->type first))))
             ;; Now make sure there isn't an illegal combination.
             ((when (and (member-eq s-zero *vl-ds0-keywords*)
                         (member-eq s-one *vl-ds1-keywords*)
                         (or (not (eq s-zero :vl-kwd-highz0))
                             (not (eq s-one  :vl-kwd-highz1)))))
              ;; It's fine.  Build a gate strength token.
              (mv nil
                  (make-vl-gatestrength
                   :zero (cdr (assoc-eq s-zero *vl-ds0-alist*))
                   :one (cdr (assoc-eq s-one *vl-ds1-alist*)))
                  tokstream)))
          (vl-parse-error "Invalid drive strength.")))))

(defparser vl-parse-optional-drive-strength ()
  :short "Never fails.  If there's a valid @('drive_strength'), we match it and
return a @(see vl-gatestrength-p).  Otherwise, we don't do anything to the
token list and just return nil."
  :result (vl-maybe-gatestrength-p val)
  :resultp-of-nil t
  :fails never
  :count strong-on-value
  (b* ((backup (vl-tokstream-save))
       ((mv erp val tokstream) (vl-parse-drive-strength))
       ((unless erp)
        (mv erp val tokstream))

       (tokstream (vl-tokstream-restore backup)))
    ;; Don't do anything to the token list, just return nil.
    (mv nil nil tokstream)))

(defval *vl-charge-strengths-alist*
  :showval t
  '((:vl-kwd-small  . :vl-small)
    (:vl-kwd-medium . :vl-medium)
    (:vl-kwd-large  . :vl-large)))

(defval *vl-charge-strengths-keywords*
  :showval t
  (strip-cars *vl-charge-strengths-alist*))

(defparser vl-parse-charge-strength ()
  :short "Match @('charge_strength'), return a @(see vl-cstrength-p)."
  :result (vl-cstrength-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seq tokstream
       (:= (vl-match-token :vl-lparen))
       (cstr := (vl-match-some-token *vl-charge-strengths-keywords*))
       (:= (vl-match-token :vl-rparen))
       (return (cdr (assoc-eq (vl-token->type cstr)
                              *vl-charge-strengths-alist*)))))

(defparser vl-parse-drive-strength-or-charge-strength ()
  :short "Match @('drive_strength') or @('charge_strength'), returning
a @(see vl-gatestrength-p) or a @(see vl-cstrength-p)."
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (b* (((mv ?erp val tokstream) (vl-parse-optional-drive-strength))
       ((when val)
        (mv nil val tokstream)))
    (vl-parse-charge-strength))
  ///
  (defthm vl-parse-drive-strength-or-charge-strength-forward
    (or (vl-gatestrength-p
         (mv-nth 1 (vl-parse-drive-strength-or-charge-strength)))
        (vl-cstrength-p
         (mv-nth 1 (vl-parse-drive-strength-or-charge-strength)))
        (mv-nth 0 (vl-parse-drive-strength-or-charge-strength)))
    :rule-classes ((:forward-chaining
                    :trigger-terms
                    ((vl-parse-drive-strength-or-charge-strength))))
    :hints(("Goal"
            :in-theory (enable vl-parse-drive-strength-or-charge-strength)))))

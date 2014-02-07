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




;                   PARSING DRIVE/CHARGE STRENGTHS
;
; drive_strength ::=
;    '(' strength0 ',' strength1 ')'
;  | '(' strength1 ',' strength0 ')'
;  | '(' strength0 ',' 'highz1' ')'
;  | '(' strength1 ',' 'highz0' ')'
;  | '(' 'highz0'  ',' strength1 ')'
;  | '(' 'highz1'  ',' strength0 ')'
;
; strength0 ::= 'supply0' | 'strong0' | 'pull0' | 'weak0'
; strength1 ::= 'supply1' | 'strong1' | 'pull1' | 'weak1'
;
; charge_strength ::= '(' ['small'|'medium'|'large'] ')'

(defconst *vl-strength0-alist*
  '((:vl-kwd-supply0 . :vl-supply)
    (:vl-kwd-strong0 . :vl-strong)
    (:vl-kwd-pull0   . :vl-pull)
    (:vl-kwd-weak0   . :vl-weak)))

(defconst *vl-strength1-alist*
  '((:vl-kwd-supply1 . :vl-supply)
    (:vl-kwd-strong1 . :vl-strong)
    (:vl-kwd-pull1   . :vl-pull)
    (:vl-kwd-weak1   . :vl-weak)))

(defconst *vl-ds0-alist*
  (cons '(:vl-kwd-highz0 . :vl-highz) *vl-strength0-alist*))

(defconst *vl-ds1-alist*
  (cons '(:vl-kwd-highz1 . :vl-highz) *vl-strength1-alist*))

(defconst *vl-ds0-keywords* (strip-cars *vl-ds0-alist*))
(defconst *vl-ds1-keywords* (strip-cars *vl-ds1-alist*))
(defconst *vl-ds0/1-keywords* (append *vl-ds0-keywords* *vl-ds1-keywords*))

(defparser vl-parse-drive-strength ()
  :result (vl-gatestrength-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
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
                   tokens warnings)))
           (vl-parse-error "Invalid drive strength.")))))

(defparser vl-parse-optional-drive-strength ()
  ;; This never fails.  If there's a valid drive strength, we return a
  ;; vl-gatestrength-p object.  Otherwise, we don't do anything to the token
  ;; list and just return nil.
  :result (vl-maybe-gatestrength-p val)
  :resultp-of-nil t
  :fails never
  :count strong-on-value
  (b* (((mv erp val explore new-warnings) (vl-parse-drive-strength))
       ((when erp)
        (mv nil nil tokens warnings)))
    (mv nil val explore new-warnings)))

(defconst *vl-charge-strengths-alist*
  '((:vl-kwd-small  . :vl-small)
    (:vl-kwd-medium . :vl-medium)
    (:vl-kwd-large  . :vl-large)))

(defconst *vl-charge-strengths-keywords*
  (strip-cars *vl-charge-strengths-alist*))

(defparser vl-parse-charge-strength ()
  :result (vl-cstrength-p val)
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (seqw tokens warnings
        (:= (vl-match-token :vl-lparen))
        (cstr := (vl-match-some-token *vl-charge-strengths-keywords*))
        (:= (vl-match-token :vl-rparen))
        (return (cdr (assoc-eq (vl-token->type cstr)
                               *vl-charge-strengths-alist*)))))

(defparser vl-parse-drive-strength-or-charge-strength ()
  ;; Returns either a vl-gatestrength-p or a vl-cstrength-p.
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (b* (((mv ?erp val tokens warnings) (vl-parse-optional-drive-strength))
       ((when val)
        (mv nil val tokens warnings)))
    (vl-parse-charge-strength)))

(defthm vl-parse-drive-strength-or-charge-strength-forward
  (equal (or (vl-gatestrength-p
              (mv-nth 1 (vl-parse-drive-strength-or-charge-strength)))
             (vl-cstrength-p
              (mv-nth 1 (vl-parse-drive-strength-or-charge-strength))))
         (not (mv-nth 0 (vl-parse-drive-strength-or-charge-strength))))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((vl-parse-drive-strength-or-charge-strength))))
  :hints(("Goal"
          :in-theory (enable vl-parse-drive-strength-or-charge-strength))))

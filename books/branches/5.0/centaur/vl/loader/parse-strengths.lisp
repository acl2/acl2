; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
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
(include-book "parse-utils")
(include-book "../parsetree")
(local (include-book "../util/arithmetic"))




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

(with-output
 :gag-mode :goals
 (defparser vl-parse-drive-strength (tokens warnings)
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
          (mv-let (s-zero s-one)
                  ;; Sort them so that we know which is the strength0.
                  (if (member-eq (vl-token->type first) *vl-ds0-keywords*)
                      (mv (vl-token->type first)
                          (vl-token->type second))
                    (mv (vl-token->type second)
                        (vl-token->type first)))
                  ;; Now make sure there isn't an illegal combination.
                  (if (and (member-eq s-zero *vl-ds0-keywords*)
                           (member-eq s-one *vl-ds1-keywords*)
                           (or (not (eq s-zero :vl-kwd-highz0))
                               (not (eq s-one  :vl-kwd-highz1))))
                      ;; It's fine.  Build a gate strength token.
                      (mv nil
                          (make-vl-gatestrength
                           :zero (cdr (assoc-eq s-zero *vl-ds0-alist*))
                           :one (cdr (assoc-eq s-one *vl-ds1-alist*)))
                          tokens warnings)
                    (vl-parse-error "Invalid drive strength.")))))))

(defparser vl-parse-optional-drive-strength (tokens warnings)
  ;; This never fails.  If there's a valid drive strength, we return a
  ;; vl-gatestrength-p object.  Otherwise, we don't do anything to the token
  ;; list and just return nil.
  :result (vl-maybe-gatestrength-p val)
  :resultp-of-nil t
  :fails never
  :count strong-on-value
  (mv-let (erp val explore new-warnings)
          (vl-parse-drive-strength)
          (if erp
              (mv nil nil tokens warnings)
            (mv nil val explore new-warnings))))

(defconst *vl-charge-strengths-alist*
  '((:vl-kwd-small  . :vl-small)
    (:vl-kwd-medium . :vl-medium)
    (:vl-kwd-large  . :vl-large)))

(defconst *vl-charge-strengths-keywords*
  (strip-cars *vl-charge-strengths-alist*))

(defparser vl-parse-charge-strength (tokens warnings)
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

(defparser vl-parse-drive-strength-or-charge-strength (tokens warnings)
  ;; Returns either a vl-gatestrength-p or a vl-cstrength-p.
  :resultp-of-nil nil
  :fails gracefully
  :count strong
  (mv-let (erp val tokens warnings)
          (vl-parse-optional-drive-strength)
          (declare (ignore erp))
          (if val
              (mv nil val tokens warnings)
            (vl-parse-charge-strength tokens))))

(defthm vl-parse-drive-strength-or-charge-strength-forward
  (implies (force (vl-tokenlist-p tokens))
           (equal (or (vl-gatestrength-p
                       (mv-nth 1 (vl-parse-drive-strength-or-charge-strength)))
                      (vl-cstrength-p
                       (mv-nth 1 (vl-parse-drive-strength-or-charge-strength))))
                  (not (mv-nth 0 (vl-parse-drive-strength-or-charge-strength)))))
  :rule-classes ((:forward-chaining
                  :trigger-terms
                  ((vl-parse-drive-strength-or-charge-strength-fn tokens warnings))))
  :hints(("Goal"
          :in-theory (enable vl-parse-drive-strength-or-charge-strength))))





(local
 (encapsulate
  ()

  (local (include-book "lexer"))

  (program)

  (defmacro test-drive/charge-strength (&key input expect (successp 't))
    `(assert! (let ((tokens (vl-make-test-tstream ,input))
                    (warnings nil))
                (mv-let (erp val tokens warnings)
                        (vl-parse-drive-strength-or-charge-strength)
                        (declare (ignore tokens))
                        (if erp
                            (prog2$
                             (cw "ERP is ~x0.~%" erp)
                             (not ,successp))
                          (prog2$
                           (cw "VAL is ~x0.~%" val)
                           (debuggable-and ,successp
                                           (equal val ,expect)
                                           (not warnings))))))))

  (test-drive/charge-strength :input "(supply0, pull1)"
                              :expect (make-vl-gatestrength
                                       :zero :vl-supply
                                       :one :vl-pull))

  (test-drive/charge-strength :input "(weak1, highz0)"
                              :expect (make-vl-gatestrength
                                       :zero :vl-highz
                                       :one :vl-weak))

  (test-drive/charge-strength :input "(strong0, pull1)"
                              :expect (make-vl-gatestrength
                                       :zero :vl-strong
                                       :one :vl-pull))

  (test-drive/charge-strength :input "(strong0, weak0)"
                              :successp nil)

  (test-drive/charge-strength :input "(highz0, highz1)"
                              :successp nil)

  (test-drive/charge-strength :input "(supply0, supply1, weak0, weak1)"
                              :successp nil)

  (test-drive/charge-strength :input "(small)"
                              :expect :vl-small)

  (test-drive/charge-strength :input "(medium)"
                              :expect :vl-medium)

  (test-drive/charge-strength :input "(large)"
                              :expect :vl-large)

  (test-drive/charge-strength :input "(huge)"
                              :successp nil)

  (test-drive/charge-strength :input "(supply0)"
                              :successp nil)))

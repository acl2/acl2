; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

;(include-book "../svl2")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Meta for svl2-save-mod-outputs

#|(set-ignore-ok t)||#

#|(svl2-save-mod-outputs-meta-rec '(cons val1 (cons val2 (cons val3 nil)))
                                ''(wires1 wires2 wires3) nil)||#

(include-book "centaur/sv/svex/eval" :dir :system)

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "../type-defs")
(include-book "../bits-sbits-defs")

(define entry-4vec-fix (entry)
  :guard (or (consp entry)
             (not entry))
  :enabled t
  (if entry
      (cdr entry)
    (sv::4vec-x))
  ///
  (add-rp-rule entry-4vec-fix))

(define save-wires-to-env-wires ((val sv::4vec-p)
                                 (wires wire-list-p)
                                 (env-wires sv::svex-env-p))
  :returns (res sv::svex-env-p
                :hyp (and (sv::4vec-p val)
                          (wire-list-p wires)
                          (sv::svex-env-p env-wires)))
  :verify-guards nil
  (if (atom wires)
      env-wires
    (b* ((wire (car wires))
         (old-val-entry (hons-get (wire-name wire) env-wires)))
      (case-match wire
        ((& w . s) (hons-acons
                    (wire-name wire)
                    (sbits s w val (entry-4vec-fix old-val-entry))
                    (save-wires-to-env-wires (4vec-rsh w val)
                                             (cdr wires)
                                             env-wires)))
        (& (hons-acons
            (wire-name wire)
            val
            env-wires)))))
  ///

  (local
   (defthm lemma
     (IMPLIES (AND
               (WIRE-LIST-P WIRES)
               (CONSP WIRES)
               (CONSP (CAR WIRES))
               (CONSP (CDR (CAR WIRES))))
              (4VEC-P (CADR (CAR WIRES))))
     :hints (("Goal"
              :in-theory (e/d (wire-list-p 4vec-p
                                           sv::svar-p) ())))))

  (verify-guards save-wires-to-env-wires ))

(define save-wires-to-env-wires-meta (term)
  (case-match term
    (('save-wires-to-env-wires val
                               ('quote (wire . wires-rest))
                               ('falist ('quote falist) &))
     (if (consp wire)
         (b* ((old-val-entry (hons-get (wire-name wire) falist))
              (old-val (if old-val-entry (cdr old-val-entry)
                         (list 'quote (sv::4vec-x)))))
           (case-match wire
             ((& w . s)
              (mv `(hons-acons
                    ',(wire-name wire)
                    (sbits ',s ',w ,val ,old-val)
                    ,(if (equal wires-rest nil)
                         (cadddr term)
                       `(save-wires-to-env-wires (4vec-rsh ',w ,val)
                                                 ',wires-rest
                                                 ,(cadddr term))))
                  (if (equal wires-rest nil)
                      `(nil t (nil t t t t) t)
                    `(nil t
                          (nil t t t t)
                          (nil (nil t t) t t)))))
             (& (mv `(hons-acons ',(wire-name wire)
                                 ,val
                                 ,(cadddr term))
                    `(nil t t t)))))
       (mv term nil)))
    (& (mv term nil))))


(rp::def-formula-checks-default-evl
 rp::rp-evl
 (strip-cars rp::*small-evl-fncs*))

(rp::def-formula-checks save-wires-to-env-wires-formula-checks
                        (save-wires-to-env-wires-meta
                         save-wires-to-env-wires))

(local
 (defthm eval-of-SAVE-WIRES-TO-ENV-WIRES
   (implies (and (rp-evl-meta-extract-global-facts)
                 (CONSP TERM)
                 (EQUAL (CAR TERM)
                        'SAVE-WIRES-TO-ENV-WIRES)
                 (CONSP (CDR TERM))
                 (CONSP (CDDR TERM))
                 (CONSP (CdDDR TERM))
                 (not (CdDdDR TERM))
                 (save-wires-to-env-wires-formula-checks state))
            (equal (rp-evl term a)
                   (SAVE-WIRES-TO-ENV-WIRES (rp-evl (cadr term) a)
                                            (rp-evl (caddr term) a)
                                            (rp-evl (cadddr term) a))))))

(local
 (defthmd lemma1
   (implies (and (RP::FALIST-CONSISTENT-AUX x; (CADR (CADR (CADDDR TERM)))

                                            y; (CADDR (CADDDR TERM))
                                            )
                 (HONS-ASSOC-EQUAL z ;;(CAR (CAR (CADR (CADDR TERM))))
                                   x)
;(HONS-ASSOC-EQUAL z (RP-EVL y A))
                 )
            (equal (RP-EVL (CDR (HONS-ASSOC-EQUAL z x)) A)
                   (CDR (HONS-ASSOC-EQUAL z (RP-EVL y A)))))
   :hints (("Goal"
            :in-theory (e/d ((:TYPE-PRESCRIPTION O<)
                             (:REWRITE DEFAULT-CAR)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE ACL2::O-P-O-INFP-CAR)
                             (:REWRITE
                              ACL2::CAR-OF-TRUE-LIST-LIST-FIX-X-NORMALIZE-CONST-UNDER-LIST-EQUIV)) ())))))

(local
 (defthm lemma2
   (equal (sbits x y z nil)
          (sbits x y z '(-1 . 0)))
   :hints (("Goal"
            :in-theory (e/d (sbits
                             4VEC-PART-INSTALL) ())))))

(local
 (defthmd lemma3
   (implies (and (RP::FALIST-CONSISTENT-AUX x  y) )
            (iff (HONS-ASSOC-EQUAL z x)
                 (HONS-ASSOC-EQUAL z (RP-EVL y A))))))

(defthm rp-evl-of-save-wires-to-env-wires-meta
  (implies (and (rp-evl-meta-extract-global-facts)
                (rp::rp-termp term)
                (save-wires-to-env-wires-formula-checks state))
           (equal (rp-evl (mv-nth 0 (save-wires-to-env-wires-meta term)) a)
                  (rp-evl term a)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance lemma1
                            (x (CADR (CADR (CADDDR TERM))))
                            (y (CADDR (CADDDR TERM)))
                            (z (CAR (CAR (CADR (CADDR TERM))))))
                 (:instance lemma3
                            (x (CADR (CADR (CADDDR TERM))))
                            (y (CADDR (CADDDR TERM)))
                            (z (CAR (CAR (CADR (CADDR TERM)))))))
           :expand ((SAVE-WIRES-TO-ENV-WIRES (RP-EVL (CADR TERM) A)
                                             (CADR (CADDR TERM))
                                             (RP-EVL (CADDR (CADDDR TERM)) A))
                    (SAVE-WIRES-TO-ENV-WIRES (4VEC-RSH (CADR (CAR (CADR (CADDR TERM))))
                                                       (RP-EVL (CADR TERM) A))
                                             NIL (RP-EVL (CADDR (CADDDR TERM)) A)))
           :in-theory (e/d (save-wires-to-env-wires-meta)
                           (hons-acons)))))

#|(defthm all-falist-consistent-save-wires-to-env-wires-meta
  (implies (rp::all-falist-consistent term)
           (rp::all-falist-consistent (mv-nth 0 (save-wires-to-env-wires-meta
                                                 term))))
  :hints (("Goal"
           :in-theory (e/d (save-wires-to-env-wires-meta
                            RP::ALL-FALIST-CONSISTENT)
                           (hons-acons)))))||#

;; :i-am-here

;; (skip-proofs
;;  (defthm valid-rp-meta-rulep-save-wires-to-env-wires-meta
;;    (implies (and (rp-evl-meta-extract-global-facts)
;;                  (save-wires-to-env-wires-formula-checks state))
;;             (let ((rule (make rp::rp-meta-rule-rec
;;                               :fnc 'save-wires-to-env-wires-meta
;;                               :trig-fnc 'save-wires-to-env-wires
;;                               :dont-rw t
;;                               :valid-syntax t)))
;;               (and (rp::rp-meta-valid-syntaxp-sk rule state)
;;                    (rp::valid-rp-meta-rulep rule state))))
;;    :otf-flg t
;;    :hints (("Goal"
;;             :in-theory (e/d (rp::RP-META-VALID-SYNTAXP)
;;                             (rp::PSEUDO-TERMP2
;;                              rp::PSEUDO-TERM-LISTP2

;;                              rp::RP-SYNTAXP
;;                              rp::VALID-SC))))))

;; (rp::add-meta-rules save-wires-to-env-wires-formula-checks
;;                     (list (make rp::rp-meta-rule-rec
;;                                 :fnc 'save-wires-to-env-wires-meta
;;                                 :trig-fnc 'save-wires-to-env-wires
;;                                 :dont-rw t
;;                                 :valid-syntax t)))

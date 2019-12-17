; RP-REWRITER

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2019, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Mertcan Temel         <mert@utexas.edu>

(in-package "RP")

(include-book "../aux-functions")

(local
 (include-book "../proofs/aux-function-lemmas"))

(local
 (include-book "../proofs/proof-function-lemmas"))

(include-book "../eval-functions")

(include-book "../meta-rule-macros")

(local
 (include-book "../proofs/measure-lemmas"))

(encapsulate
  nil

  (defun assoc-eq-val (key alist)
    (declare (xargs :guard (and (symbolp key)
                                (alistp alist))))
    (cdr (assoc-eq key alist)))

  (defthm assoc-eq-val-nil
    (equal (assoc-eq-val key nil)
           nil))

  (defthm assoc-eq-val-cons-1
    (implies (not (equal key key2))
             (equal (assoc-eq-val key (cons (cons key2 val) rest))
                    (assoc-eq-val key rest))))

  (defthm assoc-eq-val-cons-2
    (equal (assoc-eq-val key (cons (cons key val) rest))
           val))

  (defun assoc-eq-vals (keys alist)
    (declare (xargs :guard (and (symbol-listp keys)
                                (alistp alist))))
    (if (atom keys)
        nil
      (cons (assoc-eq-val (car keys) alist)
            (assoc-eq-vals (cdr keys) alist))))

  (defthm assoc-eq-vals-cons
    (equal (assoc-eq-vals (cons key1 rest) alist)
           (cons (assoc-eq-val key1 alist)
                 (assoc-eq-vals rest alist))))

  (defthm assoc-eq-vals-nil
    (equal (assoc-eq-vals nil alist)
           nil))

  (defthmd assoc-eq-vals-def
    (equal (assoc-eq-vals keys alist)
           (if (atom keys)
               nil
             (cons (assoc-eq-val (car keys) alist)
                   (assoc-eq-vals (cdr keys) alist))))
    :hints (("Goal" :expand (assoc-eq-vals keys alist)
             :do-not-induct t))))

(defun resolve-assoc-eq-val-rec (key alist)
  (declare (xargs :guard t))
  (case-match alist
    (('cons ('cons ('quote key2) val)
            rest)
     (if (equal key key2)
         val
       (resolve-assoc-eq-val-rec key rest)))
    (('cons ('quote (key2 . val)) ;; when val is nil
            rest)
     (if (equal key2 key)
         (list 'quote val)
       (resolve-assoc-eq-val-rec key rest)))
    (''nil
     ''nil)
    (('quote ((key1 . val1) . rest1))
     (if (equal key key1)
         (list 'quote val1)
       (resolve-assoc-eq-val-rec key `',rest1)))
    (& `(assoc-eq-val (quote ,key) ,alist))))

(defund hons-get-meta (term)
  (declare (xargs :guard t))
  (case-match term
    (('hons-get ('quote key) falist)
     (b* ((falist (ex-from-rp falist)))
       (case-match falist
         (('falist ('quote fast-alist) &)
          (b* ((entry (hons-get key fast-alist)))
            (mv (if entry
                    `(cons ',(car entry) ,(cdr entry))
                  ''nil)
                t)))
         (&
          (progn$
           (mv term `(nil t t)))))))
    (&
     (progn$
      (mv term nil)))))

(defun resolve-assoc-eq-vals-rec (keys alist)
  (declare (xargs :guard t))
  (case-match keys
    (('cons ('quote e) rest)
     (list 'cons
           (resolve-assoc-eq-val-rec e alist)
           (resolve-assoc-eq-vals-rec rest alist)))
    ((quote 'nil)
     ''nil)
    (('quote 'nil)
     ''nil)
    (('quote . x)
     (if (and (consp x)
              (consp (car x)))
         (list
          'cons
          (resolve-assoc-eq-val-rec (caar x)
                                    alist)
          (resolve-assoc-eq-vals-rec (list 'quote (cdar x))
                                     alist))
       ''nil))
    (&
     `(assoc-eq-vals ,keys ,alist))))

(defun resolve-assoc-eq-vals (term)
  (declare (xargs :guard t))
  (case-match term
    (('assoc-eq-vals keys alist)
     (b* ((res (resolve-assoc-eq-vals-rec keys alist)))
       res))
    (& term)))

(defun hons-get-list-values-term (keys falist)
  (declare (xargs
            :guard t
            :measure (cons-count keys)
            :hints (("Goal"
                     :in-theory (e/d (measure-lemmas) ())))))
  (if (atom keys)
      ''nil
    (b* ((entry (hons-get (car keys) falist)))
      `(cons ,(if (consp entry) (cdr entry) ''nil)
             ,(hons-get-list-values-term
               (cdr keys)
               falist)))))

(defund assoc-eq-vals-meta (term)
  (declare (xargs :guard t))
  (case-match term
    (('assoc-eq-vals ('quote keys) falist)
     (b* ((falist (ex-from-rp falist)))
       (case-match falist
         (('falist ('quote fast-alist) &)
          (mv (hons-get-list-values-term keys fast-alist) t))
         (& (mv (resolve-assoc-eq-vals term) t)))))
    (& (mv (resolve-assoc-eq-vals term) t))))

(def-formula-checks-default-evl
  rp-evl
  (strip-cars *small-evl-fncs*))

(def-formula-checks
  hons-get-meta-formula-checks
  (hons-get
   hons-get-meta
   assoc-eq-vals
   assoc-equal
   assoc-eq-val
   assoc-eq-vals
   resolve-assoc-eq-val-rec
   resolve-assoc-eq-vals-rec
   resolve-assoc-eq-vals
   assoc-eq-vals-meta))

(local
 (defthm rp-termp-hons-get-falist
   (implies (and (falist-syntaxp falist)
                 (consp (hons-get key falist)))
            (rp-termp (cdr (hons-get key falist))))))

(local
 (in-theory (disable (:DEFINITION ACL2::APPLY$-BADGEP)
                     (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                     (:DEFINITION TRUE-LISTP)
                     (:DEFINITION SUBSETP-EQUAL)
                     (:DEFINITION MEMBER-EQUAL)
                     (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                     (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1)
                     (:REWRITE DEFAULT-CDR)
                     (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                     (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                     (:REWRITE DEFAULT-CAR)
                     (:TYPE-PRESCRIPTION MEMBER-EQUAL)
                     (:DEFINITION NATP)
                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-3)
                     (:REWRITE
                      ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-2))))

(local
 (encapsulate
   nil

   (local
    (defthm lemma1
      (implies (and (rp-termp term)
                    (is-falist (ex-from-rp term)))
               (falist-consistent-aux (cadr (cadr (ex-from-rp term)))
                                      (caddr (ex-from-rp term))))))
   (local
    (defthm lemma2
      (implies (and (rp-termp term)
                    (is-falist (ex-from-rp term)))
               (rp-termp
                (caddr (ex-from-rp term))))))

   (defthm rp-termp-resolve-assoc-eq-val-rec
     (implies (and ;(rp-termp key)
               (rp-termp alist))
              (rp-termp (resolve-assoc-eq-val-rec key alist)))
     :hints (("Goal"
              :induct (resolve-assoc-eq-val-rec key alist)
              :do-not-induct t
              :in-theory (e/d (resolve-assoc-eq-val-rec)
                              ((:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE RP-TERMP-IMPLIES-CDR-LISTP)
                               (:DEFINITION TRUE-LISTP)
                               (:TYPE-PRESCRIPTION RP-TERMP)
                               (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE IS-IF-RP-TERMP)
                               (:REWRITE DEFAULT-CAR)
                               (:TYPE-PRESCRIPTION ACL2::APPLY$-BADGEP))))))

   (defthm rp-termp-hons-get-meta
     (implies (and (rp-termp term))
              (rp-termp (mv-nth 0 (hons-get-meta term))))
     :hints (("goal"
              :do-not-induct t
              :use ((:instance falist-consistent-implies-falist-syntaxp
                               (term (caddr (ex-from-rp (caddr term))))
                               (falist (cadr (cadr (ex-from-rp (caddr term)))))))
              :in-theory (e/d (hons-get-meta)
                              (hons-get
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE RP-TERMP-IMPLIES-SUBTERMS)
                               (:DEFINITION SUBSETP-EQUAL)
                               (:DEFINITION MEMBER-EQUAL)
                               (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:REWRITE
                                ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-1))))))

   (defthm rp-termp-resolve-assoc-eq-vals-rec
     (implies (and (rp-termp keys)
                   (rp-termp alist))
              (rp-termp (resolve-assoc-eq-vals-rec keys alist)))
     :hints (("Goal"
              :do-not-induct t
              :induct (resolve-assoc-eq-vals-rec keys alist)
              :in-theory (e/d (RESOLVE-ASSOC-EQ-VALS-REC) ()))))

   (local
    (defthm rp-termp-hons-get-list-values-term-1
      (implies (and (falist-syntaxp falist))
               (rp-termp (hons-get-list-values-term
                               keys
                               falist)))
      :otf-flg t
      :hints (("Goal" :in-theory (e/d (HONS-GET-LIST-VALUES-TERM)
                                      (hons-get))))))

   (local
    (defthm lemma3-lemma
      (implies (and (rp-termp term)
                    (case-match term
                      (('assoc-eq-vals ('quote &) falist)
                       (b* ((falist (ex-from-rp falist)))
                         (case-match falist
                           (('falist ('quote &) &) t) (& nil))))
                      (& nil)))
               (rp-termp (EX-FROM-RP (CADDR TERM))))))

   
   (local
    (defthm lemma3
      (implies (and 
                    (rp-termp term)
                    (case-match term
                      (('assoc-eq-vals ('quote &) falist)
                       (b* ((falist (ex-from-rp falist)))
                         (case-match falist
                           (('falist ('quote &) &) t) (& nil))))
                      (& nil)))
               (falist-syntaxp (cadr (cadr (ex-from-rp (caddr term))))))
      :otf-flg t
      :hints (("Goal"
               :use ((:instance lemma3-lemma))
               :in-theory (e/d (ex-from-rp is-rp is-falist)
                               (lemma3-lemma
                                (:DEFINITION FALIST-SYNTAXP)
                                (:TYPE-PRESCRIPTION O<)
                                (:TYPE-PRESCRIPTION RP-TERMP)
                                (:REWRITE ACL2::O-P-O-INFP-CAR)
                                
                                (:TYPE-PRESCRIPTION O-P)
                                (:REWRITE DEFAULT-CDR)
                                (:REWRITE DEFAULT-CAR)))))))

   (local
    (defthm rp-termp-hons-get-list-values-term-main
      (implies
       (and (rp-termp term)
            (case-match term
              (('assoc-eq-vals ('quote &) falist)
               (b* ((falist (ex-from-rp falist)))
                 (case-match falist
                   (('falist ('quote &) &) t) (& nil))))
              (& nil)))
       (rp-termp
        (hons-get-list-values-term (cadr (cadr term))
                                   (cadr (cadr (ex-from-rp (caddr term)))))))
      :hints (("goal" :in-theory (enable hons-get-list-values-term)))))

   (defthm rp-termp-assoc-eq-vals-meta
     (implies (and (rp-termp term))
              (rp-termp (mv-nth 0 (assoc-eq-vals-meta term))))
     :hints (("Goal"
              :in-theory (e/d ( assoc-eq-vals-meta) ()))))))

(local
 (encapsulate
   nil
   (local
    (defthm falist-consistent-implies-for-fast-alist
      (implies
       (and (falist-consistent-aux falist term)
            (rp-termp term))
       (rp-term-listp (strip-cdrs falist)))
      :hints (("Goal" :in-theory (enable falist-consistent-aux)))))

   (local
    (defthm lemma1
      (implies (and (rp-term-listp (STRIP-CDRS FALIST))
                    (consp falist)
                    (HONS-ASSOC-EQUAL key FALIST))
               (rp-termp
                (CDR (HONS-ASSOC-EQUAL key FALIST))))))

   (local
    (defthm lemma1-2
      (implies (CONSP (HONS-ASSOC-EQUAL key FALIST))
               (consp falist))))

   (local
    (defthm lemma2
      (implies (and (rp-termp term)
                    (is-falist term))
               (rp-term-listp
                (strip-cdrs (cadr (cadr term)))))
      :hints (("goal"
               :in-theory (e/d () (ex-from-rp))))))

   (local
    (defthm lemma3
      (implies (and (rp-termp term)
                    (is-falist (ex-from-rp term)))
               (rp-term-listp
                (strip-cdrs (cadr (cadr (ex-from-rp term))))))
      :hints (("goal"
               :in-theory (e/d () (ex-from-rp))))))

   (defthm all-falist-consistent-resolve-assoc-eq-val-rec
     (implies (and ;(rp-termp key)
               (rp-termp alist))
              (rp-termp (resolve-assoc-eq-val-rec key alist)))
     :hints (("Goal"
              :in-theory (e/d (resolve-assoc-eq-val-rec)
                              ((:REWRITE DEFAULT-CAR)
                               (:REWRITE DEFAULT-CDR)
                               
                               (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                               (:TYPE-PRESCRIPTION QUOTEP))))))

   (defthm all-falist-consistent-resolve-assoc-eq-vals-rec
     (implies (and
               (rp-termp keys)
               (rp-termp alist))
              (rp-termp (resolve-assoc-eq-vals-rec keys alist)))
     :hints (("Goal"
              :in-theory (e/d (resolve-assoc-eq-vals-rec)
                              ((:REWRITE DEFAULT-CAR)
                               (:REWRITE DEFAULT-CDR)
                               
                               (:REWRITE ACL2::FN-CHECK-DEF-NOT-QUOTE)
                               (:TYPE-PRESCRIPTION QUOTEP))))))

   (local
    (defthm hons-get-list-values-term-returns-all-falist-consistent
      (implies (rp-term-listp (strip-cdrs falist))
               (rp-termp
                (hons-get-list-values-term keys falist)))
      :otf-flg t
      :hints (("Goal"
               :in-theory (enable hons-get-list-values-term
                                  HONS-ASSOC-EQUAL)))))

   (local
    (defthm all-falist-consistent-hons-get-list-values-term
      (implies (and (is-honsed-assoc-eq-values term)
                    (rp-termp term))
               (rp-termp
                (hons-get-list-values-term (cadr (cadr term))
                                           (cadr (cadr (caddr term))))))
      :hints (("goal"
               :in-theory (enable is-honsed-assoc-eq-values

                                  rp-termp)))))

   (defthm all-falist-consistent-assoc-eq-vals-meta
     (implies (and (rp-termp term)
                   )
              (rp-termp (mv-nth 0 (assoc-eq-vals-meta term))))
     :hints (("Goal"
              :in-theory (e/d ( assoc-eq-vals-meta) ()))))

   (defthm all-falist-consistent-hons-get-meta
     (implies (and (rp-termp term))
              (rp-termp (mv-nth 0 (hons-get-meta term))))
     :hints (("goal"
              :in-theory (e/d (hons-get-meta) ()))))))

(local
 (defthmd rp-evlt-of-ex-from-rp
   (equal (rp-evlt (ex-from-rp term) a)
          (rp-evlt term a))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp is-rp) ())))))

(local
 (encapsulate
   nil

   (local
    (defthm resolve-assoc-eq-val-rec-correct
      (implies (and ;(rp-termp alist)
                (rp-evl-meta-extract-global-facts)
                (hons-get-meta-formula-checks state))
               (equal (rp-evlt (resolve-assoc-eq-val-rec key alist) a)
                      (assoc-eq-val key (rp-evlt alist a))))
      :hints (("Goal" :in-theory (e/d (assoc-eq-val)
                                      ((:REWRITE
                                        RP-TERMP-IMPLIES-CDR-LISTP)
                                       (:REWRITE
                                        RP-TERMP-IMPLIES-SUBTERMS)
                                       (:REWRITE DEFAULT-CDR)))))))

   (local
    (defthm resolve-assoc-eq-vals-rec-correct
      (implies (and ;(rp-termp alist)
;(rp-termp keys)
                (rp-evl-meta-extract-global-facts)
                (hons-get-meta-formula-checks state))
               (equal (rp-evlt (resolve-assoc-eq-vals-rec keys alist) a)
                      (assoc-eq-vals (rp-evlt keys a) (rp-evlt alist a))))
      :hints (("Goal" :in-theory (e/d (assoc-eq-vals)
                                      ((:REWRITE
                                        RP-TERMP-IMPLIES-CDR-LISTP)
                                       (:REWRITE
                                        RP-TERMP-IMPLIES-SUBTERMS)
                                       (:REWRITE DEFAULT-CDR)))))))

   (local
    (defthm lemma1
      (implies (hons-get key alist)
               (equal (car (hons-get key alist))
                      key))))

   (local
    (defthm lemma2
      (implies (hons-get key alist)
               (equal (cons key (cdr (hons-get key alist)))
                      (hons-get key alist)))))

   (local
    (defthm lemma4
      (implies (and (rp-termp term)
                    (is-falist (ex-from-rp term)))
               (falist-consistent-aux (cadr (cadr (ex-from-rp term)))
                                      (caddr (ex-from-rp term))))))

   (local
    (defthm lemma5
      (implies (hons-get key a2)
               (equal (equal (cons key a1)
                             (hons-get key a2))
                      (equal a1 (cdr (hons-get key a2)))))))

   (local
    (defthm assoc-equal-is-hons-get
      (implies (alistp alist)
               (equal (assoc-equal key alist)
                      (hons-get key alist)))))

   (local
    (defthm lemma8
      (implies (and (hons-get key alist))
               (equal (cons key (cdr (hons-get key alist)))
                      (hons-get key alist)))
      :hints (("Goal"
               :in-theory (e/d (HONS-ASSOC-EQUAL) ())))))

   (local
    (defthmd lemma9
      (implies (syntaxp (equal term 'term))
               (equal (rp-evlt (caddr term) a)
                      (rp-evlt (ex-from-rp (caddr term)) a)))
      :hints (("Goal"
               :in-theory (e/d (rp-evlt-of-ex-from-rp) ())))))

   (local
    (defthm lemma10
      (implies (and (HONS-GET key falist)
                    (FALIST-CONSISTENT-AUX falist term))
               (HONS-GET key (RP-EVLt term A)))))

   (local
    (defthm lemma10-5
      (implies (and (not (HONS-GET key falist))
                    (FALIST-CONSISTENT-AUX falist term))
               (not (HONS-GET key (RP-EVLt term A))))))

   (local
    (defthm lemma11
      (implies (and (FALIST-CONSISTENT-AUX falist term))
               (ALISTP (RP-EVLt term A)))))

   (local
    (defthm lemma12
      (implies (and (rp-termp term)
                    (is-falist term))
               (ALISTP (RP-EVLt (CADDR term) A)))))

   (local
    (defthmd rp-evlt-of-term-is-hons-get
      (implies (and (rp-evl-meta-extract-global-facts)
                    (hons-get-meta-formula-checks state)
                    (equal (car term) 'hons-get)
                    (CONSP TERM)
                    (CONSP (CDR TERM))
                    (CONSP (CDDR TERM))
                    (NOT (CDDDR TERM)))
               (equal (rp-evlt term a)
                      (hons-get (rp-evlt (cadr term) a)
                                (rp-evlt (caddr term) a))))
      :hints (("Goal"
               :use ((:instance
                      RP-EVL-OF-HONS-GET-WHEN-HONS-GET-META-FORMULA-CHECKS
                      (acl2::key (rp-trans (cadr term)))
                      (acl2::alist (rp-trans (caddr term)))
                      (acl2::env a)))
               :in-theory (e/d () (hons-get
                                   RP-EVL-OF-HONS-GET-WHEN-HONS-GET-META-FORMULA-CHECKS))))))

   (local
    (defthmd rp-evl-of-term-is-hons-get
      (implies (and (rp-evl-meta-extract-global-facts)
                    (hons-get-meta-formula-checks state)
                    (equal (car term) 'hons-get)
                    (CONSP TERM)
                    (CONSP (CDR TERM))
                    (CONSP (CDDR TERM))
                    (NOT (CDDDR TERM)))
               (equal (rp-evl term a)
                      (hons-get (rp-evl (cadr term) a)
                                (rp-evl (caddr term) a))))
      :hints (("Goal"
               :use ((:instance
                      RP-EVL-OF-HONS-GET-WHEN-HONS-GET-META-FORMULA-CHECKS
                      (acl2::key (cadr term))
                      (acl2::alist (caddr term))
                      (acl2::env a)))
               :in-theory (e/d () (hons-get
                                   RP-EVL-OF-HONS-GET-WHEN-HONS-GET-META-FORMULA-CHECKS))))))

   (defthm hons-get-is-resolve-assoc-eq-value-rec
     (implies
      (and (falist-consistent-aux falist term)
           (hons-get key falist))
      (equal (hons-get key falist)
             (cons key (resolve-assoc-eq-val-rec key term)))))

   (local
    (defthm lemma13
      (implies (AND (FALIST-CONSISTENT-AUX (CADR (CADR (EX-FROM-RP (CADDR TERM))))
                                           (CADDR (EX-FROM-RP (CADDR TERM))))
                    (HONS-GET (CADR (CADR TERM))
                              (CADR (CADR (EX-FROM-RP (CADDR TERM))))))
               (equal (HONS-GET (CADR (CADR TERM))
                                (CADR (CADR (EX-FROM-RP (CADDR TERM)))))
                      (CONS (CADR (CADR TERM))
                            (RESOLVE-ASSOC-EQ-VAL-REC (CADR (CADR TERM))
                                                      (CADDR (EX-FROM-RP (CADDR TERM)))))))
      :hints (("Goal"
               :use ((:instance hons-get-is-resolve-assoc-eq-value-rec
                                (falist (cadr (cadr (ex-from-rp (caddr term)))))
                                (key (cadr (cadr term)))
                                (term (caddr (ex-from-rp (caddr term))))))
               :in-theory (e/d () (hons-get))))))

   (defthm rp-evl-of-hons-get-rp-meta
     (implies (and (rp-termp term)
                   (rp-evl-meta-extract-global-facts)
                   (hons-get-meta-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (hons-get-meta term)) a)
                     (rp-evlt term a)))
     :otf-flg t
     :hints (("goal"
              :in-theory (e/d (hons-get-meta
                               lemma9
                               rp-evl-of-term-is-hons-get)
                              (hons-get
                               rp-evlt-of-ex-from-rp
                               RP-EVL-OF-HONS-GET-WHEN-HONS-GET-META-FORMULA-CHECKS)))))

   (local
    (defthmd rp-evlt-of-term-is-assoc-eq-vals
      (implies (and (rp-evl-meta-extract-global-facts)
                    (hons-get-meta-formula-checks state)
                    (equal (car term) 'assoc-eq-vals)
                    (CONSP TERM)
                    (CONSP (CDR TERM))
                    (CONSP (CDDR TERM))
                    (NOT (CDDDR TERM)))
               (equal (rp-evlt term a)
                      (assoc-eq-vals (rp-evlt (cadr term) a)
                                     (rp-evlt (caddr term) a))))
      :hints (("Goal"
               :in-theory (e/d
                           (RP-EVL-OF-assoc-eq-vals-WHEN-HONS-GET-META-FORMULA-CHECKS)
                           (hons-get))))))

   (local
    (defthmd rp-evl-of-term-is-assoc-eq-vals
      (implies (and (rp-evl-meta-extract-global-facts)
                    (hons-get-meta-formula-checks state)
                    (equal (car term) 'assoc-eq-vals)
                    (CONSP TERM)
                    (CONSP (CDR TERM))
                    (CONSP (CDDR TERM))
                    (NOT (CDDDR TERM)))
               (equal (rp-evl term a)
                      (assoc-eq-vals (rp-evl (cadr term) a)
                                     (rp-evl (caddr term) a))))
      :hints (("Goal"
               :in-theory (e/d
                           (RP-EVL-OF-assoc-eq-vals-WHEN-HONS-GET-META-FORMULA-CHECKS)
                           (hons-get))))))

   (local
    (defthm hons-get-is-resolve-assoc-eq-value-rec-not-consp
      (implies
       (and (falist-consistent-aux falist term)
            (rp-termp term)
            (not (hons-get key falist)))
       (equal (assoc-eq-val key (rp-evlt term a))
              nil))))

   (local
    (defthm lemma14-2
      (implies (and (FALIST-CONSISTENT-AUX FALIST TERM)
                    )
               (CONSP TERM))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (falist-consistent-aux) ())))))

   (local
    (defthm rp-evl-of-hons-get-list-values-term-lemma
      (implies (and (falist-consistent-aux falist term)
                    (rp-termp term)
                    (rp-evl-meta-extract-global-facts)
                    (hons-get-meta-formula-checks state))
               (equal (rp-evlt (hons-get-list-values-term keys falist) a)
                      (assoc-eq-vals keys (rp-evlt term a))))
      :hints (("Goal"
               :expand (ASSOC-EQ-VALS KEYS (RP-EVLt TERM A))
               :in-theory
               (e/d (RESOLVE-ASSOC-EQ-VAL-REC-CORRECT)
                    (hons-get
                     resolve-assoc-eq-vals-rec-correct
                     falist-consistent-aux
                     assoc-eq-vals-cons
                     assoc-eq-vals-nil
                     assoc-eq-val))))))

   (defthm falist-consistent-aux-lemma1
     (implies (and (rp-termp term)
                   (case-match term
                     (('assoc-eq-vals ('quote &) falist)
                      (b* ((falist (ex-from-rp falist)))
                        (case-match falist
                          (('falist ('quote &) &) t) (& nil))))
                     (& nil)))

              (falist-consistent-aux (CADR (CADR (EX-FROM-RP (CADDR
                                                              TERM))))
                                     (CAdDR (EX-FROM-RP (CADDR TERM))))))

   (local
    (defthm lemma15
      (implies (and (rp-termp term)
                    (case-match term
                      (('assoc-eq-vals ('quote &) falist)
                       (b* ((falist (ex-from-rp falist)))
                         (case-match falist
                           (('falist ('quote &) &) t) (& nil))))
                      (& nil)))
               (RP-TERMP (CADDR (EX-FROM-RP (CADDR TERM)))))
      :hints (("Goal"
               :use ((:instance EXTRACT-FROM-RP-PSEUDO-TERM-LISTP
                                (term (CADDR TERM))))
               :in-theory (e/d (ex-from-rp is-rp)
                               (EXTRACT-FROM-RP-PSEUDO-TERM-LISTP))))))

   (defthm rp-evl-of-assoc-eq-vals-meta
     (implies (and (rp-termp term)
                   (rp-termp term)
                   (rp-evl-meta-extract-global-facts)
                   (hons-get-meta-formula-checks state))
              (equal (rp-evlt (mv-nth 0 (assoc-eq-vals-meta term)) a)
                     (rp-evlt term a)))
     :hints (("goal"
              :use ((:instance rp-evl-of-hons-get-list-values-term-lemma
                               (keys  (CADR (CADR TERM)))
                               (term (CADDR (EX-FROM-RP (CADDR TERM))))
                               (falist (CADR (CADR (EX-FROM-RP (CADDR
                                                                TERM)))))))
              :in-theory (e/d (ASSOC-EQ-VALS-META
                               lemma9
                               assoc-eq-vals
                               rp-evl-of-term-is-assoc-eq-vals)
                              (hons-get
                               rp-evl-of-hons-get-list-values-term-lemma
                               rp-evl-of-ex-from-rp
                               RP-EVL-OF-assoc-eq-vals-WHEN-HONS-GET-META-FORMULA-CHECKS)))))))

(local
 (encapsulate
   nil

   (local
    (defthm valid-sc-resolve-assoc-eq-val-rec
      (implies (valid-sc alist a)
               (valid-sc (resolve-assoc-eq-val-rec key alist) a))
      :hints (("Goal"
               :in-theory (e/d (resolve-assoc-eq-val-rec
                                is-rp
                                is-if)
                               ())))))
   (local
    (defthm valid-sc-resolve-assoc-eq-vals-rec
      (implies (and (valid-sc alist a)
                    (valid-sc keys a))
               (valid-sc (resolve-assoc-eq-vals-rec keys alist) a))
      :hints (("Goal"
               :in-theory (e/d (resolve-assoc-eq-vals-rec
                                is-rp
                                is-if)
                               ())))))

   (local
    (defthm lemma1
      (implies (and (valid-sc term a)
                    (is-honsed-assoc-eq-values term))
               (valid-sc (caddr (caddr term)) a))
      :hints (("goal"
; :expand ((valid-sc term a))
               :in-theory (e/d (is-if is-rp is-falist)
                               ())))))

   (local
    (defthm lemma2
      (implies (and (is-falist term)
                    (valid-sc term a))
               (valid-sc (caddr term) a))
      :hints (("Goal"
               :expand (valid-sc (caddr term) a)
               :in-theory (e/d (is-if is-rp) (ex-from-rp))))))

   (local
    (defthm lemma3
      (IMPLIES
       (and (rp-termp term)
            (is-falist term))
       (FALIST-CONSISTENT-AUX (CADR (CADR term))
                              (CADDR term)))))

   (defthm valid-sc-cdr-hons-equal-falist-consistent-aux
     (implies
      (valid-sc term-alist a)
      (valid-sc (resolve-assoc-eq-val-rec key term-alist) a))
     :hints (("Goal"
              :in-theory (e/d (is-if
                               is-rp) ()))))

   (local
    (defthm valid-sc-hons-get-rp-meta-lemma
      (implies (and (valid-sc term a)
                    (falist-consistent-aux falist term))
               (valid-sc (cdr (hons-get key falist)) a))
      :hints (("Goal"
               :cases ((hons-get key falist))
               :use ((:instance hons-get-is-resolve-assoc-eq-value-rec))
               :in-theory (e/d (is-rp is-if)
                               (hons-get
                                hons-get-is-resolve-assoc-eq-value-rec))))))

   (defthm valid-sc-hons-get-rp-meta
     (implies (and (valid-sc term a)
                   (rp-termp term))
              (valid-sc (mv-nth 0 (hons-get-meta term)) a))
     :hints (("Goal"
              :use ((:instance valid-sc-hons-get-rp-meta-lemma
                               (falist (CADR (CADR (EX-FROM-RP (CADDR TERM)))))
                               (key (CADR (CADR TERM)))
                               (term  (CAdDR (EX-FROM-RP (CADDR TERM))))))
              :in-theory (e/d (hons-get-meta is-rp is-if)
                              (hons-get
                               valid-sc-hons-get-rp-meta-lemma)))))

   (local
    (defthm valid-sc-hons-get-list-values-term-lemma
      (implies (and (valid-sc term-alist a)
                    (falist-consistent-aux falist term-alist))
               (valid-sc (hons-get-list-values-term keys falist)
                         a))
      :hints (("Goal"
               :in-theory (e/d (is-rp is-if) (hons-get))))))

   (defthm valid-sc-assoc-eq-vals-meta
     (implies (and (valid-sc term a)
                   (rp-termp term))
              (valid-sc (mv-nth 0 (assoc-eq-vals-meta term)) a))
     :hints (("Goal"
              :use ((:instance valid-sc-hons-get-list-values-term-lemma
                               (keys (CADR (CADR TERM)))
                               (falist (CADR (CADR (EX-FROM-RP (CADDR TERM)))))
                               (term-alist (CAdDR (EX-FROM-RP (CADDR TERM))))))
              :in-theory (e/d (assoc-eq-vals-meta is-if is-rp) ()))))))

#|(local
 (encapsulate
   nil

   (local
    (defthm rp-syntaxp-resolve-assoc-eq-val-rec
      (implies (rp-syntaxp alist)
               (rp-syntaxp (resolve-assoc-eq-val-rec key alist)))
      :hints (("Goal"
               :in-theory (e/d (resolve-assoc-eq-val-rec
                                is-rp)
                               ())))))

   (local
    (defthm rp-syntaxp-resolve-assoc-eq-vals-rec
      (implies (and (rp-syntaxp alist)
                    (rp-syntaxp keys))
               (rp-syntaxp (resolve-assoc-eq-vals-rec keys alist)))
      :hints (("Goal"
               :in-theory (e/d (resolve-assoc-eq-vals-rec
                                is-rp)
                               ())))))

   (local
    (defthm lemma1
      (implies (and (is-falist term)
                    (rp-syntaxp term))
               (rp-syntaxp (caddr term)))
      :hints (("goal"
               :expand (valid-sc (caddr term) a)
               :in-theory (e/d (is-if is-rp) (ex-from-rp))))))

   (DEFTHM LEMMA2
     (IMPLIES (AND (ALL-FALIST-CONSISTENT TERM)
                   (IS-FALIST TERM))
              (FALIST-CONSISTENT-AUX (CADR (CADR TERM))
                                     (CADDR TERM))))

   (local
    (defthm rp-syntaxp-hons-get-meta-lemma
      (implies (and (rp-syntaxp term)
                    (falist-consistent-aux falist term))
               (rp-syntaxp (cdr (hons-get key falist))))
      :hints (("goal"
               :cases ((hons-get key falist))
               :use ((:instance hons-get-is-resolve-assoc-eq-value-rec))
               :in-theory (e/d (is-rp is-if)
                               (hons-get
                                hons-get-is-resolve-assoc-eq-value-rec))))))

   (defthm rp-syntaxp-hons-get-meta
     (implies (and (all-falist-consistent term)
                   (rp-syntaxp term))
              (rp-syntaxp (mv-nth 0 (hons-get-meta term))))
     :hints (("goal"
              :use ((:instance rp-syntaxp-hons-get-meta-lemma
                               (falist (cadr (cadr (ex-from-rp (caddr term)))))
                               (key (cadr (cadr term)))
                               (term  (caddr (ex-from-rp (caddr term))))))
              :in-theory (e/d (hons-get-meta) (hons-get)))))

   (local
    (defthm rp-syntaxp-hons-get-list-values-term-lemma
      (implies (and (rp-syntaxp term-alist)
                    (falist-consistent-aux falist term-alist))
               (rp-syntaxp (hons-get-list-values-term keys falist)))
      :hints (("goal"
               :in-theory (e/d (is-rp is-if) (hons-get))))))

   (defthm rp-state-assoc-eq-vals-meta
     (implies (and (all-falist-consistent term)
                   (rp-syntaxp term))
              (rp-syntaxp (mv-nth 0 (assoc-eq-vals-meta term))))
     :hints (("Goal"
              :use  ((:instance rp-syntaxp-hons-get-list-values-term-lemma
                                (keys (CADR (CADR TERM)))
                                (falist (CADR (CADR (EX-FROM-RP (CADDR TERM)))))
                                (term-alist (CAdDR (EX-FROM-RP (CADDR TERM))))))
              :in-theory (e/d (assoc-eq-vals-meta) ()))))))||#

(local
 (defthm dont-rw-syntaxp-hons-get-meta
   (dont-rw-syntaxp (mv-nth 1 (hons-get-meta term)))
   :hints (("Goal"
            :in-theory (e/d (DONT-RW-SYNTAXP
                             hons-get-meta)
                            ())))))

(local
 (defthm dont-rw-syntaxp-assoc-eq-vals-meta
   (dont-rw-syntaxp (mv-nth 1 (assoc-eq-vals-meta term)))
   :hints (("Goal"
            :in-theory (e/d (DONT-RW-SYNTAXP
                             assoc-eq-vals-meta)
                            ())))))

(defthm hons-get-meta-is-valid-rp-meta-rulep
  (implies (and (hons-get-meta-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'hons-get-meta
                             :trig-fnc 'hons-get
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (RP-TERMP
                            hons-get-meta
                            VALID-SC)))))

(defthm assoc-eq-vals-meta-is-valid-rp-meta-rulep
  (implies (and (hons-get-meta-formula-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'assoc-eq-vals-meta
                             :trig-fnc 'assoc-eq-vals
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP)
                           (RP-TERMP
                            assoc-eq-vals-meta
                            VALID-SC)))))

(rp::add-meta-rules
 hons-get-meta-formula-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'hons-get-meta
        :trig-fnc 'hons-get
        :dont-rw t
        :valid-syntax t)

  (make rp-meta-rule-rec
        :fnc 'assoc-eq-vals-meta
        :trig-fnc 'assoc-eq-vals
        :dont-rw t
        :valid-syntax t)))

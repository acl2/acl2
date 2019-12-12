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
(include-book "../rp-rewriter")
(include-book "aux-function-lemmas")
(include-book "local-lemmas")
(include-book "proof-functions")
(include-book "rp-equal-lemmas")
(include-book "proof-function-lemmas")

(make-flag rp-apply-bindings :defthm-macro-name defthm-apply-bindings)

(in-theory (disable rp-iff-flag rp-lhs rp-rhs rp-hyp))

(local
 (in-theory (disable (:DEFINITION SUBSETP-EQUAL))))



(encapsulate
  nil
  ;; rp-apply-bindings returns rp-termp

  #|(local
  (defthm lemma1
  (implies (and (pseudo-term-listp (strip-cdrs bindings))
  (alistp bindings))
  (pseudo-termp (cdr (assoc-equal term bindings))))))||#

  #|(local
  (defthm lemma2
  (implies (and (pseudo-term-listp lst)
  (not (equal s 'quote))
  (symbolp s))
  (pseudo-termp (cons s lst)))))||#

  #|(local
  (defthm lemma3
  (implies (and (pseudo-termp term)
  (not (equal (car term) 'quote))
  (consp term)
  (atom (car term)))
  (symbolp (car term)))))||#

  (defthm len-of-rp-apply-bindings-subterms-is-len-of-subterms
    (equal (len (rp-apply-bindings-subterms subterms bindings))
           (len subterms)))

  (local
   (defthm lemma1
     (implies (IS-RP (LIST 'RP TERM3 TERM5))
              (IS-RP (LIST 'RP
                           (RP-APPLY-BINDINGS TERM3 BINDINGS)
                           (RP-APPLY-BINDINGS TERM5 BINDINGS))))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma2
     (implies (IS-RP (LIST 'RP term3 term4))
              (equal (RP-APPLY-BINDINGS TERM3 BINDINGS)
                     term3))
     :hints (("Goal"
              :do-not-induct t
              :in-theory (e/d (is-rp) ())))))


  (defthm-apply-bindings
    (defthm rp-apply-bindings-is-rp-termp
      (implies (and (rp-termp term)
                    (not (include-fnc term 'falist))
                    (bindings-alistp bindings))
               (rp-termp (rp-apply-bindings term bindings)))
      :flag rp-apply-bindings)

    (defthm rp-apply-bindings-subterms-is-rp-termp
      (implies (and (rp-term-listp subterms)
                    (not (include-fnc-subterms subterms 'falist))
                    (bindings-alistp bindings))
               (rp-term-listp (rp-apply-bindings-subterms subterms bindings)))
      :flag rp-apply-bindings-subterms)
    :hints (("Goal"
             :in-theory (e/d (IS-RP-IMPLIES-FC is-rp) (FALIST-CONSISTENT))))))



(defthm rp-evlt-cons
  (implies (and (case-split (is-falist (cons x y))))
           (equal (rp-evl (rp-trans (cons x y)) a)
                  (rp-evl (rp-trans (cadr y)) a))))


(encapsulate
  nil

  (defun rp-trans-bindings (bindings)
    (if (atom bindings)
        nil
      (acons (caar bindings)
             (rp-trans (cdar bindings))
             (rp-trans-bindings (cdr bindings)))))
  (local
   (defthm lemma1
     (implies (alistp bindings)
              (equal (CONSP (ASSOC-EQUAL TERM (RP-TRANS-BINDINGS BINDINGS)))
                     (CONSP (ASSOC-EQUAL TERM BINDINGS))))))

  (local
   (defthm lemma2
     (IMPLIES (AND (ALISTP BINDINGS)
                   (CONSP (ASSOC-EQUAL TERM BINDINGS)))
              (EQUAL (RP-TRANS (CDR (ASSOC-EQUAL TERM BINDINGS)))
                     (CDR (ASSOC-EQUAL TERM (RP-TRANS-BINDINGS BINDINGS)))))))

  (defthm-apply-bindings
    (defthm rp-trans-of-rp-apply-bindings
      (implies (and (not (include-fnc term 'list))
                    (alistp bindings))
               (equal (rp-evlt (rp-apply-bindings term bindings) a)
                      (rp-evl (rp-apply-bindings term
                                                 (rp-trans-bindings bindings))
                              a)))
      :flag rp-apply-bindings)
    (defthm rp-trans-lst-of-rp-apply-bindings-subterms
      (implies (and (not (include-fnc-subterms subterms 'list))
                    (alistp bindings))
               (equal (rp-evlt-lst (rp-apply-bindings-subterms subterms
                                                               bindings)
                                   a)
                      (rp-evl-lst (rp-apply-bindings-subterms subterms
                                                              (rp-trans-bindings bindings))
                                  a)))
      :flag rp-apply-bindings-subterms)
    :hints (("Goal"
             :in-theory (e/d (rp-evl-of-fncall-args) ())))
    :otf-flg t))


(encapsulate
  nil

  ;; rule for
  ;; (equal (rp-evl (rp-apply-bindings term bindings) a)
  ;;        (rp-evl term (bind-bindings bindings a)))

  (defun bind-bindings-aux (b1 b2)
    (declare (ignorable b1 b2))
    (if (atom b1)
        nil
      (cons (cons (caar b1) (rp-evl (cdar b1) b2))
            (bind-bindings-aux (cdr b1) b2))))

  (defmacro bind-bindings (b1 b2)
    `(append (bind-bindings-aux ,b1 ,b2) ,b2))

  (local
   (defthm lemma1
     (implies (and (not (consp (assoc-equal term bindings)))
                   (alistp bindings))
              (not (consp (assoc-equal term (bind-bindings-aux bindings a)))))))

  (local
   (defthm lemma2
     (implies (and
               ;(not (consp term))
               ;(symbolp term)
               ;term
               ;(alistp a)
               ;(alistp bindings)
               ;(symbol-listp (strip-cars bindings))
               ;(rp-term-listp (strip-cdrs bindings))
               (consp (assoc-equal term bindings))
               )
              (equal (rp-evl (cdr (assoc-equal term bindings))
                             a)
                     (cdr (assoc-equal term
                                       (append (bind-bindings-aux bindings a)
                                               a)))))))

  (local
   (defthm lemma3

     #|(implies
       (and (rp-term-listp (strip-cdrs bindings))
            (not (consp (assoc-equal term bindings))))
       (equal (equal (cdr (assoc-equal term a))
                     (cdr (assoc-equal term
                                       (append (bind-bindings-aux bindings a)
                                               a))))
              t))||#
     
     (implies (and
               ;(not (consp term))
               ;(symbolp term)
               (or term
                   (rp-term-listp (strip-cdrs bindings)))
               ;(alistp a)
               ;(alistp bindings)
               ;(symbol-listp (strip-cars bindings))
               #|(rp-term-listp (strip-cdrs bindings))||#
               (not (consp (assoc-equal term bindings))))
              (equal (equal (cdr (assoc-equal term a))
                            (cdr (assoc-equal term
                                              (append (bind-bindings-aux bindings a)
                                                      a))))
                     t))))

  #|(local
   (defthm lemma3-v2
     (implies (and
               (not (consp term))
               (rp-term-listp (strip-cdrs bindings))
               (not (consp (assoc-equal term bindings)))
               (case-split (equal term nil)))
              (equal (equal (rp-evl term a)
                            (rp-evl term
                                    (append (bind-bindings-aux bindings a)
                                            a)))
                     t))
     :hints (("goal"
              :in-theory (e/d () ())))))||#

  (local
   (defthm lemma4
     (implies (and (consp term)
                   (not (equal (car term) 'quote))
                   (equal (rp-evl-lst (rp-apply-bindings-subterms (cdr term)
                                                                  bindings)
                                      a)
                          (rp-evl-lst (cdr term)
                                      (append (bind-bindings-aux bindings a)
                                              a))))
              (equal (equal (rp-evl (cons (car term)
                                          (rp-apply-bindings-subterms (cdr term)
                                                                      bindings))
                                    a)
                            (rp-evl term
                                    (append (bind-bindings-aux bindings a)
                                            a)))
                     t))
     :hints (("goal" :in-theory (enable rp-evl-of-fncall-args)))))

  (local
   (defthm lemma5
     (implies (and (consp term)
                   (not (equal (car term) 'quote))
                   (not (consp (cdr term))))
              (equal (rp-evl (list (car term)) a)
                     (rp-evl term
                             (append (bind-bindings-aux bindings a)
                                     a))))
     :hints (("goal" :in-theory (enable rp-evl-of-fncall-args)))))

  (local
   (defthm lemma6
     (implies (and (consp term)
                   (not (equal 'quote (car term)))
                   (not (cdr term)))
              (equal (rp-evl (rp-apply-bindings term bindings)
                             a)
                     (rp-evl term
                             (append (bind-bindings-aux bindings a)
                                     a))))))

  (local
   (defthm lemma7
     (implies (consp subterms)
              (equal (rp-evl-lst (rp-apply-bindings-subterms subterms bindings)
                                 a)
                     (cons (rp-evl (rp-apply-bindings (car subterms)
                                                      bindings)
                                   a)
                           (rp-evl-lst (rp-apply-bindings-subterms (cdr subterms)
                                                                   bindings)
                                       a))))))

  (defthm-apply-bindings
    (defthm rp-apply-bindings-to-evl
      (implies (and (rp-termp term)
                    (bindings-alistp bindings))
               (and (equal (rp-evl (rp-apply-bindings term bindings) a)
                           (rp-evl term (bind-bindings bindings a)))))
      :flag rp-apply-bindings)

    (defthm rp-apply-bindings-subterms-to-evl-lst
      (implies (and (rp-term-listp subterms)
                    (bindings-alistp bindings))
               (and (equal (rp-evl-lst (rp-apply-bindings-subterms subterms bindings) a)
                           (rp-evl-lst subterms (bind-bindings bindings a)))))
      :flag rp-apply-bindings-subterms)
    :hints (("Goal"
             :expand ((RP-APPLY-BINDINGS TERM BINDINGS)
                      (RP-APPLY-BINDINGS-SUBTERMS NIL BINDINGS))
             :in-theory (e/d () (lambda-exp-free-listp
                                 rp-apply-bindings
                                 rp-apply-bindings-subterms
                                 lambda-exp-free-p))))
    :otf-flg t))





(defthm rp-apply-bindings-equiv-iff
  (implies (and (valid-rulep rule)
                (alistp a)
                (rp-evl (rp-apply-bindings (rp-hyp rule) bindings) a)
                (bindings-alistp bindings)
                (rp-iff-flag rule))
           (iff (rp-evl (rp-apply-bindings (rp-lhs rule) bindings) a)
                (rp-evl (rp-apply-bindings (rp-rhs rule) bindings) a)))
  :hints (("goal"
           :in-theory (e/d (rule-syntaxp)
                           (valid-rulep-sk-necc
                            (:DEFINITION FALIST-CONSISTENT)
                            (:REWRITE VALID-RULEP-IMPLIES-VALID-SC)))
           :use (:instance valid-rulep-sk-necc
                           (a (bind-bindings bindings a))))))

(defthm rp-apply-bindings-equiv-not-iff
  (implies (and (valid-rulep rule)
                (alistp a)
                (rp-evl (rp-apply-bindings (rp-hyp rule) bindings) a)
                (bindings-alistp bindings)
                (not (rp-iff-flag rule)))
           (equal (rp-evl (rp-apply-bindings (rp-lhs rule) bindings) a)
                  (rp-evl (rp-apply-bindings (rp-rhs rule) bindings) a)))
  :hints (("goal"
           :in-theory (e/d (rule-syntaxp)
                           (valid-rulep-sk-necc))
           :use (:instance valid-rulep-sk-necc
                           (a (bind-bindings bindings a))))))

(encapsulate
  nil

  (defthmd  rp-equal2-bindings-1to1-remove-bindings-from-rp
    (implies (and (bindings-alistp bindings))
             (rp-equal2-bindings-1to1 (remove-rp-from-bindings bindings)
                                      bindings))
    :hints (("goal"
             :induct (remove-rp-from-bindings bindings)
             :do-not-induct t
             :expand (rp-equal2-bindings-1to1
                      (cons (cons (car (car bindings))
                                  (ex-from-rp (cdr (car bindings))))
                            (remove-rp-from-bindings (cdr bindings)))
                      bindings)
             :in-theory (enable ex-from-rp-loose
                                remove-rp-from-bindings))))

  (defthmd rp-equal2-bindings-1to1-consp
    (implies (rp-equal2-bindings-1to1 bindings bindings2)
             (equal (consp bindings2) (consp bindings)))
    :hints (("goal"
             :expand (rp-equal2-bindings-1to1 bindings bindings2))))

  (defthmd rp-equal2-bindings-1to1-consp-2
    (implies (and (bindings-alistp bindings)
                  (bindings-alistp bindings2)
                  (rp-equal2-bindings-1to1 bindings bindings2))
             (equal (consp (assoc-equal term bindings2))
                    (consp (assoc-equal term bindings))))
    :hints (("goal"
             :in-theory (enable rp-equal2-bindings-1to1)
             :induct (rp-equal2-bindings-1to1 bindings bindings2) )))

  (defthmd rp-equal2-bindings-1to1-assoc-eq
    (implies (and (bindings-alistp bindings)
                  (bindings-alistp bindings2)
                  (consp (assoc-equal term bindings))
                  (rp-equal2-bindings-1to1 bindings bindings2))
             (rp-equal2 (cdr (assoc-equal term bindings))
                        (cdr (assoc-equal term bindings2))))
    :hints (("goal"
             :in-theory (enable rp-equal2-bindings-1to1)
             :induct (rp-equal2-bindings-1to1 bindings bindings2)))))

#|(defthm-apply-bindings
  (defthm valid-falist-apply-bindings
    (implies (and (all-falist-consistent-bindings bindings)
                  (not (include-fnc term 'falist)))
             (all-falist-consistent (rp-apply-bindings term bindings)))
    :flag rp-apply-bindings)
  (defthm valid-falist-apply-bindings-subterms
    (implies (and (all-falist-consistent-bindings bindings)
                  (not (include-fnc-subterms subterms 'falist)))
             (all-falist-consistent-lst
              (rp-apply-bindings-subterms subterms bindings)))
    :flag rp-apply-bindings-subterms))||#

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies
      (and (symbolp term)
           term
           (bindings-alistp bindings)
           (consp (assoc-equal term
                               (remove-rp-from-bindings bindings))))
      (equal (rp-evl (cdr (assoc-equal term
                                       (remove-rp-from-bindings bindings)))
                     a)
             (rp-evl (cdr (assoc-equal term bindings))
                     a)))))

  (local
   (defthm lemma2
     (implies (and (bindings-alistp bindings)
                   (consp (assoc-equal term (remove-rp-from-bindings bindings))))
              (consp (assoc-equal term bindings)))))

  (local
   (defthm lemma3
     (implies (and (bindings-alistp bindings)
                   (not (consp (assoc-equal term (remove-rp-from-bindings bindings)))))
              (not (consp (assoc-equal term bindings))))))

  (defthm-apply-bindings
    (defthm rp-apply-bindings-with-remove-rp-from-bindings
      (implies
       (and (rp-termp term)
            (bindings-alistp bindings))
       (equal (rp-evl (rp-apply-bindings term (remove-rp-from-bindings bindings)) a)
              (rp-evl (rp-apply-bindings term bindings) a)))
      :flag rp-apply-bindings)

    (defthm rp-apply-bindings-subterms-remove-rp-from-bindings
      (implies
       (and (rp-term-listp subterms)
            (bindings-alistp bindings))
       (equal (rp-evl-lst (rp-apply-bindings-subterms subterms (remove-rp-from-bindings bindings)) a)
              (rp-evl-lst (rp-apply-bindings-subterms subterms bindings) a)))
      :flag rp-apply-bindings-subterms)

    :hints (("goal" :in-theory (enable rp-evl-of-fncall-args))))

  #|(local
  (defthm lemma4
  (implies (and (all-falist-consistent
  (cdr (assoc-equal term bindings)))
  (consp (assoc-equal term bindings)))
  (all-falist-consistent
  (cdr (assoc-equal term (remove-rp-from-bindings bindings)))))))||#

  #|(defthm-apply-bindings
  (defthm valid-falist-apply-bindings-with-remove-rp-from-bindings
  (implies (and (all-falist-consistent-bindings bindings)
  (bindings-alistp bindings)
  (not (include-fnc term 'falist)))
  (all-falist-consistent
  (rp-apply-bindings term
  (remove-rp-from-bindings bindings))))
  :flag rp-apply-bindings)
  (defthm valid-falist-apply-bindings-subterms-with-remove-rp-from-bindings
  (implies (and (all-falist-consistent-bindings bindings)
  (bindings-alistp bindings)
  (not (include-fnc-subterms subterms 'falist)))
  (all-falist-consistent-lst
  (rp-apply-bindings-subterms subterms (remove-rp-from-bindings bindings))))
  :flag rp-apply-bindings-subterms))||#)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|(encapsulate
  nil

  (local
   (defthm lemma1
     (implies (and (RP-SYNTAXP TERM)
                   (NOT (EQUAL (CAR TERM) 'QUOTE)))
              (RP-SYNTAXP-LST (CDR TERM)))
     :hints (("Goal"
              :cases ((is-rp term))
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma2
     (implies (is-rp term)
              (is-rp (rp-apply-bindings term bindings)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma3
     (implies (is-rp term)
              (equal (rp-apply-bindings (cadr term) bindings)
                     (cadr term)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma4
     (IMPLIES (AND
               (CONSP TERM)
               (NOT (CONSP (CDDR TERM)))
               (CONSP (CDR TERM))
               (RP-SYNTAXP (CADR TERM))
               (EQUAL (CAR TERM) 'RP)
               (IS-RP TERM))
              (IS-RP (LIST 'RP (CADR TERM))))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma5
     (IMPLIES (AND
               (CONSP TERM)
               (NOT (EQUAL (CAR TERM) 'QUOTE))
               (NOT (EQUAL (CAR TERM) 'SYNP))
;(NOT (CONSP (CAR TERM)))
               (RP-SYNTAXP-LST (RP-APPLY-BINDINGS-SUBTERMS (CDR TERM)
                                                           BINDINGS))
               (RP-SYNTAXP TERM)
               (RP-SYNTAXP-LST (STRIP-CDRS BINDINGS)))
              (RP-SYNTAXP (CONS (CAR TERM)
                                (RP-APPLY-BINDINGS-SUBTERMS (CDR TERM)
                                                            BINDINGS))))
     :hints (("Goal"
              :cases ((is-rp term))
              :in-theory (e/d (is-rp) ())))))

  (defthm-apply-bindings
    (defthm rp-syntaxp-rp-apply-bindings
      (implies (and (rp-syntaxp term)
                    (rp-termp term)
                    (rp-syntaxp-bindings bindings))
               (rp-syntaxp (rp-apply-bindings term bindings)))
      :flag rp-apply-bindings)
    (defthm rp-syntaxp-rp-apply-bindings-subterms
      (implies (and (rp-syntaxp-lst subterms)
                    (rp-term-listp subterms)
                    (rp-syntaxp-bindings bindings))
               (rp-syntaxp-lst
                (rp-apply-bindings-subterms subterms bindings)))
      :flag rp-apply-bindings-subterms)
    :hints (("Goal"
             :in-theory (e/d (is-rp) ())))))||#



(defthm alistp-RP-TRANS-BINDINGS
  (alistp (RP-TRANS-BINDINGS bindings)))


(defthm RP-TERM-LISTP-STRIP-CDRS-RP-TRANS-BINDINGS
  (implies (rp-term-listp (strip-cdrs bindings))
           (rp-term-listp (strip-cdrs (rp-trans-bindings bindings)))))

(encapsulate
  nil

  (local
   (defthm lemma1
     (IMPLIES (AND (NOT (CONSP TERM))
                   (VALID-SC-BINDINGS BINDINGS A)
                   (CONSP (ASSOC-EQUAL TERM BINDINGS)))
              (VALID-SC (CDR (ASSOC-EQUAL TERM BINDINGS))
                        A))))

  (local
   (defthm lemma2
     (implies (NOT (EQUAL car-term 'RP))
              (not (is-rp (cons car-term
                                x))))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))

  (local
   (defthm lemma3
     (implies (is-if term)
              (CASE-MATCH TERM (('IF & & &) T)
                (& NIL)))
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (local
   (in-theory (disable is-synp)))

  (local
   (defthm lemma4
     (equal (cdr (RP-APPLY-BINDINGS-SUBTERMS SUBTERMS BINDINGS))
            (RP-APPLY-BINDINGS-SUBTERMS (cdr SUBTERMS) BINDINGS))))

  (local
   (defthm lemma5
     (implies (consp subterms)
              (equal (car (RP-APPLY-BINDINGS-SUBTERMS SUBTERMS BINDINGS))
                     (RP-APPLY-BINDINGS (CAR SUBTERMS)  BINDINGS)))))

  #|(local
  (defthm lemma6
  (implies (and (is-if term)
  (rp-syntaxp term))
  (and (rp-syntaxp (cadr term))
  (rp-syntaxp (caddr term))
  (rp-syntaxp (cadddr term))))
  :hints (("Goal"
  :in-theory (e/d (is-if) ())))
  :rule-classes :forward-chaining))||#

  (local
   (defthm lemma7
     (implies (is-if term)
              (CASE-MATCH TERM (('IF & & &) T)
                (& NIL)))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (local
   (defthm lemma8
     (implies (is-if term)
              (IS-IF (LIST* 'if
                            (RP-APPLY-BINDINGS (CADR TERM) BINDINGS)
                            (RP-APPLY-BINDINGS-SUBTERMS (CDDR TERM)
                                                        BINDINGS))))
     :hints (("Goal"
              :in-theory (e/d (is-if) ())))))

  (local
   (defthmd lemma9-lemma1
     (implies (not (is-if term))
              (not (is-if (CONS (CAR TERM)
                                (RP-APPLY-BINDINGS-SUBTERMS (CDR TERM)
                                                            BINDINGS)))))
     :hints (("Goal"
              :expand (RP-APPLY-BINDINGS-SUBTERMS (CDDDDR TERM)
                                                  BINDINGS)
              :in-theory (e/d (is-if) ())))))

  #|(local
  (defthmd lemma9-lemma2
  (implies (and (not (is-rp term))
  (rp-syntaxp term))
  (not (is-rp (CONS (CAR TERM)
  (RP-APPLY-BINDINGS-SUBTERMS (CDR TERM)
  BINDINGS)))))
  :hints (("Goal"
  :expand (RP-APPLY-BINDINGS-SUBTERMS (CDDDDR TERM)
  BINDINGS)
  :in-theory (e/d (is-if) ())))))||#

  #|(local
  (defthmd IS-LAMBDA-STRICT-of-apply-bindings
  (implies (is-lambda term)
  (equal (RP-APPLY-BINDINGS TERM BINDINGS)
  (cons (car term)
  (rp-apply-bindings-subterms (cdr term)
  BINDINGS))))
  :hints (("Goal"
  :in-theory (e/d (is-synp) ())))))||#

  (defthm valid-sc-cons
    (implies (and (not (is-rp term))
                  (rp-termp term)
;(not (consp (car term)))
                  (valid-sc-subterms (cdr term) a))
             (valid-sc term a))
    :hints (("goal"
             :expand ((valid-sc (cons car-term subterms) a)
                      (valid-sc term a)
                      (valid-sc-subterms (cdr term) a))
             :cases ((is-if term))
             :in-theory (e/d (valid-sc) ()))))

  (defthm valid-sc-cons-car-apply-bindings
    (implies (and (not (is-rp term))
                  (rp-termp term)
                  (bindings-alistp bindings)
                  (valid-sc-subterms (rp-apply-bindings-subterms (cdr term) bindings) a))
             (valid-sc (cons (car term)
                             (rp-apply-bindings-subterms (cdr term)
                                                         bindings))
                       a))
    :hints (("goal"
             :do-not-induct t
             :expand (valid-sc (cons (car term)
                                     (rp-apply-bindings-subterms (cdr term)
                                                                 bindings))
                               a)
             :in-theory (e/d (
                              is-rp
                              rp-apply-bindings-subterms
                              valid-sc-cons)
                             (ex-from-rp
                              valid-sc
                              (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                              (:DEFINITION ACL2::APPLY$-BADGEP)
                              (:REWRITE ACL2::O-P-O-INFP-CAR)
                              (:DEFINITION FALIST-CONSISTENT-AUX)
                              (:DEFINITION INCLUDE-FNC-SUBTERMS)
                              (:DEFINITION INCLUDE-FNC)
                              (:DEFINITION FALIST-CONSISTENT)
                              (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP))))))

  (defthm-apply-bindings
    (defthmd valid-sc-apply-bindings-for-hyp-lemma
      (implies
       (and (not (include-fnc term 'rp))
            (bindings-alistp bindings)
            (rp-termp term)
            (valid-sc-bindings bindings a))
       (valid-sc (rp-apply-bindings term bindings) a))
      :flag rp-apply-bindings)
    (defthmd valid-sc-apply-bindings-subterms-for-hyp-lemma
      (implies
       (and (not (include-fnc-subterms subterms 'rp))
            (bindings-alistp bindings)
            (rp-term-listp subterms)
            (valid-sc-bindings bindings a))
       (valid-sc-subterms (rp-apply-bindings-subterms subterms bindings) a))
      :flag rp-apply-bindings-subterms)
    :hints (("Goal"
             :in-theory (e/d (rule-syntaxp) ()))))

  (defthm valid-sc-apply-bindings-for-hyp
    (implies (and (valid-rulep rule)
                  (bindings-alistp bindings)
                  (valid-sc-bindings bindings a))
             (valid-sc (rp-apply-bindings (rp-hyp rule) bindings) a))
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d (valid-sc-apply-bindings-for-hyp-lemma
                              rule-syntaxp)
                             (rp-apply-bindings)))))

  (local
   (defthm lemma201
     (implies (valid-sc (RP-APPLY-BINDINGS (EX-FROM-RP TERM)
                                           BINDINGS)
                        a)
              (valid-sc (ex-from-rp (RP-APPLY-BINDINGS term BINDINGS)) a))
     :hints (("Goal"
              :induct (EX-FROM-RP TERM)
              :in-theory (e/d (ex-from-rp
                               is-rp)
                              ((:REWRITE CAR-OF-EX-FROM-RP-IS-NOT-RP)
                               (:DEFINITION RP-TERMP)
                               (:REWRITE RP-APPLY-BINDINGS-IS-RP-TERMP)))))))

  (local
   (defun eval-and-all-lst (lst a)
     (if (atom lst)
         t
       (and (eval-and-all (car lst) a)
            (eval-and-all-lst (cdr lst) a)))))

  (local
   (defun context-from-rp-bindings (bindings)
     (if (atom bindings)
         nil
       (cons (context-from-rp (cdar bindings) nil)
             (context-from-rp-bindings (cdr bindings))))))
  (local
   (encapsulate
     nil

     (local
      (defthm ilemma1
        (implies (atom bindings)
                 (and (equal (BIND-BINDINGS-AUX BINDINGS A)
                             nil)))))

     (local
      (defthm ilemma2
        (implies (and (rp-termp term)
                      (case-split (consp term))
                      (not (is-rp term)))
                 (equal (CONTEXT-FROM-RP (RP-APPLY-BINDINGS TERM BINDINGS)
                                         NIL)
                        nil))
        :hints (("Goal"
                 :in-theory (e/d (is-rp context-from-rp rp-apply-bindings) ())))))

     (local
      (defthm ilemma3
        (implies (and (atom term)
                      (eval-and-all-lst (context-from-rp-bindings bindings) a))
                 (eval-and-all (CONTEXT-FROM-RP (RP-APPLY-BINDINGS TERM BINDINGS)
                                                NIL)
                               a))
        :hints (("Goal"
                 :in-theory (e/d (context-from-rp rp-apply-bindings) ())))))

     (local
      (defthm ilemma4
        (implies
         (and (is-rp term)
              (eval-and-all (context-from-rp (rp-apply-bindings (caddr term)
                                                                bindings)
                                             nil)
                            a)
              (rp-termp term)
              (alistp a)
              (not (include-fnc term 'list))
              (bindings-alistp bindings)
              (rp-evlt (list (cadr (cadr term))
                             (ex-from-rp (caddr term)))
                      (append (bind-bindings-aux (rp-trans-bindings bindings) a)
                              a))
              (eval-and-all (context-from-rp (caddr term) nil)
                            (append (bind-bindings-aux (rp-trans-bindings bindings) a)
                                    a))
              (eval-and-all-lst (context-from-rp-bindings bindings)
                                a))
         (eval-and-all (context-from-rp (rp-apply-bindings term bindings)
                                        nil)
                       a))
        :hints (("Goal"
                 :do-not-induct t
                 :expand ((rp-apply-bindings term bindings)
                          (CONTEXT-FROM-RP (LIST 'RP
                                                 (CADR TERM)
                                                 (RP-APPLY-BINDINGS (CADDR TERM)
                                                                    BINDINGS))
                                           NIL))
                 :in-theory (e/d (is-rp
                                  rp-evl-of-fncall-args)
                                 (context-from-rp
                                  EX-FROM-RP-LEMMA1))))))

     (defthm lemma202
       (implies (and 
                     (rp-termp term)
                     (alistp a)
                     (bindings-alistp bindings)
                     (not (include-fnc term 'list))
                     (EVAL-AND-ALL (CONTEXT-FROM-RP TERM NIL)
                                   (APPEND (BIND-BINDINGS-AUX
                                            (rp-trans-bindings bindings) A) A))
                     (eval-and-all-lst (context-from-rp-bindings bindings) a))
                (EVAL-AND-ALL (CONTEXT-FROM-RP (rp-apply-bindings TERM bindings) NIL) a))
       :hints (("Goal"
                :induct (CONTEXT-FROM-RP TERM NIL)
                :in-theory (e/d (eval-and-all context-from-rp )
                                (BIND-BINDINGS-AUX is-rp
                                                   rp-apply-bindings)))))))

  (local
   (defthm lemma203
     (implies (and (EVAL-AND-ALL (CONTEXT-FROM-RP term NIL) A)
                   (VALID-SC (EX-FROM-RP term) A))
              (VALID-SC term A))
     :hints (("Goal"
              :induct (EX-FROM-RP term)
              :in-theory (e/d (ex-from-rp is-rp context-from-rp)
                              (EX-FROM-RP-LEMMA1))))))

  (local
   (defthm lemma204
     (implies (VALID-SC-BINDINGS BINDINGS A)
              (eval-and-all-lst (context-from-rp-bindings bindings) a))
     :hints (("Goal"
              :in-theory (e/d (context-from-rp is-rp)
                              (EX-FROM-RP-LEMMA1
                               (:DEFINITION RP-TERMP)
                               (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:DEFINITION INCLUDE-FNC)
                               (:REWRITE ACL2::O-P-O-INFP-CAR)
                               (:REWRITE DEFAULT-CDR)
                               (:REWRITE VALID-SC-CADR)
                               (:REWRITE EVL-OF-EXTRACT-FROM-RP-2)
                               (:REWRITE VALID-SC-CONS)))))))


  (local
   (mutual-recursion
    (defun valid-sc-with-apply (term bindings a)
      (declare (xargs
                :measure (cons-count term)
                :hints (("Goal"
                               :in-theory (e/d (measure-lemmas) ())))))
      (cond ((quotep term)
             t)
            ((atom term)
             t #|(B*
                 ((BINDING (ASSOC-EQUAL TERM BINDINGS))
                  (RES
                   (IF (CONSP BINDING)
                       (valid-sc (CDR BINDING) a)
                       t)))
               res)||#)
            ((is-synp term) ''t)
            ((is-if term)
             (AND (valid-sc-with-apply (cadr term) bindings a)
                  (IF (rp-evlt (rp-apply-bindings (cadr term) bindings) a)
                      (valid-sc-with-apply (caddr term) bindings a)
                      (valid-sc-with-apply (CADDDR TERM) bindings A))))
            ((is-rp term)
             (and #|(eval-and-all (rp-apply-bindings-subterms (context-from-rp
                                                             term nil)
                                                            bindings)
                                a)||#
                  (valid-sc-with-apply (ex-from-rp term) bindings a)))
            (t (valid-sc-with-apply-lst (cdr term) bindings a))))
    (defun valid-sc-with-apply-lst (subterms bindings a)
      (declare (xargs :measure (cons-count subterms)))
      (cond ((atom subterms) t)
            (t (and (valid-sc-with-apply (car subterms) bindings a)
                    (valid-sc-with-apply-lst (cdr subterms)
                                             bindings
                                             a)))))))

  (local
   (make-flag valid-sc-with-apply :defthm-macro-name defthm-valid-sc-with-apply
             :hints (("Goal"
                      :in-theory (e/d (measure-lemmas) ())))))



  (local
   (defthm is-rp-apply-bindings
     (implies (is-rp term)
              (is-rp (RP-APPLY-BINDINGS TERM BINDINGS)))
     :hints (("Goal"
              :in-theory (e/d (is-rp
                               is-synp) ())))))

  
  (local
   (defthm include-fnc-lemma
     (implies (and (NOT (INCLUDE-FNC TERM 'LIST))
                   (NOT (EQUAL (CAR TERM) 'QUOTE)))
              (and (not (INCLUDE-FNC-SUBTERMS (CDR TERM) 'LIST))
                   (not (INCLUDE-FNC (CADR TERM) 'LIST))
                   (not (INCLUDE-FNC (CADDR TERM) 'LIST))
                   (not (INCLUDE-FNC (CADDDR TERM) 'LIST))))))

  (local
   (defthm-valid-sc-with-apply
     (defthm rp-apply-bindings-to-valid-sc-with-different-a
       (implies (and (rp-termp term)
                     (not (include-fnc term 'list))
                     (alistp a)
                     (valid-sc-bindings bindings a)
                     (valid-sc term (bind-bindings (rp-trans-bindings bindings) a))
                     (bindings-alistp bindings))
                (valid-sc (rp-apply-bindings term bindings) a))
       :flag valid-sc-with-apply)

     (defthm rp-apply-bindings-to-valid-sc-with-different-a-subterms
       (implies (and (rp-term-listp subterms)
                     (alistp a)
                     (not (include-fnc-subterms subterms 'list))
                     (valid-sc-subterms subterms (bind-bindings (rp-trans-bindings bindings) a))
                     (valid-sc-bindings bindings a)
                     (bindings-alistp bindings))
                (valid-sc-subterms (rp-apply-bindings-subterms subterms bindings) a))
       :flag valid-sc-with-apply-lst)
     :hints (("Goal"
              :expand ((VALID-SC (RP-APPLY-BINDINGS TERM BINDINGS)
                                 A)
                       (:free (x y a) (VALID-SC (CONS x y) A)))
              ;; :induct
              ;;  (FLAG-VALID-SC FLAG TERM SUBTERMS (bind-bindings (rp-trans-bindings bindings) a))
              :in-theory (e/d ()
                              (EVL-OF-EXTRACT-FROM-RP
                               (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                               (:DEFINITION ACL2::APPLY$-BADGEP)
                               (:REWRITE RP-TERM-LISTP-IS-TRUE-LISTP)
                               (:DEFINITION TRUE-LISTP)
                               (:DEFINITION INCLUDE-FNC)
                               ;;valid-sc
                               (:DEFINITION RP-TERMP)
                               VALID-SC-EX-FROM-RP-2))))))

  (defthm valid-sc-apply-bindings-for-rhs
    (implies
     (and (valid-rulep rule)
          (not (include-fnc (rp-hyp rule) 'list))
          (not (include-fnc (rp-rhs rule) 'list))
          (alistp a)
          (valid-sc-bindings bindings a)
          (bindings-alistp bindings)
          (rp-evlt (rp-apply-bindings (rp-hyp rule) bindings) a))
     (valid-sc (rp-apply-bindings (rp-rhs rule) bindings) a))
    :otf-flg t
    :hints (("Goal"
             :use ((:instance rp-apply-bindings-to-evl
                              (term (rp-hyp rule)))
                   (:instance rp-apply-bindings-to-valid-sc-with-different-a
                              (term (rp-rhs rule)))
                   (:instance valid-rulep-sk-necc
                              (a (bind-bindings (rp-trans-bindings bindings) a)))
                   (:instance valid-sc-any-necc
                              (term (rp-rhs rule))
                              (a (bind-bindings (rp-trans-bindings bindings) a))))
             :do-not-induct t
             :in-theory (e/d (valid-rulep
                              rule-syntaxp)
                             (rp-apply-bindings
                              (:REWRITE VALID-RULEP-IMPLIES-VALID-SC)
                              ;(:DEFINITION VALID-RULEP)
                              ;(:DEFINITION RULE-SYNTAXP)
                              ;(:DEFINITION RULE-SYNTAXP)
                              (:DEFINITION FALIST-CONSISTENT)
                              valid-rulep-sk
                              valid-sc-any-necc
                              valid-rulep-sk-necc
                              valid-sc
                              valid-sc-any))))))




(defthm rp-evlt-of-apply-bindings-to-evl
  (implies (and (rp-termp term)
                (not (include-fnc term 'list))
                (bindings-alistp bindings))
           (and (equal (rp-evlt (rp-apply-bindings term bindings) a)
                       (rp-evl term (bind-bindings (rp-trans-bindings bindings)
                                                   a)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d () ()))))

(defthm rp-evlt-lst-of-apply-bindings-to-evl-lst
  (implies (and (rp-term-listp subterms)
                (not (include-fnc-subterms subterms 'list))
                (bindings-alistp bindings))
           (and (equal (rp-evlt-lst (rp-apply-bindings-subterms subterms bindings) a)
                       (rp-evl-lst subterms (bind-bindings (rp-trans-bindings bindings)
                                                   a)))))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d () ()))))

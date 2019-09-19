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

(make-flag include-fnc :defthm-macro-name defthm-include-fnc)
(make-flag pseudo-termp2 :defthm-macro-name defthm-pseudo-termp2)
(make-flag beta-search-reduce :defthm-macro-name defthm-beta-search-reduce)
(make-flag all-falist-consistent :defthm-macro-name
           defthm-all-falist-consistent)
(make-flag rp-syntaxp :defthm-macro-name defthm-rp-syntaxp)
(make-flag lambda-exp-free-p :defthm-macro-name defthm-lambda-exp-free-p)

(make-flag get-lambda-free-vars :defthm-macro-name defthm-get-lambda-free-vars)

(local
 (make-flag get-lambda-free-vars :defthm-macro-name
            defthm-get-lambda-free-vars))

(make-event
 `(defthm is-lambda-implies
    (implies (is-lambda term)
             ,(beta-search-reduce (caddar (caddr (meta-extract-formula
                                                  'is-lambda state)))
                                  1000))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (is-lambda) ())))))

(make-event
 `(defthm is-lambda-strict-implies
    (implies (is-lambda-strict x)
             ,(beta-search-reduce (caddar (caddr (meta-extract-formula
                                                  'is-lambda-strict state)))
                                  1000))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (is-lambda is-lambda-strict) ())))))

(defthm get-lambda-free-vars-implies
  (implies
   (and (mv-nth 0 (get-lambda-free-vars term))
        (is-lambda term))
   (b* (((mv valid sub-vars) (get-lambda-free-vars (caddr (car term))))
        (lambda-vars (cadr (car term)))
        ((mv valid-2 &) (get-lambda-free-vars-lst (cdr term))))
     (and valid
          valid-2
          (equal (remove-vars sub-vars lambda-vars) nil))))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (is-lambda is-lambda-strict get-lambda-free-vars)
                           ()))))

(make-event
 `(defthm pseudo-termp2-implies
    (implies (pseudo-termp2 acl2::x)
             ,(caddr (meta-extract-formula
                      'pseudo-termp2 state)))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (is-lambda is-lambda-strict) ())))))

(make-event
 `(defthm lambda-exp-free-p-implies
    (implies (lambda-exp-free-p term)
             ,(caddr (meta-extract-formula
                      'lambda-exp-free-p state)))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (is-lambda is-lambda-strict lambda-exp-free-p )
                             ())))))

(make-event
 `(defthm LAMBDA-EXP-FREE-LISTP-implies
    (implies (LAMBDA-EXP-FREE-LISTP subterms)
             ,(caddr (meta-extract-formula
                      'LAMBDA-EXP-FREE-LISTP state)))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (is-lambda is-lambda-strict lambda-exp-free-p LAMBDA-EXP-FREE-LISTP )
                             ())))))

(defthm pseudo-termp2-dumb-negate-lit2
  (implies (pseudo-termp2 term)
           (pseudo-termp2 (dumb-negate-lit2 term)))
  :hints (("goal" :in-theory (enable pseudo-term-listp2
                                     dumb-negate-lit2))))

#|(defthm-remove-return-last
  (defthm pseudo-termp2-remove-return-last
    (implies (pseudo-termp2 term)
             (pseudo-termp2 (remove-return-last term)))
    :flag remove-return-last)
  (defthm pseudo-term-listp2-remove-return-last-subterms
    (implies (pseudo-term-listp2 subterms)
             (pseudo-term-listp2 (remove-return-last-subterms subterms)))
    :flag remove-return-last-subterms)
  :hints (("Goal" :in-theory (enable pseudo-term-listp2
                                     pseudo-termp2))))||#

(defthm-pseudo-termp2
  (defthm pseudo-termp-lemma1
    (implies (pseudo-termp2 acl2::x)
             (pseudo-termp acl2::x))
    :flag pseudo-termp2)

  (defthm pseudo-term-listp-lemma1
    (implies (pseudo-term-listp2 acl2::lst)
             (pseudo-term-listp acl2::lst))
    :flag pseudo-term-listp2))

(defthm strip-cdrs-pseudo-termlistp2
  (implies
   (and (pseudo-term-listp2 (strip-cdrs alist))
        (cdr (assoc-equal key alist)))
   (pseudo-termp2 (cdr (assoc-equal key alist)))))

(defthm pseudo-termp2-bindings-lemma1
  (implies (and (pseudo-term-listp2 (strip-cdrs bindings))
                (consp (assoc-equal term bindings)))
           (cdr (assoc-equal term bindings))))

(defthm pseudo-term-listp2-is-true-listp
  (implies (pseudo-term-listp2 lst)
           (true-listp lst))
  :hints (("Goal" :expand (pseudo-term-listp2 lst))))

(encapsulate
  nil
  (local
   (in-theory (enable is-rp)))

  (defthm is-synp-implies
    (implies (is-synp term)
             (CASE-MATCH TERM (('SYNP & & &) T)
               (& NIL)))
    :hints (("Goal" :in-theory (enable is-synp))))

  (defthm pseudo-termlistp-extract-from-rp
    (implies (and (pseudo-termp2 term)
                  (not (quotep (ex-from-rp term))))
             (pseudo-term-listp2 (cdr (ex-from-rp term)))))

  (defthm pseudo-termp2-extract-from-rp
    (implies (and (pseudo-termp2 term))
             (pseudo-termp2 (ex-from-rp term))))

  (defthm extract-from-synp-to-ex-from-rp
    (equal (extract-from-synp term)
           (ex-from-synp term))
    :hints (("Goal" :in-theory (enable is-synp ex-from-synp extract-from-synp))))

  (defthm pseudo-termp-extract-from-synp
    (implies (pseudo-termp2 term)
             (pseudo-termp2 (ex-from-synp term)))
    :hints (("Goal" :in-theory (enable extract-from-synp))))

  (defthm atom-pseudo-termp2-is-symbolp
    (implies (and (atom x) (pseudo-termp2 x)) (symbolp x)))

  (defthm pseudo-termp2-context-from-rp
    (implies (and (pseudo-termp2 term)
                  (pseudo-term-listp2 context))
             (pseudo-term-listp2 (context-from-rp term context)))
    :hints (("goal" :in-theory (e/d (context-from-rp ex-from-rp is-rp) ()))))

  (defthm put-term-in-cons-is-pseudo-termp
    (pseudo-termp2 (put-term-in-cons term))
    :hints (("goal" :in-theory (enable is-rp put-term-in-cons))))

  (defthm extract-from-rp-with-context-to-no-context
    (equal (mv-nth 1 (extract-from-rp-with-context term context))
           (ex-from-rp term))
    :hints (("goal" :in-theory (enable extract-from-rp-with-context
                                       is-rp
                                       ex-from-rp))))

  (defthm extract-from-rp-with-context-context
    (equal (mv-nth 0 (extract-from-rp-with-context term context))
           (context-from-rp term context))
    :hints (("goal" :in-theory (enable extract-from-rp-with-context
                                       is-rp
                                       context-from-rp
                                       ex-from-rp))))

  (defthm cons-consp-context-from-rp
    (implies (cons-consp context)
             (cons-consp (context-from-rp term context)))
    :hints (("Goal"
             :induct (context-from-rp term context)
             :in-theory (enable cons-consp is-rp context-from-rp))))

  (defthm symbolp-ex-from-rp
    (implies (and (pseudo-termp2 term)
                  (not (consp (ex-from-rp term))))
             (symbolp (ex-from-rp term))))

  (defthm ex-from-rp-x2
    (equal (ex-from-rp (ex-from-rp term))
           (ex-from-rp term))
    :hints (("Goal" :in-theory (enable ex-from-rp is-rp))))

  (defthm ex-from-synp-ex-from-rpx2
    (equal (EX-FROM-SYNP
            (EX-FROM-RP (EX-FROM-SYNP (EX-FROM-RP term))))
           (EX-FROM-SYNP (EX-FROM-RP term)))
    :hints (("Goal" :in-theory (enable ex-from-rp
                                       ex-from-synp
                                       is-rp
                                       is-synp)))))

(defthm append-of-two-context
  (implies (and (context-syntaxp c1)
                (context-syntaxp c2))
           (context-syntaxp (append c1 c2)))
  :hints (("Goal" :in-theory (enable pseudo-term-listp2
                                     context-syntaxp))))

  ;; acl2::beta-eval-to-beta-reduce-lambda-expr

(defthm-beta-search-reduce
  (defthm eval-of-beta-search-reduce
    (implies (pseudo-termp term)
             (equal (acl2::beta-eval (beta-search-reduce term limit) a)
                    (acl2::beta-eval term a)))
    :flag beta-search-reduce)

  (defthm eval-of-beta-search-reduce-subterms
    (implies (pseudo-term-listp subterms)
             (equal (acl2::beta-eval-list (beta-search-reduce-subterms subterms limit) a)
                    (acl2::beta-eval-list subterms a)))
    :flag beta-search-reduce-subterms)
  :hints (("Goal" :in-theory (enable acl2::beta-eval-constraint-0))))

(defthm eval-of-beta-search-reduce-fixed-lim
  (implies (pseudo-termp (car cl))
           (equal (acl2::beta-eval (beta-search-reduce (car cl) *big-number*) a)
                  (acl2::beta-eval (car cl) a))))

(defthm falist-consistent-implies-falist-syntaxp
  (implies (and (pseudo-termp2 term)
                (falist-consistent-aux falist term))
           (falist-syntaxp falist)))

(defthm extract-from-rp-with-context-to-context-from-rp
  (equal (mv-nth 0 (extract-from-rp-with-context term context))
         (context-from-rp term context))
  :hints (("Goal" :in-theory (enable context-from-rp is-rp))))

(defthm remove-from-alist-returns-alistp
  (implies (alistp x)
           (alistp (remove-from-alist x key))))

;; (defthm rp-stat-add-to-rules-used-returns-rp-stat-p
;;   (implies (rp-stat-p stat)
;;            (rp-stat-p (rp-stat-add-to-rules-used rule stat failed)))
;;   :hints (("Goal" :in-theory (enable rp-stat-p
;;                                      rp-stat-add-to-rules-used))))

;; (defthm rp-stat-add-to-rules-used-returns-rp-stat-p2
;;   (implies (rp-stat-p stat)
;;            (rp-stat-p (rp-stat-add-to-rules-used-ex-cnt rule stat)))
;;   :hints (("Goal" :in-theory (enable rp-stat-p
;;                                      rp-stat-add-to-rules-used-ex-cnt))))

(defthm all-falist-consistent-bindings-lemma1
  (implies (all-falist-consistent-bindings bindings)
           (all-falist-consistent (cdr (assoc-equal term bindings)))))

(encapsulate
  nil

  (local
   (defthm is-rpl-is-not-is-falist
     (implies (is-rp term)
              (not (is-falist term)))
     :hints (("Goal" :in-theory (enable is-rp is-falist)))))

  (local
   (defthm lemma2
     (implies (is-rp term)
              (and (not (EQUAL (CAR TERM) 'QUOTE))
                   (CONSP TERM)))
     :hints (("Goal" :in-theory (enable is-rp is-falist)))))

  (defthm all-falist-consistent-ex-from-rp
    (implies (all-falist-consistent term)
             (all-falist-consistent (ex-from-rp term)))
    :hints (("Goal"
             :induct (ex-from-rp term)
             :expand ((all-falist-consistent term))
             :in-theory (e/d (ex-from-rp)
                             (IS-FALIST all-falist-consistent)))))

  (defthm all-falist-consistent-put-term-in-cons
    (implies (all-falist-consistent term)
             (all-falist-consistent (put-term-in-cons term)))
    :hints (("Goal" :in-theory (enable put-term-in-cons))))

  (defthm all-falist-consistent-lst-context-from-rp
    (implies (and (all-falist-consistent-lst context)
                  (all-falist-consistent term))
             (all-falist-consistent-lst (context-from-rp term context)))
    :hints (("Goal"
             :induct (context-from-rp term context)
             :expand ((ALL-FALIST-CONSISTENT-LST (CDDR TERM))
                      (ALL-FALIST-CONSISTENT-LST (CDR TERM)))
             :in-theory (e/d (context-from-rp is-rp)))))

  (defthm cdr-term-is-all-falist-consistent-lst
    (implies (and (not (quotep term))
                  (all-falist-consistent term))
             (all-falist-consistent-lst (cdr term)))
    :hints (("Goal"
             :expand ((ALL-FALIST-CONSISTENT TERM)
                      (ALL-FALIST-CONSISTENT-LST (CDR TERM)))
             :in-theory (enable all-falist-consistent
                                all-falist-consistent-lst
                                is-falist)))))

(defthm all-falist-consistent-lst-cdr-term-lemma
  (implies (and (all-falist-consistent term)
                (not (equal (car term) 'quote)))
           (all-falist-consistent-lst (cdr term)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((all-falist-consistent term)
                    (FALIST-CONSISTENT TERM)
                    (ALL-FALIST-CONSISTENT (CADR TERM))
                    (ALL-FALIST-CONSISTENT-LST (CDR TERM)))
           :in-theory (enable is-falist all-falist-consistent-lst))))

(defthm-all-falist-consistent
  (defthm not-include-falist-all-falist-consistent
    (implies (not (include-fnc term 'falist))
             (all-falist-consistent term))
    :flag all-falist-consistent)
  (defthm not-include-falist-all-falist-consistent-lst
    (implies (not (include-fnc-subterms lst 'falist))
             (all-falist-consistent-lst lst))
    :flag all-falist-consistent-lst)
  :hints (("Goal"
           :in-theory (e/d (is-falist
                            all-falist-consistent-lst
                            all-falist-consistent)
                           (falist-consistent)))))

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies (and (is-lambda (cons (car term) subterms))
                   (pseudo-termp2 term))
              (is-lambda-strict term))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (is-lambda-strict is-lambda) ())))))

  (defthm get-lambda-free-vars-of-cons-car-term-subterms
    (implies (and (pseudo-termp2 term)
                  (mv-nth 0 (get-lambda-free-vars-lst subterms)))
             (mv-nth 0 (get-lambda-free-vars (cons (car term)
                                                   subterms))))
    :otf-flg t
    :hints (("Goal"
             :expand ((get-lambda-free-vars (cons (car term)
                                                  subterms)))
             :in-theory (e/d () ())))))

(defthm-pseudo-termp2
  (defthm pseudo-termp2-implies-get-lambda-free-vars
    (implies (pseudo-termp2 acl2::x)
             (mv-nth 0
                     (get-lambda-free-vars acl2::x)))
    :flag pseudo-termp2)
  (defthm pseudo-term-listp2-implies-get-lambda-free-vars-lst
    (implies (pseudo-term-listp2 acl2::lst)
             (mv-nth 0
                     (get-lambda-free-vars-lst acl2::lst)))
    :flag pseudo-term-listp2))

(defthm get-lambda-free-vars-of-bindings
  (implies (and (pseudo-term-listp2 (strip-cdrs bindings))
                (consp (assoc-equal term bindings)))
           (mv-nth 0
                   (get-lambda-free-vars (cdr (assoc-equal term bindings))))))

(encapsulate
  nil

  #|(local
  (defthm lemma1
  (implies (and (is-lambda term)
  (mv-nth 0 (get-lambda-free-vars term)))
  (equal (mv-nth 1 (get-lambda-free-vars term))
  (mv-nth 1 (get-lambda-free-vars-lst (cdr term)))))
  :hints (("Goal"
  :expand ((get-lambda-free-vars term))
  :in-theory (e/d () ())))))
  (local
  (defthm lemma2
  (implies (and (booleanp x)
  x)
  (equal (equal t x) t))))

  #|(skip-proofs
  (local
  (defthm lemma3
  (booleanp (mv-nth 0 (get-lambda-free-vars-lst lst))))))||#

  (local
  (defthm-get-lambda-free-vars
  (defthm booleanp-get-lambda-free-vars
  (booleanp (mv-nth 0 (get-lambda-free-vars term)))
  :flag get-lambda-free-vars)
  (defthm booleanp-get-lambda-free-vars-lst
  (booleanp (mv-nth 0 (get-lambda-free-vars-lst lst)))
  :flag get-lambda-free-vars-lst)))

  (local
  (defthm lemma4
  (implies (and (is-lambda term)
  (mv-nth 0 (get-lambda-free-vars term)))
  (equal (mv-nth 0 (get-lambda-free-vars term))
  (mv-nth 0 (get-lambda-free-vars-lst (cdr term)))))
  :hints (("Goal"
  :expand ((get-lambda-free-vars term))
  :in-theory (e/d () ())))))

  (local
  (defthm lemma5
  (implies (and (mv-nth 0 (GET-LAMBDA-FREE-VARS-LST (CDR TERM)))
  (EQUAL (GET-LAMBDA-FREE-VARS-LST SUBTERMS)
  (GET-LAMBDA-FREE-VARS-LST (CDR TERM))))
  (MV-NTH 0 (GET-LAMBDA-FREE-VARS-LST SUBTERMS)))))||#

  (local
   ;; this was used when lambda expressions were allowed
   (defthm pseudo-termp2-cons-car-term-subterms-lemma1
     (implies (and (pseudo-termp2 term)
                   (consp term)
                   (consp (car term))
                   (equal (len subterms)
                          (len (cdr term)))
;(mv-nth 0 (get-lambda-free-vars-lst subterms))
                   #|(lambda-exp-free-listp subterms)||#
                   (pseudo-term-listp2 subterms))
              (pseudo-termp2 (cons (car term) subterms)))
     :otf-flg t
     :hints (("Goal"
              :do-not-induct t
              :expand ((pseudo-termp2 term)
                       (GET-LAMBDA-FREE-VARS (CONS (CAR TERM) SUBTERMS))
                       (is-lambda-strict (cons (car term) subterms))
                       (IS-LAMBDA (CONS (CAR TERM) SUBTERMS)))
              :in-theory (e/d () (get-lambda-free-vars))))))

  (local
   (defthm pseudo-termp2-cons-car-term-subterms-lemma2
     (implies (and (pseudo-termp2 term)
                   (consp term)
                   ;;(atom (car term))
                   ;;(symbolp (car term))
                   (not (equal (car term) 'quote))
                   (pseudo-term-listp2 subterms))
              (pseudo-termp2 (cons (car term) subterms)))
     :otf-flg t
     :hints (("Goal"
              :cases ((atom (car term)))
              :in-theory (enable true-listp pseudo-term-listp2)))))

  (defthm pseudo-termp2-cons-car-term-subterms
    (implies (and (pseudo-termp2 term)
                  (consp term)
                  #|(or ;(atom (car term))
                  #|(and (equal (len subterms)
                  (len (cdr term)))
                  #|(lambda-exp-free-listp subterms)||#)||#)||#
                  (not (equal (car term) 'quote))
                  (pseudo-term-listp2 subterms))
             (pseudo-termp2 (cons (car term) subterms)))
    :hints (("Goal"
             :cases ((atom (car term)))
             :in-theory '(pseudo-termp2-cons-car-term-subterms-lemma1
                          pseudo-termp2-cons-car-term-subterms-lemma2)))))

(defthm pseudo-term-listp2-append
  (implies (and (pseudo-term-listp2 lst1)
                (pseudo-term-listp2 lst2))
           (pseudo-term-listp2 (append lst1 lst2)))
  :hints (("Goal" :in-theory (enable append pseudo-term-listp2))))

(defthm ALL-FALIST-CONSISTENT-LST-append
  (implies (and (ALL-FALIST-CONSISTENT-LST lst1)
                (ALL-FALIST-CONSISTENT-LST lst2))
           (ALL-FALIST-CONSISTENT-LST (append lst1 lst2)))
  :hints (("Goal" :in-theory (enable append ALL-FALIST-CONSISTENT-LST))))

(encapsulate
  nil

  (local
   (defthm is-falist-remove-return-last-subterms
     (implies (consp term)
              (equal (is-falist (cons (car term)
                                      (remove-return-last-subterms (cdr term))))
                     (is-falist term)))
     :hints (("Goal"
; :in-theory (disable is-falist)
              :Expand ((REMOVE-RETURN-LAST-SUBTERMS (CDR TERM))
                       (REMOVE-RETURN-LAST-SUBTERMS (CDDDR TERM))
                       (REMOVE-RETURN-LAST-SUBTERMS (CDDR TERM)))))))

  (local
   (defthm not-is-falist-cons-quote-return-last
     (not (is-falist (cons 'return-last x)))))

  (local
   (defthm lemma1
     (implies (is-falist term)
              (equal (car term) 'falist))))
  #|
  ;; needed for the guards of rp-rw-aux
  (defthm-remove-return-last
  (defthm all-falist-consistent-remove-return-last
  (implies (all-falist-consistent term)
  (all-falist-consistent (remove-return-last term)))
  :flag remove-return-last)

  (defthm all-falist-consistent-remove-return-last-subterms
  (implies (all-falist-consistent-lst subterms)
  (all-falist-consistent-lst (remove-return-last-subterms subterms)))
  :flag remove-return-last-subterms)
  :hints (("Goal"
  :expand
  ((ALL-FALIST-CONSISTENT TERM)
  (ALL-FALIST-CONSISTENT (CONS (CAR TERM)
  (REMOVE-RETURN-LAST-SUBTERMS (CDR TERM)))))
  :in-theory (e/d () (is-falist falist-consistent-aux
  falist-consistent)))))||#)

(defthm dont-rw-syntaxp-dont-rw-if-fix
  (implies (and (dont-rw-syntaxp dont-rw))
           (and (dont-rw-syntaxp (dont-rw-if-fix dont-rw))
                (dont-rw-syntaxp (cadr (dont-rw-if-fix dont-rw)))
                (dont-rw-syntaxp (caddr (dont-rw-if-fix dont-rw)))
                (dont-rw-syntaxp (cadddr (dont-rw-if-fix dont-rw)))))
  :hints (("Goal"
           :in-theory (e/d (dont-rw-syntaxp
                            dont-rw-if-fix)
                           ()))))

#|(encapsulate
  nil
  (local
   (defthm lemma1
     (implies (is-rp term)
              (equal (REMOVE-RETURN-LAST (CADR TERM))
                     (cadr term)))
     :hints (("Goal"
              :in-theory (e/d (is-rp) ())))))
  (local
   (DEFTHM IS-RP-IMPLIES-lemma
                       (IMPLIES (IS-RP TERM)
                                (CASE-MATCH TERM
                                            (('RP ('QUOTE TYPE) &)
                                             (AND (SYMBOLP TYPE)
                                                  (NOT (EQUAL TYPE 'QUOTE))))
                                            (& NIL)))
                       :hints (("Goal"
                                :in-theory (e/d (is-rp) ())))
                       :rule-classes :forward-chaining))

||#

(defthm RP-SYNTAXP-EX-FROM-RP-TERM
  (implies (rp-syntaxp term)
           (rp-syntaxp (ex-from-rp term)))
  :hints (("Goal"
           :induct (ex-from-rp term)
           :in-theory (e/d (is-rp
                            ex-from-rp) ()))))

(defthm-rp-syntaxp
  (defthm not-include-rp-means-rp-syntaxp
    (implies (not (include-fnc term 'rp))
             (rp-syntaxp term))
    :flag rp-syntaxp)
  (defthm not-include-rp-means-rp-syntaxp-lst
    (implies (not (include-fnc-subterms lst 'rp))
             (rp-syntaxp-lst lst))
    :flag rp-syntaxp-lst))

#|(defthm-remove-return-last
  (defthm not-include-rp-of-remove-return-last
    (implies (not (include-fnc term 'rp))
             (not (include-fnc (remove-return-last term) 'rp)))
    :flag remove-return-last)
  (defthm not-include-rp-of-remove-return-last-subterms
    (implies (not (include-fnc-subterms subterms 'rp))
             (Not (include-fnc-subterms (remove-return-last-subterms subterms) 'rp)))
    :flag remove-return-last-subterms))||#

(defthm rp-syntaxp-ex-from-rp
  (implies (rp-syntaxp term)
           (rp-syntaxp (ex-from-rp term)))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-rp) ()))))

(defthm rp-syntaxp-ex-from-rp-lemma
  (implies (and (rp-syntaxp term)
                (not (equal (car (ex-from-rp term))
                            'quote)))
           (rp-syntaxp-lst (cdr (ex-from-rp term))))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-rp) ()))))

(defthm rp-syntaxp-lst-context-from-rp
  (implies (and (rp-syntaxp term)
                (rp-syntaxp-lst context))
           (rp-syntaxp-lst (context-from-rp term context)))
  :hints (("Goal"
           :in-theory (e/d (context-from-rp
                            is-rp) ()))))

(defthm rp-syntaxp-put-term-in-cons
  (implies
   (should-term-be-in-cons rule-lhs term)
   (and (rp-syntaxp (put-term-in-cons term))
        (RP-SYNTAXP-LST (CDR (PUT-TERM-IN-CONS term)))))
  :hints (("Goal"
           :in-theory (e/d (put-term-in-cons
                            should-term-be-in-cons) ()))))

(encapsulate
  nil
  (local
   (defthm lemma1
     (IMPLIES
      (AND
       (CONSP TERM)
       (NOT (EQUAL (CAR TERM) 'QUOTE))
       (NOT (EQUAL (CAR TERM) 'RP))
       (RP-SYNTAXP-LST
        (REMOVE-RETURN-LAST-SUBTERMS (CDR TERM)))
       (RP-SYNTAXP-LST (CDR TERM)))
      (RP-SYNTAXP (REMOVE-RETURN-LAST TERM)))
     :hints (("Goal"
              :cases ((is-return-last term))
              :in-theory (e/d () ())))))

  #|(defthm-rp-syntaxp
  (defthm rp-syntaxp-remove-return-last
  (implies (rp-syntaxp term)
  (rp-syntaxp (remove-return-last term)))
  :flag rp-syntaxp)
  (defthm rp-syntaxp-remove-return-last-subterms
  (implies
  (rp-syntaxp-lst lst)
  (rp-syntaxp-lst (remove-return-last-subterms lst)))
  :flag rp-syntaxp-lst)
  :hints (("Goal"
  :in-theory (e/d (is-rp) ()))))||#)

(defthmd context-syntaxp-implies
  (implies (context-syntaxp context)
           (AND (PSEUDO-TERM-LISTP2 CONTEXT)
                (RP-SYNTAXP-LST CONTEXT)
                (ALL-FALIST-CONSISTENT-LST CONTEXT)))
  :hints (("Goal"
           :in-theory (e/d (context-syntaxp) ()))))

(defthm rp-syntaxp-assoc-equal
  (IMPLIES
   (AND
    (RP-SYNTAXP-LST (STRIP-CDRS BINDINGS))
    (CONSP (ASSOC-EQUAL TERM BINDINGS)))
   (and
    (RP-SYNTAXP (CDR (ASSOC-EQUAL TERM BINDINGS)))
    (RP-SYNTAXP (CDR (hons-ASSOC-EQUAL TERM BINDINGS))))))

(defthm rp-syntaxp-lst-append
  (equal (rp-syntaxp-lst (append x y))
         (and (rp-syntaxp-lst x)
              (rp-syntaxp-lst y)))
  :hints (("Goal"
           :in-theory (e/d (rp-syntaxp-lst
                            append)
                           (rp-syntaxp)))))

(defthm is-if-implies
  (implies (is-if term)
           (CASE-MATCH TERM (('IF & & &) T)
             (& NIL)))
  :hints (("Goal"
           :in-theory (e/d (is-if) ())))
  :rule-classes :forward-chaining)

(defthmd is-rp-implies-fc
  (implies (is-rp term)
           (CASE-MATCH TERM
             (('RP ('QUOTE TYPE) &)
              (AND (SYMBOLP TYPE)
                   (NOT (BOOLEANP TYPE))
                   (NOT (EQUAL TYPE 'QUOTE))
                   (NOT (EQUAL TYPE 'RP))))
             (& NIL)))
  :rule-classes :forward-chaining
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthmd rule-syntaxp-implies
  (implies (rule-syntaxp rule)
           (and
            (weak-custom-rewrite-rule-p rule)
            (pseudo-termp2 (rp-hyp rule))
            (pseudo-termp2 (rp-lhs rule))
            (pseudo-termp2 (rp-rhs rule))
            ;; (rp-syntaxp (rp-lhs rule))
            (not (include-fnc (rp-lhs rule) 'rp))
            (not (include-fnc (rp-hyp rule) 'rp))
            (rp-syntaxp (rp-rhs rule))
            (not (include-fnc (rp-rhs rule) 'falist))
            (not (include-fnc (rp-hyp rule) 'falist))
            (not (include-fnc (rp-lhs rule) 'if))
            (not (include-fnc (rp-lhs rule) 'synp))
            (no-free-variablep rule)))
  :hints (("Goal" :in-theory (enable rule-syntaxp))))


(defthm ex-from-rp-loose-of-ex-from-rp-loose
  (equal (ex-from-rp-loose (ex-from-rp-loose term))
         (ex-from-rp-loose term))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp-loose
                            is-rp-loose) ()))))


(defthm all-falist-consistent-of-ex-from-rp-loose
  (implies (all-falist-consistent term)
           (all-falist-consistent (ex-from-rp-loose term)))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp-loose
                            is-rp-loose) ()))))


(defthm pseudo-termp2-ex-from-rp-loose
  (implies (pseudo-termp2 term)
           (pseudo-termp2 (ex-from-rp-loose term)))
  :hints (("Goal"
           :in-theory (e/d (pseudo-termp2
                            ex-from-rp-loose
                            is-rp-loose) ()))))


(defthm rp-syntaxp-ex-from-rp-loose
  (implies (rp-syntaxp term)
           (rp-syntaxp (ex-from-rp-loose term)))
  :hints (("Goal"
           :in-theory (e/d (rp-syntaxp
                            ex-from-rp-loose
                            is-rp-loose) ()))))


(defthm all-falist-consistent-of-ex-from-rp 
  (implies (all-falist-consistent term)
           (all-falist-consistent (ex-from-rp  term)))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp 
                            is-rp ) ()))))


(defthm
  pseudo-termp2-ex-from-rp
  (implies (pseudo-termp2 term)
           (and (pseudo-termp2 (ex-from-rp term))
                (pseudo-termp2 (ex-from-rp-loose term))))
  :hints
  (("goal" :in-theory
    (e/d (ex-from-rp-loose ex-from-rp is-rp-loose is-rp)
         nil))))


(defthm all-falist-consistent-ex-from-rp-loose
  (implies (all-falist-consistent term)
           (all-falist-consistent (ex-from-rp-loose term)))
  :hints (("Goal"
           :in-theory (e/d (all-falist-consistent
                            is-falist
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm pseudo-termp2-cadr
  (implies (and (pseudo-termp2 term)
                (consp term)
                (not (quotep term))
                (consp (cdr term)))
           (pseudo-termp2 (cadr term)))
  :hints (("Goal"
           :in-theory (e/d (pseudo-termp2
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm rp-syntaxp-cadr
  (implies (and (rp-syntaxp term)
                (consp term)
                (not (quotep term))
                (not (equal (car term) 'rp))
                (consp (cdr term)))
           (rp-syntaxp (cadr term)))
  :hints (("Goal"
           :in-theory (e/d (pseudo-termp2
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm all-falist-consistent-cadr
  (implies (and (all-falist-consistent term)
                (consp term)
                (not (quotep term))
                (consp (cdr term)))
           (all-falist-consistent (cadr term)))
  :hints (("Goal"
           :in-theory (e/d (all-falist-consistent
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm all-falist-consistent-caddr
  (implies (and (all-falist-consistent term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term)))
           (all-falist-consistent (caddr term)))
  :hints (("Goal"
           :in-theory (e/d (all-falist-consistent
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm all-falist-consistent-cadddr
  (implies (and (all-falist-consistent term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term))
                (consp (cdddr term)))
           (all-falist-consistent (cadddr term)))
  :hints (("Goal"
           :in-theory (e/d (all-falist-consistent
                            ex-from-rp-loose
                            is-rp-loose) ()))))



(defthm pseudo-termp2-caddr
  (implies (and (pseudo-termp2 term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term)))
           (pseudo-termp2 (caddr term)))
  :hints (("Goal"
           :in-theory (e/d (pseudo-termp2
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm pseudo-termp2-cadddr
  (implies (and (pseudo-termp2 term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term))
                (consp (cdddr term)))
           (pseudo-termp2 (cadddr term)))
  :hints (("Goal"
           :in-theory (e/d (pseudo-termp2
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm rp-syntaxp-caddr
  (implies (and (rp-syntaxp term)
                (consp term)
                (not (quotep term))
                ;(not (equal (car term) 'rp))
                (consp (cdr term))
                (consp (cddr term)))
           (rp-syntaxp (caddr term)))
  :hints (("Goal"
           :in-theory (e/d (pseudo-termp2
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm rp-syntaxp-cadddr
  (implies (and (rp-syntaxp term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term))
                (consp (cdddr term)))
           (rp-syntaxp (cadddr term)))
  :hints (("Goal"
           :expand ((rp-syntaxp term))
           :in-theory (e/d (pseudo-termp2
                            ex-from-rp-loose
                            rp-syntaxp
                            is-rp
                            is-rp-loose) ()))))

(defthmd ex-from-rp-loose-is-ex-from-rp
  (implies (rp-syntaxp term)
           (equal (ex-from-rp-loose term)
                  (ex-from-rp term)))
  :hints (("Goal"
           :in-theory (e/d (is-rp-loose
                            is-rp
                            ex-from-rp
                            ex-from-rp-loose) ()))))


(defthm car-of-ex-from-rp-is-not-rp
  (implies (rp-syntaxp term)
           (not (equal (car (ex-from-rp term))
                       'rp)))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-rp) ()))))


(defthm dont-rw-syntaxp-dont-rw-syntax-fix
  (dont-rw-syntaxp (dont-rw-syntax-fix dont-rw))
  :hints (("Goal"
           :in-theory (e/d (dont-rw-syntax-fix)
                           (DONT-RW-SYNTAXP)))))

 
(defthm pseudo-termp2-implies-dont-rw-syntaxp
  (implies (pseudo-termp2 term)
	   (dont-rw-syntaxp term)))

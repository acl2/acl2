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
(make-flag rp-termp :defthm-macro-name defthm-rp-termp)
(make-flag beta-search-reduce :defthm-macro-name defthm-beta-search-reduce)
#|(make-flag all-falist-consistent :defthm-macro-name
           defthm-all-falist-consistent)||#
#|(make-flag rp-syntaxp :defthm-macro-name defthm-rp-syntaxp)||#
(make-flag lambda-exp-free-p :defthm-macro-name defthm-lambda-exp-free-p)

(make-flag get-lambda-free-vars :defthm-macro-name defthm-get-lambda-free-vars)

(make-flag ex-from-rp-all2 :defthm-macro-name defthm-ex-from-rp-all2)

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

(set-ignore-ok t)

(make-event
 `(defthm rp-termp-implies
    (implies (rp-termp term)
             ,(caddr (meta-extract-formula
                      'rp-termp state)))
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

(defthm rp-termp-dumb-negate-lit2
  (implies (rp-termp term)
           (rp-termp (dumb-negate-lit2 term)))
  :hints (("goal" :in-theory (enable rp-term-listp
                                     dumb-negate-lit2))))

#|(defthm-remove-return-last
  (defthm rp-termp-remove-return-last
    (implies (rp-termp term)
             (rp-termp (remove-return-last term)))
    :flag remove-return-last)
  (defthm rp-term-listp-remove-return-last-subterms
    (implies (rp-term-listp subterms)
             (rp-term-listp (remove-return-last-subterms subterms)))
    :flag remove-return-last-subterms)
  :hints (("Goal" :in-theory (enable rp-term-listp
                                     rp-termp))))||#

(defthm-rp-termp
  (defthm rp-termp-implies-pseudo-termp
    (implies (rp-termp term)
             (pseudo-termp term))
    :flag rp-termp)

  (defthm rp-term-list-implies-pseudo-term-listp
    (implies (rp-term-listp lst)
             (pseudo-term-listp lst))
    :flag rp-term-listp)
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm strip-cdrs-pseudo-termlistp2
  (implies
   (and (rp-term-listp (strip-cdrs alist))
        (cdr (assoc-equal key alist)))
   (rp-termp (cdr (assoc-equal key alist)))))

(defthm rp-termp-bindings-lemma1
  (implies (and (rp-term-listp (strip-cdrs bindings))
                (consp (assoc-equal term bindings)))
           (cdr (assoc-equal term bindings))))

(defthm rp-term-listp-is-true-listp
  (implies (rp-term-listp lst)
           (true-listp lst))
  :hints (("Goal" :expand (rp-term-listp lst))))

(encapsulate
  nil
  (local
   (in-theory (enable is-rp)))

;; Removed in July 2021 by Matt Kaufmann since the right-hand sides of the
;; generated rules are now all constants, due to enhancements to
;; remove-guard-holders.
#||
  (defthm is-synp-implies
    (implies (is-synp term)
             (CASE-MATCH TERM (('SYNP & & &) T)
               (& NIL)))
    :hints (("Goal" :in-theory (enable is-synp))))
||#

  (defthm pseudo-termlistp-extract-from-rp
    (implies (and (rp-termp term)
                  (not (quotep (ex-from-rp term))))
             (rp-term-listp (cdr (ex-from-rp term))))
    :hints (("Goal"
             :Expand (rp-termp term)
             :in-theory (e/d (is-rp) ()))))

  (defthm rp-termp-extract-from-rp
    (implies (and (rp-termp term))
             (rp-termp (ex-from-rp term))))

  (defthm extract-from-synp-to-ex-from-rp
    (equal (extract-from-synp term)
           (ex-from-synp term))
    :hints (("Goal" :in-theory (enable is-synp ex-from-synp extract-from-synp))))

  (defthm pseudo-termp-extract-from-synp
    (implies (rp-termp term)
             (rp-termp (ex-from-synp term)))
    :hints (("Goal" :in-theory (enable extract-from-synp))))

  (defthm atom-rp-termp-is-symbolp
    (implies (and (atom x) (rp-termp x)) (symbolp x)))

  (defthm rp-termp-context-from-rp
    (implies (and (rp-termp term)
                  (rp-term-listp context))
             (rp-term-listp (context-from-rp term context)))
    :hints (("goal"
             :in-theory (e/d (context-from-rp ex-from-rp is-rp) ())
             :expand (rp-termp term))))

  (defthm put-term-in-cons-is-pseudo-termp
    (rp-termp (put-term-in-cons term))
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
    (implies (and (rp-termp term)
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
  :hints (("Goal" :in-theory (enable rp-term-listp
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
  (implies (and (rp-termp term)
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

#|(defthm all-falist-consistent-bindings-lemma1
  (implies (all-falist-consistent-bindings bindings)
           (all-falist-consistent (cdr (assoc-equal term bindings)))))||#

#|(encapsulate
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
                                is-falist)))))||#

#|(defthm all-falist-consistent-lst-cdr-term-lemma
  (implies (and (all-falist-consistent term)
                (not (equal (car term) 'quote)))
           (all-falist-consistent-lst (cdr term)))
  :hints (("Goal"
           :do-not-induct t
           :expand ((all-falist-consistent term)
                    (FALIST-CONSISTENT TERM)
                    (ALL-FALIST-CONSISTENT (CADR TERM))
                    (ALL-FALIST-CONSISTENT-LST (CDR TERM)))
           :in-theory (enable is-falist all-falist-consistent-lst))))||#

#|(defthm-all-falist-consistent
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
                           (falist-consistent)))))||#

(encapsulate
  nil

  (local
   (defthm lemma1
     (implies (and (is-lambda (cons (car term) subterms))
                   (rp-termp term))
              (is-lambda-strict term))
     :rule-classes :forward-chaining
     :hints (("Goal"
              :in-theory (e/d (is-lambda-strict is-lambda) ())))))

  (defthm get-lambda-free-vars-of-cons-car-term-subterms
    (implies (and (rp-termp term)
                  (mv-nth 0 (get-lambda-free-vars-lst subterms)))
             (mv-nth 0 (get-lambda-free-vars (cons (car term)
                                                   subterms))))
    :otf-flg t
    :hints (("Goal"
             :expand ((get-lambda-free-vars (cons (car term)
                                                  subterms)))
             :in-theory (e/d () ())))))

(defthm-rp-termp
  (defthm rp-termp-implies-get-lambda-free-vars
    (implies (rp-termp term)
             (mv-nth 0
                     (get-lambda-free-vars term)))
    :flag rp-termp)
  (defthm rp-term-listp-implies-get-lambda-free-vars-lst
    (implies (rp-term-listp lst)
             (mv-nth 0
                     (get-lambda-free-vars-lst lst)))
    :flag rp-term-listp)
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm get-lambda-free-vars-of-bindings
  (implies (and (rp-term-listp (strip-cdrs bindings))
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

  #|(local
  ;; this was used when lambda expressions were allowed
  (defthm rp-termp-cons-car-term-subterms-lemma1
  (implies (and (rp-termp term)
  (consp term)
  (consp (car term))
  (equal (len subterms)
  (len (cdr term)))
;(mv-nth 0 (get-lambda-free-vars-lst subterms)) ;
  #|(lambda-exp-free-listp subterms)||#
  (rp-term-listp subterms))
  (rp-termp (cons (car term) subterms)))
  :otf-flg t
  :hints (("Goal"
  :do-not-induct t
  :expand ((rp-termp term)
  (GET-LAMBDA-FREE-VARS (CONS (CAR TERM) SUBTERMS))
  (is-lambda-strict (cons (car term) subterms))
  (IS-LAMBDA (CONS (CAR TERM) SUBTERMS)))
  :in-theory (e/d () (get-lambda-free-vars))))))||#


  (defthm rp-termp-cons-car-term-subterms
    (implies (and (rp-termp term)
                  (consp term)
                  #|(or ;(atom (car term))
                  #|(and (equal (len subterms)
                  (len (cdr term)))
                  #|(lambda-exp-free-listp subterms)||#)||#)||#
                  (not (equal (car term) 'quote))
                  (force (or (not (equal (car term) 'rp))
                             (is-rp (cons (car term) subterms))))
                  (force (or (not (equal (car term) 'falist))
                             (falist-consistent (cons (car term) subterms))))
                  (rp-term-listp subterms))
             (rp-termp (cons (car term) subterms)))
    :hints (("Goal"
             :in-theory (e/d (is-rp) ())))
    ))

(defthm rp-term-listp-append
  (implies (and (rp-term-listp lst1)
                (rp-term-listp lst2))
           (rp-term-listp (append lst1 lst2)))
  :hints (("Goal" :in-theory (enable append rp-term-listp))))

#|(defthm ALL-FALIST-CONSISTENT-LST-append
  (implies (and (ALL-FALIST-CONSISTENT-LST lst1)
                (ALL-FALIST-CONSISTENT-LST lst2))
           (ALL-FALIST-CONSISTENT-LST (append lst1 lst2)))
  :hints (("Goal" :in-theory (enable append ALL-FALIST-CONSISTENT-LST))))||#

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

;; (defthm RP-SYNTAXP-EX-FROM-RP-TERM
;;   (implies (rp-syntaxp term)
;;            (rp-syntaxp (ex-from-rp term)))
;;   :hints (("Goal"
;;            :induct (ex-from-rp term)
;;            :in-theory (e/d (is-rp
;;                             ex-from-rp) ()))))

;; (defthm-rp-syntaxp
;;   (defthm not-include-rp-means-rp-syntaxp
;;     (implies (not (include-fnc term 'rp))
;;              (rp-syntaxp term))
;;     :flag rp-syntaxp)
;;   (defthm not-include-rp-means-rp-syntaxp-lst
;;     (implies (not (include-fnc-subterms lst 'rp))
;;              (rp-syntaxp-lst lst))
;;     :flag rp-syntaxp-lst))

#|(defthm-remove-return-last
  (defthm not-include-rp-of-remove-return-last
    (implies (not (include-fnc term 'rp))
             (not (include-fnc (remove-return-last term) 'rp)))
    :flag remove-return-last)
  (defthm not-include-rp-of-remove-return-last-subterms
    (implies (not (include-fnc-subterms subterms 'rp))
             (Not (include-fnc-subterms (remove-return-last-subterms subterms) 'rp)))
    :flag remove-return-last-subterms))||#

#|(defthm rp-syntaxp-ex-from-rp
  (implies (rp-syntaxp term)
           (rp-syntaxp (ex-from-rp term)))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp
                            is-rp) ()))))||#
#|
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
           (AND (RP-TERM-LISTP CONTEXT)
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
                           (rp-syntaxp)))))||#

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
  (implies (and (rule-syntaxp rule :warning warning)
                (not (rp-rule-metap rule)))
           (and
            (weak-custom-rewrite-rule-p rule)
            (rp-termp (rp-hyp rule))
            (rp-termp (rp-lhs rule))
            (rp-termp (rp-rhs rule))
            ;; (rp-syntaxp (rp-lhs rule))
            (not (include-fnc (rp-lhs rule) 'rp))
            (not (include-fnc (rp-hyp rule) 'rp))
            ;;(rp-syntaxp (rp-rhs rule))
            (not (include-fnc (rp-rhs rule) 'falist))
            (not (include-fnc (rp-hyp rule) 'falist))
            ;;(not (include-fnc (rp-lhs rule) 'if))
            (not (include-fnc (rp-lhs rule) 'synp))
            (no-free-variablep rule)
            (not (include-fnc (rp-lhs rule) 'list))
            (not (include-fnc (rp-hyp rule) 'list))
            (not (include-fnc (rp-rhs rule) 'list))))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable rule-syntaxp))))

(defthmd rule-syntaxp-implies-2
  (implies (and (rule-syntaxp rule :warning warning)
                (rp-rule-metap rule))
           (AND (SYMBOLP (RP-RULE-TRIG-FNC RULE))
                (RP-RULE-TRIG-FNC RULE)
                (SYMBOLP (RP-RULE-META-FNC RULE))
                (RP-RULE-META-FNC RULE)))
  :rule-classes (:rewrite :forward-chaining)
  :hints (("Goal" :in-theory (enable rule-syntaxp))))

(defthm ex-from-rp-loose-of-ex-from-rp-loose
  (equal (ex-from-rp-loose (ex-from-rp-loose term))
         (ex-from-rp-loose term))
  :hints (("Goal"
           :in-theory (e/d (ex-from-rp-loose
                            is-rp-loose) ()))))

;; (defthm all-falist-consistent-of-ex-from-rp-loose
;;   (implies (all-falist-consistent term)
;;            (all-falist-consistent (ex-from-rp-loose term)))
;;   :hints (("Goal"
;;            :in-theory (e/d (ex-from-rp-loose
;;                             is-rp-loose) ()))))

;; (defthm rp-termp-ex-from-rp-loose
;;   (implies (rp-termp term)
;;            (rp-termp (ex-from-rp-loose term)))
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-termp
;;                             ex-from-rp-loose
;;                             is-rp-loose) ()))))

;; (defthm rp-syntaxp-ex-from-rp-loose
;;   (implies (rp-syntaxp term)
;;            (rp-syntaxp (ex-from-rp-loose term)))
;;   :hints (("Goal"
;;            :in-theory (e/d (rp-syntaxp
;;                             ex-from-rp-loose
;;                             is-rp-loose) ()))))

;; (defthm all-falist-consistent-of-ex-from-rp
;;   (implies (all-falist-consistent term)
;;            (all-falist-consistent (ex-from-rp  term)))
;;   :hints (("Goal"
;;            :in-theory (e/d (ex-from-rp
;;                             is-rp ) ()))))

(defthm
  rp-termp-ex-from-rp
  (implies (rp-termp term)
           (and (rp-termp (ex-from-rp term))
                (rp-termp (ex-from-rp-loose term))))
  :hints
  (("goal" :in-theory
    (e/d (ex-from-rp-loose ex-from-rp is-rp-loose is-rp)
         nil))))

;; (defthm all-falist-consistent-ex-from-rp-loose
;;   (implies (all-falist-consistent term)
;;            (all-falist-consistent (ex-from-rp-loose term)))
;;   :hints (("Goal"
;;            :in-theory (e/d (all-falist-consistent
;;                             is-falist
;;                             ex-from-rp-loose
;;                             is-rp-loose) ()))))

(defthm rp-termp-cadr
  (implies (and (rp-termp term)
                (consp term)
                (not (quotep term))
                (consp (cdr term)))
           (rp-termp (cadr term)))
  :hints (("Goal"
           :in-theory (e/d (rp-termp
                            is-rp
                            ex-from-rp-loose
                            is-rp-loose) ()))))

#|(defthm rp-syntaxp-cadr
  (implies (and (rp-syntaxp term)
                (consp term)
                (not (quotep term))
                (not (equal (car term) 'rp))
                (consp (cdr term)))
           (rp-syntaxp (cadr term)))
  :hints (("Goal"
           :in-theory (e/d (rp-termp
                            ex-from-rp-loose
                            is-rp-loose) ()))))||#

#|(defthm all-falist-consistent-cadr
  (implies (and (all-falist-consistent term)
                (consp term)
                (not (quotep term))
                (consp (cdr term)))
           (all-falist-consistent (cadr term)))
  :hints (("Goal"
           :in-theory (e/d (all-falist-consistent
                            ex-from-rp-loose
                            is-rp-loose) ()))))||#

#|(defthm all-falist-consistent-caddr
  (implies (and (all-falist-consistent term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term)))
           (all-falist-consistent (caddr term)))
  :hints (("Goal"
           :in-theory (e/d (all-falist-consistent
                            ex-from-rp-loose
                            is-rp-loose) ()))))||#

#|(defthm all-falist-consistent-cadddr
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
                            is-rp-loose) ()))))||#

(defthm rp-termp-caddr
  (implies (and (rp-termp term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term)))
           (rp-termp (caddr term)))
  :hints (("Goal"
           :in-theory (e/d (rp-termp
                            is-rp
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm rp-termp-cadddr
  (implies (and (rp-termp term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term))
                (consp (cdddr term)))
           (rp-termp (cadddr term)))
  :hints (("Goal"
           :in-theory (e/d (rp-termp
                            is-rp
                            ex-from-rp-loose
                            is-rp-loose) ()))))

(defthm rp-termp-caddddr
  (implies (and (rp-termp term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term))
                (consp (cdddr term))
                (consp (cddddr term)))
           (rp-termp (car (cddddr term))))
  :hints (("Goal"
           :in-theory (e/d (rp-termp
                            is-rp
                            ex-from-rp-loose
                            is-rp-loose) ()))))

#|(defthm rp-syntaxp-caddr
  (implies (and (rp-syntaxp term)
                (consp term)
                (not (quotep term))
                ;(not (equal (car term) 'rp))
                (consp (cdr term))
                (consp (cddr term)))
           (rp-syntaxp (caddr term)))
  :hints (("Goal"
           :in-theory (e/d (rp-termp
                            ex-from-rp-loose
                            is-rp-loose) ()))))||#

#|(defthm rp-syntaxp-cadddr
  (implies (and (rp-syntaxp term)
                (consp term)
                (not (quotep term))
                (consp (cdr term))
                (consp (cddr term))
                (consp (cdddr term)))
           (rp-syntaxp (cadddr term)))
  :hints (("Goal"
           :expand ((rp-syntaxp term))
           :in-theory (e/d (rp-termp
                            ex-from-rp-loose
                            rp-syntaxp
                            is-rp
                            is-rp-loose) ()))))||#

(defthmd ex-from-rp-loose-is-ex-from-rp
  (implies (rp-termp term)
           (equal (ex-from-rp-loose term)
                  (ex-from-rp term)))
  :hints (("Goal"
           :in-theory (e/d (is-rp-loose
                            is-rp
                            ex-from-rp
                            ex-from-rp-loose) ()))))

(defthm car-of-ex-from-rp-is-not-rp
  (implies (rp-termp term)
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

(defthm rp-termp-implies-dont-rw-syntaxp
  (implies (rp-termp term)
	   (dont-rw-syntaxp term)))

(defthm rp-termp-ex-from-falist
  (implies (rp-termp x)
           (rp-termp (ex-from-falist x)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal"
           :expand (ex-from-falist x)
           :in-theory (e/d () ()))))

(defthm is-falist-strict-to-is-falist
  (implies (rp-termp term)
           (equal (is-falist-strict term)
                  (is-falist term))))

(defthm rp-termp-trans*-list
  (implies (and (rp-term-listp lst)
                (consp lst))
           (rp-termp (trans-list lst))))

(defthm consp-rp-trans-lst
  (equal (consp (rp-trans-lst lst))
         (consp lst))
  :hints (("Goal"
           :induct (len lst)
           :in-theory (e/d () ()))))

(defthm is-rp-rp-trans-lst
  (IMPLIES (AND (RP-TERMP TERM)
                (is-rp term))
           (IS-RP (CONS 'RP (RP-TRANS-LST (CDR TERM)))))
  :hints (("Goal"
           :in-theory (e/d (is-rp) ()))))

(defthm-rp-trans
  (defthm rp-termp-of-rp-trans
    (implies (rp-termp term)
             (rp-termp (rp-trans term)))
    :flag rp-trans)
  (defthm rp-term-listp-of-rp-trans-lst
    (implies (rp-term-listp lst)
             (rp-term-listp (rp-trans-lst lst)))
    :flag rp-trans-lst)
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d ()
                           ()))))

#|(defthm-rp-trans
(defthm rp-trans-is-term-when-list-is-absent
(implies (not (include-fnc term 'list))
(equal (rp-trans term) term))
:flag rp-trans)
(defthm rp-trans-lst-is-lst-when-list-is-absent
(implies (not (include-fnc-subterms lst 'list))
(equal (rp-trans-lst lst) lst))
:flag rp-trans-lst))||#

(defthm rp-state-new-run-returns-rp-statep
  (implies (rp-statep rp-state)
           (rp-statep (rp-state-new-run rp-state)))
  :hints (("Goal"
           :in-theory (e/d (rp-state-new-run
                            rp-statep)
                           ()))))


(defthm RP-TERM-LISTP-of-append
  (implies (and (rp-term-listp lst1)
                (rp-term-listp lst2))
           (rp-term-listp (append lst1 lst2))))


(defthm rp-state-preservedp-of-the-same
  (implies (rp-statep rp-state)
           (rp-state-preservedp rp-state rp-state))
  :hints (("Goal"
           :in-theory (e/d (rp-state-preservedp) ()))))

(defthm rp-state-preservedp-implies-rp-statep
  (implies (and (rp-statep rp-state)
                (rp-state-preservedp rp-state new-rp-state))
           (rp-statep new-rp-state))
  :hints (("Goal"
           :in-theory (e/d (rp-state-preservedp) ()))))

(defthm rp-state-preservedp-implies-valid-rp-state-syntaxp
  (implies (and (valid-rp-state-syntaxp rp-state)
                (rp-state-preservedp rp-state new-rp-state))
           (valid-rp-state-syntaxp new-rp-state))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance RP-STATE-PRESERVEDP-SK-necc
                            (key (VALID-RP-STATE-SYNTAXP-AUX-WITNESS
                                  NEW-RP-STATE))
                            (OLD-RP-STATE rp-state))
                 (:instance VALID-RP-STATE-SYNTAXP-AUX-necc
                            (key (VALID-RP-STATE-SYNTAXP-AUX-WITNESS NEW-RP-STATE))))
           :expand (VALID-RP-STATE-SYNTAXP-AUX NEW-RP-STATE)
           :in-theory (e/d (rp-state-preservedp
                            valid-rp-state-syntaxp)
                           (RP-STATE-PRESERVEDP-SK
                            VALID-RP-STATE-SYNTAXP-AUX
                            RP-STATEP)))))



#|(local
 (defthmd rp-termp-ex-from-rp-all2-lemma
     (implies (syntaxp (not (include-fnc term 'ex-from-rp)))
              (equal (rp-termp term)
                     (and (hide (rp-termp term))
                          (rp-termp (ex-from-rp term))))) 
  :hints
  (("goal"
    :expand (hide (rp-termp term))
    :in-theory
    (e/d (ex-from-rp-loose ex-from-rp is-rp-loose is-rp)
         nil)))))|#
 

(defthm-ex-from-rp-all2
    (defthm rp-termp-ex-from-rp-all2
        (implies (rp-termp term)
                 (rp-termp (ex-from-rp-all2 term)))
      :flag ex-from-rp-all2)
    (defthm rp-term-listp-ex-from-rp-all2-lst
        (implies (rp-term-listp lst)
                 (rp-term-listp (ex-from-rp-all2-lst lst)))
      :flag ex-from-rp-all2-lst)
  :hints (("Goal"
           :do-not-induct t
           :expand (RP-TERMP (EX-FROM-RP TERM))
           :in-theory (e/d (
                            EX-FROM-RP-ALL2
                            IS-RP-LOOSE
                            is-rp
                            ;;rp-termp-ex-from-rp-all2-lemma
                            ex-from-rp-all2-lst
                            )
                           (ex-from-rp
                            ;;FALIST-CONSISTENT
                            RP-TERMP-EX-FROM-RP
                            RP-TERMP-CONS-CAR-TERM-SUBTERMS
                            )))))

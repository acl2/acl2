; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2020, Regents of the University of Texas
; All rights reserved.
; Copyright (C) 2022 Intel Corporation

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

(include-book "../meta-rule-macros")

(include-book "../misc")

(local
 (include-book "../proofs/aux-function-lemmas"))

(local
 (include-book "../proofs/proof-function-lemmas"))

(local
 (include-book "../proofs/match-lhs-lemmas"))

(local
 (include-book "../proofs/rp-equal-lemmas"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Casesplit from context

;; when the meta function is disabled
(def-rp-rule casesplit-from-context-trig-expand
  (equal (casesplit-from-context-trig x)
         x)
  :hints (("Goal"
           :in-theory (e/d (casesplit-from-context-trig)
                           ()))))

(add-rp-rule casesplit-from-context-trig-expand
             :outside-in :both)

(local
 (in-theory (disable rp-equal-cnt
                     (:REWRITE ACL2::LEXORDER-REFLEXIVE)
                     (:REWRITE ACL2::LEXORDER-TRANSITIVE)
                     FALIST-CONSISTENT)))

(acl2::defines cc-st-p
  (define cc-st-p (x)
    :enabled t
    (and (consp x)
         (consp (cdr x))
         (consp (cddr x))
         (booleanp (first (cdr x)))
         (cond ((equal (car x) ':term)
                (if (rp-termp (third x)) t nil))
               ((equal (car x) ':and-list)
                (cc-st-listp (third x)))
               ((equal (car x) ':or-list)
                (cc-st-list-listp (third x))))))
  
  (define cc-st-listp (lst)
    :enabled t
    (if (atom lst)
        (equal lst nil)
      (and (cc-st-p (car lst))
           (cc-st-listp (cdr lst))))
    ///
    (defthm cc-st-listp-of-append
      (implies (and (cc-st-listp lst1)
                    (cc-st-listp lst2))
               (cc-st-listp (append lst1 lst2))))

    (defthm cc-st-listp-implies-true-listp
      (implies (cc-st-listp lst1)
               (true-listp lst1))))

  (define cc-st-list-listp (lst)
    :enabled t
    (if (atom lst)
        (equal lst nil)
      (and (cc-st-listp (car lst))
           (cc-st-list-listp (cdr lst)))))
  ///

  (define cc-st-make (&key
                      (type ':term)
                      ((sign booleanp) 'nil)
                      e)
    :guard (cond ((equal type ':term) (rp-termp e))
                 ((equal type ':and-list) (cc-st-listp e))
                 ((equal type ':or-list) (cc-st-list-listp e)))
    :returns (res cc-st-p :hyp (and (or (equal type ':term)
                                        (equal type ':and-list)
                                        (equal type ':or-list))
                                    (booleanp sign)
                                    (implies (equal type ':term)
                                             (rp-termp e))
                                    (implies (equal type ':and-list)
                                             (cc-st-listp e))
                                    (implies (equal type ':or-list)
                                             (cc-st-list-listp e))))
    (list type sign e))
  
  (define cc-st->type ((st cc-st-p))
    :returns type
    (car st)
    ///
    (defret val-of-<fn>
      (implies (cc-st-p st)
               (or (equal type ':term)
                   (equal type ':and-list)
                   (equal type ':or-list)))
      :rule-classes (:rewrite :type-prescription :forward-chaining))
    (defthm cc-st->type-of-cc-st-make
      (equal (cc-st->type (cc-st-make :type type :sign sign :e e))
             type)
      :hints (("Goal"
               :in-theory (e/d (CC-ST-MAKE) ())))))

  (local
   (in-theory (enable cc-st->type)))

  (define cc-st-remove-sign ((st cc-st-p))
    :returns (res cc-st-p :hyp (cc-st-p st)
                  :hints (("Goal"
                           :expand ((:free (x y)
                                           (CC-ST-P (cons x y)))))))
    (list* (cc-st->type st) nil (cddr st)))

  (define cc-st->e ((st cc-st-p))
    :returns (e)
    (third st)
    ///
    (defthm acl2-count-of-cc-st->term
      (implies (cc-st-p st)
               (o< (acl2-count (cc-st->e st))
                   (acl2-count st))))

    (defret rp-termp-of-<fn>
      (implies (and (cc-st-p st)
                    (equal (cc-st->type st) ':term))
               (rp-termp e)))
    
    (defret CC-ST-LIST-LISTP-of-<fn>
      (implies (and (cc-st-p st)
                    (equal (cc-st->type st) :or-list))
               (cc-st-list-listp e)))

    (defret CC-ST-LISTP-of-<fn>
      (implies (and (cc-st-p st)
                    (equal (cc-st->type st) :and-list))
               (cc-st-listp e)))

    (defthm cc-st->e-of-cc-st-make
      (equal (cc-st->e (cc-st-make :type type :sign sign :e e))
             e)
      :hints (("Goal"
               :in-theory (e/d (CC-ST-MAKE) ()))))
    )


  (define cc-st->sign ((st cc-st-p))
    :returns (res booleanp :hyp (cc-st-p st)
                  :rule-classes (:rewrite :type-prescription))
    (second st)
    ///
    (defthm acl2-count-of-cc-st->sign
      (implies (cc-st-p st)
               (o< (acl2-count (cc-st->sign st))
                   (acl2-count st))))
    (defthm cons-count-of-cc-st->sign
      (implies (cc-st-p st)
               (< (cons-count (cc-st->sign st))
                  (cons-count st)))
      :hints (("Goal"
               :in-theory (e/d (cons-count) ()))))

    (defthm cc-st->sign-of-cc-st-make
      (equal (cc-st->sign (cc-st-make :type type :sign sign :e e))
             sign)
      :hints (("Goal"
               :in-theory (e/d (CC-ST-MAKE) ())))))

  (defthm CC-ST-LIST-LISTP-of-or*/and*
    (and (equal (CC-ST-LIST-LISTP (or* a b))
                (if a (CC-ST-LIST-LISTP a)
                  (CC-ST-LIST-LISTP b)))
         (equal (CC-ST-LIST-LISTP (and* a b))
                (if a (CC-ST-LIST-LISTP b) t)))
    :hints (("Goal"
             :in-theory (e/d (or* and*) ()))))

  (defthm CC-ST-LISTP-of-or*/and*
    (and (equal (CC-ST-LISTP (or* a b))
                (if a (CC-ST-LISTP a)
                  (CC-ST-LISTP b)))
         (equal (CC-ST-LISTP (and* a b))
                (if a (CC-ST-LISTP b) t)))
    :hints (("Goal"
             :in-theory (e/d (or* and*) ())))))
           


(define cc-st-tree-p (entry)
  :enabled t
  (and (consp entry)
       (consp (cdr entry))
       (cc-st-p (car entry))
       (or (not (cadr entry))
           (cc-st-tree-p (cadr entry)))
       (or (not (cddr entry))
           (cc-st-tree-p (cddr entry))))
  ///
  (define cc-st-tree-make (&key term pos-branch neg-branch)
    :returns (res cc-st-tree-p :hyp (and (cc-st-p term)
                                         (or (not pos-branch)
                                             (cc-st-tree-p pos-branch))
                                         (or (not neg-branch)
                                             (cc-st-tree-p neg-branch))))
    :guard (and (cc-st-p term)
                (or (not pos-branch)
                    (cc-st-tree-p pos-branch))
                (or (not neg-branch)
                    (cc-st-tree-p neg-branch)))
    (list* term pos-branch neg-branch)))
  
  
(acl2::defines cc-st-equal
  :flag-local nil

  (define cc-st-equal ((x cc-st-p)
                       (y cc-st-p))
    :returns equiv
    (and (mbt (and (cc-st-p x) ;; for measure
                   (cc-st-p y)))
         (equal (cc-st->type x)
                (cc-st->type y))
         (equal (cc-st->sign x)
                (cc-st->sign y))
         (cond ((equal (cc-st->type x)
                       :term)
                (rp-equal-cnt (cc-st->e x)
                              (cc-st->e y)
                              3))
               ((equal (cc-st->type x)
                       :and-list)
                (cc-st-equal-lst (cc-st->e x)
                                 (cc-st->e y)))
               ((equal (cc-st->type x)
                       :or-list)
                (cc-st-equal-lst-lst (cc-st->e x)
                                     (cc-st->e y))))))
  (define cc-st-equal-lst ((x cc-st-listp)
                           (y cc-st-listp))
    :returns equiv
    (if (or (atom x)
            (atom y))
        (equal x y)
      (and (cc-st-equal (car x) (car y))
           (cc-st-equal-lst (cdr x) (cdr y)))))
  (define cc-st-equal-lst-lst ((x cc-st-list-listp)
                               (y cc-st-list-listp))
    :returns equiv
    (if (or (atom x)
            (atom y))
        (equal x y)
      (and (cc-st-equal-lst (car x) (car y))
           (cc-st-equal-lst-lst (cdr x) (cdr y))))))

(define count-common-cases ((lst1 cc-st-listp)
                            (lst2 cc-st-listp))
  :measure (+ (acl2-count lst1)
              (acl2-count lst2))
  :returns (mv (res natp)
               evals-to-nil)
  (cond ((atom lst1)
         (mv 0 nil))
        ((atom lst2)
         (mv 0 nil))
        ((equal (car lst1) (car lst2))
         (b* (((mv rest rest-evals-to-nil)
               (count-common-cases (cdr lst1)
                                   (cdr lst2))))
           (mv (1+ rest)
               rest-evals-to-nil)))
        ((and (equal (cc-st->type (car lst1)) ':term) 
              (equal (cc-st->e (car lst1)) ''nil))
         (if (cc-st->sign (car lst1))
             (count-common-cases (cdr lst1)
                                 lst2)
           (mv 0 t)))
        ((and (equal (cc-st->type (car lst2)) ':term) 
              (equal (cc-st->e (car lst2)) ''nil))
         (if (cc-st->sign (car lst2))
             (count-common-cases lst1
                                 (cdr lst2))
           (mv 0 t)))
        (t
         (b* (((when (and (not (equal (cc-st->sign (car lst1))
                                      (cc-st->sign (car lst2))))
                          (equal (cc-st-remove-sign (car lst1))
                                 (cc-st-remove-sign (car lst2)))))
               (mv 0 t))
              (e1 (cc-st->e (car lst1)))
              (e2 (cc-st->e (car lst2)))
              (order (not (lexorder e2 e1)))
              ((mv rest rest-evals-to-nil)
               (count-common-cases (if order (cdr lst1) lst1)
                                   (if order lst2 (cdr lst2)))))
           (mv rest
               rest-evals-to-nil)))))

(define collect-cases-merge-lst ((lst1 cc-st-listp)
                                 (lst2 cc-st-listp))
  :measure (+ (acl2-count lst1)
              (acl2-count lst2))
  :returns (mv (res cc-st-listp
                    :hyp (and (cc-st-listp lst1)
                              (cc-st-listp lst2)))
               evals-to-nil)
  (cond ((atom lst1)
         (mv lst2 nil))
        ((atom lst2)
         (mv lst1 nil))
        ((equal (car lst1) (car lst2))
         (b* (((mv rest rest-evals-to-nil)
               (collect-cases-merge-lst (cdr lst1)
                                        (cdr lst2))))
           (mv (cons (car lst1) rest)
               rest-evals-to-nil)))
        ((and (equal (cc-st->type (car lst1)) ':term) 
              (equal (cc-st->e (car lst1)) ''nil))
         (if (cc-st->sign (car lst1))
             (collect-cases-merge-lst (cdr lst1)
                                      lst2)
           (mv nil t)))
        ((and (equal (cc-st->type (car lst2)) ':term) 
              (equal (cc-st->e (car lst2)) ''nil))
         (if (cc-st->sign (car lst2))
             (collect-cases-merge-lst lst1
                                      (cdr lst2))
           (mv nil t)))
        (t
         (b* (((when (and (not (equal (cc-st->sign (car lst1))
                                      (cc-st->sign (car lst2))))
                          (equal (cc-st-remove-sign (car lst1))
                                       (cc-st-remove-sign (car lst2)))))
               (mv nil t))
              (e1 (cc-st->e (car lst1)))
              (e2 (cc-st->e (car lst2)))
              (order (If (> (len e2) (len e1)) t (not (lexorder e2 e1))))
              ((mv rest rest-evals-to-nil)
               (collect-cases-merge-lst (if order (cdr lst1) lst1)
                                        (if order lst2 (cdr lst2)))))
           (mv (cons (if order (car lst1) (car lst2))
                     rest)
               rest-evals-to-nil)))))

(progn
  (define collect-cases-crossx-aux ((e1 cc-st-listp)
                                    (lst2 cc-st-list-listp))
    :returns (res cc-st-list-listp
                  :hyp (and (cc-st-list-listp lst2)
                            (cc-st-listp e1)))
    (if (atom lst2)
        nil
      (b* (((mv & evals-to-nil)
            (count-common-cases e1 (car lst2)))
           ((when evals-to-nil)
            (collect-cases-crossx-aux e1 (cdr lst2)))
           ((mv cur evals-to-nil)
            (collect-cases-merge-lst e1 (car lst2))))
        (if (not evals-to-nil)
            (cons cur
                  (collect-cases-crossx-aux e1 (cdr lst2)))
          (collect-cases-crossx-aux e1 (cdr lst2))))))

  (define collect-cases-crossx ((lst1 cc-st-list-listp)
                                (lst2 cc-st-list-listp))
    :returns (res cc-st-list-listp
                  :hyp (and (cc-st-list-listp lst2)
                            (cc-st-list-listp lst1)))
    (if (atom lst1)
        nil
      (append (collect-cases-crossx-aux (car lst1) lst2)
              (collect-cases-crossx (cdr lst1) lst2)))))

(progn
  (define collect-cases-negate-lst ((e cc-st-listp))
    :returns (res)
    (if (atom e)
        nil
      (cons
       (cond ((equal (cc-st->type (car e)) :term)
              (b* ((cur (car e))
                   (sign (cc-st->sign cur))
                   (term (cc-st->e cur)))
                (list (cc-st-make :type :term
                                  :sign (not sign)
                                  :e term))))
             ((equal (cc-st->type (car e)) :and-list)
              (b* ((cur (car e))
                   (sign (cc-st->sign cur))
                   (and-list (cc-st->e cur)))
                ;;(if sign
                ;;  (collect-cases-negate-lst and-list)
                (list (cc-st-make :type :and-list
                                  :sign (not sign)
                                  :e and-list)))) ;;)
             ((equal (cc-st->type (car e)) :or-list)
              (b* ((cur (car e))
                   (sign (cc-st->sign cur))
                   (or-list (cc-st->e cur)))
                (list (cc-st-make :type :or-list
                                  :sign (not sign)
                                  :e or-list)))))
       (collect-cases-negate-lst (cdr e))))
    ///
    (defret cc-st-list-listp-of-collect-cases-negate-lst
      (implies (cc-st-listp e)
               (and (cc-st-list-listp res)
                    (implies (consp e) res)
                    ))))

  (define collect-cases-negate-lst-lst ((lst cc-st-list-listp))
    :returns (res cc-st-list-listp
                  :hyp (cc-st-list-listp lst))
    (if (atom lst)
        '(())
      (collect-cases-crossx (collect-cases-negate-lst (car lst))
                            (collect-cases-negate-lst-lst (cdr lst)))))

  (define collect-cases-negate-lst-lst-lw ((lst cc-st-list-listp))
    :returns (res cc-st-listp
                  :hyp (cc-st-list-listp lst))
    (if (atom lst)
        nil
      (cons (cc-st-make :type :and-list
                        :sign t
                        :e (car lst))
            (collect-cases-negate-lst-lst-lw (cdr lst)))))

  (define collect-cases-negate-main ((lst cc-st-list-listp))
    :returns (res cc-st-list-listp
                  :hyp (cc-st-list-listp lst))
    (b* ((res1 (collect-cases-negate-lst-lst lst))
         ((unless (> (len res1) (* 4 (len lst))))
          res1)
         (res2 (collect-cases-negate-lst-lst-lw lst)))
      `(,res2))))

(verify-guards cons-count)

(define collect-cases-merge-lst-lst ((lst1 cc-st-list-listp)
                                     (lst2 cc-st-list-listp))
  :measure (+ (acl2-count lst1)
              (acl2-count lst2))
  :returns (res cc-st-list-listp
                :hyp (and (cc-st-list-listp lst1)
                          (cc-st-list-listp lst2)))
  (cond ((atom lst1)
         lst2)
        ((atom lst2)
         lst1)
        ((equal (car lst1) (car lst2))
         (b* ((rest
               (collect-cases-merge-lst-lst (cdr lst1)
                                            (cdr lst2))))
           (cons (car lst1) rest)))
        (t
         (b* ((cur1 (car lst1))
              (cur2 (car lst2))
              (order (if (> (Len cur2) (Len cur1)) ;;(cons-count-compare cur2 (cons-count cur1))
                         t
                         (not (lexorder cur2 cur1))))
              (rest
               (collect-cases-merge-lst-lst (if order (cdr lst1) lst1)
                                            (if order lst2 (cdr lst2)))))
           (cons (if order (car lst1) (car lst2))
                 rest))))
  ///
  (defret collect-cases-merge-lst-lst-never-nil
    (implies (and (cc-st-list-listp lst1)
                  (cc-st-list-listp lst2)
                  (or lst1 lst2))
             res)))


(define collect-cases-sort-lst-lst ((lst1 cc-st-list-listp))
  :verify-guards :after-returns
  :prepwork ((local
              (defthm len-of-evens/odds
                (implies (and (consp lst)
                              (consp (cdr lst)))
                         (and (< (len (evens lst))
                                 (len lst))
                              (< (len (odds lst))
                                 (len lst))))
                :hints (("Goal"
                         :expand ((EVENS (CDDR LST)))
                         :induct (and (evens lst)
                                      (len lst))
                         :in-theory (e/d () ())))))
             (local
              (defthm cc-st-list-listp-evens/odds
                (implies (and (cc-st-list-listp lst1)
                              (consp (cdr lst1)))
                         (and (cc-st-list-listp (evens lst1))
                              (cc-st-list-listp (odds lst1))))))
             (Local
              (in-theory (disable len odds evens))))
  :measure (len lst1)
  :returns (res cc-st-list-listp :hyp (cc-st-list-listp lst1))
  (if (endp (cdr lst1)) lst1
    (collect-cases-merge-lst-lst
     (collect-cases-sort-lst-lst (odds lst1))
     (collect-cases-sort-lst-lst (evens lst1)))))
                                    


(define cc-st-to-term-dont-rw-aux (term)
  :guard-hints (("Goal"
                 :in-theory (e/d (is-rp-loose) ())))
  (cond ((or (atom term)
             (quotep term))
         nil)
        ((is-rp-loose term)
         `(nil t ,(cc-st-to-term-dont-rw-aux (caddr term))))
        (t `(nil ,(repeat (len (cdr term)) t))))) 

(acl2::defines cc-st-to-term
  :flag-local nil
  (define cc-st-to-term ((st cc-st-p))
    :returns (mv (res rp-termp :hyp (cc-st-p st))
                 (dont-rw))
    (cond ((not (mbt (cc-st-p st)))
           (mv nil nil))
          ((equal (cc-st->type st) :term)
           (b* ((term (cc-st->e st)))
             (mv (if (cc-st->sign st)
                     `(if ,term 'nil 't)
                   `(if ,term 't 'nil))
                 `(nil ,(cc-st-to-term-dont-rw-aux term) t t))))
          ((equal (cc-st->type st) :and-list)
           (b* ((and-list (cc-st->e st))
                ((mv term dont-rw) (cc-st-lst-to-term and-list)))
             (mv (if (cc-st->sign st)
                     `(if ,term 'nil 't)
                   `(if ,term 't 'nil))
                 `(nil ,dont-rw t t))))
          ((equal (cc-st->type st) :or-list)
           (b* ((or-list (cc-st->e st))
                ((mv term dont-rw) (cc-st-lst-lst-to-term or-list)))
             (mv (if (cc-st->sign st)
                     `(if ,term 'nil 't)
                   `(if ,term 't 'nil))
                 `(nil ,dont-rw t t))))
          (t (mv nil nil))))
  (define cc-st-lst-to-term ((st-lst cc-st-listp))
    :returns (mv (res rp-termp :hyp (cc-st-listp st-lst))
                 (dont-rw))
    (if (atom st-lst)
        (mv ''t t)
      (b* (((mv term1 dont-rw1) (cc-st-to-term (car st-lst)))
           ((mv term2 dont-rw2) (cc-st-lst-to-term (cdr st-lst))))
        (Mv `(if ,term1 ,term2 'nil)
            `(nil ,dont-rw1 ,dont-rw2 t)))))
  (define cc-st-lst-lst-to-term ((st-lst-lst cc-st-list-listp))
    :returns (mv (res rp-termp :hyp (cc-st-list-listp st-lst-lst))
                 (dont-rw))
    (if (atom st-lst-lst)
        (mv ''nil t)
      (b* (((mv term1 dont-rw1) (cc-st-lst-to-term (car st-lst-lst)))
           ((mv term2 dont-rw2) (cc-st-lst-lst-to-term (cdr st-lst-lst))))
        (mv `(if ,term1 't ,term2)
            `(nil ,dont-rw1 t ,dont-rw2))))))

(define collect-unburied-cases ((term rp-termp)
                                &key
                                ((iff-flg booleanp) 't))
  :returns (mv res evals-to-nil)
  :verify-guards nil
  
  (cond
   ((equal term ''nil)
    (mv `((,(cc-st-make :E ''nil)))
        iff-flg))
   ((atom term)
    (mv `((,(cc-st-make :E term))) nil))
   ((quotep term)
    (mv `((,(cc-st-make :e term))) nil))
   ((is-if term)
    (b* ((a (cadr term))
         (b (caddr term))
         (c (cadddr term))
         ((mv cases-a a-eval-to-nil) (collect-unburied-cases a :iff-flg t))
         ((when a-eval-to-nil) (collect-unburied-cases c :iff-flg iff-flg))
         ((mv cases-b b-eval-to-nil) (collect-unburied-cases b :iff-flg iff-flg))
         ((mv cases-c c-eval-to-nil) (collect-unburied-cases c :iff-flg iff-flg)))
      (mv (collect-cases-merge-lst-lst (and (not b-eval-to-nil)
                                            (collect-cases-crossx cases-a cases-b))
                                       (and (not c-eval-to-nil)
                                            (collect-cases-crossx (collect-cases-negate-main cases-a)
                                                                  cases-c)))
          (and b-eval-to-nil c-eval-to-nil))))
   (t (mv `((,(cc-st-make :e term))) nil)))
  ///
  (defret cc-st-list-listp-of<fn>
    (implies (rp-termp term)         ;
             (cc-st-list-listp res)) ;
    :fn collect-unburied-cases)

  (verify-guards collect-unburied-cases-fn))

(define group-long-and-chain ((term rp-termp)
                              (iff-flg booleanp)
                              (cnt integerp))
  :Returns (mv (res cc-st-listp :hyp (rp-termp term))
               (valid booleanp))
  (case-match term
    (('if e1 rest ''nil)
     (b* (((when (include-fnc e1 'if)) (mv nil nil))
          ((mv rest rest-valid)
           (group-long-and-chain rest iff-flg (1- cnt))))
       (mv (cons (cc-st-make :e e1) rest) rest-valid)))
    (('if & & &)
     (mv nil nil))
    
    (&
     (b* (((unless (< cnt 0)) (mv nil nil))
          ((when iff-flg) (mv (list (cc-st-make :e term)) t)))
       (mv nil (equal term ''t))))))
              



;; (define merge-buried-cases-aux1 ((cur cc-st-listp)
;;                                 (lst2 cc-st-list-listp)
;;                                 (index natp))
;;   ;; index should start with 0
;;   :returns (mv (res-index integerp :hyp (natp index))
;;                (common-cases integerp))
;;   :verify-guards :after-returns
;;   (if (atom lst2)
;;       (mv -1 -1)
;;     (b* (((mv rest-index rest-common-cases)
;;           (merge-buried-cases-aux1 cur (cdr lst2)
;;                                   (1+ index)))
;;          ((mv cur-common-cases cur-evals-to-nil)
;;           (count-common-cases cur (car lst2)))
;;          ((when cur-evals-to-nil)
;;           (mv rest-index rest-common-cases)))
;;       (if (or (equal rest-index -1)
;;               (> cur-common-cases rest-common-cases))
;;           (mv index cur-common-cases)
;;         (mv rest-index rest-common-cases))))
;;   ///
;;   (defret index-is-inbounds-for-merge-buried-cases-aux1
;;     (implies (not (equal res-index -1))
;;              (and (< (- res-index index)
;;                      (len lst2))
;;                   (<= 0 (- res-index index)))))

;;   (defret index-is-inbounds-for-merge-buried-cases-aux1-index=0
;;     (implies (and (not (equal res-index -1))
;;                   (equal index 0))
;;              (and (< res-index (len lst2))
;;                   (<= 0 res-index)))
;;     :hints (("Goal"
;;              :do-not-induct t
;;              :use ((:instance index-is-inbounds-for-merge-buried-cases-aux1
;;                               (index 0)))
;;              :in-theory (e/d ()
;;                              (index-is-inbounds-for-merge-buried-cases-aux1))))))

;; (define merge-buried-cases-aux2 ((lst1 cc-st-list-listp)
;;                                  (lst2 cc-st-list-listp))
;;   :returns (res cc-st-list-listp
;;                 :hyp (and (cc-st-list-listp lst1)
;;                           (cc-st-list-listp lst2)))
;;   :prepwork ((local
;;               (defthm cc-st-listp-of-nth
;;                 (implies (and (natp index)
;;                               (< index (len lst))
;;                               (cc-st-list-listp lst))
;;                          (cc-st-listp (nth index lst)))))

;;              (local
;;               (defthm cc-st-list-listp-implies-true-listp
;;                 (implies (cc-st-list-listp lst)
;;                          (true-listp lst))))

;;              (local
;;               (defthm cc-st-list-listp-of-update-nth
;;                 (implies (and (natp index)
;;                               (< index (len lst))
;;                               (cc-st-list-listp lst)
;;                               (cc-st-listp val))
;;                          (cc-st-list-listp (update-nth index val lst))))))
;;   (if (atom lst1)
;;       lst2
;;     (b* ((rest (merge-buried-cases-aux2 (cdr lst1) lst2))
;;          ((mv index &)
;;           (merge-buried-cases-aux1 (car lst1) rest 0))
;;          ((when (equal index -1))
;;           (cons (car lst1) rest))
;;          ((mv cur evals-to-nil)
;;           (collect-cases-merge-lst (car lst1)
;;                                    (nth index rest))))
;;       (if evals-to-nil
;;           (cons (car lst1) rest)
;;         (update-nth index cur rest)))))

;; (define merge-buried-cases ((lst1 cc-st-list-listp)
;;                             (lst2 cc-st-list-listp))
;;   :returns (res cc-st-list-listp
;;                 :hyp (and (cc-st-list-listp lst1)
;;                           (cc-st-list-listp lst2)))
;;   (b* ((unsorted-lst (merge-buried-cases-aux2 lst1 lst2))
;;        (lst (collect-cases-sort-lst-lst unsorted-lst)))
;;     lst))


(acl2::defines collect-buried-cases
  :flag-local nil
  (define collect-buried-cases ((term rp-termp)
                                &key
                                ((iff-flg booleanp) 't))
    :returns (mv res subcases evals-to-nil)
    :verify-guards nil
  
    (cond
     ((equal term ''nil)
      (mv (if iff-flg `((,(cc-st-make :e ''nil))) `(()))  
          '(())
          iff-flg))
     ((or (atom term)
          (equal (car term) 'falist))
      (mv (If iff-flg `((,(cc-st-make :E term))) `(())) '(()) nil))
     ((quotep term)
      (mv `(()) '(()) nil))
     ((is-if term)
      (b* (((mv and-chain and-chain-valid)
            (group-long-and-chain term iff-flg 2))
           ((when and-chain-valid) (mv (if iff-flg
                                           `((,(cc-st-make :e and-chain
                                                           :type :and-list)))
                                         `((,(cc-st-make :e and-chain
                                                         :type :and-list))
                                           (,(cc-st-make :e and-chain
                                                         :sign t
                                                         :type :and-list))))
                                       '(())
                                       nil))
           (a (cadr term))
           (b (caddr term))
           (c (cadddr term))
           ((mv cases-a subcases-a a-eval-to-nil) (collect-buried-cases a :iff-flg t))
           ((when a-eval-to-nil) (collect-buried-cases c :iff-flg iff-flg))
           ((mv cases-b subcases-b b-eval-to-nil) (collect-buried-cases b :iff-flg iff-flg))
           ((mv cases-c subcases-c c-eval-to-nil) (collect-buried-cases c :iff-flg iff-flg)))
        (mv (collect-cases-merge-lst-lst (and* (not b-eval-to-nil)
                                               (collect-cases-crossx cases-a cases-b))
                                         (and* (not c-eval-to-nil)
                                               (collect-cases-crossx (collect-cases-negate-main cases-a)
                                                                     cases-c)))
            (collect-cases-crossx (or* subcases-a '(()))
                                  (collect-cases-crossx
                                   (or* (and* (not b-eval-to-nil)
                                              subcases-b)
                                       '(()))
                                   (or* (and* (not c-eval-to-nil)
                                              subcases-c)
                                       '(()))))               
            (and b-eval-to-nil c-eval-to-nil))))
     (t
      (b* ((subcases (collect-buried-cases-lst (cdr term))))
        (mv (if iff-flg `((,(cc-st-make :e term))) `(())) subcases nil)))))
  (define collect-buried-cases-lst ((lst rp-term-listp))
    :returns subcases
    (if (atom lst)
        '(())
      (b* (((mv cases1 subcases1 evals-to-nil)
            (collect-buried-cases (car lst) :iff-flg nil))
           (subcases2 (collect-buried-cases-lst (cdr lst))))
        (collect-cases-crossx
         (or* (and (not evals-to-nil) cases1) '(()))
         (collect-cases-crossx (or* (and* (not evals-to-nil) subcases1)
                                    '(()))
                               (or* subcases2
                                    '(())))))))
                                     
  ///
  (defret-mutual cc-st-list-listp-of-collect-buried-cases
    (defret cc-st-list-listp-of<fn>
      (implies (rp-termp term) ;
               (and (cc-st-list-listp res)
                    (cc-st-list-listp subcases))) ;
      :fn collect-buried-cases)
    (defret cc-st-list-listp-of<fn>
      (implies (rp-term-listp lst)
               (cc-st-list-listp subcases))
      :fn collect-buried-cases-lst))

  (verify-guards collect-buried-cases-lst))


(acl2::Defines dont-rw-for-context-term
  (define dont-rw-for-context-term ((context-term rp-termp))
    (cond ((or (atom context-term)
               (quotep context-term))
           t)
          ((is-if context-term)
           `(Nil ,(dont-rw-for-context-term (cadr context-term))
                 ,(dont-rw-for-context-term (caddr context-term))
                 ,(dont-rw-for-context-term (cadddr context-term))))
          ((include-fnc context-term 'if)
           `(nil . ,(dont-rw-for-context-term-lst (cdr context-term))))
          (t t)))
  (define dont-rw-for-context-term-lst ((lst rp-term-listp))
    (if (atom lst)
        nil
      (cons (dont-rw-for-context-term (car lst))
            (dont-rw-for-context-term-lst (cdr lst))))))


;; (define buried-cases-to-tree ((buried-cases cc-st-list-listp))
;;   (if (atom buried-cases)
      

(define casesplit-from-context-attach-buried ((term rp-termp)
                                              (term-dont-rw)
                                              (context-term rp-termp)
                                              (context-term-dont-rw)
                                              (buried-cases cc-st-list-listp)
                                              (subgoal-prefix stringp)
                                              (cnt integerp))
  :returns (mv (res rp-termp
                    :hyp (and (rp-termp term)
                              (rp-termp context-term)
                              (cc-st-list-listp buried-cases)))
               dont-rw)
  (if (atom buried-cases)
      (mv term t)
    (b* (#|((when (not (car buried-cases)))
          (casesplit-from-context-attach-buried term term-dont-rw
                                                context-term
                                                context-term-dont-rw
                                                (cdr buried-cases)
                                                subgoal-prefix (1- cnt)))|#
         ((mv cur-cond-term ?cur-cond-dont-rw) (cc-st-lst-to-term (car
                                                                  buried-cases)))

         (subgoal-message-1 `(fmt-to-comment-window
                              ',(concatenate 'string
                                             subgoal-prefix "."
                                             (str::int-to-dec-string cnt)
                                             "~%")
                              'nil                  
                              '0 'nil 'NIL))
         #|(subgoal-message-2 `(fmt-to-comment-window
                              ',(concatenate 'string
                                             subgoal-prefix "."
                                             (str::int-to-dec-string (1- cnt))
                                             "~%")
                              'nil                  
                              '0 'NIL 'NIL))|#

         #|(rewriting-cond-message `(fmt-to-comment-window
                                   '"Rewriting final cond ~p0 ~%"
                                   (PAIRLIS2 '(#\0 #\1 #\2 #\3 #\4 #\5)
                                             (CONS ,context-term 'NIL))               
                                   '0 '(nil 5 6 nil) 'NIL))|#
         
         ((when (atom (cdr buried-cases)))
          (mv `(if (dont-rw-context ,cur-cond-term)
                   (if (dont-rw-context ,context-term)
                       (return-last 'progn ,subgoal-message-1 ,term)
                     't)
                 't
                 #|(if (dont-rw-context ,context-term)
                     (return-last 'progn ,subgoal-message-2 ,term) 't)|#)
              `(if (nil ,cur-cond-dont-rw)
                   (if (nil ,context-term-dont-rw)
                       (nil nil nil ,term-dont-rw)
                     t)
                 t
                 #|(if (nil ,context-term-dont-rw)
                     (nil nil nil t)
                   t)|#)))
         ((mv rest rest-dont-rw)
          (casesplit-from-context-attach-buried term term-dont-rw
                                                context-term
                                                context-term-dont-rw
                                                (cdr buried-cases)
                                                subgoal-prefix (1- cnt))))
      (mv `(if (dont-rw-context ,cur-cond-term)
               (if (dont-rw-context ,context-term)
                   (return-last 'progn ,subgoal-message-1 ,term)
                   't)
             ,rest)
          `(nil (dont-rw-context ,cur-cond-dont-rw)
                (if (nil ,context-term-dont-rw)
                    (nil nil nil ,term-dont-rw)
                  t)
                ,rest-dont-rw)))))
         

#|(define remove-nils-from-cc-st-list-list ((lst cc-st-list-listp))
  :Returns (res-lst cc-st-list-listp
                    :hyp (cc-st-list-listp lst))
  (If (atom lst)
      nil
      (if (car lst)
          (cons-with-hint (car lst)
                          (remove-nils-from-cc-st-list-list (cdr lst))
                          lst)
        (remove-nils-from-cc-st-list-list (cdr lst)))))|#
  

(define casesplit-from-context-attach ((term rp-termp)
                                       (term-dont-rw)
                                       (unburied-cases cc-st-list-listp)
                                       (cnt integerp))
  :returns (mv (res rp-termp
                    :hyp (and (rp-termp term)
                              (cc-st-list-listp unburied-cases)))
               dont-rw)
  (if (atom unburied-cases)
      (mv ''t t)
    (b* (((mv rest rest-dontrw)
          (casesplit-from-context-attach term term-dont-rw
                                         (cdr unburied-cases)
                                         (1- cnt)))
         ((mv cond-term cond-term-dont-rw) (cc-st-lst-to-term
                                            (car unburied-cases)))
         ((mv & buried-cases &)
          (collect-buried-cases cond-term))
         #|(buried-cases (remove-nils-from-cc-st-list-list buried-cases))|#
         (- (cw "There are ~p0 buried cases.~%" (len buried-cases)))
         (subgoal-prefix (string-append "Subgoal "
                                         (str::int-to-dec-string cnt)))
         ((mv term-with-buried term-with-buried-dont-rw)
          (casesplit-from-context-attach-buried term term-dont-rw
                                                cond-term cond-term-dont-rw
                                                buried-cases
                                                subgoal-prefix
                                                (len buried-cases)))

         (subgoal-message (string-append subgoal-prefix "~%")))
      (mv `(if (dont-rw-context ,cond-term)
               (return-last 'progn (fmt-to-comment-window ',SUBGOAL-MESSAGE
                                                          'nil                  
                                                          '0 'NIL 'NIL)
                            ,term-with-buried)
             ,rest)
          `(nil t;(nil ,cond-term-dont-rw)
                (nil nil nil ,term-with-buried-dont-rw)
                ,rest-dontrw)))))

(define collect-cases-gather-context-term ((context rp-term-listp))
  :returns (context-term rp-termp :hyp (rp-term-listp context))
  (if (atom context)
      ''t
    (if (include-fnc (car context) 'if)
        `(if ,(car context)
             ,(collect-cases-gather-context-term (cdr context))
           'nil)
      (collect-cases-gather-context-term (cdr context)))))

(define collect-cases-from-context-aux ((term rp-termp)
                                        (dont-rw)
                                        (context rp-term-listp))
  :Returns (mv (res-term rp-termp :hyp (and (rp-termp term)
                                            (rp-term-listp context)))
               dont-rw)
  (b* ((context-term (collect-cases-gather-context-term context))
       (context-term (ex-from-rp-all2 context-term))
       ((when (equal context-term ''t)) (mv term dont-rw))
       ((mv unburied-cases &)
        (collect-unburied-cases context-term))
       (- (cw "There are ~p0 unburied cases.~%" (len unburied-cases))))
    (casesplit-from-context-attach term dont-rw unburied-cases (len unburied-cases))))

(define casesplit-from-context ((term rp-termp)
                                dont-rw
                                (context rp-term-listp))
  :Returns (mv res dont-rw)
  (case-match term
    (('casesplit-from-context-trig term)
     (collect-cases-from-context-aux term
                                     (dont-rw-car (dont-rw-cdr dont-rw))
                                     context))
    (& (mv term dont-rw))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Proofs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(local
 (in-theory (enable DONT-RW-CONTEXT)))

(local
 (acl2::defines eval-of-cc-st
  (define eval-of-cc-st ((st cc-st-p)
                         (a))
    :returns eval-res
    (b* (((unless (mbt (cc-st-p st)))  ;; for measure
          nil)
         (eval
          (cond ((equal (cc-st->type st) :term)
                 (rp-evlt (cc-st->e st) a))
                ((equal (cc-st->type st) :and-list)
                 (eval-of-cc-st-lst (cc-st->e st) a))
                ((equal (cc-st->type st) :or-list)
                 (eval-of-cc-st-lst-lst (cc-st->e st) a)))))
      (if (cc-st->sign st)
          (not eval)
        (if eval t nil))))

  (define eval-of-cc-st-lst  ((lst cc-st-listp)
                              (a))
    :returns eval-res
    (if (atom lst)
        t
      (b* ((cur (car lst))
           (cur-eval (eval-of-cc-st cur a))
           (rest-eval (eval-of-cc-st-lst (cdr lst) a)))
        (and cur-eval rest-eval))))

  (define eval-of-cc-st-lst-lst ((lst-lst cc-st-list-listp)
                                 (a))
    (if (atom lst-lst)
        nil
      (b* ((cur (car lst-lst))
           (cur-eval
            (eval-of-cc-st-lst cur a))
           (rest-eval
            (eval-of-cc-st-lst-lst (cdr lst-lst) a)))
        (or cur-eval rest-eval))))))

(local
 (acl2::defines cc-st-valid-p 
  (define cc-st-valid-p ((st cc-st-p)
                         (a))
    (declare (ignorable a))
    :verify-guards nil
    :returns correct-p
    :measure (acl2-count st)
    (cond ((not (mbt (cc-st-p st))) nil) ;; for measure
          ((equal (cc-st->type st) :term)
           (b* ((term (cc-st->e st)))
             (not (include-fnc term 'rp));;(valid-sc term a)
             ))
          ((equal (cc-st->type st) :and-list)
           (cc-st-lst-valid-p (cc-st->e st) a))
          ((equal (cc-st->type st) :or-list)
           (cc-st-lst-lst-valid-p (cc-st->e st) a))))

  (define cc-st-lst-valid-p  ((lst cc-st-listp)
                              (a))
    :returns correct-p
    :measure (acl2-count lst)
    (if (atom lst)
        (equal lst nil)
      (b* ((cur-valid-p
            (cc-st-valid-p (car lst) a))
           (rest-valid-p
            (cc-st-lst-valid-p (cdr lst) a)))
        (and cur-valid-p rest-valid-p))))
  (define cc-st-lst-lst-valid-p ((lst-lst cc-st-list-listp)
                                 (a))
    :returns correct-p
    :measure (acl2-count lst-lst)
    (if (atom lst-lst)
        (equal lst-lst nil)
      (b* ((cur-valid-p
            (cc-st-lst-valid-p (car lst-lst) a))
           (rest-valid-p
            (cc-st-lst-lst-valid-p (cdr lst-lst) a)))
        (and cur-valid-p rest-valid-p))))))


(local
 (defthm EVAL-OF-CC-ST-LST-LST-of-or*/and*
   (and (equal (EVAL-OF-CC-ST-LST-LST (or* x y) a)
               (if x
                   (EVAL-OF-CC-ST-LST-LST x a)
                 (EVAL-OF-CC-ST-LST-LST y a)))
        (equal (EVAL-OF-CC-ST-LST-LST (and* x y) a)
               (if x
                   (EVAL-OF-CC-ST-LST-LST y a)
                 (EVAL-OF-CC-ST-LST-LST nil a))))))

(local
 (defthm  CC-ST-LST-LST-VALID-P-of-or*/and*
   (and (equal (CC-ST-LST-LST-VALID-P (or* x y) a)
               (if x
                   (CC-ST-LST-LST-VALID-P x a)
                 (CC-ST-LST-LST-VALID-P y a)))
        (equal (CC-ST-LST-LST-VALID-P (and* x y) a)
               (if x
                   (CC-ST-LST-LST-VALID-P y a)
                 (CC-ST-LST-LST-VALID-P nil a))))))
 

#|(acl2::defines cc-st-valid-p2

  :hints (("Goal"
           :in-theory (e/d (CC-ST->SUBCASES) ())))
  (define cc-st-valid-p2 ((st cc-st-p)
                          (a))
    :verify-guards nil
    :returns correct-p
    :measure (acl2-count st)
    (cond ((not (mbt (cc-st-p st))) nil) ;; for measure
          ((equal (cc-st->type st) :term)
           (b* ((term (cc-st->term st))
                (subcases (cc-st->subcases st))
                (subcases-valid-p (cc-st-lst-lst-valid-p2 subcases a)))
             (and subcases-valid-p
                  (valid-sc term a))))
          ((equal (cc-st->type st) :and-list)
           (cc-st-lst-valid-p2 (cc-st->and-list st) a))
          ((equal (cc-st->type st) :or-list)
           (cc-st-lst-valid-p2 (cc-st->or-list st) a))))

  (define cc-st-lst-valid-p2  ((lst cc-st-listp)
                               (a))
    :returns correct-p
    :measure (acl2-count lst)
    (if (atom lst)
        (equal lst nil)
      (b* ((cur-valid-p
            (cc-st-valid-p2 (car lst) a))
           (cur-eval
            (eval-of-cc-st (car lst) a))
           (rest-valid-p
            (cc-st-lst-valid-p2 (cdr lst) a)))
        (and cur-valid-p (implies cur-eval rest-valid-p)))))
  (define cc-st-lst-lst-valid-p2 ((lst-lst cc-st-list-listp)
                                  (a))
    :returns correct-p
    :measure (acl2-count lst-lst)
    (if (atom lst-lst)
        (equal lst-lst nil)
      (b* ((cur-valid-p
            (cc-st-lst-valid-p2 (car lst-lst) a))
           (cur-eval
            (eval-of-cc-st-lst (car lst-lst) a))
           (rest-valid-p
            (cc-st-lst-lst-valid-p2 (cdr lst-lst) a)))
        (and cur-valid-p (implies (not cur-eval) rest-valid-p)))))

  ///
  (defret-mutual cc-st-valid-p-implies-cc-st-valid-p2
    (defret  cc-st-valid-p-implies-cc-st-valid-p2
      (implies (cc-st-valid-p st a)
               correct-p)
      :fn cc-st-valid-p2)
    (defret  cc-st-lst-valid-p-implies-cc-st-lst-valid-p2
      (implies (cc-st-lst-valid-p lst a)
               correct-p)
      :fn cc-st-lst-valid-p2)
    (defret cc-st-lst-lst-valid-p-implies-cc-st-lst-lst-valid-p2
      (implies (cc-st-lst-lst-valid-p lst-lst a)
               correct-p)
      :fn cc-st-lst-lst-valid-p2)
    :hints (("Goal"
             :in-theory (e/d (cc-st-lst-lst-valid-p
                              cc-st-valid-p
                              cc-st-lst-valid-p
                              ) ())))))|#

(local
 (defthm rp-evlt-of-not
   (implies (case-match term (('not &) t))
            (equal (rp-evlt term a)
                   (not (rp-evlt (cadr term) a))))))

(local
 (defthm rp-evlt-of-rp-equal-better
   (implies (rp-equal term1 term2)
            (equal (rp-evlt term1 a)
                   (rp-evlt term2 a)))
   :rule-classes :congruence
   :hints (("Goal"
            :use ((:instance rp-evlt-of-rp-equal))
            :in-theory (e/d ()
                            ())))))

(local
 (defret-mutual cc-st-equal-and-eval-equiv
   (defret cc-st-equal-and-eval-equiv
     (implies (and equiv
                   (syntaxp (not (lexorder y x))))
              (equal (eval-of-cc-st x a)
                     (eval-of-cc-st y a)))
     :fn cc-st-equal)
   (defret cc-st-equal-lst-and-eval-equiv
     (implies (and equiv
                   (syntaxp (not (lexorder y x))))
              (equal (eval-of-cc-st-lst x a)
                     (eval-of-cc-st-lst y a)))
     :fn cc-st-equal-lst)
   (defret cc-st-equal-lst-lst-and-eval-equiv
     (implies (and equiv
                   (syntaxp (not (lexorder y x))))
              (equal (eval-of-cc-st-lst-lst x a)
                     (eval-of-cc-st-lst-lst y a)))
     :fn cc-st-equal-lst-lst)
   :mutual-recursion cc-st-equal
   :hints (("Goal"
            :in-theory (e/d (cc-st-equal
                             cc-st-equal-lst
                             cc-st-equal-lst-lst
                             eval-of-cc-st-LST-LST
                             eval-of-cc-st-LST
                             eval-of-cc-st) ())))))

(local
 (defthm eval-of-cc-st-of-CC-ST-REMOVE-SIGN
   (implies (cc-st-p x)
            (iff (eval-of-cc-st (cc-st-remove-sign x) a)
                 (if (cc-st->sign x)
                     (not (eval-of-cc-st x a))
                   (eval-of-cc-st x a))))
   :hints (("Goal"
            :expand ((eval-of-cc-st X A)
                     (eval-of-cc-st (LIST* (CAR X) NIL (CDDR X))
                                    A))
            :do-not-induct t
            :in-theory (e/d (eval-of-cc-st
                             CC-ST->SIGN
                             CC-ST->TYPE
                             CC-ST->e
                             cc-st-remove-sign) ())))))

(local
 (defthm collect-cases-merge-lst-eval-correct-lemma
   (implies (and
             
             (cc-st-p x)
             (cc-st-p y)
             (equal (cc-st-remove-sign x)
                    (cc-st-remove-sign y))
             #|(cc-st-equal (cc-st-remove-sign x)
             (cc-st-remove-sign y))|#
             (not (equal (cc-st->sign x)
                         (cc-st->sign y)))
             (syntaxp (not (lexorder y x))))
            (iff (eval-of-cc-st x A)
                 (not (eval-of-cc-st y A))))
   :hints (("Goal"
            :use ((:instance eval-of-cc-st-of-CC-ST-REMOVE-SIGN)
                  (:instance eval-of-cc-st-of-CC-ST-REMOVE-SIGN
                             (x y))
                  #|(:instance cc-st-equal-and-eval-equiv
                             (x (CC-ST-REMOVE-SIGN X))
                             (y (CC-ST-REMOVE-SIGN Y)))|#)
            :in-theory (e/d ()
                            (cc-st-equal-and-eval-equiv
                             eval-of-cc-st-of-CC-ST-REMOVE-SIGN))))))

(local
 (defthmd collect-cases-merge-lst-eval-correct-lemma-2
   (implies (and (cc-st-p term)
                 (EQUAL (CC-ST->TYPE term) :TERM)
                 (EQUAL (CC-ST->e term) ''NIL))
            (equal (EVAL-OF-CC-ST term A) (CC-ST->SIGN term)))
   :hints (("Goal"
            :expand (EVAL-OF-CC-ST term A)
            :in-theory (e/d () ())))))

(local
 (defret count-common-cases-evals-to-nil-eval-correct
  (implies (and (cc-st-listp lst1)
                (cc-st-listp lst2))
           (implies evals-to-nil
                    (not (and (eval-of-cc-st-lst lst1 a)
                              (eval-of-cc-st-lst lst2 a)))))
  :fn count-common-cases
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-of-cc-st-LST LST1 A)
                    ;;(eval-of-cc-st (CAR LST1) A)
                    ;;(eval-of-cc-st (CAR LST2) A)
                    (eval-of-cc-st-LST LST2 A))
           :induct (count-common-cases lst1 lst2)
           :in-theory (e/d (eval-of-cc-st-lst
                            collect-cases-merge-lst-eval-correct-lemma-2
                            count-common-cases
                            eval-of-cc-st-lst
                            )
                           (rp-trans
                            
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret count-common-cases-evals-to-nil-eval-correct-nil-1
   (implies (and (eval-of-cc-st-lst lst1 a)
                 (cc-st-listp lst1)
                 (cc-st-listp lst2))
            (implies evals-to-nil
                     (not (eval-of-cc-st-lst lst2 a))))
   :rule-classes :forward-chaining
   :fn count-common-cases
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance count-common-cases-evals-to-nil-eval-correct))))))

(local
 (defret count-common-cases-evals-to-nil-eval-correct-nil-2
   (implies (and (eval-of-cc-st-lst lst2 a)
                 (cc-st-listp lst1)
                 (cc-st-listp lst2))
            (implies evals-to-nil
                     (not (eval-of-cc-st-lst lst1 a))))
   :rule-classes :forward-chaining
   :fn count-common-cases
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance count-common-cases-evals-to-nil-eval-correct))))))

(local
 (defret collect-cases-merge-lst-eval-correct
  (implies (and (cc-st-listp lst1)
                (cc-st-listp lst2))
           (and (cc-st-listp res)
                (implies evals-to-nil
                         (not (and (eval-of-cc-st-lst lst1 a)
                                   (eval-of-cc-st-lst lst2 a))))
                (implies (not evals-to-nil)
                         (equal (eval-of-cc-st-lst res a)
                                (and (eval-of-cc-st-lst lst1 a)
                                     (eval-of-cc-st-lst lst2 a))))))
  :fn collect-cases-merge-lst
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-of-cc-st-LST LST1 A)
                    ;;(eval-of-cc-st (CAR LST1) A)
                    ;;(eval-of-cc-st (CAR LST2) A)
                    (eval-of-cc-st-LST LST2 A))
           :induct (collect-cases-merge-lst lst1 lst2)
           :in-theory (e/d (eval-of-cc-st-lst
                            collect-cases-merge-lst-eval-correct-lemma-2
                            collect-cases-merge-lst
                            eval-of-cc-st-lst
                            )
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-merge-lst-eval-correct-derivative-for-evals-to-nil
  (implies (and (eval-of-cc-st-lst lst1 a)
                evals-to-nil
                (cc-st-listp lst1)
                (cc-st-listp lst2))
           (not (eval-of-cc-st-lst lst2 a)))
  :rule-classes :forward-chaining
  :fn collect-cases-merge-lst
  :hints (("Goal"
           :use ((:instance collect-cases-merge-lst-eval-correct))
           :do-not-induct t
           :in-theory (e/d ()
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-merge-lst-eval-correct-derivative-for-evals-to-nil-2
  (implies (and (eval-of-cc-st-lst lst2 a)
                evals-to-nil
                (cc-st-listp lst1)
                (cc-st-listp lst2))
           (not (eval-of-cc-st-lst lst1 a)))
  :rule-classes :forward-chaining
  :fn collect-cases-merge-lst
  :hints (("Goal"
           :use ((:instance collect-cases-merge-lst-eval-correct))
           :do-not-induct t
           :in-theory (e/d ()
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-merge-lst-eval-valid
  (implies (and (cc-st-listp lst1)
                (cc-st-listp lst2)
                (cc-st-lst-valid-p lst1 a)
                (cc-st-lst-valid-p lst2 a))
           (cc-st-lst-valid-p res a))
  :fn collect-cases-merge-lst
  :hints (("Goal"
           :do-not-induct t
           :expand ()
           :induct (collect-cases-merge-lst lst1 lst2)
           :in-theory (e/d (cc-st-lst-valid-p
                            eval-of-cc-st-lst
                            collect-cases-merge-lst
                            eval-of-cc-st-lst
                            )
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

#|(defret collect-cases-merge-lst-eval-valid2
  (implies (and (cc-st-listp lst1)
                (cc-st-listp lst2)
                (cc-st-lst-valid-p2 lst1 a)
                (cc-st-lst-valid-p2 lst2 a))
           (cc-st-lst-valid-p2 res a))
  :fn collect-cases-merge-lst
  :hints (("Goal"
           :do-not-induct t
           :expand ()
           :induct (collect-cases-merge-lst lst1 lst2)
           :in-theory (e/d (cc-st-lst-valid-p2
                            eval-of-cc-st-lst
                            collect-cases-merge-lst
                            eval-of-cc-st-lst
                            )
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal)))))|#

(local
 (defret collect-cases-crossx-aux-correct
  (implies (and (cc-st-listp e1)
                (cc-st-list-listp lst2))
           (equal (eval-of-cc-st-lst-lst res a)
                  (and (eval-of-cc-st-lst e1 a)
                       (eval-of-cc-st-lst-lst lst2 a))))
  :fn collect-cases-crossx-aux
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-of-cc-st-LST-LST LST2 A))
           :induct (COLLECT-CASES-CROSSX-AUX E1 LST2)
           :in-theory (e/d (eval-of-cc-st-lst-lst
                            collect-cases-crossx-aux
                            eval-of-cc-st-lst)
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-crossx-aux-valid
  (implies (and (cc-st-listp e1)
                (cc-st-list-listp lst2)
                (cc-st-lst-valid-p e1 a)
                (cc-st-lst-lst-valid-p lst2 a))
           (cc-st-lst-lst-valid-p res a))
  :fn collect-cases-crossx-aux
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-of-cc-st-LST-LST LST2 A))
           :induct (COLLECT-CASES-CROSSX-AUX E1 LST2)
           :in-theory (e/d (CC-ST-LST-LST-VALID-P
                            collect-cases-crossx-aux
                            eval-of-cc-st-lst)
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defthm eval-of-cc-st-LST-LST-of-append
  (equal (eval-of-cc-st-LST-LST (append x y) a)
         (or (eval-of-cc-st-LST-LST x a)
             (eval-of-cc-st-LST-LST y a)))
  :hints (("Goal"
           :in-theory (e/d (eval-of-cc-st-LST-LST) ())))))

(local
 (defret collect-cases-crossx-correct
  (implies (and (cc-st-list-listp lst1)
                (cc-st-list-listp lst2))
           (equal (eval-of-cc-st-lst-lst res a)
                  (and (eval-of-cc-st-lst-lst lst1 a)
                       (eval-of-cc-st-lst-lst lst2 a))))
  :fn collect-cases-crossx
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-of-cc-st-LST-LST LST2 A))
           :induct (COLLECT-CASES-CROSSX lst1 LST2)
           :in-theory (e/d (eval-of-cc-st-lst-lst
                            collect-cases-crossx
                            eval-of-cc-st-lst)
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defthm CC-ST-LST-LST-VALID-P-of-append
  (implies (true-listp x)
           (equal (CC-ST-LST-LST-VALID-P (append x y) a)
                  (and (CC-ST-LST-LST-VALID-P x a)
                       (CC-ST-LST-LST-VALID-P y a))))
  :hints (("Goal"
           :in-theory (e/d (CC-ST-LST-LST-VALID-P) ())))))

(local
 (defret collect-cases-crossx-valid
  (implies (and (cc-st-list-listp lst1)
                (cc-st-list-listp lst2)
                (cc-st-lst-lst-valid-p lst1 a)
                (cc-st-lst-lst-valid-p lst2 a))
           (cc-st-lst-lst-valid-p res a))
  :fn collect-cases-crossx
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-of-cc-st-LST-LST LST2 A))
           :induct (COLLECT-CASES-CROSSX lst1 LST2)
           :in-theory (e/d (CC-ST-LST-LST-VALID-P
                            collect-cases-crossx
                            eval-of-cc-st-lst)
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))



(local
 (defret collect-cases-negate-lst-correct
  (implies (cc-st-listp e)
           (equal (eval-of-cc-st-lst-lst res a)
                  (not (eval-of-cc-st-lst e  a))))
  :fn collect-cases-negate-lst
  :hints (("Goal"
           :do-not-induct t
           :expand ((eval-of-cc-st-LST-LST LST2 A)
                    (:free (x y)
                           (CC-ST->TYPE (cons x y)))
                    (:free (x y)
                           (cc-st->sign (cons x y)))
                    
                    (:free (x y)
                           (cc-st->e (cons x y)))
                    (:free (x y)
                           (eval-of-cc-st-lst (cons x y)
                                              A))
                    (:free (x y)
                           (eval-of-cc-st-lst-lst (cons x y)
                                                  A))
                    (:free (x y)
                           (eval-of-cc-st (cons x y)
                                          A)))
           :induct (collect-cases-negate-lst e)
           :in-theory (e/d (CC-ST-MAKE
                            eval-of-cc-st-lst-lst
                            collect-cases-negate-lst
                            eval-of-cc-st
                            CC-ST-MAKE
                            
                            eval-of-cc-st-lst)
                           (rp-trans

                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

#|(defthm cc-st-valid-p-of-cc-st-make
  (implies (and (rp-termp term)
                (cc-st-list-listp subcases))
           (equal (cc-st-valid-p (cc-st-make term subcases) a)
                  (b* ((subcases-eval-res
                        (eval-of-cc-st-lst-lst subcases a))
                       (subcases-valid-p
                        (cc-st-lst-lst-valid-p subcases a)))
                    (and subcases-valid-p
                         (valid-sc term a)
                         subcases-eval-res))))
  :hints (("goal"
           :expand (cc-st-valid-p (cons term subcases)
                                  a)
           :in-theory (e/d (cc-st-make
                            cc-st->subcases
                            cc-st->term
                            cc-st-valid-p)
                           ()))))|#

(local
 (defret collect-cases-negate-lst-valid
  (implies (and (cc-st-listp e)
                (cc-st-lst-valid-p e a))
           (cc-st-lst-lst-valid-p res a))
  :fn collect-cases-negate-lst
  :hints (("Goal"
           :do-not-induct t
           :expand (
                    (:free (x y)
                           (CC-ST->TYPE (cons x y)))
                    (:free (x y)
                           (cc-st->e (cons x y)))
                   
                    (:free (x y)
                           (CC-ST-VALID-P (cons x y) a))
                    (:free (x y)
                           (CC-ST-LST-VALID-P (cons x y) a)))
           :induct (collect-cases-negate-lst e)

           :in-theory (e/d (CC-ST-MAKE
                            CC-ST-LST-LST-VALID-P
                            collect-cases-negate-lst
                            ;;CC-ST-MAKE
                            CC-ST-VALID-P
                            ;;CC-ST->TERM
                            CC-ST-LST-VALID-P
                            is-rp is-if
                            ;;CC-ST->SUBCASES
                            eval-of-cc-st-lst)
                           (rp-trans
                            valid-sc
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-negate-lst-lst-correct
  (implies (cc-st-list-listp lst)
           (equal (eval-of-cc-st-lst-lst res a)
                  (not (eval-of-cc-st-lst-lst lst  a))))
  :fn collect-cases-negate-lst-lst
  :hints (("Goal"
           :do-not-induct t
           :expand ()
           :induct (collect-cases-negate-lst-lst lst)
           :in-theory (e/d (eval-of-cc-st-lst-lst
                            collect-cases-negate-lst-lst
                            eval-of-cc-st
                            CC-ST-MAKE
                            CC-ST->e
                            eval-of-cc-st-lst)
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-negate-lst-lst-valid
  (implies (and (cc-st-list-listp lst)
                (cc-st-lst-lst-valid-p lst a))
           (cc-st-lst-lst-valid-p res a))
  :fn collect-cases-negate-lst-lst
  :hints (("Goal"
           :do-not-induct t
           :expand ()
           :induct (collect-cases-negate-lst-lst lst)
           :in-theory (e/d (CC-ST-LST-LST-VALID-P
                            collect-cases-negate-lst-lst
                            ;;CC-ST-MAKE
                            CC-ST-VALID-P
                            ;;CC-ST->e
                            CC-ST-LST-VALID-P
                            is-rp is-if
                            ;;CC-ST->SUBCASES
                            eval-of-cc-st-lst)
                           (rp-trans
                            valid-sc
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))


(local
 (defret collect-cases-negate-lst-lst-lw-correct
  (implies (cc-st-list-listp lst)
           (equal (eval-of-cc-st-lst res a)
                  (not (eval-of-cc-st-lst-lst lst  a))))
  :fn collect-cases-negate-lst-lst-lw
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x y)
                           (eval-of-cc-st (cons x y) a))
                    (:free (x y)
                           (CC-ST->TYPE (cons x y)))
                    (:free (x y)
                           (cc-st->e (cons x y)))
                    
                    
                    (:free (x y)
                           (CC-ST->SIGN (cons x y))))
           :induct (collect-cases-negate-lst-lst-lw lst)
           :in-theory (e/d (eval-of-cc-st-lst-lst
                            collect-cases-negate-lst-lst-lw
                            eval-of-cc-st
                            CC-ST-MAKE
                            CC-ST->e
                            eval-of-cc-st-lst)
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-negate-lst-lst-lw-valid
  (implies (and (cc-st-list-listp lst)
                (cc-st-lst-lst-valid-p lst a))
           (cc-st-lst-valid-p res a))
  :fn collect-cases-negate-lst-lst-lw
  :hints (("Goal"
           :do-not-induct t
           :expand ((:free (x y)
                           (CC-ST->TYPE (cons x y)))
                    (:free (x y)
                           (cc-st->e (cons x y)))
                    (:free (x y)
                           (CC-ST->SIGN (cons x y)))
                    (:free (x y)
                           (CC-ST-VALID-P (cons x y) A)))
           :induct (collect-cases-negate-lst-lst-lw lst)
           :in-theory (e/d (CC-ST-LST-LST-VALID-P
                            CC-ST-MAKE
                            collect-cases-negate-lst-lst-lw
                            ;;CC-ST-MAKE
                            CC-ST-VALID-P
                            ;;CC-ST->e
                            CC-ST-LST-VALID-P
                            is-rp is-if
                            ;;CC-ST->SUBCASES
                            eval-of-cc-st-lst)
                           (rp-trans
                            valid-sc
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-negate-main-correct
  (implies (cc-st-list-listp lst)
           (equal (eval-of-cc-st-lst-lst res a)
                  (not (eval-of-cc-st-lst-lst lst  a))))
  :fn collect-cases-negate-main
  :hints (("Goal"
           :do-not-induct t
           :expand ()

           :in-theory (e/d (eval-of-cc-st-lst-lst
                            collect-cases-negate-main
                            eval-of-cc-st
                            CC-ST-MAKE
                            CC-ST->e
                            eval-of-cc-st-lst)
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-negate-main-valid
  (implies (and (cc-st-list-listp lst)
                (cc-st-lst-lst-valid-p lst a))
           (cc-st-lst-lst-valid-p res a))
  :fn collect-cases-negate-main
  :hints (("Goal"
           :do-not-induct t
           :expand ()

           :in-theory (e/d (CC-ST-LST-LST-VALID-P
                            collect-cases-negate-main
                            ;;CC-ST-MAKE
                            CC-ST-VALID-P
                            ;;CC-ST->e
                            CC-ST-LST-VALID-P
                            is-rp is-if
                            ;;CC-ST->SUBCASES
                            eval-of-cc-st-lst)
                           (rp-trans
                            valid-sc
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-merge-lst-lst-correct
  (implies (and (cc-st-list-listp lst1)
                (cc-st-list-listp lst2))
           (equal (eval-of-cc-st-lst-lst res a)
                  (or (eval-of-cc-st-lst-lst lst1 a)
                      (eval-of-cc-st-lst-lst lst2 a))))
  :fn collect-cases-merge-lst-lst
  :hints (("Goal"
           :do-not-induct t
           :expand ()
           :induct (collect-cases-merge-lst-lst lst1 lst2)
           :in-theory (e/d (eval-of-cc-st-lst-lst
                            collect-cases-merge-lst-lst
                            eval-of-cc-st
                            CC-ST-MAKE
                            CC-ST->e
                            eval-of-cc-st-lst)
                           (rp-trans
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))

(local
 (defret collect-cases-merge-lst-lst-valid
  (implies (and (cc-st-list-listp lst1)
                (cc-st-list-listp lst2)
                (cc-st-lst-lst-valid-p lst1 a)
                (cc-st-lst-lst-valid-p lst2 a))
           (cc-st-lst-lst-valid-p res a))
  :fn collect-cases-merge-lst-lst
  :hints (("Goal"
           :do-not-induct t
           :expand ()
           :induct (collect-cases-merge-lst-lst lst1 lst2)
           :in-theory (e/d (CC-ST-LST-LST-VALID-P
                            collect-cases-merge-lst-lst
                            ;;CC-ST-MAKE
                            CC-ST-VALID-P
                            ;;CC-ST->e
                            CC-ST-LST-VALID-P
                            is-rp is-if
                            ;;CC-ST->SUBCASES
                            eval-of-cc-st-lst)
                           (rp-trans
                            valid-sc
                            not-include-rp
                            rp-termp
                            ex-from-rp
                            include-fnc
                            rp-equal))))))


(local
 (define collect-cases-induct (term iff-flg)
   :returns res
   :verify-guards nil
   :enabled t
   (cond
    ((equal term ''nil)
     nil)
    ((atom term)
     nil)
    ((quotep term)
     nil)
    ((is-if term)
     (b* ((a (cadr term))
          (b (caddr term))
          (c (cadddr term))
          (cases-a (collect-cases-induct a t))
          (cases-b (collect-cases-induct b iff-flg))
          (cases-c (collect-cases-induct c iff-flg)))
       (append iff-flg cases-a cases-b cases-c)))
    (t nil))))

(local
 (defthm rp-evlt-when-is-if
   (implies (is-if x)
            (equal (rp-evlt x a)
                   (if (rp-evlt (cadr x) a)
                       (rp-evlt (caddr x) a)
                     (rp-evlt (cadddr x) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans
                             is-if)
                            ())))))

(local
 (defret collect-unburied-cases-is-correct
  (implies (rp-termp term)
           (and (iff (eval-of-cc-st-lst-lst res a)
                     (rp-evlt term a))
                (implies evals-to-nil
                         (iff (rp-evlt term a) nil))))
  :fn collect-unburied-cases
  :hints (("Goal"
           :do-not-induct t
           :expand ((COLLECT-unburied-CASES TERM :iff-flg IFF-FLG)
                    (eval-of-cc-st-LST NIL A)
                    (eval-of-cc-st-LST-LST NIL A)
                    (:free (x y)
                           (CC-ST->SIGN (cons x y)))
                    (:free (x y)
                           (CC-ST->TYPE (cons x y)))
                    (:free (x y)
                           (CC-ST->e (cons x y)))
                    (:free (x y)
                           (eval-of-cc-st-LST-LST (cons x y) a))
                    (:free (x y)
                           (eval-of-cc-st-LST (cons x y) a))
                    (:free (x y)
                           (eval-of-cc-st (cons x y) a)))
           :induct (collect-cases-induct TERM  IFF-FLG)
           :in-theory (e/d (COLLECT-unburied-CASES
                            CC-ST-MAKE
                            ;;is-if
                            eval-of-cc-st)
                           (rp-termp
                            if*
                            INCLUDE-FNC
                            rp-trans))))))

#|(local
 (defthm valid-sc-subterms-cdr-lemma
   (implies (and (valid-sc term a)
                 (or (not (equal (car term) 'if))
                     (not (is-if term)))
                 (not (equal (car term) 'quote)))
            (valid-sc-subterms (cdr term) a))
   :hints (("Goal"
            :cases ((is-rp term))
            :use ((:instance valid-sc-single-step))
            :in-theory (e/d (is-rp
                             is-if)
                            (valid-sc-single-step))))))|#


(local
 (defret collect-cases-is-valid
  (implies (and (rp-termp term)
                (not (include-fnc term 'rp)))
           (cc-st-lst-lst-valid-p res a))
  :fn collect-unburied-cases
  :hints (("Goal"
           :do-not-induct t
           :induct (collect-unburied-cases-fn term iff-flg)
           :expand (
                    (CC-ST-LST-VALID-P NIL A)
                    (CC-ST-LST-LST-VALID-P NIL A)
                    (collect-unburied-cases TERM :iff-flg IFF-FLG)
                    (CC-ST-LST-VALID-P NIL A)
                    (CC-ST-LST-LST-VALID-P NIL A)
                    (eval-of-cc-st-LST NIL A)
                    (eval-of-cc-st-LST-LST NIL A)
                    (:free (x)
                           (COLLECT-CASES-MERGE-LST-LST nil x))
                    (:free (x y)
                           (CC-ST->SIGN (cons x y)))
                    
                    (:free (x y)
                           (CC-ST->TYPE (cons x y)))
                    (:free (x y)
                           (CC-ST->e (cons x y)))
                    (:free (x y)
                           (cc-st-lst-lst-valid-p (cons x y) a))
                    (:free (x y)
                           (cc-st-lst-valid-p (cons x y) a))
                    (:free (x y)
                           (cc-st-valid-p (cons x y) a))
                    (:free (x y)
                           (cc-st-lst-lst-valid-p (cons x y) a))
                    (:free (x y)
                           (cc-st-lst-valid-p (cons x y) a))
                    (:free (x y)
                           (cc-st-valid-p (cons x y) a))
                    (:free (x y)
                           (eval-of-cc-st (cons x y) a)))

           :in-theory (e/d (include-fnc
                            collect-unburied-cases
                            valid-sc
                            CC-ST-MAKE
                            not-include-rp-means-valid-sc
                            eval-of-cc-st)
                           (rp-termp
                            if*
                            rp-trans))))))


(local
 (defret-mutual cc-st-to-term-correct
  (defret cc-st-to-term-correct
    (equal (rp-evlt res a)
           (eval-of-cc-st st a)
           )
    :fn cc-st-to-term)
  (defret cc-st-lst-to-term-correct
    (equal (rp-evlt res a)
           (eval-of-cc-st-lst st-lst a)
           )
    :fn cc-st-lst-to-term)
  (defret cc-st-lst-lst-to-term-correct
    (equal (rp-evlt res a)
           (eval-of-cc-st-lst-lst st-lst-lst a)
           )
    :fn cc-st-lst-lst-to-term)
  :mutual-recursion cc-st-to-term
  :hints (("Goal"
           :in-theory (e/d (cc-st-to-term
                            EVAL-OF-CC-ST-LST-LST
                            EVAL-OF-CC-ST-LST
                            EVAL-OF-CC-ST
                            cc-st-lst-to-term
                            cc-st-lst-lst-to-term
                            ) ())))))

(local
 (defret-mutual cc-st-to-term-valid-sc
  (defret cc-st-to-term-valid-sc
    (implies (cc-st-valid-p st a)
             (not (include-fnc res 'rp)))
    :fn cc-st-to-term)
  (defret cc-st-lst-to-term-valid-sc
    (implies (cc-st-lst-valid-p st-lst a)
             (not (include-fnc res 'rp)))
    :fn cc-st-lst-to-term)
  (defret cc-st-lst-lst-to-term-valid-sc
    (implies (cc-st-lst-lst-valid-p st-lst-lst a)
             (not (include-fnc res 'rp)))
    :fn cc-st-lst-lst-to-term)
  :mutual-recursion cc-st-to-term
  :hints (("Goal"
           :in-theory (e/d (cc-st-to-term
                            cc-st-lst-to-term
                            cc-st-lst-lst-to-term
                            CC-ST-LST-LST-VALID-P
                            CC-ST-LST-VALID-P
                            CC-ST-VALID-P
                            ) ())))))


(local
 (defret casesplit-from-context-attach-buried-correct
   (implies (and (rp-evlt context-term a)
                 (cc-st-list-listp buried-cases)
                 (eval-of-cc-st-lst-lst buried-cases a)
                 )
            (equal (rp-evlt res a)
                   (rp-evlt term a)))
   :fn casesplit-from-context-attach-buried
   :hints (("Goal"
            :do-not-induct t
            :induct (casesplit-from-context-attach-buried TERM TERM-DONT-RW
                                                          CONTEXT-TERM CONTEXT-TERM-DONT-RW
                                                          BURIED-CASES SUBGOAL-PREFIX CNT)
            :expand ((EVAL-OF-CC-ST-LST-LST BURIED-CASES A))
            :in-theory (e/d (casesplit-from-context-attach-buried
                             eval-of-cc-st-lst-lst
                             eval-of-cc-st-lst
                             eval-of-cc-st)
                            ())))))

(local
 (defret casesplit-from-context-attach-buried-valid-sc
  (implies (and (valid-sc term a)
                (valid-sc context-term a)
                (cc-st-lst-lst-valid-p buried-cases a))
           (valid-sc res a))
  :fn casesplit-from-context-attach-buried
  :hints (("Goal"
           :in-theory (e/d (casesplit-from-context-attach-buried
                            valid-sc
                            not-include-rp-means-valid-sc
                            is-rp
                            is-if
                            CC-ST-LST-LST-VALID-P
                            CC-ST-LST-VALID-P
                            CC-ST-VALID-P)
                           (eval-and-all))))))

(local
 (defret eval-of-GROUP-LONG-AND-CHAIN
   (implies (and valid
                 (rp-termp term))
            (and (implies iff-flg
                          (iff (eval-of-cc-st-lst res a)
                               (rp-evlt term a)))
                 (implies (not iff-flg)
                          (equal (eval-of-cc-st-lst res a)
                                 (rp-evlt term a)))))
   :fn group-long-and-chain
   :hints (("Goal"
            :in-theory (e/d (GROUP-LONG-AND-CHAIN
                             EVAL-OF-CC-ST
                             EVAL-OF-CC-ST-LST)
                            ())))))


(define collect-buried-cases-induct (term iff-flg) 
  :verify-guards nil
  :enabled t
  (cond
   ((equal term ''nil)
    nil)
   ((or (atom term)
        (equal (car term) 'falist))
    nil)
   ((quotep term)
    nil)
   ((is-if term)
    (b* (((mv ?and-chain and-chain-valid)
          (group-long-and-chain term iff-flg 2))
         ((when and-chain-valid) nil)
         (a (cadr term))
         (b (caddr term))
         (c (cadddr term))
         )
      (list (collect-buried-cases-induct a iff-flg)
            (collect-buried-cases-induct b iff-flg)
            (collect-buried-cases-induct c iff-flg))))
    (t
     t)))

(local
 (defret COLLECT-BURIED-CASES-valid-subcases-lemma
   (implies (and (booleanp iff-flg)
                 (rp-termp term))
            (and (implies (and evals-to-nil)
                          (and (not (rp-evlt term a))
                               (not (eval-of-cc-st-lst-lst res a))))
                 (implies (and (not iff-flg))
                          (eval-of-cc-st-lst-lst res a))
                 (implies (and iff-flg)
                          (iff (eval-of-cc-st-lst-lst res a)
                               (rp-evlt term a)))))
   :fn collect-buried-cases
   :hints (("Goal"
            :expand ((COLLECT-BURIED-CASES TERM
                                           :IFF-FLG IFF-FLG))
            :induct (collect-buried-cases-induct term iff-flg)
            :do-not-induct t
            :in-theory (e/d (collect-unburied-cases
                             EVAL-OF-CC-ST-LST-LST
                             EVAL-OF-CC-ST-LST
                             EVAL-OF-CC-ST
                             collect-buried-cases)
                            ())))))



(local
 (defret-mutual COLLECT-BURIED-CASES-valid-subcases
  (defret COLLECT-BURIED-CASES-valid-subcases
    (implies (rp-termp term)
             (and (eval-of-cc-st-lst-lst subcases a)
                  ))
    :fn collect-buried-cases)
  (defret COLLECT-BURIED-CASES-lst-valid-subcases
    (implies (rp-term-listp lst)
             (eval-of-cc-st-lst-lst subcases a))
    :fn collect-buried-cases-lst)
  :mutual-recursion collect-buried-cases
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (eval-of-cc-st-lst-lst
                            eval-of-cc-st-lst
                            eval-of-cc-st
                            collect-buried-cases-lst
                            collect-buried-cases)
                           (rp-termp
                            ))))))


(local
 (defret casesplit-from-context-attach-correct
  (implies (and (cc-st-list-listp unburied-cases)
                (eval-of-cc-st-lst-lst unburied-cases a))
           (equal (rp-evlt res a)
                  (rp-evlt term a)))
  :fn casesplit-from-context-attach
  :hints (("Goal"
           :in-theory (e/d (casesplit-from-context-attach
                            EVAL-OF-CC-ST-LST-LST
                            EVAL-OF-CC-ST-LST
                            EVAL-OF-CC-ST)
                           ())))))

(local
 (defthm CC-ST-VALID-P-of-CC-ST-MAKE-term
  (implies (and (not (include-fnc term 'rp))
                (rp-termp term)
                (booleanp sign))
           (CC-ST-VALID-P (CC-ST-MAKE :TYPE :TERM
                                      :SIGN sign
                                      :E TERM)
                          A))
  :hints (("Goal"
           :in-theory (e/d (CC-ST-MAKE
                            cc-st->type
                            CC-ST->E
                            CC-ST-VALID-P)
                           ())))))

(local
 (defthm CC-ST-VALID-P-of-CC-ST-MAKE-and-list
  (implies (and (cc-st-lst-valid-p and-list a)
                (CC-ST-LISTP AND-LIST)
                (booleanp sign))
           (CC-ST-VALID-P (CC-ST-MAKE :TYPE :and-list
                                      :SIGN sign
                                      :E and-list)
                          A))
  :hints (("Goal"
           :in-theory (e/d (CC-ST-MAKE
                            cc-st-lst-valid-p
                            cc-st->type
                            CC-ST->E
                            CC-ST-VALID-P)
                           ())))))

(local
 (defthm CC-ST-VALID-P-of-CC-ST-MAKE-or-list
  (implies (and (cc-st-lst-lst-valid-p or-list a)
                (CC-ST-list-LISTP or-LIST)
                (booleanp sign))
           (CC-ST-VALID-P (CC-ST-MAKE :TYPE :or-list
                                      :SIGN sign
                                      :E or-list)
                          A))
  :hints (("Goal"
           :in-theory (e/d (CC-ST-MAKE
                            cc-st-lst-valid-p
                            cc-st->type
                            CC-ST->E
                            CC-ST-VALID-P)
                           ())))))

(local
 (defret GROUP-LONG-AND-CHAIN-valid-sc
  (implies (and (not (include-fnc term 'rp))
                (rp-termp term))
           (CC-ST-LST-VALID-P res a))
  :fn group-long-and-chain
  :hints (("Goal"
           :in-theory (e/d (CC-ST-LST-VALID-P
                            CC-ST-VALID-P
                            GROUP-LONG-AND-CHAIN)
                           ())))))

(local
 (defret-mutual COLLECT-BURIED-CASES-valid-sc
  (defret COLLECT-BURIED-CASES-valid-sc
    (implies (and (not (include-fnc term 'rp))
                  (rp-termp term))
             (and (cc-st-lst-lst-valid-p res a)
                  (cc-st-lst-lst-valid-p subcases a)))
    :fn collect-buried-cases)
  (defret COLLECT-BURIED-CASES-lst-valid-sc
    (implies (and (not (include-fnc-subterms lst 'rp))
                  (rp-term-listp lst))
             (cc-st-lst-lst-valid-p subcases a))
    :fn collect-buried-cases-lst)
  :mutual-recursion collect-buried-cases
  :hints (("Goal"
           :in-theory (e/d (cc-st-lst-lst-valid-p
                            cc-st-lst-valid-p
                            cc-st-valid-p
                            collect-buried-cases-lst
                            collect-buried-cases)
                           (rp-termp
                            ))))))


  

(local
 (defret casesplit-from-context-attach-valid-sc
  (implies (and (cc-st-list-listp unburied-cases)
                (valid-sc term a)
                (cc-st-lst-lst-valid-p unburied-cases a))
           (valid-sc res a))
  :fn casesplit-from-context-attach
  :hints (("Goal"
           :in-theory (e/d (casesplit-from-context-attach
                            cc-st-lst-lst-valid-p
                            cc-st-lst-valid-p
                            cc-st-valid-p
                            is-rp
                            is-if
                            not-include-rp-means-valid-sc)
                           (eval-and-all))))))


(local
 (defret collect-cases-gather-context-term-correct
   (implies (and (rp-term-listp context)
                 (eval-and-all context a))
            (rp-evlt context-term a))
   :fn collect-cases-gather-context-term
   :hints (("Goal"
            :in-theory (e/d (collect-cases-gather-context-term) ())))))

(local
 (defret collect-cases-from-context-aux-correct
  (implies (and (rp-termp term)
                (rp-term-listp context)
                (eval-and-all context a))
           (equal (rp-evlt res-term a)
                  (rp-evlt term a)))
  :fn collect-cases-from-context-aux
  :hints (("Goal"
           :in-theory (e/d (collect-cases-from-context-aux)
                           ())))))

(local
 (defret collect-cases-from-context-aux-valid-sc
  (implies (and (rp-termp term)
                (rp-term-listp context)
                (valid-sc term a))
           (valid-sc res-term a))
  :fn collect-cases-from-context-aux
  :hints (("Goal"
           :in-theory (e/d (collect-cases-from-context-aux)
                           ())))))



(defthmd implies-redef-with-casesplit-from-context-trig
  (equal (implies p q)
         (if p (casesplit-from-context-trig (if q t nil)) t))
  :hints (("Goal"
           :in-theory (e/d (casesplit-from-context-trig
                            implies)
                           ()))))

(add-rp-rule implies-redef-with-casesplit-from-context-trig
             :outside-in t)


(rp::add-meta-rule
 :meta-fnc casesplit-from-context
 :trig-fnc casesplit-from-context-trig
 :valid-syntaxp t
 :outside-in t
 :disabledp t
 :returns (mv term dont-rw)
 :hints (("Goal"
          :in-theory (e/d (casesplit-from-context
                           casesplit-from-context-trig)
                          ()))))



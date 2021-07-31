; Flattens partial products and applies associated lemmas to already simplified
; summation tree terms.

; Copyright (C) 2021 Centaur Technology
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
; Original Author(s):
; Mertcan Temel         <mert@centtech.edu>

(in-package "RP")

(include-book "summation-tree-meta-fncs")

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

(local
 (include-book "lemmas"))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))


(local
 (in-theory (disable +-IS-SUM)))

(local
 (in-theory (disable rp-termp)))

(local
 (in-theory (disable ex-from-rp
                     (:definition acl2::apply$-badgep)
                     (:linear acl2::apply$-badgep-properties . 1)
                     (:definition subsetp-equal)
                     (:definition member-equal)
                     (:rewrite
                      acl2::member-equal-newvar-components-1)
                     include-fnc)))



(define unpack-booth-for-pp-lst ((pp-lst rp-term-listp))
  :returns (res-pp-lst rp-term-listp :hyp (rp-term-listp pp-lst))
  :verify-guards :after-returns
  :prepwork ((local
              (in-theory (enable rp-term-listp))))
  (if (atom pp-lst)
      nil
    (pp-sum-merge-aux (cond ((pp-term-p (car pp-lst))
                             (pp-flatten (car pp-lst) nil :unpack-now t))
                            ((or (and-list-p (car pp-lst))
                                 (--.p (car pp-lst))
                                 (bit-of-p (car pp-lst)))
                             (list (car pp-lst)))
                            (t
                             (progn$ (hard-error 'unpack-booth-for-pp-lst
                                                 "Unexpected pp-arg ~p0 ~%"
                                                 (list (cons #\0 (car pp-lst))))
                                     (list (car pp-lst)))))
                      (unpack-booth-for-pp-lst (cdr pp-lst)))))


(acl2::defines
 unpack-booth-for-s

 :flag-defthm-macro defthm-unpack-booth-for-s
 :flag-local nil
 
 :prepwork ((local
             (in-theory (enable measure-lemmas)))

         
            (local
             (defthm cons-count-of-list-to-lst-1
               (implies (and (consp s-term)
                             (consp (cdr s-term))
                             (consp (cddr s-term))
                             (consp (cdddr s-term))
                             (not (cddddr s-term)))
                        (o< (cons-count (list-to-lst (cadddr s-term)))
                            (cons-count s-term)))
               :hints (("goal"
                        :do-not-induct t
                        :expand ((cons-count s-term)
                                 (cons-count (cdr s-term))
                                 (list-to-lst (cadddr s-term)))
                        :in-theory (e/d (cons-count
                                         list-to-lst
                                         )
                                        ())))))

            (local
             (defthm cons-count-of-list-to-lst-2
               (implies (and (consp c-term)
                             
                             (consp (cdr c-term))
                             (consp (cddr c-term))
                             (consp (cdddr c-term))
                             (consp (cddddr c-term))
                             (not (cdr (cddddr c-term))))
                        (o< (cons-count (list-to-lst (car (cddddr c-term))))
                            (cons-count c-term)))
               :hints (("goal"
                        :do-not-induct t
                        :expand ((cons-count c-term)
                                 (cons-count (cdr c-term))
                                 (list-to-lst (car (cddddr c-term))))
                        :in-theory (e/d (cons-count
                                         list-to-lst
                                         )
                                        ())))))

            

            (local
             (defthm cons-count-of-list-to-lst-3
               (implies (and (consp c-term)
                             (consp (cdr c-term))
                             (consp (cddr c-term))
                             (consp (cdddr c-term))
                             (consp (cddddr c-term))
                             (not (cdr (cddddr c-term))))
                        (o< (cons-count (list-to-lst (caddr c-term)))
                            (cons-count c-term)))
               :hints (("goal"
                        :do-not-induct t
                        :expand ((cons-count c-term)
                                 (CONS-COUNT (CDDR C-TERM))
                                 (CONS-COUNT (CDDDR C-TERM))
                                 (cons-count (cdr c-term))
                                 (list-to-lst (caddr c-term)))
                        :in-theory (e/d (cons-count
                                         list-to-lst
                                         )
                                        ())))))

            (local
             (defthm cons-count-of-ex-from-rp
               (<= (cons-count (ex-from-rp term))
                   (cons-count term))))

            (local
             (defthm dummy-mes-lemma
               (implies (and      
                         (integerp other)
                         (o< other (cons-count (ex-from-rp term))))
                        (o< other (cons-count term)))
               :hints (("Goal"
                        :do-not-induct t
                        :use ((:instance cons-count-of-ex-from-rp))
                        :in-theory (e/d (o<) (cons-count-of-ex-from-rp))))))


            (local
             (defthm dummy-equiva-lemma
               (implies (and (<= x y)
                             (natp x)
                             (natp y)
                             (natp a)
                             (natp b))
                        (<= x (+ a y b)))))
            
             (local
             (defthm cons-count-of-ex-from-rp-2
               (<= (cons-count (ex-from-rp (cadr term)))
                   (cons-count term))
               :hints (("Goal"
                        :expand ((CONS-COUNT TERM)
                                 (CONS-COUNT (CDR TERM)))
                        :use ((:instance cons-count-of-ex-from-rp (term (cadr term)))
                              (:instance dummy-equiva-lemma
                                         (x (CONS-COUNT (EX-FROM-RP (CADR
                                                                     TERM))))
                                         (y    (CONS-COUNT (CADR TERM)))
                                         (a (CONS-COUNT (CAR TERM)))
                                         (b (CONS-COUNT (CDDR TERM)))))
                        :in-theory (e/d () (cons-count-of-ex-from-rp))))))
            
            (local
             (defthm dummy-mes-lemma-2
               (implies (and      
                         (integerp other)
                         (consp term)
                         (consp (cdr term))
                         (o< other (cons-count (ex-from-rp (cadr term)))))
                        (o< other (cons-count term)))
               :hints (("Goal"
                        :do-not-induct t 
                        :use ((:instance cons-count-of-ex-from-rp-2))
                        :in-theory (e/d (o<) (cons-count-of-ex-from-rp))))))

            

            )

 :verify-guards nil
 
 (define unpack-booth-for-s ((s-term rp-termp))
   :returns (mv (s-res-lst rp-term-listp
                           :hyp (rp-termp s-term))
                (pp-res-lst rp-term-listp
                            :hyp (rp-termp s-term))
                (c-res-lst rp-term-listp
                           :hyp (rp-termp s-term)))
   :measure (cons-count s-term)
   (b* ((?orig s-term)
        (term (ex-from-rp s-term)))
     (case-match term
       (('s & pp-arg c-arg)
        (b* (;; first lest unpack these pp args
             (pp-arg-lst (list-to-lst pp-arg))
             (pp-arg-lst (unpack-booth-for-pp-lst pp-arg-lst))
             ;; then unpack the c-args
             (c-arg-lst (list-to-lst c-arg))
             ((mv s-arg-lst2 pp-arg-lst2 c-arg-lst)
              (unpack-booth-for-c-lst c-arg-lst))
             ;; merge the new pp args derived from the c args
             (pp-arg-lst (pp-sum-merge-aux pp-arg-lst pp-arg-lst2))
             ((mv pp-arg-lst c-arg-lst)
              (s-of-s-fix-lst s-arg-lst2 pp-arg-lst c-arg-lst))
             (pp-arg-lst (s-fix-pp-args-aux pp-arg-lst))
             (c-arg-lst (s-fix-pp-args-aux c-arg-lst)))
          (create-s-instance (create-list-instance pp-arg-lst)
                             (create-list-instance c-arg-lst))))
       (''0
        (mv nil nil nil))
       (& (progn$
           (hard-error 'unpack-booth-for-s
                       "Unrecognized s instance: ~p0 ~%"
                       (list (cons #\0 orig)))
           (mv (list term) nil nil))))))
 
 (define unpack-booth-for-s-lst ((s-lst rp-term-listp))
   :returns (mv (s-res-lst rp-term-listp
                           :hyp (rp-term-listp s-lst))
                (pp-res-lst rp-term-listp
                            :hyp (rp-term-listp s-lst))
                (c-res-lst rp-term-listp
                           :hyp (rp-term-listp s-lst)))
   :measure (cons-count s-lst)
   (if (atom s-lst)
       (mv nil nil nil)
     (b* (((mv s-res-lst1 pp-res-lst1 c-res-lst1)
           (unpack-booth-for-s (car s-lst)))
          ((mv s-res-lst2 pp-res-lst2 c-res-lst2)
           (unpack-booth-for-s-lst (cdr s-lst))))
       (mv (s-sum-merge-aux s-res-lst1 s-res-lst2)
           (pp-sum-merge-aux pp-res-lst1 pp-res-lst2)
           (s-sum-merge-aux c-res-lst1 c-res-lst2)))))
 
 (define unpack-booth-for-c ((c-term rp-termp))
   :returns (mv (s-res-lst rp-term-listp
                           :hyp (rp-termp c-term))
                (pp-res-lst rp-term-listp
                            :hyp (rp-termp c-term))
                (c-res-lst rp-term-listp
                           :hyp (rp-termp c-term)))
   :measure (cons-count c-term)
   (b* ((?orig c-term)
        ((mv c-term signed)
         (case-match c-term
           (('-- term) (mv term t))
           (& (mv c-term nil))))
        (term (ex-from-rp c-term))
        )
     (case-match term
       (('c & s-arg pp-arg c-arg)
        (b* (;; first lest unpack these pp args
             (pp-arg-lst (list-to-lst pp-arg))
             (pp-arg-lst (unpack-booth-for-pp-lst pp-arg-lst))
             ;; then unpack the s-args
             (s-arg-lst (list-to-lst s-arg))
             ((mv s-arg-lst pp-arg-lst2 c-arg-lst2)
              (unpack-booth-for-s-lst s-arg-lst))
             (pp-arg-lst (pp-sum-merge-aux pp-arg-lst pp-arg-lst2))
             
             ;; unpack the c-args
             ((mv s-arg-lst3 pp-arg-lst3 c-arg-lst)
              (unpack-booth-for-c-lst (list-to-lst c-arg)))
             (c-arg-lst (s-sum-merge-aux c-arg-lst
                                         c-arg-lst2))
             (s-arg-lst (s-sum-merge-aux s-arg-lst s-arg-lst3))
             (pp-arg-lst (pp-sum-merge-aux pp-arg-lst pp-arg-lst3))
             ;; cough out s-args
             ((mv coughed-s-lst s-arg-lst)
              (c-fix-arg-aux s-arg-lst t))

             ;; TODO add c-of-s-fix-lst here
             ((mv pp-arg-lst c-arg-lst
                  coughed-s-lst2 coughed-pp-lst2 coughed-c-lst2)
              (c-of-s-fix-lst s-arg-lst pp-arg-lst c-arg-lst nil))
             (s-arg-lst nil)
             
             ;; cough out pp-args
             ((mv coughed-pp-lst pp-arg-lst)
              (c-fix-arg-aux pp-arg-lst t))
             
             ;; create-c-instance
             ((mv s-res-lst pp-res-lst c-res-lst)
              (create-c-instance s-arg-lst pp-arg-lst c-arg-lst))

             (c-res-lst (s-sum-merge-aux c-res-lst coughed-c-lst2))
             (s-res-lst (s-sum-merge-aux s-res-lst coughed-s-lst))
             (s-res-lst (s-sum-merge-aux s-res-lst coughed-s-lst2))
             (pp-res-lst (pp-sum-merge-aux pp-res-lst coughed-pp-lst))
             (pp-res-lst (pp-sum-merge-aux pp-res-lst coughed-pp-lst2)))

          (if signed
              (mv (negate-lst s-res-lst)
                  (Negate-Lst pp-res-lst)
                  (negate-lst c-res-lst))    
            (mv s-res-lst pp-res-lst c-res-lst))))
       (''0
        (mv nil nil nil))
       (& (progn$
           (hard-error 'unpack-booth-for-c
                       "Unrecognized c instance: ~p0 ~%"
                       (list (cons #\0 orig)))
           (mv (list orig) nil nil))))))

 (define unpack-booth-for-c-lst ((c-lst rp-term-listp))
   :returns (mv (s-res-lst rp-term-listp
                           :hyp (rp-term-listp c-lst))
                (pp-res-lst rp-term-listp
                            :hyp (rp-term-listp c-lst))
                (c-res-lst rp-term-listp
                           :hyp (rp-term-listp c-lst)))
   :measure (cons-count c-lst)
   (if (atom c-lst)
       (mv nil nil nil)
     (b* (((mv s-res-lst1 pp-res-lst1 c-res-lst1)
           (unpack-booth-for-c (car c-lst)))
          ((mv s-res-lst2 pp-res-lst2 c-res-lst2)
           (unpack-booth-for-c-lst (cdr c-lst))))
       (mv (s-sum-merge-aux s-res-lst1 s-res-lst2)
           (pp-sum-merge-aux pp-res-lst1 pp-res-lst2)
           (s-sum-merge-aux c-res-lst1 c-res-lst2)))))

 ///

 (verify-guards unpack-booth-for-c-lst))


(memoize 'unpack-booth-for-c-lst :aokp t)
(memoize 'unpack-booth-for-s-lst :aokp t)
(memoize 'unpack-booth-for-s :aokp t)
(memoize 'unpack-booth-for-c :aokp t)


(define unpack-booth-meta ((term rp-termp))
  :returns (mv (res rp-termp :hyp (rp-termp term))
               (dont-rw))
  (case-match term
    (('unpack-booth subterm)
     (b* ((orig subterm)
          ((unless (unpack-booth-later-enabled))
           (mv term nil))
          (subterm (ex-from-rp subterm))
          ((mv s-res-lst pp-res-lst c-res-lst)
           (case-match subterm
             (('s & & &)
              (unpack-booth-for-s orig))
             (('c & & & &)
              (unpack-booth-for-c orig))
             (('s-c-res s-arg pp-arg c-arg)
              (b* (((mv s-res-lst1 pp-res-lst1 c-res-lst1)
                    (unpack-booth-for-s-lst (list-to-lst s-arg)))
                   ((mv s-res-lst2 pp-res-lst2 c-res-lst2)
                    (unpack-booth-for-c-lst (list-to-lst c-arg)))
                   ;; merge  the results
                   (pp-res-lst (unpack-booth-for-pp-lst (list-to-lst pp-arg)))
                   (pp-res-lst (pp-sum-merge-aux pp-res-lst
                                                 (pp-sum-merge-aux pp-res-lst1
                                                                   pp-res-lst2)))
                   (s-res-lst (s-sum-merge-aux s-res-lst1 s-res-lst2))
                   (c-res-lst (s-sum-merge-aux c-res-lst1 c-res-lst2)))
                (mv s-res-lst pp-res-lst c-res-lst)))
             (& (progn$ (hard-error 'unpack-booth-meta
                                    "Unrecognized term ~p0 ~%"
                                    (list (cons #\0 orig)))
                        (mv (list orig) nil nil)))))
          (res (create-s-c-res-instance s-res-lst pp-res-lst c-res-lst nil))
          (& (and (not (equal res ''0))
                  (hard-error 'unpack "term:~p0 ~% res:~p1~%" (list (cons #\0 term)
                                                               (cons #\1 res))))))
       (mv res t)))
    (&
     (mv term nil))))
     

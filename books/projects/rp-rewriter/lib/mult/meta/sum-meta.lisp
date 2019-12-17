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

(include-book "../mult-defs")
;(include-book "pp-sum-meta")
(include-book "tools/templates" :dir :system)

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "../greedy-lemmas"))
(local
 (in-theory (disable n2b f2 m2 d2 p+ b+ ba pp type-fix merge-pp+)))

(def-formula-checks-default-evl
 rp-evl
 (strip-cars *small-evl-fncs*))

(encapsulate
  nil

  #|(defun get-first-pp (a)
    (declare (xargs
              :guard t
              ;;              :mode :program
              :verify-guards t))
    (cond
     ((atom a)
      a)
     ((eq (car a) 'pp)
      a)
     ((case-match a (('rp::rp & &) t) (& nil))
      (get-first-pp (caddr a)))
     ((consp (cdr a))
      (get-first-pp (cadr a)))
     (t a)))||#

  (defun get-first-function (a)
    (declare (xargs
              :guard t
              :verify-guards t))
    (cond
     ((atom a) 0)
     ((and (atom (car a))
           (symbolp (car a)))
      (cond ((eq (car a) 'm2) 1)
            ((or (eq (car a) 'pp)
                 (eq (car a) 'p+))
             2)
            ((or (eq (car a) 'f2)
                 ;(eq (car a) 'binary-and)
                 (eq (car a) 'd2))
             3)
            ((or (eq (car a) 'b+)
                 #|(eq (car a) 'bin-and)||#
                 #|(eq (car a) 'b-m2+)||#)
             4)
            ((eq (car a) '[])
             5)
            #|((or (eq (car a) 'times2)
                 (eq (car a) 'minus))
             6)||#
            ((case-match a (('rp::rp & &) t) (& nil))
             (get-first-function (caddr a)))
            ((case-match a (('rp::-- &) t) (& nil))
             (get-first-function (cadr a)))
            (t 0)))
     ((consp (cdr a))
      (get-first-function (cadr a)))
     (t 0)))

  (local
   (defthm integerp-of-get-first-function
     (integerp (get-first-function a))))

  #|(defun get-pp+-depth (x)
    (declare (xargs
              :guard t
              :verify-guards t))
    (if (atom x)
        0
      (1+ (if (and (consp (cdr x))
                   (consp (cddr x)))
              (get-pp+-depth (caddr x))
            0))))||#

  #|(local
   (defthm integerp-get-pp+-depth
     (integerp (get-pp+-depth x))))||#

  #|(defun count-pp (x)
  (declare (xargs
  :guard t
  :verify-guards t))
  (if (atom x)
  0
  (+ (if (consp (car x))
  (if (equal (caar x) 'pp+)
  (get-pp+-depth (car x))
  (count-pp (car x)))
  0)
  (count-pp (cdr x)))))||#

  #|(local
  (defthm integerp-countpp
  (integerp (count-pp x))))||#

  (defun ex-from-rp/--/b-*/binary-not (term)
    (declare (xargs :guard t))
    (case-match term
      (('-- x)
       (ex-from-rp/--/b-*/binary-not x))
      (('rp & x)
       (ex-from-rp/--/b-*/binary-not x))
      (('b-* x y)
       (if (quotep x)
           (ex-from-rp/--/b-*/binary-not y)
         (ex-from-rp/--/b-*/binary-not x)))
      (('binary-not x)
       (ex-from-rp/--/b-*/binary-not x))
      (& term)))

  (defun s-order (x y)
    (declare (xargs :guard t))
    (let ((x-fn (get-first-function x))
          (y-fn (get-first-function y)))
      (cond
       ((or (= x-fn 4)
            (= y-fn 4))
        nil)
       #|((or (= y-fn 6)
            (= x-fn 6))
        (not (= y-fn 6)))||#
       ((or (and (= y-fn 1)
                 (= x-fn 1)))
        (b* ((x (ex-from-rp-loose x))
             (y (ex-from-rp-loose y))
             (x-is-minus
              (and (consp x) (consp (cdr x)) (equal (car x) '--)))
             (y-is-minus
              (and (consp y) (consp (cdr y)) (equal (car y) '--)))
             (x (if x-is-minus (cadr x) x))
             (y (if y-is-minus (cadr y) y))
             ((mv order-res equal-x-y)
              (lexorder2 y x)))
          (if equal-x-y
              (and x-is-minus (not y-is-minus))
            order-res)))
       ((and (= x-fn 5)
             (= y-fn 5))
        (b* (((mv order-res &)
              (lexorder2 x y)))
          order-res))
       (t
        (or
         (and (= x-fn 1))
         (and (= y-fn 3)
              (not (= x-fn 3))))))))

  (defthmd s-order-sanity
    (implies (s-order x y)
             (not (s-order y x)))
    :hints (("Goal"
             :in-theory (e/d (GET-FIRST-FUNCTION
                              lexorder2-sanity-lemma1
                              lexorder2-sanity-lemma2
                              lexorder2-sanity-lemma3
                              EX-FROM-RP-Loose
                              is-rp
                              LEXORDER2-SANITY) ()))))

  (verify-guards s-order
    :hints (("Goal"
             :in-theory
             (e/d () (get-first-function lexorder2 #|get-pp+-depth||# #|count-pp||#))))))

(encapsulate
  nil

  (local
   (in-theory (enable measure-lemmas)))

  (defund-inline should-sum-terms-cancel (term1 term2)
    (declare (xargs :verify-guards t))
    (b* (;;(term1 (ex-from-rp term1))
         ;;(term2 (ex-from-rp term2))
         )
      (or (and (case-match term1 (('-- &) t))
               (rp-equal-cnt (cadr term1) term2 0))
          (and (case-match term2 (('-- &) t))
               (rp-equal-cnt (cadr term2) term1 0)))))

  (define is-a-type-fixed-fnc (term)
    :inline t
    (case-match term
      (('b+ & &) t)
      (('m2 &) t)
      (('f2 &) t)
      (('d2 &) t)
      (('-- &) t)
      (('p+ & &) t)
      (('merge-b+ & &) t)
      (('merge-pp+ & &) t)))

  (defun resolve-b+-order-rec (y z)
    (declare (xargs :guard t
                    :measure (+ (cons-count y)
                                (cons-count z))
                    :verify-guards t))
    (b* ((orig-y y)
         (orig-z z)
         (y (ex-from-rp y))
         (z (ex-from-rp z)))
      (case-match y
        (('b+ a b)
         (if (equal a ''0)
             (resolve-b+-order-rec b z)
           (case-match z
             (('b+ c d)
              (cond ((equal c ''0)
                     (resolve-b+-order-rec y d))
                    ((should-sum-terms-cancel a c)
                     (resolve-b+-order-rec b d))
                    ((s-order a c)
                     (b* (((mv rest rest-dont-rw)
                           (resolve-b+-order-rec b orig-z)))
                       (mv `(b+ ,a ,rest)
                           (list nil t rest-dont-rw))))
                    (t
                     (b* (((mv rest rest-dont-rw)
                           (resolve-b+-order-rec orig-y d)))
                       (mv `(b+ ,c ,rest)
                           (list nil t rest-dont-rw))))))
             (''0 (mv orig-y t))
             (&
              (cond
               ((should-sum-terms-cancel a z)
                (if (is-a-type-fixed-fnc b)
                    (mv b t)
                  (mv `(type-fix ,b) `(nil t))))
               ((s-order a z)
                (b* (((mv rest rest-dont-rw)
                      (resolve-b+-order-rec b orig-z)))
                  (mv `(b+ ,a ,rest)
                      (list nil t rest-dont-rw))))
               (t
                (mv `(b+ ,orig-z ,orig-y)
                    (list nil t t))))))))
        (''0
         (if (is-a-type-fixed-fnc z)
             (mv orig-z t)
           (mv `(type-fix ,orig-z) `(nil t))))
        (&
         (case-match z
           (('b+ c d)
            (cond
             ((should-sum-terms-cancel c y)
              (if (is-a-type-fixed-fnc d)
                  (mv d t)
                (mv `(type-fix ,d) `(nil t))))
             ((s-order y c)
              (mv `(b+ ,orig-y (b+ ,c ,d))
                  `(nil t (nil t t))))
             (t
              (b* (((mv rest rest-dont-rw)
                    (resolve-b+-order-rec orig-y d)))
                (mv `(b+ ,c ,rest)
                    (list nil t rest-dont-rw))))))
           (''0
            (if (is-a-type-fixed-fnc y)
                (mv orig-y t)
              (mv `(type-fix ,orig-y) `(nil t))))
           (&
            (cond
             ((should-sum-terms-cancel z y)
              (mv ''0 t))
             ((s-order orig-y orig-z)
              (mv `(b+ ,orig-y ,orig-z)
                  `(nil t t)))
             (t (mv
                 `(b+ ,orig-z ,orig-y)
                 `(nil t t)))))))))))

(defund-inline does-belong-to-pp+ (term)
  (declare (xargs :guard t))
  (b* ((term (ex-from-rp term)))
    (case-match term
      (('m2 &) nil)
      (('b+ & &) nil)
      (('f2 &) nil)
      (('d2 &) nil)
      #|(('[] & &) nil)||#
      (('type-fix x) (does-belong-to-pp+ x))
      (('-- x) (does-belong-to-pp+ x))
      (& t))))

(defund mv-nth-cw (i x)
  (declare (xargs :guard (natp i)
                  :verify-guards t))
  (if (atom x)
      (cw "mv-nth-cw: the term is shorter than the requested index. ~%")
    (if (zp i)
        (car x)
      (mv-nth-cw (1- i)
                 (cdr x)))))

(defund resolve-b+-sweep-into-pp+ (term old-dont-rw)
  (declare (xargs :guard t
                  :verify-guards t))
  ;; collect every term that is not m2, f2 or f2o in merge-pp+
  (cond
   ((equal old-dont-rw t)
    (if (does-belong-to-pp+ term)
        (mv `(merge-pp+ ,term '0)
            `(nil ,old-dont-rw t))
      (mv term old-dont-rw)))
   ((and (consp term)
         (or (equal (car term) 'f2)
             (equal (car term) 'd2)))
    (mv term old-dont-rw))
   (t
    (case-match term
      (('b+ a b)
       (b* (((mv rest-term rest-dont-rw)
             (resolve-b+-sweep-into-pp+ b (mv-nth-cw 2 old-dont-rw))))
         (cond
          ((not (does-belong-to-pp+ a))
           (mv ;;`(b+ ,a ,rest-term)
            (cons-with-hint 'b+
                            (cons-with-hint a
                                            (cons-with-hint rest-term
                                                            nil
                                                            (cddr term))
                                            (cdr term))
                            term)
            `(nil t ,rest-dont-rw)))
          ((equal rest-dont-rw t)
           (if (does-belong-to-pp+ rest-term)
               (mv `(merge-pp+ ,a ,rest-term)
                   `(nil t ,rest-dont-rw))
             (mv `(b+ (merge-pp+ ,a '0) ,rest-term)
                 `(nil (nil t t) ,rest-dont-rw))))
          (t
           (case-match rest-term
             (('b+ ('p+ & &) &)
              (mv `(b+ (merge-pp+ ,a ,(cadr rest-term)) ,(caddr rest-term))
                  `(nil (nil t ,(mv-nth-cw 1 rest-dont-rw)) ,(mv-nth-cw 2 rest-dont-rw))))
             (('b+ ('merge-pp+ & &) &)
              (mv `(b+ (merge-pp+ ,a ,(cadr rest-term)) ,(caddr rest-term))
                  `(nil (nil t ,(mv-nth-cw 1 rest-dont-rw)) ,(mv-nth-cw 2 rest-dont-rw))))
             (&
              (if (does-belong-to-pp+ rest-term)
                  (mv `(merge-pp+ ,a ,rest-term)
                      `(nil t ,rest-dont-rw))
                (mv `(b+ (merge-pp+ ,a '0) ,rest-term)
                    `(nil (nil t t) ,rest-dont-rw)))))))))
      (&
       (if (does-belong-to-pp+ term)
           (mv `(merge-pp+ ,term '0)
               `(nil ,old-dont-rw t))
         (mv term old-dont-rw)))))))


(defun is-b+-sweeped-right (term)
  (declare (xargs :guard t))
  (b* ((term (ex-from-rp term)))
    (case-match term
      (('adder-b+ & &)
       t)
      (('b+ ('p+ & &) b)
       (is-b+-sweeped-right b))
      (('b+ ('merge-pp+ & &) b)
       (is-b+-sweeped-right b))
      (('b+ a b)
       (and (not (does-belong-to-pp+ a))
            (is-b+-sweeped-right b)))
      (('p+ & &)
       t)
      (('merge-pp+ & &)
       t)
      (('-- &)
       t)
      (& (not (does-belong-to-pp+ term))))))   
       

#|(encapsulate
  nil
  (local
   (in-theory (enable measure-lemmas)))

  (defmacro resolve-b-fnc+-order-rec-create (fnc type-fix)
    (acl2::template-subst
     `(defun resolve-<fnc>-order-rec (y z)
        (declare (xargs :guard t
                        :measure (+ (cons-count y)
                                    (cons-count z))
                        :verify-guards nil))
        (b* ((orig-y y)
             (orig-z z)
             (y (ex-from-rp y))
             (z (ex-from-rp z)))
          (case-match y
            ((',fnc a b)
             (if (equal a ''0)
                 (resolve-<fnc>-order-rec b z)
               (case-match z
                 ((',fnc c d)
                  (cond ((equal c ''0)
                         (resolve-<fnc>-order-rec y d))
                        ((s-order a c)
                         (b* (((mv rest rest-dont-rw)
                               (resolve-<fnc>-order-rec b z)))
                           (mv `(,',fnc ,a ,rest)
                               (list nil t rest-dont-rw))))
                        (t
                         (b* (((mv rest rest-dont-rw)
                               (resolve-<fnc>-order-rec y d)))
                           (mv `(,',fnc ,c ,rest)
                               (list nil t rest-dont-rw))))))
                 (''0 (mv orig-y t))
                 (&
                  (cond
                   ((s-order a orig-z)
                    (b* (((mv rest rest-dont-rw)
                          (resolve-<fnc>-order-rec b orig-z)))
                      (mv `(,',fnc ,a ,rest)
                          (list nil t rest-dont-rw))))
                   (t
                    (mv `(,',fnc ,orig-z ,orig-y)
                        (list nil t t))))))))
            (''0
             (case-match z
               ((',fnc & &) (mv orig-z t))
               (& (mv `(,',type-fix ,orig-z) `(nil t)))))
            (&
             (case-match z
               ((',fnc c d)
                (cond ((s-order y c)
                       (mv `(,',fnc ,orig-y (,',fnc ,c ,d))
                           `(nil t (nil t t))))
                      (t
                       (b* (((mv rest rest-dont-rw)
                             (resolve-<fnc>-order-rec orig-y d)))
                         (mv `(,',fnc ,c ,rest)
                             (list nil t rest-dont-rw))))))
               (''0 (mv `(,',type-fix ,orig-y)
                        `(nil t)))
               (&
                (cond ((s-order orig-y orig-z)
                       (mv `(,',fnc ,orig-y ,orig-z)
                           `(nil t t)))
                      (t
                       (mv
                        `(,',fnc ,orig-z ,orig-y)
                        `(nil t t))))))))))
     :str-alist `(("<FNC>" . ,(symbol-name fnc)))
     :pkg-sym 'RP))

  #|(resolve-b-fnc+-order-rec-create b+ type-fix)||#
  (resolve-b-fnc+-order-rec-create b-m2+ m2)
;(resolve-b-fnc+-order-rec-create b+ type-fix)
  )||#

(defun is-b+-ordered (term)
  (declare (xargs :guard t))
  (case-match term
    (('b+ a ('b+ b c))
     (and (not (s-order b a))
          (is-b+-ordered `(b+ ,b ,c))))
    (('b+ a b)
     (not (s-order b a)))
    (&
     t)))

(defun resolve-b+-order (term)
  (declare (xargs :guard t
                  :verify-guards t))
  (case-match term
    (('merge-b+ x z)
     (b* (((mv res dont-rw) (resolve-b+-order-rec x z))
          ;(- (cw "inter result ~p0 ~%" res))
          ((mv res dont-rw) (case-match res
                              (('b+ & &)
                               (resolve-b+-sweep-into-pp+ res dont-rw))
                              (& (mv res dont-rw))))
          #|(- (if (not (is-b+-ordered x))
                 (cw "Some input was not ordered ~p0 ~%" x)
               nil))||#
          #|(- (if (not (is-b+-ordered z))
                 (cw "Some input was not ordered ~p0 ~%" z)
               nil))||#
          #|(- (if (not (is-b+-ordered res))
                 (progn$ (cw "Result is not ordered x=~p0 z=~p1 res:~p2 ~%" x z
                             res)
                         (hard-error 'resolve-b+-order
                                     "error! ~%"
                                     nil))
          nil))||#
          #|(- (if (not (is-b+-sweeped-right res))
                 (progn$ (cw "Result is not swept right x=~p0 z=~p1 res:~p2 ~%" x z
                             res)
                         (hard-error 'resolve-b+-order
                                     "error! ~%"
                                     nil))
               nil))||#)
       (mv res dont-rw)))
    (& (mv term nil))))

;; :i-am-here
;; (resolve-b+-order
;;  '(merge-b+ (RP 'BITP (B+ (-- (BINARY-AND a b)) (F2 x)))
;;             (RP 'BITP (M2 (PP+ n m)))))

(local
 (defthm hide-x-def
   (equal (hide x)
          x)
   :hints (("Goal"
            :expand (hide x)
            :in-theory (e/d () ())))))

(local
 (defthm rec-lemma1
   (equal (type-fix (+ (type-fix a) (type-fix b)))
          (+ (type-fix a) (type-fix b)))
   :hints (("Goal"
            :in-theory (e/d (type-fix) ())))))

(local
 (defthm rec-lemma2
   (equal (type-fix (type-fix a) )
          (type-fix a))
   :hints (("Goal"
            :in-theory (e/d (type-fix) ())))))


(local
 (defthm rec-lemma3
   (implies (equal x (+ (type-fix a) (type-fix b)))
            (equal (equal (+ c (type-fix x))
                          (+ (type-fix a) c (type-fix b)))
                   t))))

(local
 (defthm rec-lemma4
   (implies (equal x (+ (type-fix a) (type-fix b) (type-fix c)))
            (equal (equal (+ m (type-fix x))
                          (+ m x))
                   t))
   :hints (("Goal"
            :in-theory (e/d (type-fix) ())))))

(local
 (defthm rec-lemma5
   (implies (equal x (+ (type-fix a) (type-fix b) ))
            (equal (equal (+ m (type-fix x))
                          (+ m x))
                   t))
   :hints (("Goal"
            :in-theory (e/d (type-fix) ())))))

(local
 (defthm extract-from-type-fix
   (implies (integerp x)
            (equal (type-fix x)
                   x))
   :hints (("Goal"
            :in-theory (e/d (type-fix) ())))))

(encapsulate
  nil

  (local
   (in-theory (disable s-order
                       ex-from-rp
                       RESOLVE-B+-SWEEP-INTO-PP+
                       is-b+-ordered
                       ALL-SUMS-IS-SUM
                       (:TYPE-PRESCRIPTION DOES-BELONG-TO-PP+$INLINE)
                       DOES-BELONG-TO-PP+
                       ex-from-rp-loose
                       resolve-b+-order-rec)))

  (def-formula-checks
   sum-meta-formal-checks
   (b+
    --
    type-fix
    resolve-b+-order
    hide
    m2
    f2
    minus
    times2
    d2
    p+
    merge-b+
    merge-pp+)))

(local
 (in-theory (disable rp-trans)))

(defun mv-nth-0-resolve-b+-order (term)
  (b* (((mv term &) (resolve-b+-order term)))
    term))

(local
 (defthmd rp-evl-of-ex-from-rp-reverse
   (implies (syntaxp (or (atom term)
                         #|(and (not (equal (car term)
                         'ex-from-rp))
                         (not (quotep term)))||#))
            (equal
             (rp-evlt term a)
             (rp-evlt (ex-from-rp term) a)
             ))
   :hints (("Goal"
            :in-theory (e/d (ex-from-rp
                             is-rp) ())))))

(local
 (defthm is-rp-ex-from-rp
   (not (is-rp (ex-from-rp term)))
   :hints (("Goal"
            :in-theory (e/d (is-rp
                             ex-from-rp) ())))))

(local
 (defthm ex-from-rp-is-zero
   (implies (EQUAL (EX-FROM-RP X) ''0)
            (equal (rp-evlt x a) 0))
   :hints (("Goal"
            :in-theory (e/d (rp-evl-of-ex-from-rp-reverse)
                            (rp-evl-of-ex-from-rp))))))

(local
 (defthm dummy-lemma1
   (implies (EQUAL m
                   (+ (TYPE-FIX (RP-EVLT (EX-FROM-RP Y) A))
                      (TYPE-FIX (RP-EVLT (EX-FROM-RP (CADDR (EX-FROM-RP X)))
                                        A))))
            (equal (EQUAL (+ (TYPE-FIX (RP-EVLT (CADR (EX-FROM-RP X)) A))
                             m)
                          (+ (TYPE-FIX (RP-EVLT (EX-FROM-RP Y) A))
                             (TYPE-FIX (RP-EVLT (CADR (EX-FROM-RP X)) A))
                             (TYPE-FIX (RP-EVLT (CADDR (EX-FROM-RP X)) A))))
                   t))
   :hints (("Goal"
            :in-theory (e/d (rp-evlt-of-ex-from-rp) ())))))

#|(local
 (defthm type-fix-is-ifix
   (equal (type-fix x)
          (ifix x))))||#

#|(local
 (progn
   (defthm try-to-cancel-with-rest-returns-rp-termp
     (implies (and (rp-termp term1)
                   (rp-termp term2))
              (rp-termp (mv-nth 0 (try-to-cancel-with-rest term1 term2 dont-rw))))
     :hints (("Goal"
              :in-theory (e/d (try-to-cancel-with-rest)
                              ((:DEFINITION EX-FROM-RP)
                               (:DEFINITION SHOULD-B+-CANCEL))))))

   (defthm try-to-cancel-with-rest-returns-dont-rw-syntaxp
     (implies (and (dont-rw-syntaxp dont-rw))
              (dont-rw-syntaxp (mv-nth 1 (try-to-cancel-with-rest term1 term2 dont-rw))))
     :hints (("Goal"
              :in-theory (e/d (try-to-cancel-with-rest
                               dont-rw-syntaxp)
                              ((:DEFINITION EX-FROM-RP)
                               (:DEFINITION SHOULD-B+-CANCEL))))))))||#

(local
 (defthm b+-minus-a-a
   (and (equal (sum (-- x) x)
               0)
        (equal (sum x (-- x))
               0)
        (equal (sum x (-- x) b)
               (sum b 0))
        (equal (sum (-- x) x b)
               (sum b 0)))
   :hints (("Goal"
            :in-theory (e/d (sum type-fix) ())))))

(local
 (encapsulate
   nil

   (local
    (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

   (local
    (defthmd dl1
      (implies (and (CONSP X)
                    (EQUAL (CAR X) '--)
                    (CONSP (CDR X))
                    (NOT (CDDR X))
                    (syntaxp (or (atom x)
                                 (and (equal (car x) 'ex-from-rp)
                                      (consp (cdr x))
                                      (atom (cadr x))))))
               (and (equal (rp-evlt x a)
                           (rp-evlt `(-- ,(cadr x)) a))
                    (equal (rp-evl x a)
                           (rp-evl `(-- ,(cadr x)) a))))))

   (local
    (defthm dl2
      (implies (and (CONSP X)
                    (EQUAL (CAR X) '--)
                    (CONSP (CDR X))
                    (NOT (CDDR X))
                    (rp-evl-meta-extract-global-facts)
                    (sum-meta-formal-checks state)
                    (syntaxp (or (atom x)
                                 (and (equal (car x) 'ex-from-rp)
                                      (consp (cdr x))
                                      (atom (cadr x))))))
               (and (equal (rp-evlt x a)
                           (-- (rp-evlt (cadr x) a)))
                    (equal (rp-evl x a)
                           (-- (rp-evl (cadr x) a)))))
      :hints (("Goal"
               :expand ((RP-TRANS (LIST '-- (CADR X))))
               :in-theory (e/d (dl1) ())))))

   (local
    (defthm dl3
      (and (implies (and (RP-TERMP X)
                         (not (quotep x))
                         (CONSP X)
                         (CONSP (CDR X)))
                    (RP-TERMP (CADR X))))))

   (local
    (defthm dl4
      (implies (and (EQUAL (CAR X) '--)
                    (consp x)
                    (CONSP (CDR X))
                    (NOT (CDDR X)))
               (and (CONSP (ex-from-rp X))
                    (EQUAL (CAR (ex-from-rp X)) '--)
                    (CONSP (CDR (ex-from-rp X)))
                    (NOT (CDDR (ex-from-rp X)))))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (is-rp) ())))))

   (defun SHOULD-B+-CANCEL-aux (x y)
     (if (CASE-MATCH x (('-- &) T))
         (RP-EQUAL-CNT (CADR x) y 0)
       nil))

   (LOCAL
    (defthm sum-when-SHOULD-B+-CANCEL-lemma
      (implies (and (SHOULD-B+-CANCEL-aux x y)
                    (rp-termp x)
                    (rp-termp y)
                    (rp-evl-meta-extract-global-facts)
                    (sum-meta-formal-checks state))
               (and (equal (sum (rp-evlt x a)
                                (rp-evlt y a))
                           0)
                    (equal (sum (rp-evl x a)
                                (rp-evl y a))
                           0)
                    (equal (sum (rp-evlt x a)
                                (rp-evlt y a)
                                b)
                           (sum b 0))
                    (equal (sum (rp-evl x a)
                                (rp-evl y a)
                                b)
                           (sum b 0))
                    (equal (sum (rp-evlt y a)
                                (rp-evlt x a))
                           0)
                    (equal (sum (rp-evl y a)
                                (rp-evl x a))
                           0)
                    (equal (sum (rp-evlt y a)
                                (rp-evlt x a)
                                b)
                           (sum b 0))
                    (equal (sum (rp-evl y a)
                                (rp-evl x a)
                                b)
                           (sum b 0))))
      :hints (("Goal"
               :use ((:instance rp-evlt-of-rp-equal
                                (term1 y)
                                (term2 (cadr x)))
                     (:instance rp-evl-of-rp-equal
                                (term1 y)
                                (term2 (cadr x)))

                     )
               :in-theory (e/d (IS-RP
;rp-evl-of-ex-from-rp-reverse
                                type-fix
                                ex-from-rp)
                               (rp-termp
                                rp-evl-of-rp-equal
                                rp-evlt-of-rp-equal
                                EVL-OF-EXTRACT-FROM-RP
                                EX-FROM-RP
                                (:DEFINITION NOT)
                                b+
                                --
                                (:DEFINITION FIX)
                                (:DEFINITION IFIX)
                                (:REWRITE RP-EVL-OF-VARIABLE)
;(:DEFINITION SHOULD-B+-CANCEL)
                                RP-EVLT-OF-EX-FROM-RP))))))

   (defthm SHOULD-B+-CANCEL-aux-redef
     (equal (should-sum-terms-cancel x y)
            (or (SHOULD-B+-CANCEL-aux x y)
                (SHOULD-B+-CANCEL-aux y x)))
     :hints (("Goal"
              :in-theory (e/d (should-sum-terms-cancel) ()))))

   (defthm sum-when-should-b+-cancel
     (implies (and (should-sum-terms-cancel x y)
                   (rp-termp x)
                   (rp-termp y)
                   (rp-evl-meta-extract-global-facts)
                   (sum-meta-formal-checks state))
              (and (equal (sum (rp-evlt x a)
                               (rp-evlt y a))
                          0)
                   (equal (sum (rp-evl x a)
                               (rp-evl y a))
                          0)
                   (equal (sum (rp-evlt x a)
                               (rp-evlt y a)
                               b)
                          (sum b 0))
                   (equal (sum (rp-evl x a)
                               (rp-evl y a)
                               b)
                          (sum b 0))
                   (equal (sum (rp-evlt y a)
                               (rp-evlt x a))
                          0)
                   (equal (sum (rp-evl y a)
                               (rp-evl x a))
                          0)
                   (equal (sum (rp-evlt y a)
                               (rp-evlt x a)
                               b)
                          (sum b 0))
                   (equal (sum (rp-evl y a)
                               (rp-evl x a)
                               b)
                          (sum b 0))))
     :hints (("Goal"
              :use ((:instance rp-evl-of-rp-equal
                               (term1 y)
                               (term2 (cadr x)))
                    #|(:instance rp-evlt-of-rp-equal
                               (term1 y)
                               (term2 (cadr x)))||#

                    )
              :in-theory (e/d (IS-RP
;rp-evl-of-ex-from-rp-reverse
                               type-fix
                               ex-from-rp)
                              (rp-termp
                               EVL-OF-EXTRACT-FROM-RP
                               EX-FROM-RP
                               (:DEFINITION NOT)
                               b+
                               should-sum-terms-cancel
                               SHOULD-B+-CANCEL-aux
                               --
                               (:DEFINITION FIX)
                               (:DEFINITION IFIX)
                               (:REWRITE RP-EVL-OF-VARIABLE)
                               RP-EVLT-OF-EX-FROM-RP)))))))


#|(local
 (encapsulate
   nil

   (defthm rp-termp-ex-from-rp
     (implies (and (rp-termp term))
              (rp-termp (ex-from-rp term))))))||#

#|(defthm SHOULD-B+-CANCEL-implies-fc
  (implies (SHOULD-B+-CANCEL term1 term2)
           (COND ((CASE-MATCH TERM1 (('-- &) T))
                  (RP-EQUAL-CNT (CADR TERM1) TERM2 0))
                 ((CASE-MATCH TERM2 (('-- &) T))
                  (RP-EQUAL-CNT (CADR TERM2) TERM1 0))
                 (T NIL)))
  :rule-classes :forward-chaining)||#

(local
 (defthmd sum-0
   (equal (sum 0 x)
          (type-fix x))))

(local
 (defthm sum-of-type-fix
   (and (equal (sum a (type-fix b))
               (sum a b))
        (equal (sum (type-fix b) a )
               (sum b a)))))

(local
 (defthm dumm-lemma3
   (implies (and (CONSP x)
                 (CONSP (CDR x))
                 (CONSP (CDDR x))
                 (RP-TERMP X))
            (RP-TERMP (CADDR x)))))

#|(local
 (encapsulate
   nil

   (local
    (defthm dl1
      (implies (and (CONSP REST)
                    (EQUAL (CAR REST) 'TYPE-FIX)
                    (CONSP (CDR REST))
                    (not (cddr rest))
                    (rp-evl-meta-extract-global-facts)
                    (sum-meta-formal-checks state))
               (equal (RP-EVL REST A)
                      (type-fix (rp-evl (cadr rest) a))))))

   (local
    (defthm dl2
      (implies (and (CONSP REST)
                    (EQUAL (CAR REST) 'b+)
                    (CONSP (CDR REST))
                    (CONSP (CDDR REST))
                    (NOT (CDDDR REST))
                    (rp-evl-meta-extract-global-facts)
                    (sum-meta-formal-checks state))
               (equal (RP-EVL REST A)
                      (sum (rp-evl (cadr rest) a)
                           (rp-evl (caddr rest) a))))))

   (local
    (defthm dl3
      (equal (EQUAL (TYPE-FIX x)
                    (SUM x 0))
             t)))

   (defthm rp-evl-of-try-to-cancel-with-rest
     (implies (and (rp-evl-meta-extract-global-facts)
                   (sum-meta-formal-checks state)
                   (rp-termp x)
                   (rp-termp rest))
              (equal (rp-evl (mv-nth 0 (try-to-cancel-with-rest x rest dont-rw)) a)
                     (sum (rp-evl x a) (rp-evl rest a))))
     :hints (("Goal"
              :in-theory (e/d (TRY-TO-CANCEL-WITH-REST)
                              (b+
                               type-fix
                               type-fix-is-ifix
                               RP-EVL-OF-VARIABLE
                               --
                               should-b+-cancel
                               should-b+-cancel-aux-redef)))))))||#

(local
 (defthm dumm-lemma4
   (implies (equal (sum a b) 0)
            (equal (equal (type-fix x) (sum a b x))
                   t))
   :hints (("Goal"
            :in-theory (e/d (sum type-fix) ())))
   ))

(local
 (defthm sum-of-not-integer
   (implies (not (integerp x))
            (equal (sum y x)
                   (sum y 0)))
   :hints (("Goal"
            :in-theory (e/d (sum type-fix) ())))))

(local
 (defthm dumm-lemma5
   (implies (and (CONSP x)
                 (CONSP (CDR x))
                 (CONSP (CDDR x))
                 (RP-TERMP X))
            (RP-TERMP (CADR x)))))

(local
 (defthm sum-of-ifix
   (equal (sum a (type-fix b))
          (sum a b))))

(local
 (defthm rp-termp-resolve-b+-order-rec
   (implies (and (rp-termp x)
                 (rp-termp y))
            (rp-termp (mv-nth 0 (resolve-b+-order-rec y x))))
   :hints (("Goal"
            :in-theory (e/d (resolve-b+-order-rec)
                            (s-order
                             EX-FROM-RP
                             SHOULD-B+-CANCEL-AUX-REDEF
                             SHOULD-B+-CANCEL-AUX
                             should-sum-terms-cancel
                             ))))))

(local
 (defthm rp-termp-RESOLVE-B+-SWEEP-INTO-PP+
   (implies (and (rp-termp x))
            (rp-termp (mv-nth 0 (RESOLVE-B+-SWEEP-INTO-PP+ x old-dont-rw))))
   :hints (("Goal"
            :in-theory (e/d (RESOLVE-B+-SWEEP-INTO-PP+)
                            (s-order
                             mv-nth-cw
                             EX-FROM-RP
                             SHOULD-B+-CANCEL-AUX-REDEF
                             SHOULD-B+-CANCEL-AUX
                             should-sum-terms-cancel
                             ))))))



(local
 (defthm type-fix-of-sum
   (equal (type-fix (sum a b))
          (sum a b))))

(local
 (defthm dl1
   (implies (and (CONSP REST)
                 (EQUAL (CAR REST) 'b+)
                 (CONSP (CDR REST))
                 (CONSP (CDDR REST))
                 (NOT (CDDDR REST))
                 (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state))
            (equal (RP-EVLT REST A)
                   (sum (rp-evlt (cadr rest) a)
                        (rp-evlt (caddr rest) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ())))))

(local
 (defthm merge-sum-eval
   (implies (and (CONSP REST)
                 (EQUAL (CAR REST) 'merge-b+)
                 (CONSP (CDR REST))
                 (CONSP (CDDR REST))
                 (NOT (CDDDR REST))
                 (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state))
            (equal (RP-EVLT REST A)
                   (sum (rp-evlt (cadr rest) a)
                        (rp-evlt (caddr rest) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ())))))

(local
 (defthm ----eval
   (implies (and (CONSP REST)
                 (EQUAL (CAR REST) '--)
                 (CONSP (CDR REST))
                 (NOT (CDDR REST))
                 (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state))
            (equal (RP-EVLT REST A)
                   (-- (rp-evlt (cadr rest) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ())))))

(local
 (defthm f2o--eval
   (implies (and (CONSP REST)
                 (EQUAL (CAR REST) 'd2)
                 (CONSP (CDR REST))
                 (NOT (CDDR REST))
                 (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state))
            (equal (RP-EVLT REST A)
                   (d2 (rp-evlt (cadr rest) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ())))))

(local
 (defthm times2--eval
   (implies (and (CONSP REST)
                 (EQUAL (CAR REST) 'times2)
                 (CONSP (CDR REST))
                 (NOT (CDDR REST))
                 (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state))
            (equal (RP-EVLT REST A)
                   (times2 (rp-evlt (cadr rest) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ())))))

(local
 (defthm minus--eval
   (implies (and (CONSP REST)
                 (EQUAL (CAR REST) 'minus)
                 (CONSP (CDR REST))
                 (NOT (CDDR REST))
                 (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state))
            (equal (RP-EVLT REST A)
                   (minus (rp-evlt (cadr rest) a))))
   :hints (("Goal"
            :in-theory (e/d (rp-trans) ())))))

(local
 (defthm dl2
   (equal (equal (sum a b)
                 (sum a c))
          (equal (type-fix b)
                 (type-fix c)))))

(local
 (defthm ex-from-rp-of-ex-from-rp
   (equal (ex-from-rp (ex-from-rp x))
          (ex-from-rp x))))

(local
 (defthm type-fix-of-a-is-a-type-fixed-fnc
   (implies (and (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state)
                 (is-a-type-fixed-fnc term))
            (EQUAL (TYPE-FIX (RP-EVLT term A))
                   (RP-EVLT term A)))
   :hints (("Goal"
            :expand (RP-TRANS-LST (CDR TERM))
            :in-theory (e/d (is-a-type-fixed-fnc
                             rp-trans
                             type-fix
                             d2
                             times2
                             minus)
                            ())))))



(DEFTHMd
  RP-EVL-OF-EX-FROM-RP-REVERSE-2
  (IMPLIES (SYNTAXP (OR (ATOM TERM)))
           (EQUAL (RP-EVL TERM A)
                  (RP-EVL (EX-FROM-RP TERM) A)))
  :HINTS (("Goal" :IN-THEORY (E/D (EX-FROM-RP IS-RP) NIL))))

(local
 (defthm dumm-lemma6
   (implies (equal x (sum a b))
            (equal (type-fix x)
                   x))
   :rule-classes :forward-chaining))

(local
 (defthmd resolve-b+-order-rec-correct
   (implies (and (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state)
                 (rp-termp x)
                 (rp-termp y))
            (equal (rp-evlt (mv-nth 0 (resolve-b+-order-rec y x)) a)
                   (b+ (rp-evlt y a) (rp-evlt x a))))
   :hints (("Goal"
            :induct (resolve-b+-order-rec y x)
            :do-not-induct t
            :expand ((:free (x) (RP-TRANS (cons 'TYPE-FIX x))))
            :in-theory (e/d (;sum-comm-1
                             rp-evl-of-fncall-args
                             ;sum-comm-2
                             rp-evl-of-ex-from-rp-reverse
                             RP-EVL-OF-EX-FROM-RP-REVERSE-2
                             sum-0
                             sum-reorder)
                            (s-order
                             b+
                             #|TRY-TO-CANCEL-WITH-REST||#
                             SHOULD-B+-CANCEL-AUX-REDEF
                             SHOULD-B+-CANCEL-AUX
                             should-sum-terms-cancel
                             RP-TRANS-IS-TERM-WHEN-LIST-IS-ABSENT
                             merge-b+
                             RP-EVLT-OF-EX-FROM-RP
                             type-fix
                             cons-equal
                             RP-EVL-OF-VARIABLE
                             ifix
                             EX-FROM-RP
                             ;TYPE-FIX-IS-IFIX
                             should-sum-terms-cancel
                             rp-evl-of-ex-from-rp))))))

(local
 (defthm merge-b+-to-b+
   ;; in case meta rule is disabled.
   (equal (merge-b+ a c)
          (sum a c))
   :hints (("Goal"
            :in-theory (e/d (merge-b+ b+ type-fix) ())))))

(local
 (defthm merge-b+-reorder
   ;; in case meta rule is disabled.
   (equal (merge-b+ (b+ a b) c)
          (sum a b c))
   :hints (("Goal"
            :in-theory (e/d (merge-b+ b+ type-fix) ())))))

(local
 (defthm type-fix-type
   (and (integerp (TYPE-FIX (RP-EVLT X A)))
        (ACL2-NUMBERP (TYPE-FIX (RP-EVLT X A))))
   :hints (("Goal"
            :in-theory (e/d (type-fix) ())))))

#|(local
 (defthm does-belong-to-pp+-implies
   (implies (and (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state)
                 (does-belong-to-pp+ x))
            (equal (type-fix (rp-evl x a))
                   (rp-evl x a)))
   :hints (("goal"
            :in-theory (e/d (does-belong-to-pp+
                             rp-evl-of-ex-from-rp-reverse
                             type-fix)
                            (rp-evl-of-ex-from-rp
                             TYPE-FIX-IS-IFIX))))))||#

(local
 (defthm lemma1
   (implies (equal (+ (type-fix a)
                      (type-fix b))
                   y)
            (equal (type-fix y)
                   y))))

(local
 (defthm dumm-lemma7
   (equal (RP-EVL ''0 A)
          0)))




(local
 (defthm rp-evl-of-resolve-B+-SWEEP-INTO-PP+
   (implies (and (rp-evl-meta-extract-global-facts)
                 (sum-meta-formal-checks state)
                 (case-match x
                   (('b+ & &) t)))
            (equal (rp-evlt (mv-nth 0 (resolve-b+-sweep-into-pp+ x old-dont-rw)) a)
                   (rp-evlt x a)))
   :rule-classes :rewrite
   :hints (("Goal"
            :induct (resolve-b+-sweep-into-pp+ x old-dont-rw)
            :expand ((:free (x) (rp-trans (cons 'MERGE-PP+ x)))) 
            :do-not-induct t
            :in-theory (e/d (resolve-b+-sweep-into-pp+)
                            (;TYPE-FIX-IS-IFIX
                             rp-trans
                             sum
                             pp-sum
                             type-fix
                             (:TYPE-PRESCRIPTION TYPE-FIX)
                             (:REWRITE SUM-WHEN-SHOULD-B+-CANCEL)
                             (:REWRITE SHOULD-B+-CANCEL-AUX-REDEF)
                             rp-trans-is-term-when-list-is-absent
                             (:DEFINITION SHOULD-B+-CANCEL-AUX)
                             EX-FROM-RP
                             (:DEFINITION RP-EQUAL-CNT)
                             (:REWRITE TYPE-FIX-OF-A-IS-A-TYPE-FIXED-FNC)
                             (:REWRITE F2O--EVAL)
                             (:REWRITE MERGE-SUM-EVAL)
                             (:REWRITE ----EVAL)
                             (:REWRITE RP-EVL-OF-UNARY-/-CALL)
                             (:REWRITE RP-EVL-OF-VARIABLE)
                             (:REWRITE RP-EVL-OF-UNARY---CALL)
                             (:REWRITE RP-EVL-OF-TYPESPEC-CHECK-CALL)
                             (:REWRITE RP-EVL-OF-SYNP-CALL)
                             (:REWRITE RP-EVL-OF-SYMBOLP-CALL)
                             (:REWRITE RP-EVL-OF-SYMBOL-PACKAGE-NAME-CALL)
                             (:REWRITE RP-EVL-OF-SYMBOL-NAME-CALL)
                             (:REWRITE RP-EVL-OF-STRINGP-CALL)
                             (:REWRITE RP-EVL-OF-RP-EQUAL-SUBTERMS-CALL)
                             (:REWRITE
                              RP-EVL-OF-RP-EQUAL-CNT-SUBTERMS-CALL)
                             (:REWRITE RP-EVL-OF-RP-EQUAL-CNT-CALL)
                             (:REWRITE RP-EVL-OF-RP-EQUAL-CALL)
                             (:REWRITE RP-EVL-OF-RP-CALL)
                             (:REWRITE RP-EVL-OF-RETURN-LAST-CALL)
                             (:REWRITE RP-EVL-OF-REALPART-CALL)
                             (:REWRITE RP-EVL-OF-RATIONALP-CALL)
                             (:REWRITE RP-EVL-OF-QUOTE)
                             (:REWRITE RP-EVL-OF-NUMERATOR-CALL)
                             (:REWRITE RP-EVL-OF-NOT-CALL)
                             (:REWRITE RP-EVL-OF-LAMBDA)
                             (:REWRITE
                              RP-EVL-OF-INTERN-IN-PACKAGE-OF-SYMBOL-CALL)
                             (:REWRITE RP-EVL-OF-INTEGERP-CALL)
                             (:REWRITE RP-EVL-OF-IMPLIES-CALL)
                             mv-nth-cw))))))

(local
 (defthm resolve-b+-order-correct
   (implies (and (rp-evl-meta-extract-global-facts)
                 (rp-termp x)
                 (rp-termp y)
                 (sum-meta-formal-checks state))
            (equal (rp-evlt (mv-nth 0 (resolve-b+-order x)) a)
                   (rp-evlt x a)))
   :rule-classes :rewrite
   :hints (("Goal"
            :in-theory (e/d (resolve-b+-order-rec-correct)
                            ((:DEFINITION RESOLVE-B+-ORDER-REC)))))))

(local
 (defthm resolve-b+-order-correct-1
   (implies (and (rp-evl-meta-extract-global-facts)
                 (rp-termp x)
                 (rp-termp y)
                 (sum-meta-formal-checks state))
            (equal (rp-evlt (mv-nth-0-resolve-b+-order x) a)
                   (rp-evlt x a)))
   :rule-classes :rewrite
   :hints (("Goal"
            :in-theory (e/d ()
                            (
                             (:DEFINITION RESOLVE-B+-ORDER-REC)
                             resolve-b+-order
                             type-fix
                             ifix))))))

#|(local
 (encapsulate
   nil
   (local
    (defthm all-falist-consistent-implies-1
      (implies (and (all-falist-consistent term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp term))
               (all-falist-consistent (cadr term)))))

   (local
    (defthm all-falist-consistent-implies-2
      (implies (and (all-falist-consistent term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp (cddr term))
                    (consp term))
               (all-falist-consistent (caddr term)))))

   (local
    (defthm all-falist-consistent-implies-all-falist-consistent-ex-from-rp
      (implies (all-falist-consistent term)
               (all-falist-consistent (ex-from-rp term)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp is-rp) ())))))

   (defthm all-falist-consistent-resolve-b+-order-rec
     (implies (and (all-falist-consistent x)
                   (all-falist-consistent y))
              (all-falist-consistent (mv-nth 0 (resolve-b+-order-rec y x))))
     :hints (("Goal"
              :in-theory (e/d (resolve-b+-order-rec)
                              (s-order
                               ex-from-rp
                               SHOULD-B+-CANCEL-AUX-REDEF
                               SHOULD-B+-CANCEL-AUX
                               should-sum-terms-cancel)))))

   (defthm all-falist-consistent-RESOLVE-B+-SWEEP-INTO-PP+
     (implies (and (all-falist-consistent x))
              (all-falist-consistent (mv-nth 0 (RESOLVE-B+-SWEEP-INTO-PP+ x old-dont-rw))))
     :hints (("Goal"
              :in-theory (e/d (RESOLVE-B+-SWEEP-INTO-PP+)
                              (s-order
                               ex-from-rp
                               mv-nth-cw
                               SHOULD-B+-CANCEL-AUX-REDEF
                               SHOULD-B+-CANCEL-AUX
                               should-sum-terms-cancel)))))

   (defthm all-falist-consistent-resolve-b+-order
     (implies (all-falist-consistent x)
              (all-falist-consistent (mv-nth 0 (resolve-b+-order x))))
     :hints (("Goal"
              :in-theory (e/d ()
                              (s-order
                               resolve-b+-order-rec
                               ex-from-rp
                               SHOULD-B+-CANCEL-AUX-REDEF
                               SHOULD-B+-CANCEL-AUX
                               should-sum-terms-cancel)))))))||#

#|(local
 (encapsulate
   nil

   (local
    (defthm rp-syntaxp-implies-rp-syntaxp-ex-from-rp-term
      (implies (rp-syntaxp term)
               (rp-syntaxp (ex-from-rp term)))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp is-rp) ())))))

   (local
    (defthm rp-syntaxp-implies-1
      (implies (and (rp-syntaxp term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp term)
                    (Not (is-rp term)))
               (rp-syntaxp (cadr term)))))

   (local
    (defthm rp-syntaxp-implies-2
      (implies (and (rp-syntaxp term)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp (cddr term))
                    (consp term))
               (rp-syntaxp (caddr term)))))

   (local
    (defthm rp-syntaxp-resolve-b+-order-rec
      (implies (and (rp-syntaxp x)
                    (rp-syntaxp y))
               (rp-syntaxp (mv-nth 0 (resolve-b+-order-rec y x))))
      :hints (("goal"
               :in-theory (e/d (is-if is-rp)
                               (INCLUDE-FNC
                                SHOULD-B+-CANCEL-AUX-REDEF
                                SHOULD-B+-CANCEL-AUX
                                should-sum-terms-cancel
                                s-order
                                ex-from-rp))))))

   (local
    (defthm rp-syntaxp-RESOLVE-B+-SWEEP-INTO-PP+
      (implies (and (rp-syntaxp x))
               (rp-syntaxp (mv-nth 0 (RESOLVE-B+-SWEEP-INTO-PP+ x old-dont-rw))))
      :hints (("goal"
               :in-theory (e/d (is-if is-rp RESOLVE-B+-SWEEP-INTO-PP+)
                               (INCLUDE-FNC
                                SHOULD-B+-CANCEL-AUX-REDEF
                                SHOULD-B+-CANCEL-AUX
                                should-sum-terms-cancel
                                s-order
                                mv-nth-cw
                                ex-from-rp))))))

   (defthm rp-valid-termp-resolve-b+-order
     (implies  (rp-valid-termp x)
               (rp-valid-termp (mv-nth 0 (resolve-b+-order x))))
     :hints (("Goal"
              :in-theory (e/d () (resolve-b+-order-rec s-order)))))))||#

(local
 (encapsulate
   nil
   (local
    (defthm valid-sc-implies-valid-sc-ex-from-rp-term
      (implies (valid-sc term a)
               (valid-sc (ex-from-rp term) a))
      :rule-classes :forward-chaining
      :hints (("Goal"
               :in-theory (e/d (ex-from-rp is-rp) ())))))

   (local
    (defthm valid-sc-implies-1
      (implies (and (valid-sc term a)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp term)
                    (Not (is-rp term)))
               (valid-sc (cadr term) a))))

   (local
    (defthm valid-sc-implies-2
      (implies (and (valid-sc term a)
                    (not (quotep term))
                    (consp (cdr term))
                    (consp (cddr term))
                    (Not (is-rp term))
                    (Not (is-if term))
                    (consp term))
               (valid-sc (caddr term) a))))

   (local
    (defthm valid-sc-resolve-b+-order-rec
      (implies (and (valid-sc x a)
                    (valid-sc y a))
               (valid-sc (mv-nth 0 (resolve-b+-order-rec y x)) a))
      :hints (("Goal"
               :in-theory (e/d (is-if
                                is-rp)
                               (INCLUDE-FNC
                                s-order
                                SHOULD-B+-CANCEL-AUX-REDEF
                                SHOULD-B+-CANCEL-AUX
                                should-sum-terms-cancel
                                ex-from-rp
                                ))))))

   (local
    (defthm valid-sc-RESOLVE-B+-SWEEP-INTO-PP+
      (implies (and (valid-sc x a))
               (valid-sc (mv-nth 0 (RESOLVE-B+-SWEEP-INTO-PP+ x old-dont-rw)) a))
      :hints (("Goal"
               :in-theory (e/d (is-if
                                RESOLVE-B+-SWEEP-INTO-PP+
                                is-rp)
                               (INCLUDE-FNC
                                s-order
                                mv-nth-cw
                                SHOULD-B+-CANCEL-AUX-REDEF
                                SHOULD-B+-CANCEL-AUX
                                should-sum-terms-cancel
                                ex-from-rp
                                ))))))

   (defthm valid-sc-resolve-b+-order
     (implies (valid-sc term a)
              (valid-sc (mv-nth 0 (resolve-b+-order term)) a))
     :hints (("Goal"
              :in-theory (e/d (is-if is-rp)
                              (INCLUDE-FNC
                               resolve-b+-order-rec
                               s-order)))))))

(local
 (encapsulate
   nil

   (local
    (defthm dont-rw-syntaxp-resolve-b+-order-rec
      (dont-rw-syntaxp (mv-nth 1 (resolve-b+-order-rec y x)))
      :hints (("Goal"
               :in-theory (e/d (DONT-RW-SYNTAXP)
                               (s-order
                                (:DEFINITION SHOULD-B+-CANCEL-AUX)
                                should-sum-terms-cancel
                                (:REWRITE SHOULD-B+-CANCEL-AUX-REDEF)
                                ))))))

   (local
    (defthm dont-rw-syntaxp-mv-nth-cw
      (implies (dont-rw-syntaxp old-dont-rw)
               (dont-rw-syntaxp (mv-nth-cw n old-dont-rw)))
      :hints (("Goal"
               :in-theory (e/d (dont-rw-syntaxp
                                mv-nth-cw) ())))))

   (local
    (defthm dont-rw-syntaxp-RESOLVE-B+-SWEEP-INTO-PP+
      (implies (dont-rw-syntaxp old-dont-rw)
               (dont-rw-syntaxp (mv-nth 1 (RESOLVE-B+-SWEEP-INTO-PP+ x
                                                                     old-dont-rw))))
      :otf-flg t
      :hints (("Goal"
               :in-theory (e/d (;DONT-RW-SYNTAXP
                                DONT-RW-SYNTAXP-AUX
                                RESOLVE-B+-SWEEP-INTO-PP+)
                               (s-order
                                mv-nth-cw
                                (:e mv-nth-cw)
                                (:DEFINITION SHOULD-B+-CANCEL-AUX)
                                should-sum-terms-cancel
                                (:REWRITE SHOULD-B+-CANCEL-AUX-REDEF)
                                ))))))

   (defthm dont-rw-syntaxp-resolve-b+-order
     (dont-rw-syntaxp (mv-nth 1 (resolve-b+-order x)))
     :hints (("Goal"
              :in-theory (e/d (resolve-b+-order
                               DONT-RW-SYNTAXP)
                              (resolve-b+-order-rec)))))))

(local
 (defthm rp-termp-resolve-b+-order
   (implies (rp-termp x)
            (rp-termp (mv-nth 0 (resolve-b+-order x))))
   :hints (("Goal"
            :in-theory (e/d (resolve-b+-order)
                            (rp-termp
                             (:DEFINITION RESOLVE-B+-ORDER-REC)
                             (:REWRITE DEFAULT-CDR)
                             (:REWRITE DEFAULT-CAR)))))))

(defthm resolve-b+-order-is-valid-rp-meta-rulep
  (implies (and (sum-meta-formal-checks state)
                (rp-evl-meta-extract-global-facts :state state))
           (let ((rule (make rp-meta-rule-rec
                             :fnc 'resolve-b+-order
                             :trig-fnc 'merge-b+
                             :dont-rw t
                             :valid-syntax t)))
             (and (valid-rp-meta-rulep rule state)
                  (rp-meta-valid-syntaxp-sk rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (RP-META-VALID-SYNTAXP
                            resolve-b+-order-correct)
                           (RP-TERMP
                            resolve-b+-order
                            RP-TERM-LISTP
                            
                            VALID-SC)))))

(rp::add-meta-rules
 sum-meta-formal-checks
 (list
  (make rp-meta-rule-rec
        :fnc 'resolve-b+-order
        :trig-fnc 'merge-b+
        :dont-rw t
        :valid-syntax t)))

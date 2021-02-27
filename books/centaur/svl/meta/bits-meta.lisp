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

(include-book "../bits-sbits")

(local
 (in-theory (enable bits-sbits-no-syntaxp)))

(local
 (in-theory (disable 4vec-zero-ext-is-bits)))

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))
(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(define is-sbits (term)
  :progn t
  :inline t
  (case-match term
    (('sbits ('quote s-start) ('quote s-size) & &)
     (and (natp s-start)
          (natp s-size))))
  ///
  (local
   (defthm is-sbits-implies-fc
     (implies (is-sbits term)
              (case-match term
                (('sbits ('quote s-start) ('quote s-size) & &)
                 (and (natp s-start)
                      (integerp s-start)
                      (acl2-numberp s-start)
                      (natp s-size)
                      (integerp s-size)
                      (acl2-numberp s-size)))))
     :rule-classes :forward-chaining)))

(define is-4vec-rsh (term)
  :progn t
  :inline t
  (case-match term
    (('4vec-rsh ('quote size) &) (natp size)))
  ///
  (local
   (defthm is-4vec-rsh-implies-fc
     (implies (is-4vec-rsh term)
              (case-match term
                (('4vec-rsh ('quote size) &)
                 (and (natp size)
                      (integerp size)
                      (acl2-numberp size)))))
     :rule-classes :forward-chaining)))

(define is-4vec-concat$ (term)
  :progn t
  :inline t
  (case-match term
    (('4vec-concat$ ('quote size) & &) (natp size)))
  ///
  (local
   (defthm is-4vec-concat$-implies-fc
     (implies (is-4vec-concat$ term)
              (case-match term
                (('4vec-concat$ ('quote size) & &)
                 (and (natp size)
                      (integerp size)
                      (acl2-numberp size)))))
     :rule-classes :forward-chaining)))

(define is-4vec-bitnot (term)
  :progn t
  :inline t
  (case-match term
    (('sv::4vec-bitnot &) t))
  ///
  (local
   (defthm is-4vec-bitnot-implies-fc
     (implies (is-4vec-bitnot term)
              (case-match term
                (('sv::4vec-bitnot &) t)))
     :rule-classes :forward-chaining)))

(define is-bits (term)
  :progn t
  :inline t
  (case-match term
    (('bits & ('quote start) ('quote size)) (and (natp start)
                                                 (natp size))))
  ///
  (local
   (defthm is-bits-implies-fc
     (implies (is-bits term)
              (case-match term
                (('bits & ('quote start) ('quote size))
                 (and (natp start)
                      (integerp start)
                      (acl2-numberp start)
                      (natp size)
                      (integerp size)
                      (acl2-numberp size)))))
     :rule-classes :forward-chaining)))

(define has-bitp-side-cond (term)
  :prepwork ((local
              (in-theory (e/d (rp::is-rp) ()))))
  (and (rp::is-rp term)
       (or (equal (cadr term) ''bitp)
           (has-bitp-side-cond (caddr term)))))

(define is-bits-0-pos-size-of-a-bitp (orig-term start size)
  :progn t
  :inline t
  (and (has-bitp-side-cond orig-term)
       (equal start 0)
       (posp size))
  ///
  (local
   (defthm is-bits-0-1-of-a-bitp-implies
     (implies (is-bits-0-pos-size-of-a-bitp orig-term start size)
              (and (has-bitp-side-cond orig-term)
                   (equal start 0)
                   (posp size)))
     :rule-classes :forward-chaining)))

(define is-bits-pos-start-of-a-bitp (orig-term start size)
  :progn t
  :inline t
  (and (has-bitp-side-cond orig-term)
       (posp start)
       (natp size))
  ///
  (local
   (defthm is-bits-pos-start-of-a-bitp-implies
     (implies (is-bits-pos-start-of-a-bitp orig-term start size)
              (and (has-bitp-side-cond orig-term)
                   (posp start)
                   (natp size)))
     :rule-classes :forward-chaining)))

(define is-bitand/or/xor (term)
  :progn t
  :inline t
  (case-match term
    (('4vec-bitand & &)
     t)
    (('4vec-bitor & &)
     t)
    (('sv::4vec-bitxor & &)
     t)
    (& nil))
  ///
  (local
   (defthm is-bitand/or/xor-implies-fc
     (implies (is-bitand/or/xor term)
              (and (consp term)
                   (CONSP (CDR TERM))
                   (CONSP (CDDR TERM))
                   (EQ (CDDDR TERM) NIL)
                   (not (quotep term))
                   (not (EQ (CAR TERM) 'quote))
                   (not (EQ (CAR TERM) 'if))
                   (not (EQ (CAR TERM) 'rp))
                   (or (EQ (CAR TERM) '4VEC-BITAND)
                       (EQ (CAR TERM) '4VEC-BITOR)
                       (EQ (CAR TERM) 'SV::4VEC-BITXOR))))
     :rule-classes :forward-chaining)))

(define bits-meta-fn-aux (term (start natp) (size natp))
  :measure (rp::cons-count term)
  :hints (("Goal"
           :in-theory (e/d (rp::measure-lemmas)
                           (rp::ex-from-rp))))
  :prepwork ((local
              (defthm lemma1
                (implies (is-bits (rp::ex-from-rp term))
                         (o< 1 (cons-count term)))
                :hints (("goal"
                         :in-theory (e/d (is-bits cons-count) ())))))
             (local
              (defthm lemma2
                (implies (is-sbits (rp::ex-from-rp term))
                         (o< (cons-count (car (cddddr (rp::ex-from-rp term))))
                             (cons-count term)))
                :hints (("goal"
                         :in-theory (e/d (is-bits cons-count) ())))))

             (local
              (defthm lemma3
                (implies (is-sbits (rp::ex-from-rp term))
                         (o< (cons-count (cadddr (rp::ex-from-rp term)))
                             (cons-count term)))
                :hints (("goal"
                         :in-theory (e/d (is-bits cons-count) ())))))
             (local
              (defthm integerp-implies-rationalp
                (implies (integerp x)
                         (rationalp x))))

             (local
              (in-theory (disable rp::ex-from-rp
                                  (:rewrite acl2::apply$-badgep-properties . 1)
                                  (:definition acl2::apply$-badgep)
                                  (:rewrite integerp-implies-rationalp)
                                  (:rewrite rationalp-implies-acl2-numberp)
                                  (:rewrite default-+-2)
                                  (:definition subsetp-equal)
                                  (:definition member-equal)
                                  (:rewrite
                                   acl2::member-equal-newvar-components-1)))))
  (b* ((orig-term term)
       (term (rp::ex-from-rp term)))
    (cond ((is-sbits term)
           (b* ((s-start (cadr (cadr term)))
                (s-size (cadr (caddr term)))
                (val (cadddr term))
                (old-val (caddr (cddr term))))
             (cond
              ((or (<= (+ start size) s-start) ;;case5
                   (<= (+ s-start s-size) start))
               (bits-meta-fn-aux old-val start size))
              ((and (<= (+ start size) ;;case4
                        (+ s-start s-size))
                    (<= s-start start))
               (bits-meta-fn-aux val (- start s-start) size))
              ((and (< start s-start) ;;case 3
                    (< s-start (+ start size))
                    (<= (+ start size)
                        (+ s-start s-size)))
               (b* (((mv rest-term rest-dontrw)
                     (bits-meta-fn-aux old-val start (- s-start start)))
                    ((mv rest-term2 rest-dontrw2)
                     (bits-meta-fn-aux val 0 (+ start size (- s-start)))))
                 (mv `(4vec-concat$ ',(- s-start start)
                                    ,rest-term
                                    ,rest-term2)
                     `(nil t
                           ,rest-dontrw
                           ,rest-dontrw2))))
              ((and (<= s-start start) ;;case 2
                    (< start (+ s-start s-size))
                    (< (+ s-start s-size)
                       (+ start size)))
               (b* (((mv rest-term rest-dontrw)
                     (bits-meta-fn-aux val
                                       (- start s-start)
                                       (+ s-size s-start (- start))))
                    ((mv rest-term2 rest-dontrw2)
                     (bits-meta-fn-aux old-val
                                       (+ s-start s-size)
                                       (+ size start (- (+ s-start s-size))))))
                 (mv `(4vec-concat$
                       ',(+ s-size s-start (- start))
                       ,rest-term
                       ,rest-term2)
                     `(nil
                       t
                       ,rest-dontrw
                       ,rest-dontrw2))))
              ((and (< start s-start) ;;case 1
                    (< (+ s-start s-size)
                       (+ start size)))
               (b* (((mv rest-term2 rest-dont-rw2)
                     (bits-meta-fn-aux old-val start (- s-start start)))
                    ((mv rest-term3 rest-dont-rw3)
                     (bits-meta-fn-aux val 0 s-size))
                    ((mv rest-term4 rest-dont-rw4)
                     (bits-meta-fn-aux old-val
                                       (+ s-start s-size)
                                       (- (+ start size) (+ s-start s-size)))))
                 (mv `(4vec-concat$ ',(- s-start start)
                                    ,rest-term2
                                    (4vec-concat$ ',s-size ,rest-term3 ,rest-term4))
                     `(nil t
                           ,rest-dont-rw2
                           (nil t ,rest-dont-rw3 ,rest-dont-rw4)))))
              (t
               (progn$
                (cw "unexpected instance of bits of sbits ~%")
                (hard-error 'bits-meta-fn-aux "error" nil)
                (mv `(bits ,term ',start ',size) nil))))))
          ((is-4vec-rsh term)
           (b* ((rsh-size (cadr (cadr term)))
                (val (caddr term)))
             (bits-meta-fn-aux val (+ start rsh-size) size)))
          ((is-4vec-concat$ term)
           (b* ((c-size (cadr (cadr term)))
                (term1 (caddr term))
                (term2 (cadddr term)))
             (cond
              ((<= c-size start) ;;case 2
               (bits-meta-fn-aux term2 (- start c-size) size))
              ((and (< start c-size) ;; case 3
                    (< c-size (+ start size)))
               (b* (((mv rest-term1 rest-dontrw1)
                     (bits-meta-fn-aux term1 start (- c-size start)))
                    ((mv rest-term2 rest-dontrw2)
                     (bits-meta-fn-aux term2 0 (- size (- c-size start)))))
                 (mv `(4vec-concat$ ',(- c-size start)
                                    ,rest-term1
                                    ,rest-term2)
                     `(nil t
                           ,rest-dontrw1
                           ,rest-dontrw2))))
              ((<= (+ start size) c-size)
               (bits-meta-fn-aux term1 start size))
              (t
               (progn$
                (cw "unexpected instance of bits of 4vec-concat$ ~%")
                (hard-error 'bits-meta-fn-aux "error" nil)
                (mv `(bits ,term ',start ',size) nil))))))
          ((is-4vec-bitnot term)
           (b* ((x (cadr term))
                ((mv rest rest-dontrw)
                 (bits-meta-fn-aux x start size)))
             (mv `(4vec-bitnot$ ',size ,rest)
                 `(nil t ,rest-dontrw))))
          ((is-bits term)
           (b* ((x (cadr term))
                (start1 start)
                (size1 size)
                (start2 (cadr (caddr term)))
                (size2 (cadr (cadddr term))))
             (cond
              ((< start1 size2)
               (bits-meta-fn-aux x
                                 (+ start1 start2)
                                 (min size1 (- size2 start1))))
              (t (mv ''0 t)))))
          ((is-bitand/or/xor term)
           (b* ((fnc (car term))
                (term1 (cadr term))
                (term2 (caddr term))
                ((mv rest1 dont-rw1)
                 (bits-meta-fn-aux term1 start size))
                ((mv rest2 dont-rw2)
                 (bits-meta-fn-aux term2 start size)))
             (mv (cons-with-hint fnc
                                 (cons-with-hint rest1
                                                 (cons-with-hint rest2 nil (cddr
                                                                            term))
                                                 (cdr term))
                                 term)
                 `(nil ,dont-rw1 ,dont-rw2))))
          ((is-bits-0-pos-size-of-a-bitp orig-term start size)
           (mv orig-term t))
          ((is-bits-pos-start-of-a-bitp orig-term start size)
           (mv ''0 t))
          (t
           (mv `(bits ,orig-term ',start ',size)
               `(nil t t t))))))

(define bits-meta-fn-aux-can-change (val start size)
  :inline t
  (or (is-bits-0-pos-size-of-a-bitp val start size)
      (is-bits-pos-start-of-a-bitp val start size)
      (b* ((val (rp::ex-from-rp val)))
        (or (is-bitand/or/xor val)
            (is-bits val)
            (is-4vec-bitnot val)
            (is-4vec-concat$ val)
            (is-4vec-rsh val)
            (is-sbits val)))))

(define bits-of-meta-fn (term)
  (case-match term
    (('bits val ('quote start) ('quote size))
     (cond ((and (natp start)
                 (natp size)
                 (bits-meta-fn-aux-can-change val start size))
            (bits-meta-fn-aux val start size))
           (t (mv term nil))))
    (('sv::4vec-part-select ('quote start) ('quote size) val)
     (cond ((and (natp start)
                 (natp size)
                 (bits-meta-fn-aux-can-change val start size))
            (bits-meta-fn-aux val start size))
           (t (mv `(bits ,val ,(cadr term) ,(caddr term)) `(nil t t t)))))
    (& (mv term nil))))

(define concat$-meta-aux ((size natp)
                          term1
                          term2
                          (limit natp))
  :measure (nfix limit)
  (b* ((term1-orig term1)
       (term1 (rp::ex-from-rp term1)))
    (cond
     ((zp limit)
      (mv `(4vec-concat$ ',size ,term1 ,term2)
          `(nil t t t)))
     ((is-4vec-concat$ term1)
      (b* ((c-size (cadr (cadr term1)))
           (c-term1 (caddr term1))
           (c-term2 (cadddr term1)))
        (cond
         ((<= size c-size)
          (concat$-meta-aux size c-term1 term2 (1- limit)))
         (t
          (b* (((mv rest rest-dontrw)
                (concat$-meta-aux (- size c-size)
                                  c-term2 term2
                                  (1- limit))))

            (mv `(4vec-concat$ ',c-size ,c-term1 ,rest)
                `(nil t t ,rest-dontrw)))))))
     (t
      (mv `(4vec-concat$ ',size ,term1-orig ,term2)
          `(nil t t t))))))

(define concat-meta (term)
  (case-match term
    (('4vec-concat ('quote size) term1 &)
     (if (natp size)
         (b* (((mv term1 dont-rw)
               (bits-meta-fn-aux term1 0 size)))
           (mv `(4vec-concat$ ,(cadr term) ,term1 . ,(cdddr term))
               `(nil t ,dont-rw t)))
       (mv term nil)))
    (('4vec-concat$ ('quote size) term1 term2)
     (b* ((term1-orig term1)
          (term1 (rp::ex-from-rp term1)))
       (if (and (natp size)
                (is-4vec-concat$ term1))
           (concat$-meta-aux size term1-orig term2 (expt 2 30))
         (mv term nil))))
    (& (mv term nil))))

(rp::def-formula-checks-default-evl
 rp::rp-evl
 (strip-cars rp::*small-evl-fncs*))

(encapsulate
  nil

  (local
   (in-theory (disable 4VEC-ZERO-EXT-IS-4VEC-CONCAT)))

  (with-output
    :off :all
    :gag-mode nil
    (rp::def-formula-checks bits-of-formula-checks
                            (bits sbits
                                  4vec-concat
                                  4vec-rsh
                                  sv::4vec-bitxor
                                  sv::4vec-bitand
                                  sv::4vec-bitor
                                  4vec-concat$
                                  4vec-bitnot$
                                  4vec-bitnot
                                  4vec-part-select
                                  sv::4vec-fix$inline
                                  bitp
                                  ;;concat-meta
                                  ;;bits-of-meta-fn
                                  ))))

#|(local
 (defthm rp-trans-when-quotep
   (implies (quotep x)
            (equal (rp-trans x)
                   x))))||#

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; rp-termp lemmas

(local
 (in-theory (enable 4vec-part-select-is-bits)))

(progn
  (local
   (defthm
     rp::rp-termp-caddddr
     (implies (and (rp::rp-termp rp::term)
                   (consp rp::term)
                   (not (quotep rp::term))
                   (consp (cdr rp::term))
                   (consp (cddr rp::term))
                   (consp (cdddr rp::term))
                   (consp (cdr (cdddr rp::term))))
              (rp::rp-termp (car (cddddr rp::term))))
     :hints
     (("goal"
       :in-theory
       (e/d (rp::rp-termp rp::is-rp
                          rp::ex-from-rp-loose rp::is-rp-loose)
            nil)))))

  (local
   (defthm rp-termp-concat$-meta-aux
     (implies (and (rp::rp-termp term1)
                   (natp size)
                   (rp::rp-termp term2))
              (rp::rp-termp (mv-nth 0 (concat$-meta-aux size term1 term2 limit))))
     :hints (("Goal"
              :induct (concat$-meta-aux size term1 term2 limit)
              :do-not-induct t
              :in-theory (e/d (concat$-meta-aux
                               natp) ())))))

  (local
   (defthm rp-termp-bits-meta-fn-aux
     (implies (and (natp size)
                   (natp start)
                   (rp::rp-termp term))
              (rp::rp-termp (mv-nth 0 (bits-meta-fn-aux term start size))))
     :hints (("Goal"
              :induct (bits-meta-fn-aux term start size)
              :do-not-induct t
              :in-theory (e/d (bits-meta-fn-aux
                               is-bits-0-pos-size-of-a-bitp
                               is-bits-pos-start-of-a-bitp
                               natp)
                              (rp::falist-consistent))))))

  (local
   (defthm rp-termp-of-bits-of-meta-fn
     (implies (rp::rp-termp term)
              (rp::rp-termp (mv-nth 0 (bits-of-meta-fn term))))
     :hints (("Goal"
              :in-theory (e/d (bits-of-meta-fn) ())))))

  (local
   (defthm rp-termp-of-concat-meta
     (implies (rp::rp-termp term)
              (rp::rp-termp (mv-nth 0 (concat-meta term))))
     :hints (("Goal"
              :in-theory (e/d (concat-meta) ()))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; valid-sc lemmas

(local
 (defthm
   rp::valid-sc-caddddr
   (implies (and (consp rp::term)
                 (not (equal (car rp::term) 'if))
                 (not (equal (car rp::term) 'rp))
                 (not (equal (car rp::term) 'quote))
                 (consp (cdr rp::term))
                 (consp (cddr rp::term))
                 (consp (cdddr rp::term))
                 (consp (cddddr rp::term))
                 (rp::valid-sc rp::term rp::a))
            (rp::valid-sc (car (cddddr rp::term)) rp::a))
   :hints
   (("goal" :in-theory (e/d (rp::ex-from-rp rp::is-if rp::is-rp)
                            nil)))))

(local
 (defthm valid-sc-concat$-meta-aux
   (implies (and (rp::valid-sc term1 a)
                 (natp size)
                 (rp::valid-sc term2 a))
            (rp::valid-sc (mv-nth 0 (concat$-meta-aux size term1 term2 limit)) a))
   :hints (("Goal"
            :induct (concat$-meta-aux size term1 term2 limit)
            :do-not-induct t
            :in-theory (e/d (concat$-meta-aux
                             rp::is-rp rp::is-if
                             natp) ())))))

(local
 (defthm valid-sc-bits-meta-fn-aux
   (implies (and (natp size)
                 (natp start)
                 (rp::valid-sc term a))
            (rp::valid-sc (mv-nth 0 (bits-meta-fn-aux term start size)) a))
   :hints (("goal"
            :induct (bits-meta-fn-aux term start size)
            :do-not-induct t
            :in-theory (e/d (bits-meta-fn-aux
                             is-bits-0-pos-size-of-a-bitp
                             is-bits-pos-start-of-a-bitp
                             rp::is-rp rp::is-if
                             natp)
                            (rp::falist-consistent
                             ifix
                             (:definition rp::ex-from-rp)
                             (:rewrite default-car)
                             (:rewrite default-cdr)))))))

(local
 (defthm valid-sc-of-bits-of-meta-fn
   (implies (rp::valid-sc term a)
            (rp::valid-sc (mv-nth 0 (bits-of-meta-fn term)) a))
   :hints (("Goal"
            :in-theory (e/d (bits-of-meta-fn rp::is-rp rp::is-if) ())))))

(local
 (defthm valid-sc-of-concat-meta
   (implies (rp::valid-sc term a)
            (rp::valid-sc (mv-nth 0 (concat-meta term)) a))
   :hints (("Goal"
            :in-theory (e/d (concat-meta rp::is-if rp::is-rp) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; dont-rw sytnaxp lemmas

(local
 (defthm dont-rw-syntaxp-concat$-meta-aux
   (implies t
            (rp::dont-rw-syntaxp (mv-nth 1 (concat$-meta-aux size term1 term2 limit))))
   :hints (("Goal"
            :induct (concat$-meta-aux size term1 term2 limit)
            :do-not-induct t
            :in-theory (e/d (concat$-meta-aux
                             natp) ())))))

(local
 (defthm dont-rw-syntaxp-bits-meta-fn-aux
   (implies t
            (rp::dont-rw-syntaxp (mv-nth 1 (bits-meta-fn-aux term start size))))
   :hints (("Goal"
            :induct (bits-meta-fn-aux term start size)
            :do-not-induct t
            :in-theory (e/d (bits-meta-fn-aux
                             is-bits-0-pos-size-of-a-bitp
                             is-bits-pos-start-of-a-bitp
                             natp)
                            (rp::falist-consistent))))))

(local
 (defthm dont-rw-syntaxp-of-bits-of-meta-fn
   (implies t
            (rp::dont-rw-syntaxp (mv-nth 1 (bits-of-meta-fn term))))
   :hints (("Goal"
            :in-theory (e/d (bits-of-meta-fn) ())))))

(local
 (defthm dont-rw-syntaxp-of-concat-meta
   (implies t
            (rp::dont-rw-syntaxp (mv-nth 1 (concat-meta term))))
   :hints (("Goal"
            :in-theory (e/d (concat-meta) ())))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;; rp-evlt lemmas

(local
 (defthmd rp-evlt-of-ex-from-rp-reverse
   (implies (and (syntaxp (or (equal x 'term)
                              (equal x 'term1)
                              (equal x 'term2))))
            (equal (rp::rp-evlt x a)
                   (rp::rp-evlt (rp::ex-from-rp x) a)))))

(local
 (defthm 4vec-concat-is-4vec-concat$
   (equal (4vec-concat size term1 term2)
          (4vec-concat$ size term1 term2))
   :hints (("Goal"
            :in-theory (e/d (4vec-concat$) ())))))

(local
 (progn
   (rp::create-regular-eval-lemma 4VEC-CONCAT$ 3  bits-of-formula-checks)
   (rp::create-regular-eval-lemma bits 3  bits-of-formula-checks)
   (rp::create-regular-eval-lemma 4VEC-BITAND 2 bits-of-formula-checks)
   (rp::create-regular-eval-lemma 4VEC-BITor 2 bits-of-formula-checks)
   (rp::create-regular-eval-lemma 4VEC-BITnot$ 2 bits-of-formula-checks)
   (rp::create-regular-eval-lemma 4VEC-BITnot 1 bits-of-formula-checks)
   (rp::create-regular-eval-lemma sv::4VEC-BITxor 2 bits-of-formula-checks)
   (rp::create-regular-eval-lemma 4vec-rsh 2 bits-of-formula-checks)
   (rp::create-regular-eval-lemma sbits 4 bits-of-formula-checks)))

(local
 (defthm concat$-meta-aux-correct
   (implies
    (and (rp-evl-meta-extract-global-facts)
         (natp size)
         (bits-of-formula-checks state))
    (equal (rp-evlt (mv-nth 0 (concat$-meta-aux size term1 term2 limit)) a)
           (rp-evlt `(4vec-concat$ ',size ,term1 ,term2) a)))
   :hints (("Goal"
            :induct (concat$-meta-aux size term1 term2 limit)
            :do-not-induct t
            :in-theory (e/d* (concat$-meta-aux
                              (:REWRITE
                               RP::REGULAR-RP-EVL-OF_4VEC-CONCAT$_WHEN_BITS-OF-FORMULA-CHECKS_WITH-EX-FROM-RP)
                              rp::is-rp rp::is-if
                              rp-evlt-of-ex-from-rp-reverse
                              natp)
                             (RP::RP-EVLT-OF-EX-FROM-RP
                              rp-trans))))))



(local
 (defthm HAS-BITP-SIDE-COND-lemma
  (implies (and (rp-evl-meta-extract-global-facts)
                (rp::valid-sc term a)
                (HAS-BITP-SIDE-COND TERM))
           (and (bitp (rp-evlt term a))
                ;;(bitp (rp-evl term a))
                ))
  :hints (("Goal"
           :induct (HAS-BITP-SIDE-COND TERM)
           :do-not-induct t
           :in-theory (e/d (HAS-BITP-SIDE-COND
                            rp::is-if
                            RP::VALID-SC-SINGLE-STEP
                            rp::is-rp
                            RP::VALID-SC
                            )
                           (bitp))))))

(local
 (defthm bits-meta-fn-aux-correct-lemma1
   (implies
    (and (rp-evl-meta-extract-global-facts)
         (rp::valid-sc term a)
         (is-bits-0-pos-size-of-a-bitp TERM START SIZE)
         (bits-of-formula-checks state))
    (equal (BITS (RP-EVL (RP-TRANS (RP::EX-FROM-RP TERM))
                         A)
                 start size)
           (RP-EVL (RP-TRANS (RP::EX-FROM-RP TERM))
                   A)))
   :hints (("Goal"
            :in-theory (e/d (rp::valid-sc-single-step
                             RP::IS-RP
                             is-bits-0-pos-size-of-a-bitp)
                            (rp::valid-sc))))))



(local
 (defthm bits-meta-fn-aux-correct-lemma2
   (implies
    (and (rp-evl-meta-extract-global-facts)
         (rp::valid-sc term a)
         (is-bits-pos-start-of-a-bitp TERM START SIZE)
         (bits-of-formula-checks state))
    (equal (BITS (RP-EVL (RP-TRANS (RP::EX-FROM-RP TERM))
                         A)
                 start size)
           0))
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance HAS-BITP-SIDE-COND-lemma))
            :in-theory (e/d (rp::valid-sc-single-step
                             RP::IS-RP
                             is-bits-pos-start-of-a-bitp)
                            (rp::valid-sc
                             HAS-BITP-SIDE-COND-lemma))))))

(local
 (defthm rp-evlt-of-quoted
   (equal (RP-EVL (RP-TRANS (LIST 'QUOTE START))
                  A)
          start)))

(local
 (defthm rp-trans-when-quotep
   (implies (quotep x)
            (equal (rp-trans x)
                   x))))

(local
 (defthm dummy-lemma1
   (implies (is-bits-0-pos-size-of-a-bitp TERM START SIZE)
            (is-bits-0-pos-size-of-a-bitp TERM 0 1))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (is-bits-0-pos-size-of-a-bitp) ())))))

(local
 (defthm bits-meta-fn-aux-correct
   (implies
    (and (rp-evl-meta-extract-global-facts)
         (natp size)
         (natp start)
         (rp::valid-sc term a)
         (bits-of-formula-checks state))
    (equal (rp-evlt (mv-nth 0 (bits-meta-fn-aux term start size)) a)
           (rp-evlt `(bits ,term ',start ',size) a)))
;:otf-flg t
   :hints (("Subgoal *1/10"
            :use ((:instance bits-meta-fn-aux-correct-lemma1)))
           ("Goal"
            :induct (bits-meta-fn-aux term start size)
            :do-not-induct t
            :do-not '(preprocess)
            :expand ((:free (x) (nth 3 x))
                     (:free (x) (nth 2 x))
                     (:free (x) (nth 1 x))
                     (:free (x) (nth 0 x)))
            :in-theory (e/d* (bits-meta-fn-aux
                              IS-BITAND/OR/XOR
                              rp::is-rp rp::is-if
                              rp::regular-eval-lemmas
                              rp-evlt-of-ex-from-rp-reverse
                              natp)
                             (RP::RP-EVLT-OF-EX-FROM-RP
                              rp-trans
                              NTH-ADD1
                              RP::EX-FROM-RP
                              FIX
                              RP::INCLUDE-FNC
                              RP::INCLUDE-FNC-SUBTERMS
                              NTH-0-CONS))))))

(local
 (defthm bits-of-meta-fn-correct
   (implies (and (rp::valid-sc term a)
                 (rp-evl-meta-extract-global-facts)
                 (bits-of-formula-checks state))
            (equal (rp-evlt (mv-nth 0 (bits-of-meta-fn term)) a)
                   (rp-evlt term a)))
   :hints (("Goal"
            :in-theory (e/d (bits-of-meta-fn) ())))))

(local
 (defthm convert-4vec-concat-to-4vec-concat$-reverse
   (equal (4vec-concat$ size (bits term1 0 size )
                        term2)
          (4vec-concat size term1 term2))
   :hints (("Goal"
            :use ((:instance convert-4vec-concat-to-4vec-concat$))
            :in-theory (e/d () ())))))

(local
 (defthm concat-meta-correct
   (implies (and (rp::valid-sc term a)
                 (rp-evl-meta-extract-global-facts)
                 (bits-of-formula-checks state))
            (equal (rp-evlt (mv-nth 0 (concat-meta term)) a)
                   (rp-evlt term a)))
   :hints (("Goal"
            :expand ((RP-TRANS-LST (CDDDR TERM))
                     (RP-TRANS-LST (CDDR TERM))
                     (RP-TRANS-LST (CDR TERM))
                     (:free (x) (nth 3 x))
                     (:free (x) (nth 2 x))
                     (:free (x) (nth 1 x))
                     (:free (x) (nth 0 x)))
            :in-theory (e/d (concat-meta)
                            (rp::ex-from-rp
                             natp))))))

#|(defthm valid-rp-meta-rulep-concat-meta-1
  (implies (and (rp-evl-meta-extract-global-facts)
                (bits-of-formula-checks state))
           (let ((rule (make rp::rp-meta-rule-rec
                             :fnc 'concat-meta
                             :trig-fnc 'sv::4vec-concat
                             :dont-rw t
                             :valid-syntax t)))
             (and (rp::rp-meta-valid-syntaxp-sk rule state)
                  (rp::valid-rp-meta-rulep rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp::RP-META-VALID-SYNTAXP)
                           (rp::RP-TERMP
                            rp::VALID-SC)))))||#

#|(defthm valid-rp-meta-rulep-concat-meta-2
  (implies (and (rp-evl-meta-extract-global-facts)
                (bits-of-formula-checks state))
           (let ((rule (make rp::rp-meta-rule-rec
                             :fnc 'concat-meta
                             :trig-fnc '4vec-concat$
                             :dont-rw t
                             :valid-syntax t)))
             (and (rp::rp-meta-valid-syntaxp-sk rule state)
                  (rp::valid-rp-meta-rulep rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp::RP-META-VALID-SYNTAXP)
                           (rp::RP-TERMP
                            rp::VALID-SC)))))||#

#|(defthm valid-rp-meta-rulep-bits-of-meta-fn-1
  (implies (and (rp-evl-meta-extract-global-facts)
                (bits-of-formula-checks state))
           (let ((rule (make rp::rp-meta-rule-rec
                             :fnc 'bits-of-meta-fn
                             :trig-fnc 'bits
                             :dont-rw t
                             :valid-syntax t)))
             (and (rp::rp-meta-valid-syntaxp-sk rule state)
                  (rp::valid-rp-meta-rulep rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp::rp-meta-valid-syntaxp)
                           (rp::rp-termp
                            rp::valid-sc)))))||#

#|(defthm valid-rp-meta-rulep-bits-of-meta-fn-2
  (implies (and (rp-evl-meta-extract-global-facts)
                (bits-of-formula-checks state))
           (let ((rule (make rp::rp-meta-rule-rec
                             :fnc 'bits-of-meta-fn
                             :trig-fnc 'sv::4vec-part-select
                             :dont-rw t
                             :valid-syntax t)))
             (and (rp::rp-meta-valid-syntaxp-sk rule state)
                  (rp::valid-rp-meta-rulep rule state))))
  :otf-flg t
  :hints (("Goal"
           :in-theory (e/d (rp::rp-meta-valid-syntaxp)
                           (rp::rp-termp
                            rp::valid-sc)))))||#

#|(rp::add-meta-rules bits-of-formula-checks
                    (list (make rp::rp-meta-rule-rec
                                :fnc 'bits-of-meta-fn
                                :trig-fnc 'sv::4vec-part-select
                                :dont-rw t
                                :valid-syntax t)
                          (make rp::rp-meta-rule-rec
                                :fnc 'bits-of-meta-fn
                                :trig-fnc 'bits
                                :dont-rw t
                                :valid-syntax t)
                          (make rp::rp-meta-rule-rec
                                :fnc 'concat-meta
                                :trig-fnc '4vec-concat$
                                :dont-rw t
                                :valid-syntax t)
                          (make rp::rp-meta-rule-rec
                                :fnc 'concat-meta
                                :trig-fnc 'sv::4vec-concat
                                :dont-rw t
                                :valid-syntax t)))||#


(rp::add-meta-rule
 :meta-fnc bits-of-meta-fn
 :trig-fnc sv::4vec-part-select
 :formula-checks bits-of-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc bits-of-meta-fn
 :trig-fnc bits
 :formula-checks bits-of-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc concat-meta
 :trig-fnc 4vec-concat$
 :formula-checks bits-of-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw))

(rp::add-meta-rule
 :meta-fnc concat-meta
 :trig-fnc sv::4vec-concat
 :formula-checks bits-of-formula-checks
 :valid-syntaxp t
 :returns (mv term dont-rw))

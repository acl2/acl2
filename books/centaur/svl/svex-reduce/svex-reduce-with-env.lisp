; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
; Copyright (C) 2022 Intel Corporation
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
; Original author: Mertcan Temel <mert@centtech.com>

(in-package "SVL")

(include-book "base")

(include-book "projects/rp-rewriter/top" :dir :system)

(include-book "../fnc-defs")

(include-book "svex-reduce-apply")
(include-book "simplify-bitand-or-xor")
(include-book "simplify-dont-care-branch")

(local
 (include-book "../4vec-lemmas"))

(local
 (include-book "../bits-sbits"))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/logops-lemmas" :dir :system)
  use-ihs-logops-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arithmetic-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "ihs/quotient-remainder-lemmas" :dir :system)
  use-qr-lemmas
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/equal-by-logbitp" :dir :system)
  use-equal-by-logbitp
  :disabled t))

(local
 (defthm sv::4vec->upper-and-lower-equivalance
   (implies (integerp x)
            (equal (sv::4vec->lower x)
                   (sv::4vec->upper x)))
   :hints (("goal"
            :in-theory (e/d (sv::4vec->upper
                             sv::4vec->lower
                             ) ())))))

(local
 (defthm svex-p-of-consed
   (implies (and (not (equal fn ':var))
                 (not (integerp fn)))
            (equal (svex-p (cons fn args))
                   (and (FNSYM-P fn)
                        (SVEXLIST-P args))))
   :hints (("Goal"
            :in-theory (e/d (svex-p) ())))))
(local
 (defthm natp-implies-svex-p
   (implies (natp x)
            (svex-p x))
   :rule-classes :type-prescription
   :hints (("Goal"
            :in-theory (e/d (svex-p) ())))))

(local
 (defthm 4vec-p-implies-svex-p
   (implies (4vec-p x)
            (svex-p x))
   :rule-classes :type-prescription
   :hints (("Goal"
            :in-theory (e/d (svex-p
                             4vec-p)
                            ())))))

(local
 (defthm svex-p-of-fn-call-reconstructed
   (implies (AND (FNSYM-P FN)
                 (SVEXLIST-P ARGS))
            (SVEX-P (CONS FN ARGS)))
   :hints (("Goal"
            :in-theory (e/d (SVEX-P) ())))))

;; add 4vec-?*
;; saw one that went (4vec-? (1 . 0) x y)
;; saw one sv::4vec-parity
;; (SVL::4VEC-BITNOT$
;; '1
;; (SVL::4VEC-BITNOT$
;;  '1
;;  (SVL::BITS
;;    (SV::4VEC-REDUCTION-OR
;;         (SV::4VEC-? '(1 . 0)
;;                     (SV::4VEC-BIT?! '255
;;                                     (SVL::BITS (ACL2::RP 'INTEGERP OP1)
;;                                                '23
;;                                                '8)
;;                                     '(255 . 0))
;;                     '(255 . 0)))
;;    '0
;;    '1)))

;; (SV::4VEC-? '(1 . 0)
;;                                           (SVL::BITS (ACL2::RP 'INTEGERP OP2)
;;                                                      '5
;;                                                      '2)
;;                                           '(3 . 0))

;; (SV::4VEC-PARITY
;;   (SVL::4VEC-CONCAT$ '1
;;                      (SV::4VEC-BITOR (RP::BIT-OF (ACL2::RP 'INTEGERP OP2) '7)
;;                                      '(1 . 0))
;;                      (RP::BIT-OF (ACL2::RP 'INTEGERP OP2)
;;                                  '8)))

(defmacro svex-reduce-w/-env-masked-return (term)
  `(let* ((return-term ,term)) ;; keep it in case "term" is a function call.
     (if (4vec-p return-term)
         (4vec-part-select  start size return-term)
       (hons-list 'sv::partsel start size return-term))))

(local
 (defthm dummy-svex-p-of-call-lemma
   (implies (and (NOT (EQUAL (SVEX-KIND SVEX) :QUOTE))
                 (NOT (EQUAL (SVEX-KIND SVEX) :VAR))
                 (SVEX-P SVEX))
            (and (EQUAL (SVEX-KIND SVEX) :call)
                 (consp svex)
                 (SVEXLIST-P (CDR SVEX))
                 (fnsym-p (car svex))))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (SVEX-P
                             SVEX-KIND)
                            ())))))

(local
 (defthm svex-p-of-plus-lemma
   (implies (and (integerp x)
                 (integerp y))
            (svex-p (+ x y)))
   :hints (("Goal"
            :in-theory (e/d (svex-p)
                            ())))))

(local
 (defthm svexlist-p-of-cons
   (equal (svexlist-p (cons x y))
          (and (svex-p x)
               (svexlist-p y)))
   :hints (("Goal"
            :in-theory (e/d (svexlist-p) ())))))

(local
 (defthm svex-p-of-3vec-fix
   (svex-p (sv::3vec-fix x))))

(define min-width (x y)
  (cond ((and (natp x)
              (natp y))
         (min x y))
        ((natp x)
         x)
        ((natp y)
         y)
        (t nil)))

(defmacro if*-exec (x y z)
  `(mbe :logic (if* ,x ,y ,z)
        :exec (if ,x ,y ,z)))

(defmacro and*-exec (&rest x)
  `(mbe :logic (and* ,@x)
        :exec (and ,@x)))


(local
 (defthmd 4vec-p-implies-svex-p-rw-rule
   (implies (sv::4vec-p x)
            (sv::svex-p x))))

(with-output
  :off :All
  :on (error summary)

  (defines svex-reduce-w/-env
    :flag-defthm-macro defthm-svex-reduce-with-env-meta
    :flag-local nil
    :hints (("Goal"
             :in-theory (e/d (svex-kind
                              sv::svex-call->fn
                              sv::svex-call->args
                              measure-lemmas) ())))
    :prepwork ((local
                (in-theory (enable 4vec-p-implies-svex-p-rw-rule
                                   svex-kind-wog))))

    (define svex-and/or/xor-reduce-w/-env-masked ((svex svex-p)
                                                  (start natp)
                                                  (size natp)
                                                  &key
                                                  ((env) 'env)
                                                  ((context rp::rp-term-listp) 'context)
                                                  ((config svex-reduce-config-p) 'config))
      :measure (acl2::nat-list-measure (list (cons-count svex)
                                             (nfix size)))
      :returns (res svex-p :hyp (and (natp start)
                                     (natp size)
                                     (svex-p svex)))
      (b* (((unless (equal (sv::svex-kind svex) :call))
            `(sv::partsel ,start ,size ,svex))
           ((mv fn args) (mv (car svex)
                             (cdr svex))))
        (cond
         ((zp size)
          0)
         ((not (and (or (equal fn 'sv::bitor)
                        (equal fn 'sv::bitand)
                        (equal fn 'sv::bitxor))
                    (equal-len args 2)))
          (svex-reduce-w/-env-apply 'sv::partsel (hons-list start size svex)))
         (t
          (b* ((term1 (svex-reduce-w/-env-masked (first args) start 1))
               (term2 (svex-reduce-w/-env-masked (second args) start 1))
               ;;(cur-term (bitand/or/xor-simple-constant-simplify fn term1 term2))
               (cur-term
                (if (acl2::or* (integerp term1)
                               (integerp term2))
                    (bitand/or/xor-simple-constant-simplify fn term1 term2 :1masked t)
                  (bitand/or/xor-cancel-repeated fn term1 term2
                                                 :nodes-to-skip-alist nil)))

               ((when (equal size 1))
                cur-term))
            (svex-reduce-w/-env-apply
             'sv::concat
             (hons-list 1
                        cur-term
                        (svex-and/or/xor-reduce-w/-env-masked svex
                                                              (1+ start)
                                                              (1- size)))))))))

    (define svex-reduce-w/-env-masked ((svex svex-p)
                                       (start natp)
                                       (size natp)
                                       &key
                                       ((env) 'env)
                                       ((context rp::rp-term-listp) 'context)
                                       ((config svex-reduce-config-p) 'config))
      :measure (acl2::nat-list-measure (list (cons-count svex)
                                             (1+ (nfix size))))
      :returns (res svex-p :hyp (and (natp start)
                                     (natp size)
                                     (svex-p svex)))
      :verify-guards nil
      (let* ((svex.kind (svex-kind svex)))
        (case  svex.kind
          (:quote (4vec-part-select start size svex))
          (:var
           (b* (;;(svex.name (svex-var->name svex))
                (val (hons-get svex env))
                ((unless (consp val))
                 (if (svex-reduce-config->keep-missing-env-vars config)
                     (svex-reduce-w/-env-masked-return svex)
                   (4vec-part-select start size (sv::4vec-x))))
                (val (cdr val))
                ((when (and (quotep val)
                            (consp (cdr val))
                            (4vec-p (unquote val))))
                 (4vec-part-select start size (unquote val)))
                (- (and (4vec-p val)
                        (acl2::raise "Constants are expected to be quoted in the
                                       given env. But given instead:~p0"
                                     (cons svex val)))))
             (svex-reduce-w/-env-masked-return svex)))
          (otherwise
           (b* ((fn (car svex))
                (args (cdr svex)))
             (cond
              ((and* (equal fn 'sv::partsel)
                     (equal-len args 3))
               (b* ((start2 (svex-reduce-w/-env (first args)))
                    (size2 (svex-reduce-w/-env (second args)))
                    ((unless (and (natp start2) (natp size2)))
                     (b* ((third (svex-reduce-w/-env (third args))))
                       (if (and (4vec-p start2) (4vec-p size2) (4vec-p third))
                           (4vec-part-select start size
                                             (4vec-part-select start2 size2 third))
                         (svex-reduce-w/-env-masked-return
                          (hons-list 'sv::partsel start2 size2 third))))))
                 (if (< start size2)
                     (svex-reduce-w/-env-masked (third args)
                                                (+ start start2)
                                                (min size (- size2 start)))
                   0)))
              ((and* (equal fn 'sv::zerox)
                     (equal-len args 2))
               (b* ((c-size (svex-reduce-w/-env (first args)))
                    (term1 (second args))
                    ((unless (natp c-size))
                     (b* ((term1 (svex-reduce-w/-env term1)))
                       (svex-reduce-w/-env-masked-return
                        (svex-reduce-w/-env-apply fn (hons-list c-size term1)))))
                    ((when (<= c-size start))
                     0)
                    ((when (and (< start c-size)
                                (< c-size (+ start size))))
                     (b* ((term1 (svex-reduce-w/-env-masked term1
                                                            start
                                                            (- c-size start))))
                       term1))
                    ((when (<= (+ start size) c-size))
                     (svex-reduce-w/-env-masked term1 start size)))
                 (svex-reduce-w/-env-apply fn ;; should never come here.
                                           (hons-list c-size
                                                      (svex-reduce-w/-env term1)))))
              ((and* (equal fn 'sv::signx)
                     (equal-len args 2))
               (b* ((s-size (svex-reduce-w/-env (first args)))
                    (term1 (second args))
                    ((unless (natp s-size))
                     (b* ((term1 (svex-reduce-w/-env term1)))
                       (svex-reduce-w/-env-masked-return
                        (svex-reduce-w/-env-apply fn (hons-list s-size
                                                                term1)))))
                    ((when (equal s-size 0))
                     (sv::4vec-part-select 0 size (sv::4vec-x)))
                    ((when (<= s-size start)) ;; only signextend bit repeated
                     (b* ((term1 (svex-reduce-w/-env-masked term1
                                                            (1- s-size)
                                                            1))
                          ((when (= size 1))
                           term1)
                          (start 0))
                       (svex-reduce-w/-env-masked-return
                        (svex-reduce-w/-env-apply fn (hons-list 1 term1)))))
                    ((when (and (< start s-size)
                                (< s-size (+ start size))))
                     (b* ((term1 (svex-reduce-w/-env-masked term1
                                                            start
                                                            (- s-size start)))
                          (new-s-size (- s-size start))
                          (start 0))
                       (svex-reduce-w/-env-masked-return
                        (svex-reduce-w/-env-apply fn (hons-list new-s-size term1)))))
                    ((when (<= (+ start size) s-size))
                     (svex-reduce-w/-env-masked term1 start size)))
                 (svex-reduce-w/-env-apply fn ;; should never come here.
                                           (hons-list s-size
                                                      (svex-reduce-w/-env term1)))))
              ((and* (equal fn 'sv::concat)
                     (equal-len args 3))
               (b* ((c-size (svex-reduce-w/-env (first args)))
                    (term1 (second args))
                    (term2 (third args))
                    ((unless (natp c-size))
                     (b* ((term1 (svex-reduce-w/-env term1))
                          (term2 (svex-reduce-w/-env term2)))
                       (if (and (4vec-p c-size) (4vec-p term1) (4vec-p term2))
                           (4vec-part-select start size
                                             (4vec-concat c-size term1 term2))
                         (svex-reduce-w/-env-masked-return
                          (svex-reduce-w/-env-apply fn (hons-list c-size term1 term2))))))
                    ((when (<= c-size start))
                     (svex-reduce-w/-env-masked term2
                                                (- start c-size)
                                                size))
                    ((when (<= (+ start size) c-size))
                     (svex-reduce-w/-env-masked term1 start size))
                    ((when (and (< start c-size)
                                (< c-size (+ start size))))
                     (b* ((term1 (svex-reduce-w/-env-masked term1
                                                            start
                                                            (- c-size start)))
                          (term2 (svex-reduce-w/-env-masked term2
                                                            0
                                                            (- size (- c-size start))))
                          ((when (equal term2 0)) term1)
                          (res
                           (svex-reduce-w/-env-apply fn
                                                     (hons-list (- c-size start)
                                                                term1 term2))))
                       res)))
                 (hons-list 'sv::concat c-size ;; should never come to this case
                            (svex-reduce-w/-env-masked term1 0 c-size )
                            (svex-reduce-w/-env term2))))
              ((and* (equal fn 'sv::lsh)
                     (equal-len args 2))
               (b* ((lsh-size (svex-reduce-w/-env (first args)))
                    (term (second args))
                    ((unless (natp lsh-size))
                     (b* ((term (svex-reduce-w/-env term)))
                       (svex-reduce-w/-env-masked-return
                        (svex-reduce-w/-env-apply fn (hons-list lsh-size
                                                                term)))))
                    ((when (>= start lsh-size))
                     (svex-reduce-w/-env-masked term
                                                (+ start (- lsh-size))
                                                size))
                    ((when (>= lsh-size (+ start size)))
                     0)
                    (term (svex-reduce-w/-env-masked term
                                                     0
                                                     (+ size (- (+ lsh-size (- start)))))))
                 (svex-reduce-w/-env-apply fn
                                           (hons-list (+ lsh-size (- start)) term))))
              ((and* (equal fn 'sv::rsh)
                     (equal-len args 2))
               (b* ((rsh-size (svex-reduce-w/-env (first args)))
                    (term (second args))
                    ((unless (natp rsh-size))
                     (b* ((term (svex-reduce-w/-env term)))
                       (if (and (4vec-p rsh-size) (4vec-p term))
                           (4vec-part-select start size
                                             (4vec-rsh rsh-size term))
                         (svex-reduce-w/-env-masked-return
                          (hons-list 'sv::rsh rsh-size term))))))
                 (svex-reduce-w/-env-masked term (+ start rsh-size) size)))
              ((and* (or* (equal fn 'sv::bitor)
                          (equal fn 'sv::bitand)
                          (equal fn 'sv::bitxor))
                     (equal-len args 2))
               (svex-and/or/xor-reduce-w/-env-masked svex start size)
               #|(b* ((term1 (svex-reduce-w/-env-masked (first args) start size env))
               (term2 (svex-reduce-w/-env-masked (second args) start size env))
               ((when (and (equal fn 'sv::bitand)
               (or (equal term1 (4vec-part-select 0 size -1))
               (equal term2 (4vec-part-select 0 size -1)))))
               (if (equal term1 (4vec-part-select 0 size -1))
               (svex-reduce-w/-env-apply 'sv::unfloat (hons-list term2))
               (svex-reduce-w/-env-apply 'sv::unfloat (hons-list term1))))
               ((when (and (equal fn 'sv::bitor)
               (or (equal term1 0)
               (equal term2 0))))
               (if (equal term1 0)
               (svex-reduce-w/-env-apply 'sv::unfloat (hons-list term2))
               (svex-reduce-w/-env-apply 'sv::unfloat (hons-list term1)))))
               (svex-reduce-w/-env-apply fn (hons-list term1 term2)))|#)

              ((and* (equal fn 'sv::bitnot)
                     (equal-len args 1))
               (b* ((term1 (svex-reduce-w/-env-masked (first args) start size))
                    (start 0)
                    (res
                     (svex-reduce-w/-env-masked-return
                      (svex-reduce-w/-env-apply fn (hons-list term1)))))
                 res))

              ((and* (equal fn 'sv::res)
                     (equal-len args 2))
               (b* ((term1 (svex-reduce-w/-env-masked (first args) start size ))
                    ((when (equal term1 (4vec-part-select 0 size
                                                          (sv::4vec-x))))
                     term1)
                    (term2 (svex-reduce-w/-env-masked (second args) start size ))
                    ((when (equal term2 (4vec-part-select 0 size (sv::4vec-x))))
                     term2))
                 (cond ((equal term1 (4vec-part-select 0 size (sv::4vec-z)))
                        term2)
                       ((equal term2 (4vec-part-select 0 size (sv::4vec-z)))
                        term1)
                       (t
                        (svex-reduce-w/-env-apply fn (hons-list term1 term2))))))

              ((and* (or ;; can use improvements here....
                      (equal fn 'sv::unfloat))
                     (equal-len args 1))
               (b* ((term1 (svex-reduce-w/-env-masked (first args) start size))
                    #|((when (and*-exec (consp term1)
                    ;; minimize calls to integerp-of-svex
                    (hide (equal (car term1) 'sv::partsel))
                    (integerp-of-svex term1)))
                    term1)|#)
                 (svex-reduce-w/-env-apply fn (hons-list term1))))

              ((and* (or ;; can use improvements here....
                      (equal fn 'sv::?!))
                     (equal-len args 3))
               (b* ((test (svex-reduce-w/-env (first args)))
                    (term1 (svex-reduce-w/-env-masked (second args) start size ))
                    (term2 (svex-reduce-w/-env-masked (third args) start size )))
                 (svex-reduce-w/-env-apply fn (hons-list test term1 term2))))

              ((and* (or (equal fn 'sv::?) ;; can use improvements here....
                         (equal fn 'sv::?*))
                     (equal-len args 3))
               (b* ((test (svex-reduce-w/-env (first args)))
                    ((when (4vec-p test))
                     (b* ((test (sv::3vec-fix test))
                          (then (second args))
                          (else (third args))
                          ((sv::4vec test))
                          ((when (eql test.upper 0))
                           (svex-reduce-w/-env-masked else start size ))
                          ((when (not (eql test.lower 0)))
                           (svex-reduce-w/-env-masked then start size ))
                          (else (svex-reduce-w/-env-masked else start size ))
                          ((when (equal else (sv::4vec-part-select 0 size (sv::4vec-x))))
                           else)
                          (then (svex-reduce-w/-env-masked then start size ))
                          ((when (equal then (sv::4vec-part-select 0 size (sv::4vec-x))))
                           then))
                       (svex-reduce-w/-env-apply fn (hons-list test then else))))
                    (term1 (svex-reduce-w/-env-masked (second args) start size ))
                    (term2 (svex-reduce-w/-env-masked (third args) start size))
                    (res (svex-reduce-w/-env-apply fn (hons-list test term1 term2)))
                    (res (simplify-dont-care-branch res)))
                 res))
              ((and* (equal fn 'sv::partinst)
                     (equal-len args 4))
               (b* ((s-start (svex-reduce-w/-env (first args)))
                    (s-size (svex-reduce-w/-env (second args)))
                    (old-term (third args))
                    (term (fourth args)))
                 (cond ((not (and (natp s-start)
                                  (natp s-size)))
                        (b* ((old-term (svex-reduce-w/-env old-term))
                             (term (svex-reduce-w/-env term)))
                          (if (and* (4vec-p s-start) (4vec-p s-size)
                                    (4vec-p old-term) (4vec-p term))
                              (4vec-part-select
                               start size
                               (4vec-part-install s-start s-size old-term
                                                  term))
                            (svex-reduce-w/-env-masked-return
                             (hons-list 'sv::partinst
                                        s-start s-size
                                        old-term
                                        term)))))
                       ((and ;;(hide "case5")
                              (not (and (> (+ start size) s-start) ;;case5
                                        (> (+ s-start s-size) start))))
                        (svex-reduce-w/-env-masked old-term start size ))
                       ((and ;;(hide "case4")
                              (<= (+ start size) ;;case4
                                  (+ s-start s-size))
                              (<= s-start start))
                        (svex-reduce-w/-env-masked term (- start s-start)
                                                   size ))
                       ((and ;;(hide "case3")
                             (< start s-start) ;;case 3
                             (< s-start (+ start size))
                             (<= (+ start size)
                                 (+ s-start s-size)))
                        (b* ((term1 (svex-reduce-w/-env-masked
                                     old-term start (- s-start start) ))
                             (term2 (svex-reduce-w/-env-masked
                                     term 0 (+ start size (- s-start)) )))
                          (if (and* (4vec-p term1) (4vec-p term2))
                              (4vec-concat (- s-start start) term1 term2)
                            (svex-reduce-w/-env-apply 'sv::concat
                                                      (hons-list
                                                       (- s-start start)
                                                       term1
                                                       term2)))))
                       ((and ;;(hide "case2")
                             (<= s-start start) ;;case 2
                             (< start (+ s-start s-size))
                             (< (+ s-start s-size)
                                (+ start size)))
                        (b* ((term1 (svex-reduce-w/-env-masked
                                     term (- start s-start)
                                     (+ s-size s-start (- start))
                                     ))
                             (term2 (svex-reduce-w/-env-masked
                                     old-term
                                     (+ s-start s-size)
                                     (+ size start (- (+ s-start s-size)))
                                     ))
                             (c-size (+ s-size s-start (- start))))
                          (if (and* (4vec-p term1) (4vec-p term2))
                              (4vec-concat c-size term1 term2)
                            (svex-reduce-w/-env-apply 'sv::concat
                                                      (hons-list c-size term1 term2)))))
                       ((and ;;(hide "case1")
                         (< start s-start) ;;case 1
                         (< (+ s-start s-size)
                            (+ start size)))
                        (b* ((c-size1 (- s-start start))
                             (term1 (svex-reduce-w/-env-masked old-term start
                                                               (- s-start start) ))
                             (c-size2 s-size)
                             (term2 (svex-reduce-w/-env-masked term 0 s-size
                                                               ))
                             (term3 (svex-reduce-w/-env-masked old-term
                                                               (+ s-start s-size)
                                                               (- (+ start size)
                                                                  (+ s-start s-size))
                                                               ))
                             (m-term2 (if (and* (4vec-p term2) (4vec-p term3))
                                          (4vec-concat c-size2 term2 term3)
                                        (hons 'sv::concat ;; TODO. turn this into svex-reduce-w/-env-apply
                                              (hons-list c-size2 term2 term3))))
                             (mterm1 (if (and* (4vec-p term1) (4vec-p m-term2))
                                         (4vec-concat c-size1 term1 m-term2)
                                       (svex-reduce-w/-env-apply 'sv::concat
                                                      (hons-list c-size1 term1 m-term2)))))
                          Mterm1))
                       (t (hons-list 'sv::partinst ;; should never come here.
                                     s-start
                                     s-size
                                     (svex-reduce-w/-env old-term)
                                     (svex-reduce-w/-env term))))))
              ((and* (equal fn 'sv::bit?!)
                     (equal-len args 3))
               (b* ((first (svex-reduce-w/-env-masked (first args)
                                                      start size
                                                      ))
                    ((when (equal first (sv::4vec-part-select start size -1)))
                     (svex-reduce-w/-env-masked (second args)
                                                start size
                                                ))
                    ((when (or (equal first 0)
                               (equal first (sv::4vec-part-select start
                                                                  size (sv::4vec-x)))
                               (equal first (sv::4vec-part-select start size (sv::4vec-z)))))
                     (svex-reduce-w/-env-masked (third args)
                                                start size
                                                ))
                    (second (svex-reduce-w/-env-masked (second args)
                                                       start size
                                                       ))
                    (third (svex-reduce-w/-env-masked (third args)
                                                      start size
                                                      )))
                 (svex-reduce-w/-env-apply fn (hons-list first second third))))

              ((and* (equal fn 'sv::bit?)
                     (equal-len args 3))
               (b* ((first (svex-reduce-w/-env-masked (first args)
                                                      start size
                                                      ))
                    ((when (equal first (sv::4vec-part-select start size -1)))
                     (svex-reduce-w/-env-masked (second args)
                                                start size
                                                ))
                    ((when (equal first 0))
                     (svex-reduce-w/-env-masked (third args)
                                                start size
                                                ))
                    (second (svex-reduce-w/-env-masked (second args)
                                                       start size
                                                       ))
                    (third (svex-reduce-w/-env-masked (third args)
                                                      start size
                                                      ))
                    (- (and* (sv::4vec-p first)
                             (cw "The test case (~p0) for bit? is 4vec-p ~
but did not resolve the branch ~%" first))))
                 (svex-reduce-w/-env-apply fn (hons-list first second third))))
              (t
               (b* ((args-evaluated (svex-reduce-w/-env-lst args))
                    (new-svex (svex-reduce-w/-env-apply fn
                                                        args-evaluated)))
                 (svex-reduce-w/-env-masked-return new-svex)))))))))

    (define svex-reduce-w/-env-unmasked-bitand ((svex svex-p)
                                                &key
                                                ((env) 'env)
                                                ((context rp::rp-term-listp) 'context)
                                                ((config svex-reduce-config-p) 'config))
      ;; Splitting this case into another function because proofs are just too slow otherwise.
      :measure (acl2::nat-list-measure (list (cons-count svex)
                                             0))
      :guard (and (equal (svex-kind svex) :call)
                  (equal (car svex) 'sv::bitand)
                  (equal-len (cdr svex) 2))
      :returns (res svex-p :hyp (svex-p svex))
      (b* ((fn (car svex))
           (args (cdr svex)))
        (cond
         ((mbt (and* (equal (svex-kind svex) :call)
                     (equal fn 'sv::bitand)
                     (equal-len args 2)))
          (b* ((term1 (first args))
               (term2 (second args))
               (term1-width (width-of-svex term1))
               (term2-width (width-of-svex term2))

               ;; first get the min width
               (min-width (min-width term1-width term2-width))
               ;; simplify term1
               (term1 (if*-exec (natp min-width)
                                (svex-reduce-w/-env-masked term1 0 min-width)
                                (svex-reduce-w/-env term1)))

               ;; recalculate term1's width because it might be smaller now.
               (term1-width (width-of-svex term1))
               (min-width (min-width min-width term1-width))

               (term2 (if*-exec (natp min-width)
                                (svex-reduce-w/-env-masked term2 0 min-width)
                                (svex-reduce-w/-env term2)))

               ;; !!!!
               ;; TODO:
               ;; IDEALLY, WE RECALCULATE TERM2'S WIDTH HERE AND RECURSE IF IT'S SMALLER THAN MIN-WIDTH

               ;; ;; recalculate term2's width
               ;; (term2-width (width-of-svex term2))

               ;; (min-width (min-width term2-width min-width))

               ;; ;; if  term1 can  be simplified  with a  smaller width
               ;; ;; after term2's  simplification, redo the work  on it
               ;; ;; (simplified  term1 could  be  passed  too but  then
               ;; ;; proving measure becomes difficult.
               ;; (term1 (if*-exec (and* min-width term1-width (< (nfix min-width) (nfix term1-width)))
               ;;                  (svex-reduce-w/-env-masked (first args) 0 min-width)
               ;;                  term1))

               ;; TODO: bitand of mask cases could be simplified here maybe.

               ((when (acl2::or* (integerp term1)
                                 (integerp term2)))
                (bitand/or/xor-simple-constant-simplify fn term1 term2)))
            (bitand/or/xor-cancel-repeated fn term1 term2
                                           :nodes-to-skip-alist nil)))

         (t (acl2::impossible svex)))))

    (define svex-reduce-w/-env ((svex svex-p)
                                &key
                                ((env) 'env)
                                ((context rp::rp-term-listp) 'context)
                                ((config svex-reduce-config-p) 'config))
      :measure (acl2::nat-list-measure (list (cons-count svex)
                                             1))
      :returns (res svex-p :hyp (svex-p svex))
      (let* ((svex.kind (svex-kind svex)))
        (case  svex.kind
          (:quote svex)
          (:var
           (b* ((val (hons-get svex env))
                ((unless (consp val))
                 (if (svex-reduce-config->keep-missing-env-vars config)
                     svex
                   (sv::4vec-x)))
                (val (cdr val))
                ((when (and (quotep val)
                            (consp (cdr val))
                            (4vec-p (unquote val))))
                 (unquote val))
                (- (and (4vec-p val)
                        (acl2::raise "Constants are expected to be quoted in the
                                       given env. But given instead:~p0" (cons svex val)))))
             svex))
          (otherwise
           (b* ((fn (car svex))
                (args (cdr svex)))
             (cond ((and* (equal fn 'sv::partsel)
                          (equal-len args 3))
                    (b* ((start (svex-reduce-w/-env (first args)))
                         (size (svex-reduce-w/-env (second args)))
                         ((unless (and (natp start) (natp size)))
                          (b* ((third (svex-reduce-w/-env (third args)))
                               (args-evaluated (hons-list start size third)))
                            (svex-reduce-w/-env-apply fn
                                                      args-evaluated))))
                      (svex-reduce-w/-env-masked (third args) start size )))
                   ((and* (equal fn 'sv::concat)
                          (equal-len args 3))
                    (b* ((size (svex-reduce-w/-env (first args)))
                         (third (svex-reduce-w/-env (third args)))
                         ((unless (and (natp size)))
                          (b* ((second (svex-reduce-w/-env (second args)))
                               (args-evaluated (hons-list size second third)))
                            (svex-reduce-w/-env-apply fn
                                                      args-evaluated)))
                         (second
                          (svex-reduce-w/-env-masked (second args) 0 size ))
                         ((when (equal third 0)) second)
                         (args-evaluated (hons-list size second third))
                         (res (svex-reduce-w/-env-apply fn args-evaluated)))
                      res))
                   ((and* (equal fn 'sv::signx)
                          (equal-len args 2))
                    (b* ((size (svex-reduce-w/-env (first args)))
                         ((unless (and (natp size)))
                          (b* ((subterm (svex-reduce-w/-env (second args)))
                               (args-evaluated (hons-list size subterm)))
                            (svex-reduce-w/-env-apply fn
                                                      args-evaluated)))
                         (subterm (svex-reduce-w/-env-masked (second args) 0 size))
                         (args-evaluated (hons-list size subterm))
                         (res (svex-reduce-w/-env-apply fn args-evaluated)))
                      res))
                   ((and* (equal fn 'sv::bitand)
                          (equal-len args 2))
                    (svex-reduce-w/-env-unmasked-bitand svex))
                   ((and* (or (equal fn 'sv::bitor)
                              (equal fn 'sv::bitxor))
                          (equal-len args 2))
                    (b* ((term1 (svex-reduce-w/-env (first args)))
                         (term2 (svex-reduce-w/-env (second args)))
                         ((when (acl2::or* (integerp term1)
                                           (integerp term2)))
                          (bitand/or/xor-simple-constant-simplify fn term1 term2)))
                      (bitand/or/xor-cancel-repeated fn term1 term2
                                                     :nodes-to-skip-alist nil)))
                   (t (b* ((args-evaluated (svex-reduce-w/-env-lst args)))
                        (svex-reduce-w/-env-apply fn args-evaluated)))))))))

    (define svex-reduce-w/-env-lst ((svex-list svexlist-p)
                                    &key
                                    ((env) 'env)
                                    ((context rp::rp-term-listp) 'context)
                                    ((config svex-reduce-config-p) 'config))
      :measure (acl2::nat-list-measure (list (cons-count svex-list)
                                             0))
      :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p svex-list))
      (if (atom svex-list)
          nil
        (hons (svex-reduce-w/-env (car svex-list))
              (svex-reduce-w/-env-lst (cdr svex-list)))))
    ///

    (acl2::more-returns
     svex-reduce-w/-env-lst
     (res-lst true-listp
              :hints (("Goal"
                       :induct (true-listp svex-list)
                       :in-theory (e/d () ())))))))

(local
 (defthm svex-p-implies-4vec-p
   (IMPLIES (AND (SVEX-P SVEX)
                 (CONSP SVEX)
                 (INTEGERP (CAR SVEX)))
            (4VEC-P SVEX))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (svex-p) ())))))

(local
 (defthm svex-p-implies-4vec-p-2
   (IMPLIES (AND (SVEX-P SVEX)
                 (NOT (CONSP SVEX))
                 (NOT (STRINGP SVEX))
                 (NOT (SYMBOLP SVEX)))
            (4VEC-P SVEX))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (svex-p sv::svar-p) ())))))

(with-output
  :off :All
  :on (error summary)
  (verify-guards svex-reduce-w/-env-lst-fn
    :guard-debug t
    :hints (("Goal"
             :expand ((SVEX-P SVEX))
             :do-not-induct t
             :in-theory (e/d (svex-kind)
                             (subsetp-equal
                              (:e tau-system)))))))

(memoize 'svex-reduce-w/-env
         :condition '(equal (svex-kind svex) :call)
         ;;:aokp t
         )

(memoize 'svex-reduce-w/-env-masked
         :condition '(equal (svex-kind svex) :call)
         ;;:aokp t
         )

(define svex-alist-reduce-w/-env ((svex-alist sv::svex-alist-p)
                                  &key
                                  ((env) 'env)
                                  ((context rp::rp-term-listp) 'context)
                                  ((config svex-reduce-config-p) 'config))
  :returns (res-alist sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  (if (atom svex-alist)
      (progn$ (clear-memoize-table 'svex-reduce-w/-env)
              (clear-memoize-table 'svex-reduce-w/-env-masked)
              nil)
    (hons (hons (caar svex-alist)
                (svex-reduce-w/-env (cdar svex-alist)))
          (svex-alist-reduce-w/-env (cdr svex-alist)))))

;;

;; (svex-reduce-w/-env  '(partsel 0 1 (sv::bitand x y))
;;                      (make-fast-alist
;;                       '((x . '1)
;;                         (y . b))))

;; (SVEX-REDUCE-WITH-ENV-META 'X
;;                            (make-fast-alist
;;                             '((X QUOTE 0) (Y . B))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-opener-when-call
    (implies (and (syntaxp (and (consp fn)
                                (quotep fn)))
                  (fnsym-p fn))
             (equal (svex-eval (cons fn args) env)
                    (sv::svex-apply fn
                                    (SVEXLIST-EVAL args env))))
    :hints (("Goal"
             :expand (svex-eval (cons fn args) env)
             :in-theory (e/d (SVEX-CALL->FN
                              SVEX-VAR->NAME
                              SVEX-KIND
                              SVEX-CALL->ARGS)
                             ()))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-when-4vec-p
    (implies (4vec-p x)
             (equal (svex-eval x env)
                    x))
    :hints (("Goal"
             :expand ((SVEX-EVAL X ENV)
                      (4VEC-P X))
             :in-theory (e/d (SVEX-KIND
                              SV::SVEX-QUOTE->VAL)
                             ()))))))

(local
 (defthm 4VEC-BITOR-of-1
   (equal (4VEC-BITOR -1 then)
          -1)
   :hints (("Goal"
            :expand (4VEC-BITOR -1 then)
            :in-theory (e/d (SV::3VEC-BITOR) ())))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-svex-reduce-w/-env-apply-correct-when-returns-4vec-p
    (implies (and (force (fnsym-p fn))
                  (4vec-p (svex-reduce-w/-env-apply fn args)))
             (and (equal (equal (svex-reduce-w/-env-apply fn args) x)
                         (equal (svex-eval `(,fn . ,args) (rp-evlt env-term a)) x))
                  (equal (equal (4vec-part-select start size (svex-reduce-w/-env-apply fn args)) x)
                         (equal (4vec-part-select start size (svex-eval `(,fn . ,args) (rp-evlt env-term a))) x))))
    :hints (("goal"
             :do-not-induct t
             :use ((:instance svex-eval-svex-reduce-w/-env-apply-correct
                              (env (rp-evlt env-term a))))
             :in-theory (e/d ()
                             (svex-eval-svex-reduce-w/-env-apply-correct)))))))

(local
 (defthm 4vec-p-implies-integerp-when-not-consp
   (implies (and (4vec-p x)
                 (not (consp x)))
            (integerp x))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :in-theory (e/d (4vec-p) ())))))

#|(local
(defthm svex-reduce-w/-env-apply-specials-is-svex-apply-when-4vec-p
(implies (and (fnsym-p fn)
(4VEC-P (SVEX-REDUCE-W/-ENV-APPLY-SPECIALS fn args)))
(equal (SVEX-REDUCE-W/-ENV-APPLY-SPECIALS fn args)
(SV::SVEX-APPLY fn args)))
:hints (("goal"
:do-not-induct t
:use ((:instance bit?!-resolve-is-svex-apply-when-4vec-p
(test (car args))
(then (cadr args))
(else (caddr args))
(limit 1073741824))
(:instance svex-reduce-w/-env-apply-correct)
(:instance svex-reduce-w/-env-apply-specials-correct))
:expand ((SV::4VEC->LOWER (CAR ARGS))
(:free (x y) (4VEC-P (CONS x y)))

(:free (x y) (4VECLIST-NTH-SAFE x y))
(:free (x y) (nth x y))
;; (:free (x) (SV::SVEX-APPLY 'BITAND x))
;; (:free (x) (SV::SVEX-APPLY 'SV::BITOR x))
;; (:free (x) (SV::SVEX-APPLY 'sv::? x))
;; (:free (x) (SV::SVEX-APPLY 'sv::?* x))
;; (:free (x) (SV::SVEX-APPLY 'sv::?! x))
;; (:free (x) (SV::SVEX-APPLY 'sv::bit?! x))
;; (:free (x) (SV::SVEX-APPLY 'sv::bit? x))
)
:in-theory (e/d (;;svex-reduce-w/-env-apply-specials
;;4VEC-?
;;SV::4VEC-BIT?!
;;4VEC-P
;;4VEC-?*
;;SV::3VEC-BIT?
;;SV::3VEC-?*
;;SV::4VEC-BIT?!
;;SV::4VEC-?!
;;SV::4VEC->UPPER
;;SV::3VEC-?
)
(bit?!-resolve-is-svex-apply-when-4vec-p
svex-reduce-w/-env-apply-correct
svex-reduce-w/-env-apply-specials-correct
))))))|#

#|(local
(defthm svex-reduce-w/-env-apply-is-SVEX-APPLY-when-4vec-p
(implies (and (fnsym-p fn)
(4VEC-P (SVEX-REDUCE-W/-ENV-APPLY fn args)))
(equal (SVEX-REDUCE-W/-ENV-APPLY fn args)
(SV::SVEX-APPLY fn args)))
:hints (("goal"
:do-not-induct t
:expand ((SVEXLIST-EVAL ARGS ENV)
(:free (x y)
(SVEX-REDUCE-W/-ENV-APPLY x y))
(:free (x y)
(SV::SVEX-APPLY x y))
;;(SV::SVEX-APPLY FN ARGS)
(:free (fn args)
(4VEC-P (CONS FN ARGS)))
(SVEX-EVAL (CONS FN ARGS) ENV)
(SVEX-REDUCE-W/-ENV-APPLY FN ARGS))
:use ((:instance svex-reduce-w/-env-apply-correct))
:in-theory (e/d (SVEX-KIND
4VEC-?
SV::3VEC-?
SV::4VEC-BIT?
SVEX-CALL->ARGS
SVEX-CALL->FN)
(svex-reduce-w/-env-apply-correct))))))|#

(local
 (defthm SVEX-VAR->NAME-when-svexp
   (implies (and (equal (svex-kind svex) :var)
                 (svex-p svex))
            (equal (SVEX-VAR->NAME SVEX)
                   svex))
   :hints (("Goal"
            :in-theory (e/d (svex-kind
                             SVEX-P
                             SVEX-VAR->NAME)
                            ())))))

(local
 (defthmd SVEX-ENV-LOOKUP-when-svex-p
   (implies (and (force (sv::svar-p svex)))
            (equal (SV::SVEX-ENV-LOOKUP svex env)
                   (4vec-fix (LET ((SV::LOOK (HONS-GET svex env)))
                                  (IF SV::LOOK  (CDR SV::LOOK)
                                      (SV::4VEC-X))))))
   :hints (("Goal"
            :expand ((svex-p svex))
            :in-theory (e/d (svex-p
                             SV::SVAR-FIX
                             4vec-p
                             SV::SVEX-ENV-LOOKUP)
                            ())))))

(local
 (defthm rp::falist-consistent-aux-lemma
   (implies (and (rp::falist-consistent-aux env-falist term)
                 (hons-assoc-equal x env-falist))
            (equal (cdr (hons-assoc-equal x (rp-evlt term a)))
                   (rp-evlt (cdr (hons-assoc-equal x env-falist))
                            a)))))

(local
 (defthm rp::falist-consistent-aux-lemma-2
   (implies (and (rp::falist-consistent-aux env-falist term))
            (iff (hons-assoc-equal x (rp-evlt term a))
                 (hons-assoc-equal x env-falist)))))

(local
 (defthm remove-consp-HONS-ASSOC-EQUAL
   (iff (consp (HONS-ASSOC-EQUAL SVEX ENV))
        (HONS-ASSOC-EQUAL SVEX ENV))))

(local
 (svex-eval-lemma-tmpl
  (defthmd svex-eval-when-entry-is-absent
    (IMPLIES (AND (RP::FALIST-CONSISTENT-AUX ENV ENV-TERM)
                  ;; (CONSP SVEX)
                  ;; (EQUAL (CAR SVEX) :VAR)
                  (equal (svex-kind svex) :var)
                  (NOT (HONS-ASSOC-EQUAL SVEX ENV))
                  (SVEX-P SVEX))
             (and (equal (EQUAL '(-1 . 0)
                                (SVEX-EVAL SVEX (RP-EVLT ENV-TERM A)))
                         t)
                  (equal (EQUAL '(-1 . 0)
                                (SV::SVEX-ENV-LOOKUP SVEX (RP-EVLT ENV-TERM A)))
                         t)))
    :rule-classes :rewrite
    :hints (("Goal"
             :do-not-induct t
             :expand ((SVEX-EVAL SVEX (RP-EVLT ENV-TERM A)))
             :in-theory (e/d (svex-kind
                              SVEX-P
                              SVEX-ENV-LOOKUP-when-svex-p
                              ;;SVEX-VAR->NAME
                              ;;SV::SVEX-ENV-LOOKUP
                              ;;SV::SVAR-FIX
                              )
                             ()))))))

(local
 (defthmd when-entry-is-present-but-not-4vec-p
   (IMPLIES (AND (RP::FALIST-CONSISTENT-AUX ENV ENV-TERM)
                 ;; (CONSP SVEX)
                 ;; (EQUAL (CAR SVEX) :VAR)
                 (equal (svex-kind svex) :var)
                 (HONS-ASSOC-EQUAL SVEX ENV)
                 (QUOTEP (CDR (HONS-ASSOC-EQUAL SVEX ENV)))
                 (CONSP (CDDR (HONS-ASSOC-EQUAL SVEX ENV)))
                 (4VEC-P (CADDR (HONS-ASSOC-EQUAL SVEX ENV)))
                 (SVEX-P SVEX))
            (and (equal (EQUAL (CADDR (HONS-ASSOC-EQUAL SVEX ENV))
                               (SV::SVEX-ENV-LOOKUP SVEX (RP-EVLT ENV-TERM A)))
                        t)
                 ))
   :rule-classes :rewrite
   :hints (("Goal"
            :do-not-induct t
            :in-theory (e/d (svex-kind
                             SVEX-P

                             SVEX-ENV-LOOKUP-when-svex-p
                             ;;SVEX-VAR->NAME
                             ;;SV::SVEX-ENV-LOOKUP
                             ;;SV::SVAR-FIX
                             )
                            ())))))

(local
 (defthm dummy-svex-p-lemma-1
   (implies (and (svex-p svex)
                 (fnsym-p (car svex))
                 (consp svex))
            (and (implies (equal-len (cdr svex) 4)
                          (and (svex-p (cadr svex))
                               (svex-p (caddr svex))
                               (svex-p (cadddr svex))
                               (svex-p (cadddr (cdr svex)))))
                 (implies (equal-len (cdr svex) 3)
                          (and (svex-p (cadr svex))
                               (svex-p (caddr svex))
                               (svex-p (cadddr svex))))
                 (implies (equal-len (cdr svex) 2)
                          (and (svex-p (cadr svex))
                               (svex-p (caddr svex))))
                 (implies (equal-len (cdr svex) 1)
                          (and (svex-p (cadr svex))))))
   :rule-classes :rewrite
   :hints (("Goal"
            :in-theory (e/d (svex-p
                             SVEX-KIND
                             ) ())))))

#|(skip-proofs
(defthm 4vec-part-select-of-4vec-bit?
(implies (and (natp start)
(natp size))
(equal (4vec-part-select start size
(sv::4vec-bit? test then else))
(sv::4vec-bit? (4vec-part-select start size test)
(4vec-part-select start size then)
(4vec-part-select start size else))))))|#

(local
 (defthm 4vec-bit?-of-masked-dont-care
   (implies (and (natp start)
                 (natp size))
            (EQUAL (SV::4VEC-BIT? (4VEC-PART-SELECT START SIZE '(-1 . 0))
                                  (4VEC-PART-SELECT START SIZE '(-1 . 0))
                                  (4VEC-PART-SELECT START SIZE '(-1 . 0)))
                   (4VEC-PART-SELECT START SIZE '(-1 . 0))))
   :hints (("Goal"
            :use ((:instance 4vec-part-select-of-4vec-bit?
                             (test '(-1 . 0))
                             (then '(-1 . 0))
                             (else '(-1 . 0))))
            :in-theory (e/d () (4vec-part-select-of-4vec-bit?))))))

(local
 (defthm 4VEC-?*-when-upper-and-lower-test-is-not-0
   (implies (and (not (EQUAL
                       (SV::4VEC->UPPER (SV::3VEC-FIX test))
                       0))
                 (not (EQUAL
                       (SV::4VEC->lower (SV::3VEC-FIX test))
                       0)))
            (and (equal (4vec-?* test then else)
                        (4vec-fix then))
                 (equal (4vec-? test then else)
                        (4vec-fix then))))
   :hints (("Goal"
            :in-theory (e/d (4vec-?*
                             4vec-?
                             SV::3VEC-?*
                             SV::3VEC-?)
                            ())))))

(local
 (defthm 4vec-part-select-of-dont-care-z-or--1-with-start
   (implies (and (natp start)
                 (natp size)
                 (syntaxp (and (not (equal start 0))
                               (not (equal start ''0)))))
            (and (equal (4VEC-PART-SELECT start SIZE '(-1 . 0))
                        (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
                 (equal (4VEC-PART-SELECT start SIZE '(0 . -1))
                        (4VEC-PART-SELECT 0 SIZE '(0 . -1)))
                 (equal (4VEC-PART-SELECT start SIZE -1)
                        (4VEC-PART-SELECT 0 SIZE -1))
                 (equal (4VEC-PART-SELECT START SIZE 0)
                        0)))
   :hints (("Goal"
            :expand ((4VEC-RSH START '(-1 . 0))
                     (4VEC-RSH START -1)
                     (4VEC-RSH START '(0 . -1)))
            :in-theory (e/d (4VEC-PART-SELECT
                             4VEC
                             (:REWRITE ACL2::|(- (- x))|)
                             (:REWRITE ACL2::|(floor 0 y)|)
                             (:REWRITE SV::4VEC->UPPER-AND-LOWER-EQUIVALANCE)
                             (:REWRITE 4VEC-ZERO-EXT-IS-4VEC-CONCAT)
                             (:REWRITE ACL2::ASH-TO-FLOOR)
                             (:REWRITE ACL2::FLOOR-X-Y-=--1 . 2)
                             (:REWRITE ACL2::REMOVE-WEAK-INEQUALITIES)
                             (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)
                             (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)
                             (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE)
                             SV::4VEC->LOWER

                             4VEC-SHIFT-CORE
                             SV::4VEC->UPPER)
                            ())))))

(local
 (defthm 4VEC-?*-when-upper-is-0
   (implies (and (EQUAL
                  (SV::4VEC->UPPER (SV::3VEC-FIX test))
                  0)
                 (natp start)
                 (natp size)
                 )
            (and (equal (4vec-?* test then else)
                        (4vec-fix else))
                 (equal (4vec-? test then else)
                        (4vec-fix else))))
   :hints (("Goal"
            :in-theory (e/d (4vec-?*
                             SV::3VEC-?*
                             4vec-?
                             SV::3VEC-?)
                            ())))))

(local
 (defthm 4VEC-?*-when-upper-is-not-0-and-lower-test-is-0
   (implies (and (natp start)
                 (natp size)
                 (not (EQUAL
                       (SV::4VEC->UPPER (SV::3VEC-FIX test))
                       0))
                 (EQUAL
                  (SV::4VEC->lower (SV::3VEC-FIX test))
                  0))
            (and (equal (4vec-part-select start size (4vec-?* test '(-1 . 0) else))
                        (4VEC-PART-SELECT 0 size '(-1 . 0)))
                 (equal (4vec-part-select start size (4vec-?* test then '(-1 . 0)))
                        (4VEC-PART-SELECT 0 size '(-1 . 0)))
                 (equal (4vec-part-select start size (4vec-? test '(-1 . 0) else))
                        (4VEC-PART-SELECT 0 size '(-1 . 0)))
                 (equal (4vec-part-select start size (4vec-? test then '(-1 . 0)))
                        (4VEC-PART-SELECT 0 size '(-1 . 0)))))
   :hints (("Goal"
            :in-theory (e/d (4vec-?*
                             SV::3VEC-?*
                             4vec-?
                             SV::3VEC-?)
                            ())))))

(local
 (defthm 4vec-?*-when-upper-is-not-0-and-lower-test-is-0-2
   (implies
    (and (natp start)
         (natp size)
         (not (EQUAL
               (SV::4VEC->UPPER (SV::3VEC-FIX test))
               0))
         (EQUAL
          (SV::4VEC->lower (SV::3VEC-FIX test))
          0))
    (and (equal (4vec-?* test
                         (4vec-part-select 0 size '(-1 . 0))
                         (4vec-part-select start size else))
                (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
         (equal (4vec-?* test
                         (4vec-part-select start size then)
                         (4vec-part-select 0 size '(-1 . 0)))
                (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
         (equal (4vec-? test
                        (4vec-part-select 0 size '(-1 . 0))
                        (4vec-part-select start size else))
                (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
         (equal (4vec-? test
                        (4vec-part-select start size then)
                        (4vec-part-select 0 size '(-1 . 0)))
                (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))))
   :hints (("Goal"
            :use ((:instance 4VEC-?*-when-upper-is-not-0-and-lower-test-is-0)
                  )
            :in-theory (e/d ()
                            (4VEC-?*-when-upper-is-not-0-and-lower-test-is-0
                             ))))))

(local
 (defthm SV::4VEC-BIT?!-of-constants
   (and (equal (SV::4VEC-BIT?! -1 then else)
               (4vec-fix then))
        (equal (SV::4VEC-BIT?! 0 then else)
               (4vec-fix else))
        (equal (SV::4VEC-BIT?! '(0 . -1) then else)
               (4vec-fix else))
        (equal (SV::4VEC-BIT?! '(-1 . 0) then else)
               (4vec-fix else)))
   :hints (("Goal"
            :expand ((:free (x y) (SV::4VEC-BIT?! 0 x y))
                     (:free (x y) (SV::4VEC-BIT?! -1 x y))
                     (:free (x y) (SV::4VEC-BIT?! '(0 . -1) x y))
                     (:free (x y) (SV::4VEC-BIT?! '(-1 . 0) x y)))
            :in-theory (e/d ()
                            (4VEC-BIT?!-WHEN-TEST-IS-QUOTED))))))

(local
 (defthm 4VEC-bit?!-of-4vec-part-select-constants
   (implies (and (natp start)
                 (natp size))
            (and (equal (SV::4VEC-BIT?!
                         (4VEC-PART-SELECT 0 SIZE '(-1 . 0))
                         (4VEC-PART-SELECT START SIZE
                                           then)
                         (4VEC-PART-SELECT START SIZE
                                           else))
                        (4VEC-PART-SELECT START SIZE
                                          else))
                 (equal (SV::4VEC-BIT?!
                         (4VEC-PART-SELECT 0 SIZE '(0 . -1))
                         (4VEC-PART-SELECT START SIZE
                                           then)
                         (4VEC-PART-SELECT START SIZE
                                           else))
                        (4VEC-PART-SELECT START SIZE
                                          else))
                 (equal (SV::4VEC-BIT?! (4VEC-PART-SELECT 0 SIZE '-1)
                                        (4VEC-PART-SELECT START SIZE
                                                          then)
                                        (4VEC-PART-SELECT START SIZE
                                                          else))
                        (4VEC-PART-SELECT START SIZE
                                          then))
                 (equal (SV::4VEC-BIT?!
                         0
                         (4VEC-PART-SELECT START SIZE
                                           then)
                         (4VEC-PART-SELECT START SIZE
                                           else))
                        (4VEC-PART-SELECT START SIZE
                                          else))))
   :hints (("Goal"
            :use ((:instance SV::4VEC-BIT?!-of-constants)
                  (:instance 4vec-part-select-of-4vec-bit?!
                             (test '(-1 . 0)))
                  (:instance 4vec-part-select-of-4vec-bit?!
                             (test '(0 . -1)))
                  (:instance 4vec-part-select-of-4vec-bit?!
                             (test -1))
                  (:instance 4vec-part-select-of-4vec-bit?!
                             (test 0)))
            :in-theory (e/d () (SV::4VEC-BIT?!-of-constants
                                4vec-part-select-of-4vec-bit?!

                                (:REWRITE 4VEC-BIT?!-WHEN-TEST=-1-MASKED)
                                (:REWRITE 4VEC-BIT?!-WHEN-TEST=-DONT-CARE-OR-Z-MASKED)
                                (:REWRITE 4VEC-BIT?!-WHEN-TEST=DONT-CARE)
                                (:REWRITE 4VEC-BIT?!-WHEN-TEST=Z)

                                ))))))

(local
 (defthm SV::4VEC-BIT?-of-constants
   (and (equal (SV::4VEC-BIT? -1 then else)
               (4vec-fix then))
        (equal (SV::4VEC-BIT? 0 then else)
               (4vec-fix else))
        #|(equal (SV::4VEC-BIT? '(0 . -1) then else)
        (4vec-fix else))
        (equal (SV::4VEC-BIT? '(-1 . 0) then else)
        (4vec-fix else))|#)
   :hints (("Goal"
            :expand ((:free (x y) (SV::4VEC-BIT? 0 x y))
                     (:free (x y) (SV::4VEC-BIT? -1 x y))
                     (:free (x y) (SV::4VEC-BIT? '(0 . -1) x y))
                     (:free (x y) (SV::4VEC-BIT? '(-1 . 0) x y)))
            :in-theory (e/d (SV::3VEC-BIT?)
                            ())))))

(local
 (defthm 4VEC-bit?-of-4vec-part-select-constants
   (implies (and (natp start)
                 (natp size))
            (and
             (equal (SV::4VEC-BIT? (4VEC-PART-SELECT 0 SIZE '-1)
                                   (4VEC-PART-SELECT START SIZE
                                                     then)
                                   (4VEC-PART-SELECT START SIZE
                                                     else))
                    (4VEC-PART-SELECT START SIZE
                                      then))
             (equal (SV::4VEC-BIT?
                     0
                     (4VEC-PART-SELECT START SIZE
                                       then)
                     (4VEC-PART-SELECT START SIZE
                                       else))
                    (4VEC-PART-SELECT START SIZE
                                      else))))
   :hints (("Goal"
            :use ((:instance SV::4VEC-BIT?-of-constants)
                  (:instance 4vec-part-select-of-4vec-bit?
                             (test -1))
                  (:instance 4vec-part-select-of-4vec-bit?
                             (test 0)))
            :in-theory (e/d () (SV::4VEC-BIT?-of-constants
                                4vec-part-select-of-4vec-bit?
                                ))))))

(progn
  (local
   (use-arithmetic-5 t))
  (local
   (defthm 4vec-?-of-dont-care
     (IMPLIES (natp size)

              (EQUAL (4VEC-? '(-1 . 0)
                             (4VEC-PART-SELECT 0 SIZE '(-1 . 0))
                             (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
                     (4VEC-PART-SELECT 0 SIZE '(-1 . 0))))
     :hints (("Goal"
              :in-theory (e/d (4VEC-PART-SELECT
                               4VEC-CONCAT
                               SV::4VEC->UPPER
                               SV::4VEC->lower
                               4VEC-?
                               SV::3VEC-?
                               )
                              ( ))))))
  (local
   (use-arithmetic-5 nil)))

(local
 (defthm 4vec-?!-of-dont-care
   (IMPLIES (natp size)

            (EQUAL (sv::4VEC-?! '(-1 . 0)
                                (4VEC-PART-SELECT 0 SIZE '(-1 . 0))
                                (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
                   (4VEC-PART-SELECT 0 SIZE '(-1 . 0))))
   :hints (("Goal"
            :in-theory (e/d (4VEC-PART-SELECT
                             4VEC-CONCAT
                             SV::4VEC->UPPER
                             SV::4VEC->lower
                             sv::4VEC-?!
                             SV::3VEC-?
                             )
                            ( ))))))

(local
 (defthm 4vec-res-of-dont-care-and-z
   (and (equal (sv::4vec-res '(-1 . 0) other)
               (sv::4vec-x))
        (equal (sv::4vec-res other '(-1 . 0))
               (sv::4vec-x))
        (equal (sv::4vec-res '(0 . -1) other)
               (sv::4vec-fix other))
        (equal (sv::4vec-res other '(0 . -1))
               (sv::4vec-fix other)))
   :hints (("Goal"
            :in-theory (e/d (sv::4vec-res) ())))))

(local
 (defthm 4vec-res-of-dont-care-and-z-masked
   (implies (and (natp start)
                 (natp size))
            (and (equal (sv::4vec-res (4vec-part-select 0 size '(-1 . 0))
                                      (4vec-part-select start size other))
                        (4vec-part-select 0 size '(-1 . 0)))
                 (equal (sv::4vec-res (4vec-part-select start size other)
                                      (4vec-part-select 0 size '(-1 . 0)))
                        (4vec-part-select 0 size '(-1 . 0)))
                 (equal (sv::4vec-res (4vec-part-select 0 size '(0 . -1))
                                      (4vec-part-select start size other))
                        (4vec-part-select start size other))
                 (equal (sv::4vec-res (4vec-part-select start size other)
                                      (4vec-part-select 0 size '(0 . -1)))
                        (4vec-part-select start size other))))
   :hints (("goal"
            :use ((:instance 4vec-res-of-dont-care-and-z)
                  (:instance 4vec-part-select-of-4vec-res
                             (x '(-1 . 0))
                             (y other))
                  (:instance 4vec-part-select-of-4vec-res
                             (y '(-1 . 0))
                             (x other))
                  (:instance 4vec-part-select-of-4vec-res
                             (x '(0 . -1))
                             (y other))
                  (:instance 4vec-part-select-of-4vec-res
                             (y '(0 . -1))
                             (x other)))
            :in-theory (e/d ()
                            (4vec-part-select-of-4vec-res
                             4vec-res-of-dont-care-and-z))))))

(local
 (defthm 3vec-fix-of-4vec-part-select-of-dont-care
   (equal (sv::3vec-fix (4vec-part-select 0 size '(-1 . 0)))
          (4vec-part-select 0 size '(-1 . 0)))
   :hints (("goal"
            :in-theory (e/d (4vec-part-select
                             (:rewrite acl2::|(* 0 x)|)
                             (:rewrite acl2::|(+ (+ x y) z)|)
                             (:rewrite acl2::|(+ 0 x)|)
                             (:rewrite acl2::|(+ y x)|)
                             (:rewrite acl2::|(equal (if a b c) x)|)
                             (:rewrite acl2::|(logand y x)|)
                             (:rewrite acl2::|(logior y x)|)
                             (:rewrite acl2::|(mod 0 y)|)
                             (:rewrite sv::4vec->lower-of-4vec)
                             (:rewrite sv::4vec->upper-of-4vec)
                             (:rewrite 4vec-zero-ext-is-4vec-concat)
                             (:rewrite acl2::logand-mask)
                             (:rewrite acl2::logior-0-x)
                             (:rewrite acl2::mod-x-y-=-x+y . 2)
                             (:rewrite acl2::remove-weak-inequalities)
                             (:type-prescription acl2::expt-type-prescription-integerp-base)
                             (:type-prescription acl2::expt-type-prescription-nonnegative-base)
                             (:type-prescription acl2::expt-type-prescription-positive-base)
                             4vec-concat
                             sv::4vec->upper
                             sv::4vec->lower
                             sv::3vec-fix)
                            ())))))

(local
 (defthm 4vec-bitand-of--1-masked
   (implies (and (natp start)
                 (natp size))
            (and (equal (4vec-bitand (4vec-part-select 0 size -1)
                                     (4vec-part-select start size x))
                        (sv::3vec-fix (4vec-part-select start size x)))
                 (equal (4vec-bitand  (4vec-part-select start size x)
                                      (4vec-part-select 0 size -1))
                        (sv::3vec-fix (4vec-part-select start size x)))))
   :hints (("goal"
            :use ((:instance 4vec-bitand-with--1)
                  (:instance 4vec-part-select-of-4vec-bitand-better
                             (val1 -1)
                             (val2 x))
                  (:instance 4vec-part-select-of-4vec-bitand-better
                             (val1 x)
                             (val2 -1)))
            :in-theory (e/d () (4vec-bitand-with--1
                                4vec-part-select-of-4vec-bitand-better))))))

(local
 (defthm 4vec-?*-of-dont-care
   (Implies (natp size)
            (EQUAL (4VEC-?* '(-1 . 0)
                            (4VEC-PART-SELECT 0 SIZE '(-1 . 0))
                            (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
                   (4VEC-PART-SELECT 0 SIZE '(-1 . 0))))
   :hints (("Goal"
            :use ((:instance 4vec-part-select-of-4vec-?*
                             (test '(-1 . 0))
                             (start 0)
                             (x '(-1 . 0))
                             (y '(-1 . 0))))
            :in-theory (e/d ()
                            (4vec-part-select-of-4vec-?*))))))

(local
 (defthm 4vec-bitxor-of-dont-care
   (implies (natp size)
            (equal (SV::4VEC-BITXOR (4VEC-PART-SELECT 0 SIZE '(-1 . 0))
                                    (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
                   (4VEC-PART-SELECT 0 SIZE '(-1 . 0))))
   :hints (("Goal"
            :use ((:instance 4vec-part-select-of-4vec-bitxor-better
                             (val1 '(-1 . 0))
                             (val2 '(-1 . 0))
                             (start 0)))
            :in-theory (e/d () ())))))

(defthm 4vec-part-select-of-0
  (implies (and (natp start)
                (natp size))
           (equal (4vec-part-select start size 0)
                  0))
  :hints (("Goal"
           :in-theory (e/d (4vec-part-select
                            SV::4VEC->UPPER
                            SV::4VEC->lower)
                           ()))))

(local
 (defthm 4vec-lsh-to-4vec-concat
   (implies (natp size)
            (equal (4vec-lsh size x)
                   (4vec-concat size 0 x)))
   :hints (("Goal"
            :in-theory (e/d (4vec-lsh
                             4VEC-CONCAT
                             SV::4VEC->UPPER
                             4VEC-SHIFT-CORE)
                            ())))))

(progn
  (local
   (use-arithmetic-5 t))
  (local
   (defthm 4vec-part-select-of-4vec-part-select-of-repeated
     (equal (4vec-part-select 0 size
                              (4vec-part-select 0 size x))
            (4vec-part-select 0 size x))
     :hints (("goal"
              :in-theory (e/d (4vec-part-select
                               4vec-concat
                               4vec
                               sv::4vec->upper
                               sv::4vec->lower)
                              ((:e tau-system)
                               4vec-concat-insert-4vec-part-select))))))
  (local
   (use-arithmetic-5 nil)))

(local
 (defthm rp-evlt-when-quotep-lemma
   (implies (quotep (cdr (hons-assoc-equal svex env)))
            (equal (rp-evlt (cdr (hons-assoc-equal svex env))
                            a)
                   (caddr (hons-assoc-equal svex env))))
   :hints (("goal"
            :in-theory (e/d (rp-trans) ())))))

(local
 (defthm svar-p-lemma
   (IMPLIES (AND (or (and (CONSP SVEX)
                          (EQUAL (CAR SVEX) :VAR))
                     (STRINGP SVEX)
                     (symbolp svex))
                 (SVEX-P SVEX))
            (SV::SVAR-P SVEX))
   :hints (("Goal"
            :in-theory (e/d (SVEX-P
                             SV::SVAR-P
                             )
                            ())))))

(local
 (defthm 4vec-concat-of-sign-extended-compress-when-bitp
   (implies (and (posp size)
                 (bitp x))
            (equal (4vec-concat 1 x (- x))
                   (- x)))))

(local
 (defthm unary-cancel
   (and (equal (+ x (- x)) 0)
        (implies (acl2-numberp other)
                 (equal (+ x (- x) other) other)))))

(local
 (defthmd 4vec-concat-insert-4vec-part-select-local
   (implies
    (syntaxp
     (and (not (equal val1 '0))
          (not (equal val1 ''0))
          (or (and (consp val1)
                   (not (equal (car val1) 'sv::4vec-part-select))
                   (not (equal (car val1) 'sv::4vec-bitxor))
                   (not (equal (car val1) 'sv::4vec-bitand))
                   (not (equal (car val1) 'sv::4vec-bitor))
                   (not (equal (car val1) 'sv::3vec-fix)))
              (atom val1))))
    (equal (4vec-concat size val1 val2)
           (4vec-concat size (4vec-part-select 0 size val1)
                        val2)))
   :hints (("goal"
            :use ((:instance 4vec-concat-insert-4vec-part-select))
            :in-theory (e/d () ())))))

(local
 (defthm 4vec-rsh-of-4vec
   (implies (and (natp size)
                 (integerp x)
                 (integerp y)
                 )
            (equal (4vec-rsh size (4vec x y))
                   (4vec
                    (4vec-rsh size (ifix x))
                    (4vec-rsh size (ifix y)))))
   :hints (("Goal"
            :in-theory (e/d (4vec-rsh
                             4vec
                             SV::4VEC->LOWER
                             SV::4VEC->UPPER
                             4VEC-SHIFT-CORE)
                            (floor ash))))))

(local
 (defthm 4vec-bitand-with-all-ones-constant-without-syntaxp
   (implies (and (integerp num)
                 (equal (acl2::logmask (integer-length num))
                        num))
            (and (equal (sv::4vec-bitand num x)
                        (sv::4vec-part-select 0 (integer-length num) (sv::3vec-fix x)))
                 (equal (sv::4vec-bitand x num)
                        (sv::4vec-part-select 0 (integer-length num) (sv::3vec-fix x)))))
   :hints (("goal"
            :use ((:instance 4vec-bitand-with-all-ones-constant))
            :in-theory (e/d ()
                            ())))))

(local
 (defthm 4vec-p-implies-svex-p-rw
   (implies (sv::4vec-p x)
            (sv::svex-p x))))

(local
 (defthm 4vec-bitand-of-only-one-part-select
   (implies (and (or (equal (4vec-part-select 0 size x) x)
                     (equal (sv::4vec-bitand (4vec-part-select 0 size x) y)
                            (sv::4vec-bitand x y)))
                 (natp size))
            (equal (4vec-bitand x (4vec-part-select 0 size y))
                   (4vec-bitand x y)))
   :hints (("Goal"
            :in-theory (e/d (move-over-part-select-from-4vec-bitand) ())))))

(local
 (defthm 4vec-bitand-of-two--part-selects-with-known-relation
   (implies (and (natp size1)
                 (natp size2)
                 (case-split (<= size1 size2)))
            (and (equal (4vec-bitand (4vec-part-select 0 size1 x)
                                     (4vec-part-select 0 size2 y))
                        (4vec-bitand x
                                     (4vec-part-select 0 size1 y)))
                 (equal (4vec-bitand (4vec-part-select 0 size2 x)
                                     (4vec-part-select 0 size1 y))
                        (4vec-bitand x
                                     (4vec-part-select 0 size1 y)))))
   :hints (("Goal"
            :in-theory (e/d (move-over-part-select-from-4vec-bitand) ())))))

(local
 (defthm 4vec-bitand-of-same-sized-args
   (implies (and (natp start)
                 (natp size))
            (equal (4vec-bitand (4vec-part-select 0 size x)
                                (4vec-part-select start size y))
                   (4vec-bitand x
                                (4vec-part-select start size y))))
   :hints (("goal"
            :use ((:instance move-over-part-select-from-4vec-bitand
                             (width size)
                             (y x)
                             (x (4vec-part-select start size y))))
            :in-theory (e/d ()
                            (4vec-bitand-of-only-one-part-select))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-of-width-of-svex-more-general-lemma
    (implies (and (sv::Svex-p x)
                  (sv::Svex-p y)
                  (:@ :dollar-eval
                      (width-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->width-extns config)))
                  (:@ :normal-eval
                      (equal (svex-reduce-config->width-extns config) nil))
                  (width-of-svex x)
                  (equal (svex-eval x env-term)
                         (svex-eval y env-term)))
             (equal (4vec-part-select 0 (width-of-svex x) (svex-eval y env-term))
                    (svex-eval y env-term))))))

(local
 (svex-eval-lemma-tmpl
  (defthm svex-eval-of-width-of-svex-more-general-lemma-2
    (implies (and (sv::Svex-p x)
                  (sv::Svex-p y)
                  (:@ :dollar-eval
                      (width-of-svex-extn-correct<$>-lst
                       (svex-reduce-config->width-extns config)))
                  (:@ :normal-eval
                      (equal (svex-reduce-config->width-extns config) nil))
                  (width-of-svex x)
                  (equal (4vec-bitand other (svex-eval x env-term))
                         (4vec-bitand other (svex-eval y env-term))))
             (equal (4vec-bitand other
                                 (4vec-part-select 0 (width-of-svex x) (svex-eval y env-term)))
                    (4vec-bitand other
                                 (svex-eval y env-term))))
    :hints (("Goal"
             :use ((:instance PULL-OUT-PART-SELECT-FROM-4VEC-BITAND
                              (width (width-of-svex x))
                              (y (svex-eval y env-term))
                              (x other))
                   (:instance PULL-OUT-PART-SELECT-FROM-4VEC-BITAND
                              (width (width-of-svex x))
                              (y (svex-eval x env-term))
                              (x other)))
             :in-theory (e/d () ()))))))

;; (local
;;  (svex-eval-lemma-tmpl
;;   (defthm svexl-eval-of-reduce-lemma-for-integerp-of-svex
;;     (implies (and ;;(INTEGERP-OF-SVEX (SVEX-REDUCE-W/-ENV-MASKED svex START SIZE)) ;; redundant for trigger
;;                   (integerp (svex-eval (SVEX-REDUCE-W/-ENV-MASKED svex START SIZE) env))
;;                   (natp start)
;;                   (natp size)
;;                   (equal (svex-eval (SVEX-REDUCE-W/-ENV-MASKED svex START SIZE) env)
;;                          (4vec-part-select start size (svex-eval svex env))))
;;              (integerp (4vec-part-select start size (svex-eval svex env)))))))


(encapsulate nil
  (local
   (in-theory (disable acl2::logmask
                       integer-length
                       (:definition acl2::apply$-badgep)
                       svex-eval$-svex-reduce-w/-env-apply-correct-when-returns-4vec-p
                       svex-eval-svex-reduce-w/-env-apply-correct-when-returns-4vec-p
                       sv::svex-apply$-is-svex-apply
                       (:definition rp::eval-and-all)
                       (:rewrite
                        acl2::simplify-products-gather-exponents-equal)
                       ;;(:rewrite not-consp-hons-assoc-equal)
                       (:rewrite acl2::acl2-numberp-x)
                       (:rewrite acl2::rationalp-x)
                       (:rewrite acl2::apply$-badgep-properties . 1)
                       (:definition hons-assoc-equal)
                       (:definition quotep)
                       (:definition hons-equal)
                       (:definition acl2::weak-apply$-badge-p)
                       (:rewrite acl2::apply$-badgep-properties . 2)
                       (:definition rp-trans)
                       (:rewrite sv::4vec-p-of-car-when-4veclist-p)
                       (:rewrite
                        sv::4veclist-p-of-cdr-when-4veclist-p)
                       (:definition subsetp-equal)
                       (:rewrite sv::4veclist-p-when-not-consp)
                       (:definition rp::is-falist)
                       (:rewrite acl2::natp-when-gte-0)
                       (:rewrite acl2::prefer-positive-addends-equal)
                       ;;(:definition hons-get)
                       (:type-prescription hons-assoc-equal)
                       (:rewrite acl2::simplify-sums-equal)
                       (:rewrite
                        acl2::acl2-number-listp-implies-acl2-numberp)
                       (:rewrite
                        acl2::reduce-additive-constant-equal)
                       (:rewrite
                        acl2::reduce-multiplicative-constant-equal)
                       acl2::equal-of-predicates-rewrite
                       (:rewrite acl2::|(equal c (- x))|)
                       (:rewrite acl2::|(equal (/ x) c)|)
                       (:rewrite acl2::|(equal (/ x) (/ y))|)
                       (:rewrite acl2::|(equal (- x) c)|)
                       (:rewrite acl2::|(equal (- x) (- y))|)
                       ;;                       (:rewrite acl2::o-p-o-infp-car)
                       (:rewrite acl2::reduce-integerp-+)
                       (:rewrite acl2::integerp-minus-x)
                       (:rewrite
                        acl2::integer-listp-implies-integerp)
                       (:meta acl2::meta-integerp-correct)
                       (:type-prescription acl2::apply$-badgep)
                       (:definition rp::trans-list)
                       (:rewrite sv::4vec-p-when-maybe-4vec-p)
                       (:rewrite acl2::apply$-badgep-properties . 3)
                       (:rewrite acl2::reduce-rationalp-+)
                       (:rewrite default-car)
                       (:definition len)
                       (:rewrite acl2::reduce-rationalp-*)
                       (:rewrite acl2::rationalp-minus-x)
                       (:rewrite acl2::reduce-rationalp-*)
                       (:rewrite
                        acl2::rational-listp-implies-rationalp)
                       (:meta acl2::meta-rationalp-correct)
                       (:rewrite sv::4veclist-nth-safe-out-of-bounds)
                       (:rewrite sv::maybe-4vec-p-when-4vec-p)
                       (:rewrite sv::len-of-svexlist-eval)
                       (:linear acl2::apply$-badgep-properties . 1)
                       (:rewrite acl2::natp-when-integerp)
                       (:rewrite sv::4vec->lower-when-2vec-p)
                       (:rewrite acl2::symbol-listp-implies-symbolp)
                       (:rewrite
                        sv::4vec-p-when-member-equal-of-4veclist-p)
                       (:rewrite default-cdr)
                       (:rewrite bitp-implies-4vecp)
                       (:type-prescription natp-implies-svex-p)
                       (:rewrite default-+-2)
                       (:rewrite default-+-1)
                       (:type-prescription equal-len)

                       ;;(:definition natp)
                       ;;(:type-prescription 4vec-p)
                       (:rewrite default-<-2)
                       (:rewrite default-<-1)
                       (:rewrite acl2::fold-consts-in-+)
                       (:rewrite sv::svex-p-when-maybe-svex-p)
                       ;;                       (:rewrite acl2::o-infp->neq-0)
                       (:rewrite sv::maybe-svex-p-when-svex-p)
                       (:type-prescription o-finp)
                       ;;                       (:rewrite acl2::o-first-expt-o-infp)
                       (:rewrite
                        acl2::member-equal-newvar-components-3)
                       (:rewrite acl2::default-less-than-2)
                       acl2::|(equal c (/ x))|

                       rp::falist-consistent-aux
                       rp::eval-and-all

                       (:type-prescription rp::falist-consistent-aux)
                       (:type-prescription 4veclist-nth-safe)
                       (:type-prescription sv::4vec-bit?!)
                       (:type-prescription sv::4vec-?!)
                       (:type-prescription sv::4vec-bit?)
                       (:type-prescription 4vec-?*)
                       (:type-prescription 4vec-?)
                       (:type-prescription sv::4vec-bitxor)
                       (:type-prescription 4vec-bitor)
                       (:type-prescription 4vec-bitand)

                       natp
                       rp::valid-sc
                       (:TYPE-PRESCRIPTION ACL2::BINARY-OR*)

                       ACL2::OR*-TRUE-FIRST
                       ACL2::OR*-TRUE-SECOND
                       ACL2::OR*-FORWARD
                       (:TYPE-PRESCRIPTION ACL2::BINARY-AND*)
                       (:REWRITE-QUOTED-CONSTANT
                        SV::MAYBE-4VEC-FIX-UNDER-MAYBE-4VEC-EQUIV)
                       (:REWRITE-QUOTED-CONSTANT
                        SV::4VEC-FIX-UNDER-4VEC-EQUIV)
                       )))

  (svex-eval-lemma-tmpl
   (with-output
     :off :All
     :on (error summary)

     (defret-mutual svex-eval-of-svex-reduce-w/-env-correct

       (defret svex-eval-of-svex-and/or/xor-reduce-w/-env-masked-correct
         (implies (and (svex-p svex)
                       (natp start)
                       (natp size)
                       (rp::rp-term-listp context)
                       (rp::valid-sc env-term a)
                       (rp::eval-and-all context a)
                       (sub-alistp env big-env)
                       (rp::falist-consistent-aux big-env env-term)
                       (:@ :dollar-eval
                           (width-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->width-extns config))
                           (integerp-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->integerp-extns config)))
                       (:@ :normal-eval
                           (equal (svex-reduce-config->width-extns config) nil)
                           (equal (svex-reduce-config->integerp-extns config) nil))

                       ;; if not keeping env-vars, then big-env and env should
                       ;; be the same.
                       (or* (svex-reduce-config->keep-missing-env-vars config)
                            (equal env big-env))
                       )
                  (and (equal (svex-eval (svex-and/or/xor-reduce-w/-env-masked svex start size) (rp-evlt env-term a))
                              (4vec-part-select start size (svex-eval svex (rp-evlt env-term a))))

                       #|(implies (or (acl2::and* (acl2::or* (equal (car svex) 'bitor)
                       (equal (car svex) 'bitand) ; ; ;
                       (equal (car svex) 'bitxor)) ; ; ;
                       (equal-len (cdr svex) 2)) ; ; ;
                       (acl2::and* (equal (car svex) 'sv::unfloat) ; ; ;
                       (equal-len (cdr svex) 1))) ; ; ;
; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ; ;
                       (all-xor/and/or-nodes-are-masked-p res size (rp-evlt env-term a)))|#
                       ))
         :fn svex-and/or/xor-reduce-w/-env-masked)

       (defret svex-eval-of-svex-reduce-w/-env-masked-correct
         (implies (and (svex-p svex)
                       (natp start)
                       (natp size)
                       (rp::rp-term-listp context)
                       (rp::valid-sc env-term a)
                       (rp::eval-and-all context a)
                       (sub-alistp env big-env)
                       (rp::falist-consistent-aux big-env env-term)
                       (:@ :dollar-eval
                           (width-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->width-extns config))
                           (integerp-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->integerp-extns config)))
                       (:@ :normal-eval
                           (equal (svex-reduce-config->width-extns config) nil)
                           (equal (svex-reduce-config->integerp-extns config) nil))
                       (or* (svex-reduce-config->keep-missing-env-vars config)
                            (equal env big-env)))
                  (and (equal (svex-eval (svex-reduce-w/-env-masked svex start size) (rp-evlt env-term a))
                              (4vec-part-select start size (svex-eval svex (rp-evlt env-term a))))

                       #|(implies (or (acl2::and* (acl2::or* (equal (car svex) 'bitor)
                       (equal (car svex) 'bitand) ; ; ;
                       (equal (car svex) 'bitxor)) ; ; ;
                       (equal-len (cdr svex) 2)) ; ; ;
                       (acl2::and* (equal (car svex) 'sv::unfloat) ; ; ;
                       (equal-len (cdr svex) 1))) ; ; ;
                       (all-xor/and/or-nodes-are-masked-p res size (rp-evlt env-term a)))|#))
         :fn svex-reduce-w/-env-masked)

       (defret svex-eval-of-svex-reduce-w/-env-unmasked-bitand-correct
         (implies (and (svex-p svex)
                       (rp::rp-term-listp context)
                       (rp::valid-sc env-term a)
                       (rp::eval-and-all context a)
                       (sub-alistp env big-env)
                       (rp::falist-consistent-aux big-env env-term)
                       (:@ :dollar-eval
                           (width-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->width-extns config))
                           (integerp-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->integerp-extns config)))
                       (:@ :normal-eval
                           (equal (svex-reduce-config->width-extns config) nil)
                           (equal (svex-reduce-config->integerp-extns config) nil))
                       (or* (svex-reduce-config->keep-missing-env-vars config)
                            (equal env big-env)))
                  (equal (svex-eval (svex-reduce-w/-env-unmasked-bitand svex)
                                    (rp-evlt env-term a))
                         (svex-eval svex (rp-evlt env-term a))))
         :fn svex-reduce-w/-env-unmasked-bitand)

       (defret svex-eval-of-svex-reduce-w/-env-correct
         (implies (and (svex-p svex)
                       (rp::rp-term-listp context)
                       (rp::valid-sc env-term a)
                       (rp::eval-and-all context a)
                       (sub-alistp env big-env)
                       (rp::falist-consistent-aux big-env env-term)
                       (:@ :dollar-eval
                           (width-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->width-extns config))
                           (integerp-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->integerp-extns config)))
                       (:@ :normal-eval
                           (equal (svex-reduce-config->width-extns config) nil)
                           (equal (svex-reduce-config->integerp-extns config) nil))
                       (or* (svex-reduce-config->keep-missing-env-vars config)
                            (equal env big-env)))
                  (equal (svex-eval (svex-reduce-w/-env svex) (rp-evlt env-term a))
                         (svex-eval svex (rp-evlt env-term a))))
         :fn svex-reduce-w/-env)
       (defret svex-eval-of-svex-reduce-w/-env-lst-correct
         (implies (and (svexlist-p svex-list)
                       (rp::rp-term-listp context)
                       (rp::valid-sc env-term a)
                       (rp::eval-and-all context a)
                       (sub-alistp env big-env)
                       (rp::falist-consistent-aux big-env env-term)
                       (:@ :dollar-eval
                           (width-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->width-extns config))
                           (integerp-of-svex-extn-correct<$>-lst
                            (svex-reduce-config->integerp-extns config)))
                       (:@ :normal-eval
                           (equal (svex-reduce-config->width-extns config) nil)
                           (equal (svex-reduce-config->integerp-extns config) nil))
                       (or* (svex-reduce-config->keep-missing-env-vars config)
                            (equal env big-env)))
                  (equal (svexlist-eval (svex-reduce-w/-env-lst svex-list) (rp-evlt env-term a))
                         (svexlist-eval svex-list (rp-evlt env-term a))))
         :fn svex-reduce-w/-env-lst)
       :mutual-recursion svex-reduce-w/-env
       ;;:otf-flg t
       :hints (("Goal"
                :do-not-induct t

                :expand ((:free (x y)
                                (natp (+ x y)))
                         (SVEX-REDUCE-W/-ENV SVEX)
                         (svex-eval svex (rp-evlt env-term a))
                         (svex-eval (cons (car svex)
                                          (svex-reduce-w/-env-lst (cdr svex)))
                                    env-term)
                         (:free (x y) (4vec-p (cons x y)))
                         (:free (x y) (4VECLIST-NTH-SAFE x y))
                         (:free (x y) (nth x y))
                         (:free (x) (sv::svex-apply 'partsel x))
                         (:free (x) (sv::svex-apply 'concat x))
                         (:free (args) (sv::svex-apply 'sv::unfloat args))
                         (:free (args) (sv::svex-apply 'sv::signx args))
                         (:free (args) (sv::svex-apply 'sv::zerox args))
                         (:free (args) (sv::svex-apply 'sv::rsh args))
                         (:free (args) (sv::svex-apply 'sv::lsh args))
                         (:free (args) (sv::svex-apply 'sv::bit? args))
                         (:free (args) (sv::svex-apply 'sv::bitnot args))
                         (:free (args) (sv::svex-apply 'sv::bitand args))
                         (:free (args) (sv::svex-apply 'sv::bitor args))
                         (:free (args) (sv::svex-apply 'sv::bitxor args))
                         (:free (args) (sv::svex-apply 'sv::res args))
                         (:free (args) (sv::svex-apply 'sv::?* args))
                         (:free (args) (sv::svex-apply 'sv::?! args))
                         (:free (args) (sv::svex-apply 'sv::? args))
                         (:free (args) (sv::svex-apply 'sv::bit?! args))
                         (:free (args) (sv::svex-apply 'sv::partinst args)))
                :in-theory (e/d
                            (;;pull-out-part-select-from-4vec-bitand

                             min-width

                             ;;move-over-part-select-from-4vec-bitand

                             svex-eval-svex-reduce-w/-env-apply-correct-when-returns-4vec-P
                             svex-reduce-w/-env-masked
                             svex-reduce-w/-env-unmasked-bitand
                             svex-and/or/xor-reduce-w/-env-masked
                             sv::svex-quote->val
                             svex-env-lookup-when-svex-p
                             4vec-part-select-of-4vec-bitnot-reverse
                             4vec-concat-with-0-to-4vec-part-select
                             4vec-part-select-of-4vec-bitxor-better
                             4vec-part-select-of-4vec-bitor-better
                             4vec-part-select-of-4vec-bitand-better
                             svex-eval-when-entry-is-absent
                             when-entry-is-present-but-not-4vec-p
                             ;;convert-4vec-concat-to-4vec-concat$
                             ;;4vec-concat-insert-4vec-part-select
                             4vec-concat-insert-4vec-part-select-local
                             ;;4vec-concat-insert-4vec-part-select-to-concat$
                             ;; 4vec-concat-of-4vec-part-select-same-size
                             svex-reduce-w/-env
                             svex-call->fn
                             svex-call->args
                             svex-kind
                             bits
                             ;;svex-env-lookup-when-svex-p
                             svex-reduce-w/-env-lst

                             4vec-concat$-of-term2=0

                             4vec-sign-ext-to-4vec-concat)
                            ())))))))

(svex-eval-lemma-tmpl
 (defret svex-alist-eval-of-svex-alist-reduce-w/-env-correct
   (implies (and (sv::svex-alist-p svex-alist)
                 (rp::rp-term-listp context)
                 (rp::valid-sc env-term a)
                 (rp::eval-and-all context a)
                 (sub-alistp env big-env)
                 (rp::falist-consistent-aux big-env env-term)
                 (:@ :dollar-eval
                     (width-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->width-extns config))
                     (integerp-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->integerp-extns config)))
                 (:@ :normal-eval
                     (equal (svex-reduce-config->width-extns config) nil)
                     (equal (svex-reduce-config->integerp-extns config) nil))
                 (or* (svex-reduce-config->keep-missing-env-vars config)
                      (equal env big-env)))
            (equal (svex-alist-eval res-alist (rp-evlt env-term a))
                   (svex-alist-eval svex-alist (rp-evlt env-term a))))
   :fn svex-alist-reduce-w/-env
   :hints (("Goal"
            :do-not-induct t
            :induct (svex-alist-reduce-w/-env svex-alist)
            :in-theory (e/d (svex-alist-reduce-w/-env
                             sv::svex-alist-eval)
                            ())))))

(svex-eval-lemma-tmpl
 (defret svex-alist-eval-of-svex-alist-reduce-w/-env-correct-2
   (implies (and (sv::svex-alist-p svex-alist)
                 (rp::rp-term-listp context)
                 (rp::valid-sc env-term a)
                 (rp::eval-and-all context a)
                 (force (rp::falist-consistent-aux env env-term))
                 (:@ :dollar-eval
                     (width-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->width-extns config))
                     (integerp-of-svex-extn-correct<$>-lst
                      (svex-reduce-config->integerp-extns config)))
                 (:@ :normal-eval
                     (equal (svex-reduce-config->width-extns config) nil)
                     (equal (svex-reduce-config->integerp-extns config) nil)))
            (equal (svex-alist-eval res-alist (rp-evlt env-term a))
                   (svex-alist-eval svex-alist (rp-evlt env-term a))))
   :fn svex-alist-reduce-w/-env
   :hints (("Goal"
            :do-not-induct t
            :use ((:instance
                   svex-alist-eval-of-svex-alist-reduce-w/-env-correct
                   (big-env env)))
            :in-theory (e/d ()
                            ())))))

;;;;;;


(define add-quotes-to-4vec-values-in-alist ((x alistp))
  (if (atom x)
      nil
    (acons (caar x)
           (if (sv::4vec-p (cdar x))
               (list 'quote (cdar x))
             (cdar x))
           (add-quotes-to-4vec-values-in-alist (cdr x)))))

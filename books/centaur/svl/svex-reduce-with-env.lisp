; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2021 Centaur Technology
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

(include-book "4vec-lemmas")

(include-book "bits-sbits")


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


(define nth-4vec (n argsvar)
  :guard (natp n)
  (if (atom argsvar)
      (SV::4VEC-X)
      (if (zp n)
          (car argsvar)
          (nth-4vec (1- n) (cdr argsvar))))
  ///
  (defthm nth-4vec-opener
      (implies (natp n)
               (equal (nth-4vec n argsvar)
                      (if (atom argsvar)
                          (SV::4VEC-X)
                          (if (zp n)
                              (car argsvar)
                              (nth-4vec (1- n) (cdr argsvar))))))
    :hints (("Goal"
             :in-theory (e/d (nth-4vec) ())))))

(defund svex-apply-constants-collect-arg-meta (n max argsvar)
  (declare (xargs :measure (nfix (- (nfix max) (nfix n)))))
  (let* ((n (nfix n)) (max (nfix max)))
    (if (zp (- max n))
        nil
        (b* ((rest (svex-apply-CONSTANTS-collect-arg-meta (+ 1 n) max argsvar)))
          (cons `(nth-4vec ,n ,argsvar) rest)))))

(defund svex-apply-constant-cases-fn (argsvar optable)
  (b* (((when (atom optable))
        '((otherwise
           (or (hard-error
                'svex-apply-cases-wog-fn-meta
                "attempting to apply unknown function ~x0~%"
                (list (cons #\0 fn)))
            (sv::4vec-x)))))
       ((list sym fn args) (car optable))
       (entry-for-quoted
        (svex-apply-CONSTANTS-collect-arg-meta 0 (len args) argsvar ))
       (call
        `(,fn . ,entry-for-quoted)))
    (cons (cons sym (cons call 'nil))
          (svex-apply-constant-cases-fn argsvar (cdr optable)))))

(define equal-len (lst (size natp))
  (if (zp size)
      (atom lst)
      (and (not (atom lst))
           (equal-len (cdr lst)
                      (1- size))))
  ///

  (defthmd equal-len-opener
      (implies (not (zp size))
               (equal (equal-len lst size)
                      (and (not (atom lst))
                           (equal-len (cdr lst)
                                      (1- size))))))

   (defthmd equal-len-opener-size-0
      (implies t
               (equal (equal-len lst 0)
                      (atom lst))))
   
  (defthm equal-len-4-implies
      (implies (equal-len lst 4)
               (and (consp lst)
                    (consp (cdr lst))
                    (consp (cddr lst))
                    (consp (cdddr lst))
                    (atom (cddddr lst))))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (equal-len-opener
                              equal-len-opener-size-0)
                             ()))))

  (defthm equal-len-3-implies
      (implies (equal-len lst 3)
               (and (consp lst)
                    (consp (cdr lst))
                    (consp (cddr lst))
                    (atom (cdddr lst))))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (equal-len-opener
                              equal-len-opener-size-0)
                             ()))))

  (defthm equal-len-2-implies
      (implies (equal-len lst 2)
               (and (consp lst)
                    (consp (cdr lst))
                    (atom (cddr lst))))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (equal-len-opener
                              equal-len-opener-size-0)
                             ()))))

  (defthm equal-len-1-implies
      (implies (equal-len lst 1)
               (and (consp lst)
                    (atom (cdr lst))))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (equal-len-opener
                              equal-len-opener-size-0)
                             ()))))

  (defthm equal-len-0-implies
      (implies (equal-len lst 0)
               (and (atom lst)))
    :rule-classes :forward-chaining
    :hints (("Goal"
             :in-theory (e/d (equal-len-opener
                              equal-len-opener-size-0)
                             ())))))

(defun hons-list-macro (acl2::lst)
  (declare (xargs :guard t))
  (if (consp acl2::lst)
      (cons 'hons
            (cons (car acl2::lst)
                  (cons (hons-list-macro (cdr acl2::lst))
                        nil)))
      nil))

(DEFMACRO hons-LIST (&REST ARGS)
  (hons-list-macro ARGS))

;; (define bit?!-resolve ((test sv::4vec-p) then else (shift-amount natp))
;;   (cond ((equal test -1) then)
;;         ((or (equal test 0)
;;              (equal test (sv::4vec-x))
;;              (equal test (sv::4vec-z)))
;;          else)
;;         (t
;;          (if (equal (4vec-part-select 0 1 test) 1)
;;              (hons-list
;;               'sv::concat 1

(define calc-bit-repetition ((the-bit sv::4vec-p)
                             (num sv::4vec-p)
                             (limit natp))
  :measure (nfix limit)
  :returns (res natp)
  (cond ((zp limit) 0)
        ((not (equal (4vec-part-select 0 1 num)
                     (4vec-part-select 0 1 the-bit)))
         0)
        (t (b* ((rest (calc-bit-repetition the-bit
                                           (4vec-rsh 1 num)
                                           (1- limit))))
             (1+ rest)))))

(local
 (defthm SV::4VEC->UPPER-and-lower-equivalance
     (implies (integerp x)
              (equal (SV::4VEC->lower x)
                     (SV::4VEC->UPPER x)))
   :hints (("Goal"
            :in-theory (e/d (SV::4VEC->UPPER
                             SV::4VEC->lower
                             ) ())))))

;; (local
;;  (use-arithmetic-5 t))

;; (local
;;  (defthm dummy-lemma
;;      (implies (and (EQUAL (SV::4VEC->LOWER TEST) x)
;;                    (EQUAL (SV::4VEC->UPPER TEST) x)
;;                    (4vec-p test))
;;               (equal test x))
;;    :rule-classes :forward-chaining
;;    :hints (("Goal"
;;             :in-theory (e/d (SV::4VEC->LOWER
;;                              4VEC-P
;;                              SV::4VEC->UPPER)
;;                             ())))))


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

(define bit?-resolve ((test 4vec-p)
                       then
                       else
                      (limit natp))
  
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (4vec-rsh
                            4VEC-P
                            sv::3vec-p
                            SV::4VEC->LOWER
                            SV::4VEC->upper
                            4vec-shift-core)
                           (4vec))))
  :measure (nfix limit)
  :returns (res svex-p :hyp (and (4vec-p test)
                                 (svex-p then)
                                 (svex-p else)))
  (cond
    ((zp limit) (hons-list 'sv::bit? test then else)) ;; for measure
    ((equal test -1) then)
    ((or (equal test 0))
     else)
    ((or (equal test (sv::4vec-x))
         (equal test (sv::4vec-z)))
     (if (and (4vec-p test) (4vec-p then) (4vec-p else))
         (sv::4vec-bit? test then else)
         (hons-list 'sv::bit? test then else)))
    (t
     (b* ((first-size (calc-bit-repetition test test (expt 2 30)))
          ((unless (posp first-size)) ;; should never happen
           `(sv::bit? ,test ,then ,else))
          (test-cut (4vec-part-select 0 first-size test)) 
          (rest (bit?-resolve (4vec-rsh first-size test)
                              (if (4vec-p then)
                                  (4vec-rsh first-size then)
                                  (hons-list 'sv::rsh first-size then))
                              (if (4vec-p else)
                                  (4vec-rsh first-size else)
                                  (hons-list 'sv::rsh first-size else))
                              (1- limit))))
       (cond ((equal test-cut 0)
              (if (and (4vec-p else)
                       (4vec-p rest))
                  (4vec-concat first-size else rest)
                  (hons-list 'sv::concat first-size else rest)))
             ((equal test-cut (4vec-part-select 0 first-size -1))
              (if (and (4vec-p then)
                       (4vec-p rest))
                  (4vec-concat first-size then rest)
                  (hons-list 'sv::concat first-size then rest)))
             (t
              (if (and (4vec-p else)
                       (4vec-p then)
                       (4vec-p rest))
                  (4vec-concat first-size (sv::4vec-bit? test-cut then else) rest)
                  (hons-list 'sv::concat
                             first-size
                             (hons-list 'sv::bit? test-cut then else)
                             rest))))))))

(define bit?!-resolve ((test sv::4vec-p)
                       then
                       else
                       (limit natp))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d (4vec-rsh
                            4VEC-P
                            SV::4VEC->LOWER
                            SV::4VEC->upper
                            4vec-shift-core)
                           (4vec))))
  :measure (nfix limit)
  :returns (res svex-p :hyp (and (4vec-p test)
                                 (svex-p then)
                                 (svex-p else)))
  (cond
    ((zp limit) (hons-list 'sv::bit?! test then else)) ;; for measure
    ((equal test -1) then)
    ((or (equal test 0)
         (equal test (sv::4vec-x))
         (equal test (sv::4vec-z)))
     else)
    (t
     (b* ((first-size (calc-bit-repetition test test (expt 2 30)))
          ((unless (posp first-size)) ;; should never happen
           `(sv::bit?! ,test ,then ,else))
          (test-cut (4vec-part-select 0 first-size test))
          (rest (bit?!-resolve (4vec-rsh first-size test)
                               (if (4vec-p then)
                                   (4vec-rsh first-size then)
                                   (hons-list 'sv::rsh first-size then))
                               (if (4vec-p else)
                                   (4vec-rsh first-size else)
                                   (hons-list 'sv::rsh first-size else))
                               (1- limit))))
       (cond ((or (equal test-cut (4vec-part-select 0 first-size (sv::4vec-x)))
                  (equal test-cut (4vec-part-select 0 first-size (sv::4vec-z)))
                  (equal test-cut 0))
              (if (and (4vec-p else)
                       (4vec-p rest))
                  (4vec-concat first-size else rest)
                  (hons-list 'sv::concat first-size else rest)))
             ((equal test-cut (4vec-part-select 0 first-size -1))
              (if (and (4vec-p then)
                       (4vec-p rest))
                  (4vec-concat first-size then rest)
                  (hons-list 'sv::concat first-size then rest)))
             (t ;; should never come here
              `(sv::bit?! ,test ,then ,else)))))))


(local
 (defthm svex-p-of-fn-call-reconstructed
     (implies (AND (FNSYM-P FN)
                   (SVEXLIST-P ARGS))
              (SVEX-P (CONS FN ARGS)))
   :hints (("Goal"
            :in-theory (e/d (SVEX-P) ())))))

(define svex-reduce-w/-env-apply-specials (fn args)
  :returns (res svex-p :hyp (and (FNSYM-P fn)
                                 (SVEXLIST-P args)))
  (cond
    ((and (or (equal fn 'sv::?)
              (equal fn 'sv::?*))
          (equal-len args 3))
     (b* ((test (first args))
          ((unless (4vec-p test)) (hons fn args))
          (test (sv::3vec-fix test))
          (then (second args))
          (else (third args))
          ((sv::4vec test))
          ((when (eql test.upper 0))
           else)
          ((when (not (eql test.lower 0)))
           then))
       (hons fn args)))

    ((and (equal fn 'sv::?!)
          (equal-len args 3))
     (b* ((test (first args))
          ((unless (4vec-p test)) (hons fn args))
          ((sv::4vec test))
          (testvec (logand test.upper test.lower))
          ((when (eql testvec 0)) (third args)))
       (second args)))

    ((and (equal fn 'sv::bit?)
          (equal-len args 3))
     (b* ((test (first args))
          ((unless (4vec-p test)) (hons fn args))
          (test (sv::3vec-fix test))
          ((when (eql test 0))
           (third args))
          ((when (eql test -1))
           (second args)))
       (bit?-resolve (sv::3vec-fix test) (second args) (third args) (expt 2 30))))

    ((and (equal fn 'sv::bit?!)
          (equal-len args 3))
     (b* ((test (first args))
          ((unless (4vec-p test)) (hons fn args))
          ((when (eql test -1))
           (second args))
          ((sv::4vec test))
          ((when (eql (logand test.upper test.lower) 0))
           (third args)))
       (bit?!-resolve test (second args) (third args) (expt 2 30))))

    ((and (equal fn 'sv::bitand)
          (equal-len args 2))
     (if (or (equal (first args) 0)
             (equal (second args) 0))
         0
         (hons fn args)))

    ((and (equal fn 'sv::bitor)
          (equal-len args 2))
     (if (or (equal (first args) -1)
             (equal (second args) -1))
         -1
         (hons fn args)))

    (t (hons fn args))))

(defmacro svex-apply-constant-cases (fn args)
  `(b* ((quoted (sv::4veclist-p args))
        ((when quoted)
         (case ,fn
           ,@(svex-apply-constant-cases-fn args
                                           (cons '(ID sv::4VEC-FIX$INLINE (ACL2::X)
                                                   "identity function") ;; had to
                                                 ;; change this because 4vec-fix is
                                                 ;; the only function that is inlined
                                                 (cdr
                                                  sv::*svex-op-table*))))))
     (svex-reduce-w/-env-apply-specials
      ,fn ,args)))

(define svex-reduce-w/-env-apply (fn args)
  :guard (true-listp args)
  :returns (res svex-p :hyp (and (FNSYM-P fn)
                                 (SVEXLIST-P args)))
  (let* ((fn (fnsym-fix fn)))
    (svex-apply-constant-cases fn args)))

(verify-guards svex-reduce-w/-env-apply
    :hints (("Goal"
             :do-not-induct t
             :in-theory (e/d () ()))))


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

#|(encapsulate
    (((example-env) => *))
    (local
     (defun example-env () nil)))|#


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



(with-output
    :off :All
  :on (error summary)
  
  (defines svex-reduce-w/-env
      :flag-defthm-macro defthm-svex-reduce-with-env-meta
      :flag-local nil
      :hints (("Goal"
               :in-theory (e/d (svex-kind
                                measure-lemmas) ())))
      :prepwork ((local
                  (in-theory (enable svex-kind-wog))))

      (define svex-reduce-w/-env-masked ((svex svex-p)
                                         (start natp)
                                         (size natp)
                                         env)
        :measure (cons-count svex)
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
                  ((unless (consp val)) (4vec-part-select start size (sv::4vec-x)))
                  (val (cdr val))
                  ((when (and (quotep val)
                              (consp (cdr val))
                              (4vec-p (unquote val))))
                   (4vec-part-select start size (unquote val))))
               (svex-reduce-w/-env-masked-return svex)))
            (otherwise
             (b* ((fn (car svex))
                  (args (cdr svex)))
               (cond
                 ((and (equal fn 'sv::partsel)
                       (equal-len args 3))
                  (b* ((start2 (svex-reduce-w/-env (first args) env))
                       (size2 (svex-reduce-w/-env (second args) env))
                       ((unless (and (natp start2) (natp size2)))
                        (b* ((third (svex-reduce-w/-env (third args) env)))
                          (if (and (4vec-p start2) (4vec-p size2) (4vec-p third))
                              (4vec-part-select start size
                                                (4vec-part-select start2 size2 third))
                              (svex-reduce-w/-env-masked-return
                               (hons-list 'sv::partsel start2 size2 third))))))
                    (if (< start size2)
                        (svex-reduce-w/-env-masked (third args)
                                                   (+ start start2)
                                                   (min size (- size2 start))
                                                   env)
                        0)))
                 ((and (equal fn 'sv::zerox)
                       (equal-len args 2))
                  (b* ((c-size (svex-reduce-w/-env (first args) env))
                       (term1 (second args))
                       ((unless (natp c-size))
                        (b* ((term1 (svex-reduce-w/-env term1 env)))
                          (svex-reduce-w/-env-masked-return
                           (svex-reduce-w/-env-apply fn (hons-list c-size term1)))))
                       ((when (<= c-size start))
                        0)
                       ((when (and (< start c-size)
                                   (< c-size (+ start size))))
                        (b* ((term1 (svex-reduce-w/-env-masked term1
                                                               start
                                                               (- c-size start)
                                                               env)))
                          term1))
                       ((when (<= (+ start size) c-size))
                        (svex-reduce-w/-env-masked term1 start size env)))
                    (svex-reduce-w/-env-apply fn ;; should never come here. 
                                              (hons-list c-size
                                                         (svex-reduce-w/-env
                                                          term1 env)))))
                 ((and (equal fn 'sv::signx)
                       (equal-len args 2))
                  (b* ((s-size (svex-reduce-w/-env (first args) env))
                       (term1 (second args))
                       ((unless (natp s-size))
                        (b* ((term1 (svex-reduce-w/-env term1 env)))
                          (svex-reduce-w/-env-masked-return
                           (svex-reduce-w/-env-apply fn (hons-list s-size
                                                                   term1)))))
                       ((when (equal s-size 0))
                        (sv::4vec-part-select 0 size (sv::4vec-x)))
                       ((when (<= s-size start)) ;; only signextend bit repeated
                        (b* ((term1 (svex-reduce-w/-env-masked term1
                                                               (1- s-size)
                                                               1
                                                               env))
                             (start 0))
                          (svex-reduce-w/-env-masked-return
                           (svex-reduce-w/-env-apply fn (hons-list 1 term1))))) 
                       ((when (and (< start s-size)
                                   (< s-size (+ start size))))
                        (b* ((term1 (svex-reduce-w/-env-masked term1
                                                               start
                                                               (- s-size start)
                                                               env))
                             (new-s-size (- s-size start))
                             (start 0))
                          (svex-reduce-w/-env-masked-return
                           (svex-reduce-w/-env-apply fn (hons-list new-s-size term1)))))
                       ((when (<= (+ start size) s-size))
                        (svex-reduce-w/-env-masked term1 start size env)))
                    (svex-reduce-w/-env-apply fn ;; should never come here. 
                                              (hons-list s-size
                                                         (svex-reduce-w/-env term1 env)))))
                 ((and (equal fn 'sv::concat)
                       (equal-len args 3))
                  (b* ((c-size (svex-reduce-w/-env (first args) env))
                       (term1 (second args))
                       (term2 (third args))
                       ((unless (natp c-size))
                        (b* ((term1 (svex-reduce-w/-env term1 env))
                             (term2 (svex-reduce-w/-env term2 env)))
                          (if (and (4vec-p c-size) (4vec-p term1) (4vec-p term2))
                              (4vec-part-select start size
                                                (4vec-concat c-size term1 term2))
                              (svex-reduce-w/-env-masked-return
                               (hons-list 'sv::concat c-size term1 term2)))))
                       ((when (<= c-size start))
                        (svex-reduce-w/-env-masked term2
                                                   (- start c-size)
                                                   size
                                                   env))
                       ((when (and (< start c-size)
                                   (< c-size (+ start size))))
                        (b* ((term1 (svex-reduce-w/-env-masked term1
                                                               start
                                                               (- c-size start)
                                                               env))
                             (term2 (svex-reduce-w/-env-masked term2
                                                               0
                                                               (- size (- c-size start))
                                                               env)))
                          (svex-reduce-w/-env-apply fn
                                                    (hons-list (- c-size start)
                                                               term1 term2))))
                       ((when (<= (+ start size) c-size))
                        (svex-reduce-w/-env-masked term1 start size env)))
                    (hons-list 'sv::concat c-size ;; should never come to this case
                               (svex-reduce-w/-env-masked term1 0 c-size env)
                               (svex-reduce-w/-env term2 env))))
                 ((and (equal fn 'sv::lsh)
                       (equal-len args 2))
                  (b* ((lsh-size (svex-reduce-w/-env (first args) env))
                       (term (second args))
                       ((unless (natp lsh-size))
                        (b* ((term (svex-reduce-w/-env term env)))
                          (svex-reduce-w/-env-masked-return
                           (svex-reduce-w/-env-apply fn (hons-list lsh-size
                                                                   term)))))
                       ((when (>= start lsh-size))
                        (svex-reduce-w/-env-masked term
                                                   (+ start (- lsh-size))
                                                   size
                                                   env))
                       ((when (>= lsh-size (+ start size)))
                        0)
                       (term (svex-reduce-w/-env-masked term
                                                        0
                                                        (+ size (- (+ lsh-size (- start))))
                                                        env)))
                    (svex-reduce-w/-env-apply fn
                                              (hons-list (+ lsh-size (- start)) term))))
                 ((and (equal fn 'sv::rsh)
                       (equal-len args 2))
                  (b* ((rsh-size (svex-reduce-w/-env (first args) env))
                       (term (second args))
                       ((unless (natp rsh-size))
                        (b* ((term (svex-reduce-w/-env term env)))
                          (if (and (4vec-p rsh-size) (4vec-p term))
                              (4vec-part-select start size
                                                (4vec-rsh rsh-size term))
                              (svex-reduce-w/-env-masked-return
                               (hons-list 'sv::rsh rsh-size term))))))
                    (svex-reduce-w/-env-masked term (+ start rsh-size) size
                                               env)))
                 ((and (or (equal fn 'sv::bitor)
                           (equal fn 'sv::bitand)
                           (equal fn 'sv::bitxor))
                       (equal-len args 2))
                  (b* ((term1 (svex-reduce-w/-env-masked (first args) start size env))
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
                    (svex-reduce-w/-env-apply fn (hons-list term1 term2))))

                 ((and (equal fn 'sv::bitnot)
                       (equal-len args 1))
                  (b* ((term1 (svex-reduce-w/-env-masked (first args) start size
                                                         env))
                       (start 0)
                       (res
                        (svex-reduce-w/-env-masked-return
                         (svex-reduce-w/-env-apply fn (hons-list term1)))))
                    res))

                 ((and (equal fn 'sv::res)
                       (equal-len args 2))
                  (b* ((term1 (svex-reduce-w/-env-masked (first args) start size env))
                       ((when (equal term1 (4vec-part-select 0 size
                                                             (sv::4vec-x))))
                        term1)
                       (term2 (svex-reduce-w/-env-masked (second args) start size env))
                       ((when (equal term2 (4vec-part-select 0 size (sv::4vec-x))))
                        term2))
                    (cond ((equal term1 (4vec-part-select 0 size (sv::4vec-z)))
                           term2)
                          ((equal term2 (4vec-part-select 0 size (sv::4vec-z)))
                           term1)
                          (t
                           (svex-reduce-w/-env-apply fn (hons-list term1 term2))))))

                 ((and (or ;; can use improvements here....
                        (equal fn 'sv::?!))
                       (equal-len args 3))
                  (b* ((test (svex-reduce-w/-env (first args) env))
                       (term1 (svex-reduce-w/-env-masked (second args) start size env))
                       (term2 (svex-reduce-w/-env-masked (third args) start size env)))
                    (svex-reduce-w/-env-apply fn (hons-list test term1 term2))))


                 ((and (or (equal fn 'sv::?) ;; can use improvements here....
                           (equal fn 'sv::?*))
                       (equal-len args 3))
                  (b* ((test (svex-reduce-w/-env (first args) env))
                       ((when (4vec-p test))
                        (b* ((test (sv::3vec-fix test))
                             (then (second args))
                             (else (third args))
                             ((sv::4vec test))
                             ((when (eql test.upper 0))
                              (svex-reduce-w/-env-masked else start size env))
                             ((when (not (eql test.lower 0)))
                              (svex-reduce-w/-env-masked then start size env))
                             (else (svex-reduce-w/-env-masked else start size env))
                             ((when (equal else (sv::4vec-part-select 0 size (sv::4vec-x))))
                              else)
                             (then (svex-reduce-w/-env-masked then start size env))
                             ((when (equal then (sv::4vec-part-select 0 size (sv::4vec-x))))
                              then))
                          (svex-reduce-w/-env-apply fn (hons-list test then else))))
                       (term1 (svex-reduce-w/-env-masked (second args) start size env))
                       (term2 (svex-reduce-w/-env-masked (third args) start size env)))
                    (svex-reduce-w/-env-apply fn (hons-list test term1 term2))))

                 ((and (equal fn 'sv::partinst)
                       (equal-len args 4))
                  (b* ((s-start (svex-reduce-w/-env (first args) env))
                       (s-size (svex-reduce-w/-env (second args) env))
                       (old-term (third args))
                       (term (fourth args)))
                    (cond ((or (not (natp s-start))
                               (not (natp s-size)))
                           (b* ((old-term (svex-reduce-w/-env old-term env))
                                (term (svex-reduce-w/-env term env)))
                             (if (and (4vec-p s-start) (4vec-p s-size)
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
                          ((or (<= (+ start size) s-start) ;;case5
                               (<= (+ s-start s-size) start))
                           (svex-reduce-w/-env-masked old-term start size env))
                          ((and (<= (+ start size) ;;case4
                                    (+ s-start s-size))
                                (<= s-start start))
                           (svex-reduce-w/-env-masked term (- start s-start)
                                                      size env))
                          ((and (< start s-start) ;;case 3
                                (< s-start (+ start size))
                                (<= (+ start size)
                                    (+ s-start s-size)))
                           (b* ((term1 (svex-reduce-w/-env-masked
                                        old-term start (- s-start start) env))
                                (term2 (svex-reduce-w/-env-masked
                                        term 0 (+ start size (- s-start)) env)))
                             (if (and (4vec-p term1) (4vec-p term2))
                                 (4vec-concat (- s-start start) term1 term2)
                                 (hons-list 'sv::concat
                                            (- s-start start)
                                            term1
                                            term2))))
                          ((and (<= s-start start) ;;case 2
                                (< start (+ s-start s-size))
                                (< (+ s-start s-size)
                                   (+ start size)))
                           (b* ((term1 (svex-reduce-w/-env-masked
                                        term (- start s-start)
                                        (+ s-size s-start (- start))
                                        env))
                                (term2 (svex-reduce-w/-env-masked
                                        old-term
                                        (+ s-start s-size)
                                        (+ size start (- (+ s-start s-size)))
                                        env))
                                (c-size (+ s-size s-start (- start))))
                             (if (and (4vec-p term1) (4vec-p term2))
                                 (4vec-concat c-size term1 term2)
                                 (hons-list 'sv::concat c-size term1 term2))))
                          ((and (< start s-start) ;;case 1
                                (< (+ s-start s-size)
                                   (+ start size)))
                           (b* ((c-size1 (- s-start start))
                                (term1 (svex-reduce-w/-env-masked old-term start
                                                                  (- s-start start) env))
                                (c-size2 s-size)
                                (term2 (svex-reduce-w/-env-masked term 0 s-size
                                                                  env))
                                (term3 (svex-reduce-w/-env-masked old-term
                                                                  (+ s-start s-size)
                                                                  (- (+ start size)
                                                                     (+ s-start s-size))
                                                                  env))
                                (m-term2 (if (and (4vec-p term2) (4vec-p term3))
                                             (4vec-concat c-size2 term2 term3)
                                             (hons-list 'sv::concat c-size2 term2 term3)))
                                (mterm1 (if (and (4vec-p term1) (4vec-p m-term2))
                                            (4vec-concat c-size1 term1 m-term2)
                                            (hons-list 'sv::concat c-size1 term1 m-term2))))
                             Mterm1))
                          (t (hons-list 'sv::partinst ;; should never come here.
                                        s-start
                                        s-size
                                        (svex-reduce-w/-env old-term env)
                                        (svex-reduce-w/-env term env))))))
                 ((and (equal fn 'sv::bit?!)
                       (equal-len args 3))
                  (b* ((first (svex-reduce-w/-env-masked (first args)
                                                         start size
                                                         env))
                       ((when (equal first (sv::4vec-part-select start size -1)))
                        (svex-reduce-w/-env-masked (second args)
                                                   start size
                                                   env))
                       ((when (or (equal first 0)
                                  (equal first (sv::4vec-part-select start
                                                                     size (sv::4vec-x)))
                                  (equal first (sv::4vec-part-select start size (sv::4vec-z)))))
                        (svex-reduce-w/-env-masked (third args)
                                                   start size
                                                   env))
                       (second (svex-reduce-w/-env-masked (second args)
                                                          start size
                                                          env))
                       (third (svex-reduce-w/-env-masked (third args)
                                                         start size
                                                         env)))
                    (svex-reduce-w/-env-apply fn (hons-list first second third))))

                 ((and (equal fn 'sv::bit?)
                       (equal-len args 3))
                  (b* ((first (svex-reduce-w/-env-masked (first args)
                                                         start size
                                                         env))
                       ((when (equal first (sv::4vec-part-select start size -1)))
                        (svex-reduce-w/-env-masked (second args)
                                                   start size
                                                   env))
                       ((when (equal first 0))
                        (svex-reduce-w/-env-masked (third args)
                                                   start size
                                                   env))
                       (second (svex-reduce-w/-env-masked (second args)
                                                          start size
                                                          env))
                       (third (svex-reduce-w/-env-masked (third args)
                                                         start size
                                                         env))
                       (- (and (sv::4vec-p first)
                               (cw "The test case (~p0) for bit? is 4vec-p ~
but did not resolve the branch ~%" first))))
                    (svex-reduce-w/-env-apply fn (hons-list first second third))))
                 (t
                  (b* ((args-evaluated (svex-reduce-w/-env-lst args env))
                       (new-svex (svex-reduce-w/-env-apply fn
                                                           args-evaluated)))
                    (svex-reduce-w/-env-masked-return new-svex)))))))))

      (define svex-reduce-w/-env ((svex svex-p)
                                  env)
        :measure (cons-count svex)
        :returns (res svex-p :hyp (svex-p svex))
        (let* ((svex.kind (svex-kind svex)))
          (case  svex.kind
            (:quote svex)
            (:var
             (b* ((val (hons-get svex env))
                  ((unless (consp val)) (sv::4vec-x))
                  (val (cdr val))
                  ((when (and (quotep val)
                              (consp (cdr val))
                              (4vec-p (unquote val))))
                   (unquote val)))
               svex))
            (otherwise
             (b* ((fn (car svex))
                  (args (cdr svex)))
               (cond ((and (equal fn 'sv::partsel)
                           (equal-len args 3))
                      (b* ((start (svex-reduce-w/-env (first args) env))
                           (size (svex-reduce-w/-env (second args) env))
                           ((unless (and (natp start) (natp size)))
                            (b* ((third (svex-reduce-w/-env (third args) env))
                                 (args-evaluated (hons-list start size third)))
                              (svex-reduce-w/-env-apply fn
                                                        args-evaluated))))
                        (svex-reduce-w/-env-masked (third args) start size env)))
                     ((and (equal fn 'sv::concat)
                           (equal-len args 3))
                      (b* ((size (svex-reduce-w/-env (first args) env))
                           (third (svex-reduce-w/-env (third args) env))
                           ((unless (and (natp size)))
                            (b* ((second (svex-reduce-w/-env (second args) env))
                                 (args-evaluated (hons-list size second third)))
                              (svex-reduce-w/-env-apply fn
                                                        args-evaluated)))
                           (second
                            (svex-reduce-w/-env-masked (second args) 0 size env))
                           (args-evaluated (hons-list size second third)))
                        (svex-reduce-w/-env-apply fn args-evaluated)))
                     (t (b* ((args-evaluated (svex-reduce-w/-env-lst args env)))
                          (svex-reduce-w/-env-apply fn args-evaluated)))))))))

      (define svex-reduce-w/-env-lst ((svex-list svexlist-p)
                                      env)
        :measure (cons-count svex-list)
        :returns (res-lst sv::svexlist-p :hyp (sv::svexlist-p svex-list))
        (if (atom svex-list)
            nil
            (hons (svex-reduce-w/-env (car svex-list) env)
                  (svex-reduce-w/-env-lst (cdr svex-list) env))))
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
            :in-theory (e/d (svex-p) ())))))

(with-output
    :off :All
  :on (error summary)
  (verify-guards svex-reduce-w/-env-lst
      :hints (("Goal"
               :expand ((SVEX-P SVEX))
               :in-theory (e/d (svex-kind) ())))))

(memoize 'svex-reduce-w/-env
         :condition '(equal (svex-kind svex) :call)
         :aokp t)

(memoize 'svex-reduce-w/-env-masked
         :condition '(equal (svex-kind svex) :call)
         :aokp t)

(define svex-alist-reduce-w/-env ((svex-alist sv::svex-alist-p)
                                  env)
  :returns (res-alist sv::svex-alist-p :hyp (sv::svex-alist-p svex-alist))
  (if (atom svex-alist)
      (progn$ (clear-memoize-table 'svex-reduce-w/-env)
              (clear-memoize-table 'svex-reduce-w/-env-masked)
              nil)
      (hons (hons (caar svex-alist)
                  (svex-reduce-w/-env (cdar svex-alist) env))
            (svex-alist-reduce-w/-env (cdr svex-alist) env))))

;; 

;; (svex-reduce-w/-env  '(partsel 0 1 (sv::bitand x y))
;;                      (make-fast-alist
;;                       '((x . '1)
;;                         (y . b))))

;; (SVEX-REDUCE-WITH-ENV-META 'X
;;                            (make-fast-alist
;;                             '((X QUOTE 0) (Y . B))))



(local
 (defthm svex-eval-opener-when-call
     (implies (and (syntaxp (and (consp fn)
                                 (quotep fn)))
                   (fnsym-p fn))
              (equal (svex-eval (cons fn args) env)
                     (SV::SVEX-APPLY fn
                                     (SVEXLIST-EVAL args env))))
   :hints (("Goal"
            :expand (svex-eval (cons fn args) env)
            :in-theory (e/d (SVEX-CALL->FN
                             SVEX-VAR->NAME
                             SVEX-KIND
                             SVEX-CALL->ARGS)
                            ())))))

(local
 (defthm svex-eval-when-4vec-p
     (implies (4vec-p x)
              (equal (svex-eval x env)
                     x))
   :hints (("Goal"
            :expand ((SVEX-EVAL X ENV)
                     (4VEC-P X))
            :in-theory (e/d (SVEX-KIND
                             SV::SVEX-QUOTE->VAL)
                            ())))))

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
            :in-theory (e/d () ())))))

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

(defthm bit?!-resolve-correct
    (implies (sv::4vec-p test)
             (equal
              (svex-eval (bit?!-resolve test then else limit) env)
              (svex-eval `(sv::bit?! ,test ,then ,else) env)))
  :hints (("goal"
           :expand (
                    (bit?!-resolve test then else limit)
                    (bit?!-resolve 0 then else limit)
                    (bit?!-resolve -1 then else limit)
                    (bit?!-resolve '(0 . -1)
                                   then else limit)
                    (bit?!-resolve '(-1 . 0)
                                   then else limit)
                    (:free (x y)
                           (sv::svex-apply x y)))
           :induct (bit?!-resolve test then else limit)
           :do-not-induct t
           :in-theory (e/d (bit?!-resolve) ()))))


(progn
  (local
   (use-arithmetic-5 t))
  (local
   (defthm 3vec-p-of-4vec-rsh
       (implies (and (natp size)
                     (sv::3vec-p val)
                     (sv::4vec-p val))
                (sv::3vec-p (4vec-rsh size val)))
     :hints (("Goal"
              :expand ((4vec-rsh size val)
                       (SV::4VEC->UPPER SIZE)
                       (SV::4VEC->UPPER SIZE))
              :in-theory (e/d (4VEC-SHIFT-CORE
                               sv::3vec-p)
                              ())))))
  (local
   (use-arithmetic-5 nil)))


(defthm bit?-resolve-correct
     (implies (and (sv::4vec-p test)
                   (sv::3vec-p test))
              (equal
               (svex-eval (bit?-resolve test then else limit) env)
               (svex-eval `(sv::bit? ,test ,then ,else) env)))
  :hints (("subgoal *1/11"
           :use ((:instance 4vec-concat-of-part-select-and-rsh
                            (size (calc-bit-repetition test test 1073741824))
                            (y (sv::4vec-bit? test (svex-eval then env)
                                              (svex-eval else env))))))
           ("subgoal *1/6"
           :use ((:instance 4vec-concat-of-part-select-and-rsh
                            (size (calc-bit-repetition test test 1073741824))
                            (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
           ("subgoal *1/7"
           :use ((:instance 4vec-concat-of-part-select-and-rsh
                            (size (calc-bit-repetition test test 1073741824))
                            (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
          ("subgoal *1/8"
           :use ((:instance 4vec-concat-of-part-select-and-rsh
                            (size (calc-bit-repetition test test 1073741824))
                            (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
          ("subgoal *1/9"
           :use ((:instance 4vec-concat-of-part-select-and-rsh
                            (size (calc-bit-repetition test test 1073741824))
                            (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
          ("subgoal *1/10"
           :use ((:instance 4vec-concat-of-part-select-and-rsh
                            (size (calc-bit-repetition test test 1073741824))
                            (y (sv::4vec-bit? test (svex-eval then env) (svex-eval else env))))))
          ("goal"
            :expand (
                     (bit?-resolve test then else limit)
                     (bit?-resolve 0 then else limit)
                     (bit?-resolve -1 then else limit)
                     (bit?-resolve '(0 . -1)
                                   then else limit)
                     (bit?-resolve '(-1 . 0)
                                   then else limit)
                     (:free (x y)
                            (sv::svex-apply x y)))
            :induct (bit?-resolve test then else limit)
            :do-not-induct t
            :in-theory (e/d (bit?-resolve
                             bits
                             convert-4vec-concat-to-4vec-concat$)
                            (4vec-concat-of-part-select-and-rsh
                             equal-of-4vec-concat$-with-posp-size)))))


(local
 (defthm bit?!-resolve-is-svex-apply-when-4vec-p
     (implies (and (sv::4vec-p test)
                   (4vec-p (bit?!-resolve test then else limit)))
              (equal
               (svex-eval (bit?!-resolve test then else limit) env)
               (sv::svex-apply 'sv::bit?! (list (svex-eval test env)
                                                (svex-eval then env)
                                                (svex-eval else env)))))
   :hints (("goal"
            :use ((:instance bit?!-resolve-correct))
            :expand (
                     #|(:free (x y)
                            (sv::svex-apply x y))|#
                     (:free (x y)
                            (sv::4vec-p (cons 'SV::BIT?!  y)))
                     (:free (x y)
                            (sv::4vec-p (cons 'CONCAT  y))))
            
            :do-not-induct t
            :in-theory (e/d (bit?!-resolve
                             
                             )
                            (bit?!-resolve-correct))))))

(local
 (defthm 4VEC-BITOR-of-1
     (equal (4VEC-BITOR -1 then)
            -1)
   :hints (("Goal"
            :expand (4VEC-BITOR -1 then)
            :in-theory (e/d (SV::3VEC-BITOR) ())))))

(defthm svex-reduce-w/-env-apply-specials-correct
     (equal (svex-eval (svex-reduce-w/-env-apply-specials fn args) env)
            (svex-eval `(,fn . ,args) env))
   :hints (("Goal"
            :do-not-induct t
            :expand ((SV::4VEC->LOWER (CAR ARGS))
                     (:free (x y) (SV::4VEC-BIT? -1 x y))
                     (:free (x y) (SV::4VEC-BIT? 0 x y))
                     (:free (x y) (4VECLIST-NTH-SAFE x y))
                     (:free (x y) (nth x y))
                     (:free (x) (SV::SVEX-APPLY 'BITAND x))
                     (:free (x) (SV::SVEX-APPLY 'SV::BITOR x))
                     (:free (x) (SV::SVEX-APPLY 'sv::? x))
                     (:free (x) (SV::SVEX-APPLY 'sv::?* x))
                     (:free (x) (SV::SVEX-APPLY 'sv::?! x))
                     (:free (x) (SV::SVEX-APPLY 'sv::bit?! x))
                     (:free (x) (SV::SVEX-APPLY 'sv::bit? x)))
            :in-theory (e/d (svex-reduce-w/-env-apply-specials
                             4VEC-?
                             SV::4VEC-BIT?! 
                             4VEC-P
                             4VEC-?*
                             SV::3VEC-BIT? 
                             SV::3VEC-?*
                             ;;SV::4VEC-BIT?! 
                             SV::4VEC-?!
                             SV::4VEC->UPPER
                             SV::3VEC-?)
                            ()))))


(local
 (defthm svex-eval-when-fn-is-absent
     (implies (and (fnsym-p fn)
                   (not (member fn (strip-cars sv::*svex-op-table*))))
              (equal (svex-eval (cons fn args) env)
                     '(-1 . 0)))
   :hints (("goal"
            :expand ((svex-eval (cons fn args) env)
                     (:free (x y)
                           (sv::svex-apply x y)))
            :in-theory (e/d (svex-call->fn
                             svex-kind
                             svex-call->args)
                            ())))))

(local
 (defthm svex-apply-when-fn-is-absent
     (implies (and (fnsym-p fn)
                   (not (member fn (strip-cars sv::*svex-op-table*))))
              (equal (sv::SVEX-APPLY fn args)
                     '(-1 . 0)))
   :hints (("goal"
            :expand ((sv::SVEX-APPLY fn args)
                     (:free (x y)
                           (sv::svex-apply x y)))
            :in-theory (e/d (svex-call->fn
                             svex-kind
                             svex-call->args)
                            ())))))

(defthm svex-reduce-w/-env-apply-correct
    (implies (and (force (fnsym-p fn)))
             (equal (svex-eval (svex-reduce-w/-env-apply fn args) env)
                    (svex-eval `(,fn . ,args) env)))
  :hints (("goal"
           :do-not-induct t
           :expand ((:free (x y)
                           (sv::svex-apply x y)))
           :in-theory (e/d (svex-reduce-w/-env-apply) ()))))

(local
 (defthm svex-reduce-w/-env-apply-correct-when-returns-4vec-p
    (implies (and (force (fnsym-p fn))
                  (4vec-p (svex-reduce-w/-env-apply fn args)))
             (and (equal (equal (svex-reduce-w/-env-apply fn args) x)
                         (equal (svex-eval `(,fn . ,args) (rp-evlt env-term a)) x))
                  (equal (equal (4vec-part-select start size (svex-reduce-w/-env-apply fn args)) x)
                         (equal (4vec-part-select start size (svex-eval `(,fn . ,args) (rp-evlt env-term a))) x))))
  :hints (("goal"
           :do-not-induct t
           :use ((:instance svex-reduce-w/-env-apply-correct
                            (env (rp-evlt env-term a))))
           :in-theory (e/d ()
                           (svex-reduce-w/-env-apply-correct))))))

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
                            ())))))


(local
 (defthmd svex-eval-when-entry-is-present-but-not-4vec-p
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
            :expand ((SVEX-EVAL SVEX (RP-EVLT ENV-TERM A)))
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
                                (:REWRITE 4VEC-BIT?!-WHEN-TEST=-1)
                                (:REWRITE 4VEC-BIT?!-WHEN-TEST=-1-MASKED)
                                (:REWRITE 4VEC-BIT?!-WHEN-TEST=-DONT-CARE-OR-Z-MASKED)
                                (:REWRITE 4VEC-BIT?!-WHEN-TEST=DONT-CARE)
                                (:REWRITE 4VEC-BIT?!-WHEN-TEST=Z)
                                
                                ))))))

(local
 (defthm 4VEC-bit?-of-4vec-part-select-constants
     (implies (and (natp start)
                   (natp size))
              (and #|(equal (SV::4VEC-BIT?
                           (4VEC-PART-SELECT 0 SIZE '(-1 . 0))
                           (4VEC-PART-SELECT START SIZE
                                             then)
                           (4VEC-PART-SELECT START SIZE
                                             else))
                          (4VEC-PART-SELECT START SIZE
                                            else))
                   (equal (SV::4VEC-BIT?
                           (4VEC-PART-SELECT 0 SIZE '(0 . -1))
                           (4VEC-PART-SELECT START SIZE
                                             then)
                           (4VEC-PART-SELECT START SIZE
                                             else))
                          (4VEC-PART-SELECT START SIZE
                                            else))|#
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
                 #| (:instance 4vec-part-select-of-4vec-bit?
                             (test '(-1 . 0)))
                  (:instance 4vec-part-select-of-4vec-bit?
                             (test '(0 . -1)))|#
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
              (and (equal (sv::4vec-res (4VEC-PART-SELECT 0 SIZE '(-1 . 0))
                                        (4VEC-PART-SELECT start SIZE other))
                          (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
                   (equal (sv::4vec-res (4VEC-PART-SELECT start SIZE other)
                                        (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
                          (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
                   (equal (sv::4vec-res (4VEC-PART-SELECT 0 SIZE '(0 . -1))
                                        (4VEC-PART-SELECT start SIZE other))
                          (4VEC-PART-SELECT start SIZE other))
                   (equal (sv::4vec-res (4VEC-PART-SELECT start SIZE other)
                                        (4VEC-PART-SELECT 0 SIZE '(0 . -1)))
                          (4VEC-PART-SELECT start SIZE other))))
   :hints (("Goal"
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
     (EQUAL (SV::3VEC-FIX (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
            (4VEC-PART-SELECT 0 SIZE '(-1 . 0)))
   :hints (("Goal"
            :in-theory (e/d (4VEC-PART-SELECT
                             (:REWRITE ACL2::|(* 0 x)|)
                             (:REWRITE ACL2::|(+ (+ x y) z)|)
                             (:REWRITE ACL2::|(+ 0 x)|)
                             (:REWRITE ACL2::|(+ y x)|)
                             (:REWRITE ACL2::|(equal (if a b c) x)|)
                             (:REWRITE ACL2::|(logand y x)|)
                             (:REWRITE ACL2::|(logior y x)|)
                             (:REWRITE ACL2::|(mod 0 y)|)
                             (:REWRITE SV::4VEC->LOWER-OF-4VEC)
                             (:REWRITE SV::4VEC->UPPER-OF-4VEC)
                             (:REWRITE 4VEC-ZERO-EXT-IS-4VEC-CONCAT)
                             (:REWRITE ACL2::LOGAND-MASK)
                             (:REWRITE ACL2::LOGIOR-0-X)
                             (:REWRITE ACL2::MOD-X-Y-=-X+Y . 2)
                             (:REWRITE ACL2::REMOVE-WEAK-INEQUALITIES)
                             (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-INTEGERP-BASE)
                             (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-NONNEGATIVE-BASE)
                             (:TYPE-PRESCRIPTION ACL2::EXPT-TYPE-PRESCRIPTION-POSITIVE-BASE)
                             4VEC-CONCAT
                             sv::4VEC->UPPER
                             sv::4VEC->LOWER
                             SV::3VEC-FIX)
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
   :hints (("Goal"
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
     :hints (("Goal"
              :in-theory (e/d (4vec-part-select
                               4VEC-CONCAT
                               SV::4VEC->UPPER
                               SV::4VEC->LOWER)
                              (4VEC-CONCAT-INSERT-4VEC-PART-SELECT))))))
  (local
   (use-arithmetic-5 nil)))


(local
 (defthm rp-evlt-when-quotep-lemma
     (implies (QUOTEP (CDR (HONS-ASSOC-EQUAL SVEX ENV)))
              (equal (RP-EVLT (CDR (HONS-ASSOC-EQUAL SVEX ENV))
                              A)
                     (CADDR (HONS-ASSOC-EQUAL SVEX ENV))))
   :hints (("Goal"
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
 

 

(progn
  (local
   (in-theory (disable (:DEFINITION ACL2::APPLY$-BADGEP)
                       (:REWRITE
                        ACL2::SIMPLIFY-PRODUCTS-GATHER-EXPONENTS-EQUAL)
                       ;;(:REWRITE NOT-CONSP-HONS-ASSOC-EQUAL)
                       (:REWRITE ACL2::ACL2-NUMBERP-X)
                       (:REWRITE ACL2::RATIONALP-X)
                       (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                       (:DEFINITION HONS-ASSOC-EQUAL)
                       (:DEFINITION QUOTEP)
                       (:DEFINITION HONS-EQUAL)
                       (:DEFINITION ACL2::WEAK-APPLY$-BADGE-P)
                       (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 2)
                       (:DEFINITION RP-TRANS)
                       (:REWRITE SV::4VEC-P-OF-CAR-WHEN-4VECLIST-P)
                       (:REWRITE
                        SV::4VECLIST-P-OF-CDR-WHEN-4VECLIST-P)
                       (:DEFINITION SUBSETP-EQUAL)
                       (:REWRITE SV::4VECLIST-P-WHEN-NOT-CONSP)
                       (:DEFINITION RP::IS-FALIST)
                       (:REWRITE ACL2::NATP-WHEN-GTE-0)
                       (:REWRITE ACL2::PREFER-POSITIVE-ADDENDS-EQUAL)
                       ;;(:DEFINITION HONS-GET)
                       (:TYPE-PRESCRIPTION HONS-ASSOC-EQUAL)
                       (:REWRITE ACL2::SIMPLIFY-SUMS-EQUAL)
                       (:REWRITE
                        ACL2::ACL2-NUMBER-LISTP-IMPLIES-ACL2-NUMBERP)
                       (:REWRITE
                        ACL2::REDUCE-ADDITIVE-CONSTANT-EQUAL)
                       (:REWRITE
                        ACL2::REDUCE-MULTIPLICATIVE-CONSTANT-EQUAL)
                       acl2::EQUAL-OF-PREDICATES-REWRITE
                       (:REWRITE ACL2::|(equal c (- x))|)
                       (:REWRITE ACL2::|(equal (/ x) c)|)
                       (:REWRITE ACL2::|(equal (/ x) (/ y))|)
                       (:REWRITE ACL2::|(equal (- x) c)|)
                       (:REWRITE ACL2::|(equal (- x) (- y))|)
                       (:REWRITE ACL2::O-P-O-INFP-CAR)
                       (:REWRITE ACL2::REDUCE-INTEGERP-+)
                       (:REWRITE ACL2::INTEGERP-MINUS-X)
                       (:REWRITE
                        ACL2::INTEGER-LISTP-IMPLIES-INTEGERP)
                       (:META ACL2::META-INTEGERP-CORRECT)
                       (:TYPE-PRESCRIPTION ACL2::APPLY$-BADGEP)
                       (:DEFINITION RP::TRANS-LIST)
                       (:REWRITE SV::4VEC-P-WHEN-MAYBE-4VEC-P)
                       (:REWRITE ACL2::APPLY$-BADGEP-PROPERTIES . 3)
                       (:REWRITE ACL2::REDUCE-RATIONALP-+)
                       (:REWRITE DEFAULT-CAR)
                       (:DEFINITION LEN)
                       (:REWRITE ACL2::REDUCE-RATIONALP-*)
                       (:REWRITE ACL2::RATIONALP-MINUS-X)
                       (:REWRITE ACL2::REDUCE-RATIONALP-*)
                       (:REWRITE
                        ACL2::RATIONAL-LISTP-IMPLIES-RATIONALP)
                       (:META ACL2::META-RATIONALP-CORRECT)
                       (:REWRITE SV::4VECLIST-NTH-SAFE-OUT-OF-BOUNDS)
                       (:REWRITE SV::MAYBE-4VEC-P-WHEN-4VEC-P)
                       (:REWRITE SV::LEN-OF-SVEXLIST-EVAL)
                       (:LINEAR ACL2::APPLY$-BADGEP-PROPERTIES . 1)
                       (:REWRITE ACL2::NATP-WHEN-INTEGERP)
                       (:REWRITE SV::4VEC->LOWER-WHEN-2VEC-P)
                       (:REWRITE ACL2::SYMBOL-LISTP-IMPLIES-SYMBOLP)
                       (:REWRITE
                        SV::4VEC-P-WHEN-MEMBER-EQUAL-OF-4VECLIST-P)
                       (:REWRITE DEFAULT-CDR)
                       (:REWRITE BITP-IMPLIES-4VECP)
                       (:TYPE-PRESCRIPTION NATP-IMPLIES-SVEX-P)
                       (:REWRITE DEFAULT-+-2)
                       (:REWRITE DEFAULT-+-1)
                       (:TYPE-PRESCRIPTION EQUAL-LEN)

                       ;;(:DEFINITION NATP)
                       ;;(:TYPE-PRESCRIPTION 4VEC-P)
                       (:REWRITE DEFAULT-<-2)
                       (:REWRITE DEFAULT-<-1)
                       (:REWRITE ACL2::FOLD-CONSTS-IN-+)
                       (:REWRITE SV::SVEX-P-WHEN-MAYBE-SVEX-P)
                       (:REWRITE ACL2::O-INFP->NEQ-0)
                       (:REWRITE SV::MAYBE-SVEX-P-WHEN-SVEX-P)
                       (:TYPE-PRESCRIPTION O-FINP)
                       (:REWRITE ACL2::O-FIRST-EXPT-O-INFP)
                       (:REWRITE
                        ACL2::MEMBER-EQUAL-NEWVAR-COMPONENTS-3)
                       (:REWRITE ACL2::DEFAULT-LESS-THAN-2)
                       ACL2::|(equal c (/ x))|

                       (:TYPE-PRESCRIPTION RP::FALIST-CONSISTENT-AUX)
                       (:TYPE-PRESCRIPTION 4VECLIST-NTH-SAFE)
                       (:TYPE-PRESCRIPTION SV::4VEC-BIT?!)
                       (:TYPE-PRESCRIPTION SV::4VEC-?!)
                       (:TYPE-PRESCRIPTION SV::4VEC-BIT?)
                       (:TYPE-PRESCRIPTION 4VEC-?*)
                       (:TYPE-PRESCRIPTION 4VEC-?)
                       (:TYPE-PRESCRIPTION SV::4VEC-BITXOR)
                       (:TYPE-PRESCRIPTION 4VEC-BITOR)
                       (:TYPE-PRESCRIPTION 4VEC-BITAND)
                       )))

  (with-output
      :off :All
    :on (error summary)
  
    (defret-mutual svex-reduce-w/-env-correct
        (defret svex-reduce-w/-env-masked-correct
            (implies (and (svex-p svex)
                          (natp start)
                          (natp size)
                          (rp::falist-consistent-aux env env-term))
                     (equal (svex-eval (svex-reduce-w/-env-masked svex start size env) (rp-evlt env-term a))
                            (svex-eval `(sv::partsel ,start ,size ,svex) (rp-evlt env-term a))))
          :fn svex-reduce-w/-env-masked)
      (defret svex-reduce-w/-env-correct
          (implies (and (svex-p svex)
                        (rp::falist-consistent-aux env env-term))
                   (equal (svex-eval (svex-reduce-w/-env svex env) (rp-evlt env-term a))
                          (svex-eval svex (rp-evlt env-term a))))
        :fn svex-reduce-w/-env)
      (defret svex-reduce-w/-env-lst-correct
          (implies (and (svexlist-p svex-list)
                        (rp::falist-consistent-aux env env-term))
                   (equal (svexlist-eval (svex-reduce-w/-env-lst svex-list env) (rp-evlt env-term a))
                          (svexlist-eval svex-list (rp-evlt env-term a))))
        :fn svex-reduce-w/-env-lst)
      :mutual-recursion svex-reduce-w/-env
  
      :hints (("Goal"
               :do-not-induct t
             
               :expand ((SVEX-EVAL SVEX (RP-EVLT ENV-TERM A))
                        (SVEX-EVAL (CONS (CAR SVEX)
                                         (SVEX-REDUCE-W/-ENV-LST (CDR SVEX) ENV))
                                   ENV-TERM)
                        (:free (x y) (4vec-p (cons x y)))
                        (:free (x y) (4VECLIST-NTH-SAFE x y))
                        (:free (x y) (nth x y))
                        (:free (x) (SV::SVEX-APPLY 'PARTSEL x))
                        (:free (x) (SV::SVEX-APPLY 'concat x))
                        (:free (args) (SV::SVEX-APPLY 'SV::UNFLOAT args))
                        (:free (args) (SV::SVEX-APPLY 'SV::SIGNX args))
                        (:free (args) (SV::SVEX-APPLY 'SV::ZEROX args))
                        (:free (args) (SV::SVEX-APPLY 'SV::rsh args))
                        (:free (args) (SV::SVEX-APPLY 'SV::lsh args))
                        (:free (args) (SV::SVEX-APPLY 'SV::BIT? args))
                        (:free (args) (SV::SVEX-APPLY 'SV::BITnot args))
                        (:free (args) (SV::SVEX-APPLY 'SV::BITand args))
                        (:free (args) (SV::SVEX-APPLY 'SV::BITor args))
                        (:free (args) (SV::SVEX-APPLY 'SV::BITxor args))
                        (:free (args) (SV::SVEX-APPLY 'SV::RES args))
                        (:free (args) (SV::SVEX-APPLY 'sv::?* args))
                        (:free (args) (SV::SVEX-APPLY 'sv::?! args))
                        (:free (args) (SV::SVEX-APPLY 'sv::? args))
                        (:free (args) (SV::SVEX-APPLY 'SV::BIT?! args))
                        (:free (args) (SV::SVEX-APPLY 'SV::PARTINST args)))
               :in-theory (e/d (svex-reduce-w/-env-masked
                                SV::SVEX-QUOTE->VAL
                                SVEX-ENV-LOOKUP-when-svex-p
                                4vec-part-select-of-4vec-bitnot-reverse
                                4vec-concat-with-0-to-4vec-part-select
                                4vec-part-select-of-4vec-bitxor-better
                                4vec-part-select-of-4vec-bitor-better
                                4vec-part-select-of-4vec-bitand-better
                                svex-eval-when-entry-is-absent
                                svex-eval-when-entry-is-present-but-not-4vec-p
                                ;;convert-4vec-concat-to-4vec-concat$
                                4vec-concat-insert-4vec-part-select
                                ;; 4vec-concat-of-4vec-part-select-same-size
                                svex-reduce-w/-env
                                SVEX-CALL->FN
                                SVEX-CALL->ARGS
                                svex-kind
                                bits
                                ;;SVEX-ENV-LOOKUP-when-svex-p
                                svex-reduce-w/-env-lst

                                4vec-sign-ext-to-4vec-concat)
                               ()))))))


(defret svex-alist-reduce-w/-env-correct
    (implies (and (sv::svex-alist-p svex-alist)
                  (rp::falist-consistent-aux env env-term))
             (equal (sv::svex-alist-eval res-alist (rp-evlt env-term a))
                    (sv::svex-alist-eval svex-alist (rp-evlt env-term a))))
  :fn svex-alist-reduce-w/-env
  :hints (("Goal"
           :do-not-induct t
           :induct (svex-alist-reduce-w/-env svex-alist env)
           :in-theory (e/d (svex-alist-reduce-w/-env
                            sv::svex-alist-eval)
                           ()))))

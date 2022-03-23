
;; Mertcan Temel


(in-package "RP")
(include-book "svl-spec")

(local
 (include-book "projects/rp-rewriter/proofs/aux-function-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/eval-functions-lemmas" :dir :system))

(local
 (include-book "projects/rp-rewriter/proofs/rp-equal-lemmas" :dir :system))

#|(local
 (include-book "projects/rp-rewriter/proofs/rp-rw-lemmas" :dir :system))|#

(local
 (fetch-new-events
  (include-book "arithmetic-5/top" :dir :system)
  use-arith-5
  :disabled t))

(local
 (rp::fetch-new-events
  (include-book "centaur/bitops/ihs-extensions" :dir :system)
  use-ihs-extensions
  :disabled t))

(local
 (include-book "pp-flatten-meta-correct"))

(local
 (include-book "sum-merge-fncs-correct"))

(local
 (include-book "lemmas"))
(local
 (include-book "lemmas-2"))



#|
(BINARY-* (ACL2::RP 'INTEGERP
                    (SVL::4VEC-CONCAT$ '23
                                       (SVL::BITS (ACL2::RP 'INTEGERP SRC1)
                                                  '0
                                                  '23)
                                       '1))
          (ACL2::RP 'INTEGERP
                    (SVL::4VEC-CONCAT$ '23
                                       (SVL::BITS (ACL2::RP 'INTEGERP SRC2)
                                                  '0
                                                  '23)
'1)))

|#

(define check-context-for-integerp (term context)
  (if (atom context)
      nil
    (or (b* ((cur (ex-from-rp (car context))))
          (case-match cur
            (('integerp x)
             (rp-equal-cnt term x 1))))
        (check-context-for-integerp term (cdr context)))))

(define logsize ((x integerp))
  :prepwork ((local
              (use-arith-5 t))
             (local
              (in-theory (e/d* ()
                               (rw-dir1
                                +-IS-SUM
                                FLOOR2-IF-F2)))))
  (if (or (equal x 0)
          (equal x -1)
          (not (integerp x)))
      0
    (1+ (logsize (acl2::logcdr x)))))

(define calculate-vec-size ((x rp-termp)
                            (context rp-term-listp))
  :returns (mv (size integerp)
               (integerp booleanp))
  :verify-guards :after-returns
  :measure (cons-count x)
  :hints (("Goal"
           :in-theory (e/d (measure-lemmas
                            ACL2::DEFSORT-O<-OF-NATURALS)
                           (RW->-TO-GT
                            (:REWRITE LT-TO-GT)
                            (:REWRITE RW-<-TO-LTE)))))
  (b* ((x (ex-from-rp x)))
    (case-match x
      (('svl::bits vec ('quote start) ('quote size))
       (b* (((unless (and (natp start)
                          (natp size)))
             (mv -1 nil))
            ((mv & integerp)
             (calculate-vec-size vec context)))
         (mv size integerp)))
      (('svl::4vec-concat$ ('quote size) vec1 vec2)
       (b* (((mv & integerp1)
             (calculate-vec-size vec1 context))
            ((mv size2 integerp2)
             (calculate-vec-size vec2 context))
            ((unless (and integerp1
                          integerp2
                          (not (equal size2 -1))
                          (natp size)))
             (mv -1 nil)))
         (mv (+ size size2) t)))
      (('quote x)
       (if (natp x)
           (mv (logsize x) t)
         (mv -1 nil)))
      (&
       (if (atom x)
           (mv -1 (check-context-for-integerp x context))
         (mv -1 nil))))))

#|(calculate-vec-size '(ACL2::RP 'INTEGERP
                               (SVL::4VEC-CONCAT$ '23
                                                  (SVL::BITS (ACL2::RP 'INTEGERP SRC1)
                                                             '0
                                                             '23)
                                                  '1))
                    '((integerp src1)))|#

(define *-to-mult-spec-meta ((term rp-termp)
                             (context rp-term-listp))
  (case-match term
    (('binary-* x y)
     (b* (((mv size-x integerp-x)
           (calculate-vec-size x context))
          ((mv size-y integerp-y)
           (calculate-vec-size y context))
          ((unless (and integerp-x
                        (not (equal size-x -1))
                        (not (equal size-y -1))
                        integerp-y))
           (mv term nil)))
       (mv `(svl-mult-final-spec ,x ,y ',(+ size-x size-y))
           `(nil t t t))))
    (& (mv term nil))))

#|(*-to-mult-spec-meta  '(BINARY-* (ACL2::RP 'INTEGERP
                                           (SVL::4VEC-CONCAT$ '23
                                                              (SVL::BITS (ACL2::RP 'INTEGERP SRC1)
                                                                         '0
                                                                         '23)
                                                              '1))
                                 (ACL2::RP 'INTEGERP
                                           (SVL::4VEC-CONCAT$ '23
                                                              (SVL::BITS (ACL2::RP 'INTEGERP SRC2)
                                                                         '0
                                                                         '23)
                                                              '1)))
                      '((integerp src1)
                        (integerp src2)))|#

(encapsulate
  nil
  (local
   (in-theory
    (e/d* () (+-IS-SUM
              REWRITING-POSITIVE-LTE-GTE-GT-LT
              rw-dir1
              C-SPEC-IS-F2
              S-SPEC-IS-M2
              S-C-SPEC-IS-LIST-M2-F2
              SVL::4VEC-ZERO-EXT-IS-4VEC-CONCAT
              SVL-SUM-PPS-BYCOL-BYBIT-OPENER))))
  (with-output
    :off :all
    :gag-mode nil
    (rp::def-formula-checks *-to-mult-spec-meta-fchecks
      (svl::bits svl::4vec-concat$ *
                 SVL-MULT-FINAL-SPEC))))

(local
 (progn
   (rp::create-regular-eval-lemma svl::4VEC-CONCAT$ 3
                                  *-to-mult-spec-meta-fchecks)
   (rp::create-regular-eval-lemma SVL-MULT-FINAL-SPEC 3  *-to-mult-spec-meta-fchecks)
   (rp::create-regular-eval-lemma svl::Bits 3  *-to-mult-spec-meta-fchecks)
   (rp::create-regular-eval-lemma binary-* 2  *-to-mult-spec-meta-fchecks)
   (rp::create-regular-eval-lemma integerp 1  *-to-mult-spec-meta-fchecks)))

(local
 (defthm CHECK-CONTEXT-FOR-INTEGERP-correct
   (implies (and (eval-and-all context a)
                 (rp-evl-meta-extract-global-facts)
                 (*-to-mult-spec-meta-fchecks state)
                 (check-context-for-integerp term context))
            (integerp (rp-evlt term a)))
   :hints (("Subgoal *1/2"
            :use ((:instance rp-evlt-of-rp-equal
                             (term1 term)
                             (term2 (CADR (EX-FROM-RP (CAR CONTEXT)))))))
           ("Goal"
            :in-theory (e/d* (check-context-for-integerp
                              RP-EVLT-OF-EX-FROM-RP-REVERSE
                              regular-eval-lemmas
                              regular-eval-lemmas-with-ex-from-rp)
                             (rp-evlt-of-rp-equal
                              rp-evlt-of-ex-from-rp ))))))

(local
 (defthm rp-evlt-when-quoted
   (implies (and (quotep term)
                 (consp (cdr term)))
            (equal (rp-evlt term a)
                   (cadr term)))))


(defthm unsigned-byte-p-of-logsize
  (implies (natp x)
           (unsigned-byte-p (logsize x)
                            x))
  :hints (("Goal"
           :in-theory (e/d* (unsigned-byte-p-redef-to-recursive
                             ;;bitops::ihsext-inductions
                             ;;bitops::ihsext-recursive-redefs
                             logsize
                             )
                            (rw-dir1
                             LOGCOUNT
                             (:induction UNSIGNED-BYTE-P-RECURSIVE)
                             acl2::logcdr
                             acl2::logcar
                             +-IS-SUM)))))


(local
 (defthm unsigned-byte-p-of-logapp
   (implies (and (natp size)
                 (natp size2)
                 ;;(<= size2 size)
                 (integerp y)
                 (integerp x))
            (equal (unsigned-byte-p (+ size2 size) (logapp size2 x y))
                   (unsigned-byte-p size y)))
   :hints (("Goal"
            :do-not-induct t
            :induct (unsigned-byte-p-recursive size2 x)
            :expand ((LOGAPP SIZE2 0 Y)
                     (UNSIGNED-BYTE-P-RECURSIVE SIZE
                                 (ACL2::LOGCONS 0 (LOGAPP (+ -1 SIZE2) 0 Y))))
            :in-theory (e/d* (SVL::4VEC-CONCAT$
                              BITOPS::LOGCDR-OF-LOGCONS
                              unsigned-byte-p-redef-to-recursive
                              acl2::logapp**
                              SV::4VEC-CONCAT
                              ;;bitops::ihsext-inductions
                              bitops::ihsext-recursive-redefs
                              natp
                              SV::4VEC->UPPER
                              SV::4VEC->lower
                              SV::4VEC)
                             (+-IS-SUM
                              ACL2::LOGCONS$INLINE
                              MOD2-IS-M2
                              acl2::logcdr
                              FLOOR
                              FLOOR2-IF-F2
                              unsigned-byte-p
                              LOGAPP
                              ACL2::LOGHEAD$INLINE
                              rw-dir1))))))

(local
 (defthm unsigned-byte-p-of-4VEC-CONCAT$
   (implies (and (natp size)
                 (natp size2)
                 (integerp x)
                 (integerp y)
                 (<= size2 size))
            (equal (unsigned-byte-p size (SVL::4VEC-CONCAT$ size2 x y))
                   (unsigned-byte-p (- size size2) y)))
   :hints (("Goal"
            :use ((:instance unsigned-byte-p-of-logapp
                             (y y)
                             (size (- size size2))
                             (size2 size2)))
            :do-not-induct t
            :in-theory (e/d* (SVL::4VEC-CONCAT$
                              unsigned-byte-p-redef-to-recursive
                              
                              SV::4VEC-CONCAT
                              bitops::ihsext-inductions
                              bitops::ihsext-recursive-redefs
                              natp
                              SV::4VEC->UPPER
                              SV::4VEC->lower
                              SV::4VEC)
                             (+-IS-SUM
                              unsigned-byte-p-of-logapp
                              MOD2-IS-M2
                              FLOOR
                              FLOOR2-IF-F2
                              unsigned-byte-p
                              LOGAPP
                              ACL2::LOGHEAD$INLINE
                              rw-dir1))))))

(local
 (defthm dumy-sum-cancel-lemma
   (implies (acl2-numberp other)
            (and (equal (+ x (- x) other)
                        other)))))
(local
 (defthm integerp-implies-acl2-numberp
   (implies (integerp x)
            (acl2-numberp x))))

(local
 (defthm natp-of-sums
   (implies (and (NATP X)
                 (natp y))
            (natp (+ x y)))))

(defret calculate-vec-size-correct
  (implies (and (rp-evl-meta-extract-global-facts)
                (eval-and-all context a)
                (*-to-mult-spec-meta-fchecks state)
                integerp)
           (and (integerp (rp-evlt x a))
                (integerp size)
                (implies (not (equal size -1))
                         (and (unsigned-byte-p size
                                               (rp-evlt x a))
                              (natp size)))))
  :fn calculate-vec-size
  :hints (("Subgoal *1/7"
           :use ((:instance CHECK-CONTEXT-FOR-INTEGERP-correct
                            (term (EX-FROM-RP X)))))
          ("Goal"
           :do-not-induct t
           :induct (calculate-vec-size x context)
           :in-theory (e/d* (calculate-vec-size
                             natp
                             RP-EVLT-OF-EX-FROM-RP-REVERSE
                             regular-eval-lemmas
                             regular-eval-lemmas-with-ex-from-rp)
                            (UNSIGNED-BYTE-P
                             RP-TERMP-IMPLIES-SUBTERMS
                             RP-TERM-LISTP
                             rw-dir1
                             natp
                             +-IS-SUM
                             rp-trans
                             INCLUDE-FNC
                             rp-evlt-of-ex-from-rp
                             CHECK-CONTEXT-FOR-INTEGERP-correct
                             logcount)))))


(defret *-to-mult-spec-meta-correct
  (implies (and (rp-evl-meta-extract-global-facts)
                (eval-and-all context a)
                (*-to-mult-spec-meta-fchecks state))
           (equal (rp-evlt (mv-nth 0 (*-to-mult-spec-meta term context)) a)
                  (rp-evlt term a)))
  :hints (("Goal"
           :do-not-induct t
           :use ((:instance *-of-known-sized-vecs
                            (x (rp-evlt (cadr term) a))
                            (y (rp-evlt (caddr term) a))
                            (size1 (mv-nth 0
                                           (calculate-vec-size (cadr term)
                                                               context)))
                            (size2 (mv-nth 0
                                           (calculate-vec-size (caddr term)
                                                               context)))))
           :in-theory (e/d* (*-to-mult-spec-meta
                             regular-eval-lemmas-with-ex-from-rp
                             regular-eval-lemmas)
                            (+-IS-SUM
                             *-of-known-sized-vecs
                             SVL-MULT-FINAL-SPEC
                             RP-TRANS-LST
                             rp-trans
                             rw-dir1
                             natp
                             UNSIGNED-BYTE-P
                             RP-TRANS-OPENER
                             INCLUDE-FNC)))))

(defret *-to-mult-spec-meta-valid-sc
  (implies (valid-sc term a)
           (valid-sc (mv-nth 0 (*-to-mult-spec-meta term context)) a))
  :hints (("Goal"
           :do-not-induct t
           
           :in-theory (e/d* (*-to-mult-spec-meta
                             valid-sc is-rp is-if)
                            ()))))

(defret *-to-mult-spec-meta-rp-termp
  (implies (rp-termp term)
           (rp-termp (mv-nth 0 (*-to-mult-spec-meta term context))))
  :hints (("Goal"
           :do-not-induct t
           
           :in-theory (e/d* (*-to-mult-spec-meta
                             valid-sc is-rp is-if)
                            ()))))
(rp::add-meta-rule
 :meta-fnc *-to-mult-spec-meta
 :trig-fnc binary-*
 :valid-syntaxp t
 :formula-checks *-to-mult-spec-meta-fchecks
 :returns (mv term dont-rw))

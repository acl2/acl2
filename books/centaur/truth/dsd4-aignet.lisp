; TRUTH - integer truth table representation
; Copyright (C) 2017 Centaur Technology
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
;
; Original authors: Sol Swords <sswords@centtech.com>


(in-package "TRUTH")


(include-book "../aignet/rwlib")
(include-book "tools/symlet" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/aignet/construction" :dir :system)
(include-book "centaur/aignet/mark-impls" :dir :system)
(include-book "centaur/aignet/statsmgr" :dir :system)


(local (include-book "tools/trivial-ancestors-check" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "std/basic/arith-equivs" :dir :system))
(local (include-book "std/util/termhints" :dir :system))
(local (in-theory (disable unsigned-byte-p signed-byte-p nth update-nth)))
(local (std::add-default-post-define-hook :fix))
(local (acl2::use-trivial-ancestors-check))

(defmacro defalias (&rest args) (cons 'aignet::defalias args))
(defalias rwlib-wfp aignet::rwlib-wfp)
(defalias rwlib-correct aignet::rwlib-correct)

(defalias smm-contains-aignet-lits aignet::smm-contains-aignet-lits)
(defalias truth4-env-from-aignet-invals aignet::truth4-env-from-aignet-invals)


(defthm depends-on-of-positive-cofactor
  (implies (< (nfix n) (nfix numvars))
           (not (depends-on n (positive-cofactor n x numvars) numvars)))
  :hints (("goal" :use ((:instance depends-on-witness-correct
                         (truth (positive-cofactor n x numvars))
                         (numvars (nfix numvars))))
           :in-theory (disable depends-on-witness-correct))))

(defthm depends-on-of-negative-cofactor
  (implies (< (nfix n) (nfix numvars))
           (not (depends-on n (negative-cofactor n x numvars) numvars)))
  :hints (("goal" :use ((:instance depends-on-witness-correct
                         (truth (negative-cofactor n x numvars))
                         (numvars (nfix numvars))))
           :in-theory (disable depends-on-witness-correct))))

(defthm positive-cofactor-preserves-independent
  (implies (and (not (depends-on m x numvars))
                (< (nfix n) (nfix numvars))
                (< (nfix m) (nfix numvars)))
           (not (depends-on m (positive-cofactor n x numvars) numvars)))
  :hints (("goal" :use ((:instance depends-on-witness-correct
                         (truth (positive-cofactor n x numvars))
                         (numvars (nfix numvars))
                         (n m))
                        (:instance depends-on-correct
                         (n m)
                         (env (env-update n t (depends-on-witness m (positive-cofactor n x numvars) numvars)))
                         (truth x)
                         (val t)))
           :cases ((equal (nfix n) (nfix m)))
           :in-theory (e/d* (acl2::arith-equiv-forwarding)
                            (depends-on-witness-correct
                             depends-on-correct)))))

(defthm negative-cofactor-preserves-independent
  (implies (and (not (depends-on m x numvars))
                (< (nfix n) (nfix numvars))
                (< (nfix m) (nfix numvars)))
           (not (depends-on m (negative-cofactor n x numvars) numvars)))
  :hints (("goal" :use ((:instance depends-on-witness-correct
                         (truth (negative-cofactor n x numvars))
                         (numvars (nfix numvars))
                         (n m))
                        (:instance depends-on-correct
                         (n m)
                         (env (env-update n nil (depends-on-witness m (negative-cofactor n x numvars) numvars)))
                         (truth x)
                         (val t)))
           :cases ((equal (nfix n) (nfix m)))
           :in-theory (e/d* (acl2::arith-equiv-forwarding)
                            (depends-on-witness-correct
                             depends-on-correct)))))

(define count-truth4-deps ((x truth4-p))
  :returns (count natp :rule-classes :type-prescription)
  (+ (if (depends-on4 0 x) 1 0)
     (if (depends-on4 1 x) 1 0)
     (if (depends-on4 2 x) 1 0)
     (if (depends-on4 3 x) 1 0))
  ///
  (defret count-truth4-deps-bound
    (<= count 4)
    :rule-classes :linear)

  (defthm num-deps-of-positive-cofactor
    (implies (and (depends-on n x 4)
                  (< (nfix n) 4))
             (< (count-truth4-deps (positive-cofactor n x 4))
                (count-truth4-deps x)))
    :hints (("goal" :cases ((equal (nfix n) 0)
                            (equal (nfix n) 1)
                            (equal (nfix n) 2)
                            (equal (nfix n) 3)))))

  (defthm num-deps-of-negative-cofactor
    (implies (and (depends-on n x 4)
                  (< (nfix n) 4))
             (< (count-truth4-deps (negative-cofactor n x 4))
                (count-truth4-deps x)))
    :hints (("goal" :cases ((equal (nfix n) 0)
                            (equal (nfix n) 1)
                            (equal (nfix n) 2)
                            (equal (nfix n) 3))))))



(define truth-not-const-false-witness ((x integerp)
                             (numvars natp))
  :returns (witness-env natp :rule-classes :type-prescription)
  (bitops::trailing-0-count (truth-norm x numvars))
  ///
  (local (defthm trailing-0-count-of-loghead-bound
           (implies (posp n)
                    (< (bitops::trailing-0-count (loghead n x)) n))
           :hints(("Goal" :in-theory (enable* bitops::trailing-0-count
                                              bitops::loghead**
                                              bitops::ihsext-inductions)
                   :induct t))
           :rule-classes (:rewrite :linear)))

  (local (defthm posp-ash-1
           (implies (natp n)
                    (posp (ash 1 n)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs)))
           :rule-classes :type-prescription))

  (local (defthm trailing-0-count-unsigned-byte-p
           (implies (natp n)
                    (unsigned-byte-p n (bitops::trailing-0-count (loghead (ash 1 n) x))))
           :hints (("goal" :in-theory (enable unsigned-byte-p
                                              bitops::expt-2-is-ash)))))

  (local (defthm loghead-identity-nfix
           (implies (unsigned-byte-p (nfix n) x)
                    (equal (loghead n x) x))
           :hints(("Goal" :in-theory (enable nfix)))))

  (defret truth-not-const-false-witness-upper-bound
    (< witness-env (ash 1 (nfix numvars)))
    :hints(("Goal" :in-theory (enable truth-norm)))
    :rule-classes :linear)

  (defret truth-not-const-false-witness-correct
    (implies (not (equal (truth-norm x numvars) 0))
             (truth-eval x (truth-not-const-false-witness x numvars) numvars))
    :hints(("Goal" :in-theory (e/d (truth-eval truth-norm)
                                   (bitops::trailing-0-count-properties))
            :use ((:instance bitops::trailing-0-count-properties
                   (x (loghead (ash 1 (nfix numvars)) x))))))))

(define truth-not-const-true-witness ((x integerp)
                                (numvars natp))
  :returns (witness-env natp :rule-classes :type-prescription)
  (truth-not-const-false-witness (lognot x) numvars)
  ///
  (defret truth-not-const-true-witness-upper-bound
    (< witness-env (ash 1 (nfix numvars)))
    :hints(("Goal" :in-theory (enable truth-norm)))
    :rule-classes :linear)

  (local (defthm loghead-of-lognot-equal-0
           (equal (equal (loghead n (lognot x)) 0)
                  (equal (loghead n x) (loghead n -1)))
           :hints(("goal" :induct (loghead n x)
                   :in-theory (enable* bitops::ihsext-inductions
                                       bitops::ihsext-recursive-redefs)))))

  (defret truth-not-const-true-witness-correct
    (implies (not (equal (truth-norm x numvars)
                         (truth-norm -1 numvars)))
             (not (truth-eval x (truth-not-const-true-witness x numvars) numvars)))
    :hints (("goal" :use ((:instance truth-not-const-false-witness-correct
                           (x (lognot x))))
             :in-theory (e/d (truth-norm) (truth-not-const-false-witness-correct))))))

(define truths-not-equal-witness ((x integerp)
                                  (y integerp)
                                  (numvars natp))
  :returns (witness-env natp :rule-classes :type-prescription)
  (truth-not-const-false-witness (logxor x y) numvars)
  ///
  (defret truths-not-equal-witness-upper-bound
    (< witness-env (ash 1 (nfix numvars)))
    :hints(("Goal" :in-theory (enable truth-norm)))
    :rule-classes :linear)

  (defret truths-not-equal-witness-correct
    (implies (not (equal (truth-norm x numvars)
                         (truth-norm y numvars)))
             (not (equal (truth-eval x (truths-not-equal-witness x y numvars) numvars)
                         (truth-eval y (truths-not-equal-witness x y numvars) numvars))))
    :hints (("goal" :use ((:instance truth-not-const-false-witness-correct
                           (x (logxor x y))))
             :in-theory (e/d (truth-norm) (truth-not-const-false-witness-correct))))))

(define truth-not-const-witness ((x integerp)
                           (numvars natp))
  :returns (truth-not-const-var natp :rule-classes :type-prescription)
  (env-mismatch x
                (truth-not-const-true-witness x numvars)
                (truth-not-const-false-witness x numvars)
                numvars)
  ///
  (defret depends-on-truth-not-const-witness-when-not-constant
    (implies (and (not (equal (truth-norm x numvars) 0))
                  (not (equal (truth-norm x numvars)
                              (truth-norm -1 numvars))))
             (and (depends-on truth-not-const-var x numvars)
                  (< truth-not-const-var (nfix numvars))
                  (implies (natp numvars)
                           (< truth-not-const-var numvars))))))


(local
 (defthm positive-cofactor-equals-norm-iff-depends-on
   (implies (< (nfix n) (nfix numvars))
            (iff (equal (positive-cofactor n x numvars) (truth-norm x numvars))
                 (not (depends-on n x numvars))))
   :hints (("goal" :in-theory (disable truths-not-equal-witness-correct))
           (acl2::use-termhint
            (b* ((cof (positive-cofactor n x numvars))
                 (norm (truth-norm x numvars))
                 ;; (dep (depends-on n x numvars))
                 ((when (equal cof norm))
                  `'(:use ((:instance depends-on-of-truth-norm
                            (truth ,(hq x))))
                     :in-theory (disable depends-on-of-truth-norm)))
                 (env (truths-not-equal-witness cof norm numvars))
                 (ev-cof (truth-eval cof env numvars))
                 (ev-norm (truth-eval norm env numvars))
                 ((when (equal ev-cof ev-norm))
                  `'(:use ((:instance truths-not-equal-witness-correct
                            (x ,(hq cof)) (y ,(hq norm)))))))
              nil)))))

(local
 (defthm positive-cofactor-equals-x-iff-depends-on
   (implies (and (< (nfix n) (nfix numvars))
                 (equal (truth-norm x numvars) x))
            (iff (equal (positive-cofactor n x numvars) x)
                 (not (depends-on n x numvars))))))




;; (local
;;  (defthm independent-when-positive-cofactor-equals-x
;;    (implies (and (equal (positive-cofactor n x numvars) x)
;;                  (< (nfix n) (nfix numvars)))
;;             (not (depends-on n x numvars)))))

;; (local
;;  (defthm independent-when-positive-cofactor-equals-norm-x
;;    (implies (and (equal (positive-cofactor n x numvars) (truth-norm x numvars))
;;                  (< (nfix n) (nfix numvars)))
;;             (not (depends-on n x numvars)))
;;    :hints (("goal" :use ((:instance depends-on-of-truth-norm
;;                           (truth x)))
;;             :in-theory (disable depends-on-of-truth-norm)))))


(define dependencies-lower-bounded ((n natp)
                                    (truth integerp)
                                    (numvars natp))
  ;; Checks that truth only depends on variables greater than or equal to n.
  :guard (<= (nfix n) (nfix numvars))
  (b* (((when (zp n)) t)
       (n (1- n)))
    (and (not (depends-on n truth numvars))
         (dependencies-lower-bounded n truth numvars)))
  ///
  (local (defthm dependencies-not-lower-bounded-when-depends-on
           (implies (and (depends-on k truth numvars)
                         (< (nfix k) (nfix n)))
                    (not (dependencies-lower-bounded n truth numvars)))))

  (defthm deps-not-lower-bounded-by-numvars-when-truth-not-constant
    (implies (and (not (equal (truth-norm x numvars) 0))
                  (not (equal (truth-norm x numvars)
                              (truth-norm -1 numvars))))
             (not (dependencies-lower-bounded numvars x numvars)))
    :hints (("goal" :use ((:instance dependencies-not-lower-bounded-when-depends-on
                           (k (truth-not-const-witness x numvars))
                           (n numvars)
                           (truth x)))
             :in-theory (disable dependencies-not-lower-bounded-when-depends-on
                                 dependencies-lower-bounded))))

  (defthm dependencies-lower-bounded-preserved-by-positive-cofactor
    (implies (and (dependencies-lower-bounded n x numvars)
                  (< (nfix m) (nfix numvars))
                  (<= (nfix n) (nfix numvars)))
             (dependencies-lower-bounded n
                                         (positive-cofactor m x numvars)
                                         numvars)))

  (defthm dependencies-lower-bounded-preserved-by-negative-cofactor
    (implies (and (dependencies-lower-bounded n x numvars)
                  (< (nfix m) (nfix numvars))
                  (<= (nfix n) (nfix numvars)))
             (dependencies-lower-bounded n
                                         (negative-cofactor m x numvars)
                                         numvars)))

  (defthm dependencies-lower-bounded-incr
    (implies (and (equal nn (nfix n))
                  (dependencies-lower-bounded n x numvars)
                  (< nn (nfix numvars)))
             (and (dependencies-lower-bounded (+ 1 nn)
                                      (positive-cofactor n x numvars)
                                      numvars)
                  (dependencies-lower-bounded (+ 1 nn)
                                      (negative-cofactor n x numvars)
                                      numvars))))

  (defthm dependencies-lower-bounded-incr-when-positive-cofactor-equals-x
    (implies (and (dependencies-lower-bounded n x numvars)
                  (natp n)
                  (< (nfix n) (nfix numvars))
                  (equal (positive-cofactor n x numvars) (truth-norm x numvars)))
             (dependencies-lower-bounded (+ 1 n) x numvars)))

  (defthm dependencies-lower-bounded-of-0
    (dependencies-lower-bounded 0 x numvars)))

(defstobj-clone aignet aignet::aignet :strsubst (("ABCDE" . "ABCDE")))
(defstobj-clone strash aignet::strash :strsubst (("ABCDE" . "ABCDE")))





(local
 #!aignet
 (defthm aignet-idp-when-in-bounds
   (implies (<= (nfix id) (fanin-count aignet))
            (aignet-idp id aignet))
   :hints(("Goal" :in-theory (enable aignet-idp)))))


(define only-depends-on-aux ((n natp)
                             (truth integerp)
                             (vars true-listp)
                             (numvars natp))
  :guard (<= n numvars)
  :measure (nfix (- (nfix numvars) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        t)
       (dep (depends-on n truth numvars))
       ((when (And dep (not (member (lnfix n) vars))))
        nil))
    (only-depends-on-aux (+ 1 (nfix n)) truth vars numvars))
  ///
  (defthm only-depends-on-aux-implies-does-not-depend-on
    (implies (and (only-depends-on-aux n truth vars numvars)
                  (<= (nfix n) (nfix m))
                  (< (nfix m) (nfix numvars))
                  (not (member (nfix m) vars)))
             (not (depends-on m truth numvars)))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm only-depends-on-aux-of-positive-cofactor
    (implies (and (only-depends-on-aux n truth vars numvars)
                  (consp vars)
                  (natp (car vars))
                  (< (car vars) (nfix numvars)))
             (only-depends-on-aux n (positive-cofactor (car vars) truth numvars)
                                  (cdr vars) numvars))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm only-depends-on-aux-of-negative-cofactor
    (implies (and (only-depends-on-aux n truth vars numvars)
                  (consp vars)
                  (natp (car vars))
                  (< (car vars) (nfix numvars)))
             (only-depends-on-aux n (negative-cofactor (car vars) truth numvars)
                                  (cdr vars) numvars))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defthm only-depends-on-aux-when-does-not-depend-on
    (implies (and (only-depends-on-aux n truth vars numvars)
                  (not (depends-on (car vars) truth numvars))
                  (consp vars)
                  (natp (car vars))
                  (< (car vars) (nfix numvars)))
             (only-depends-on-aux n truth (cdr vars) numvars))))

(define only-depends-on ((truth integerp)
                         (vars true-listp)
                         (numvars natp))
  (only-depends-on-aux 0 truth vars numvars)
  ///
  (defthm only-depends-on-implies-does-not-depend-on
    (implies (and (only-depends-on truth vars numvars)
                  (< (nfix m) (nfix numvars))
                  (not (member (nfix m) vars)))
             (not (depends-on m truth numvars))))

  (defthm only-depends-on-of-positive-cofactor
    (implies (and (only-depends-on truth vars numvars)
                  (consp vars)
                  (natp (car vars))
                  (< (car vars) (nfix numvars)))
             (only-depends-on (positive-cofactor (car vars) truth numvars)
                              (cdr vars)
                              numvars)))

  (defthm only-depends-on-of-negative-cofactor
    (implies (and (only-depends-on truth vars numvars)
                  (consp vars)
                  (natp (car vars))
                  (< (car vars) (nfix numvars)))
             (only-depends-on (negative-cofactor (car vars) truth numvars)
                              (cdr vars)
                              numvars)))

  (defthm only-depends-on-when-does-not-depend-on
    (implies (and (only-depends-on truth vars numvars)
                  (not (depends-on (car vars) truth numvars))
                  (consp vars)
                  (natp (car vars))
                  (< (car vars) (nfix numvars)))
             (only-depends-on truth (cdr vars) numvars)))

  (defthm only-depends-on-atom-when-truth-not-constant
    (implies (and (not (equal (truth-norm x numvars) 0))
                  (not (equal (truth-norm x numvars)
                              (truth-norm -1 numvars))))
             (not (only-depends-on x nil numvars)))
    :hints (("goal" :use ((:instance only-depends-on-implies-does-not-depend-on
                           (m (truth-not-const-witness x numvars))
                           (truth x)
                           (vars nil)))
             :in-theory (disable only-depends-on-implies-does-not-depend-on
                                 only-depends-on)))))
  



(define aignet-build-truth4-simple ((indices (index-listp indices 4))
                                    (x truth4-p)
                                    strash
                                    aignet)
  :guard (and (only-depends-on x indices 4)
              (<= 4 (aignet::num-ins aignet)))
  :returns (mv (lit aignet::litp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  :measure (len indices)
  :verify-guards nil
  (b* ((aignet (aignet::aignet-fix aignet))
       ((when (atom indices))
        (if (eql 0 (truth4-fix x))
            (mv 0 strash aignet)
          (mv 1 strash aignet)))
       (n (lnfix (car indices)))
       (cof1 (positive-cofactor4 n x))
       ((when (eql cof1 (truth4-fix x)))
        (aignet-build-truth4-simple (cdr indices) x strash aignet))
       (cof0 (negative-cofactor4 n x))
       ((mv lit1 strash aignet) (aignet-build-truth4-simple (cdr indices) cof1 strash aignet))
       ((mv lit0 strash aignet) (aignet-build-truth4-simple (cdr indices) cof0 strash aignet)))
    (aignet::aignet-hash-mux (aignet::mk-lit (innum->id n aignet) 0)
                             lit1 lit0 9 strash aignet))
  ///
  (aignet::def-aignet-preservation-thms aignet-build-truth4-simple :stobjname aignet)

  (defret stype-counts-preserved-of-aignet-build-truth4-simple
    (let ((aignet::new-aignet new-aignet)
          (aignet::aignet aignet))
      #!aignet
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (stype-count stype new-aignet)
                      (stype-count stype aignet)))))

  (defret aignet-litp-of-aignet-build-truth4-simple
    (implies (and (<= 4 (aignet::num-ins aignet))
                  (index-listp indices 4))
             (aignet::aignet-litp lit new-aignet))
    :hints(("Goal" :in-theory (enable index-listp))))

  (verify-guards aignet-build-truth4-simple
    :hints(("Goal" :expand ((index-listp indices 4))))
    :guard-debug t)


  (local (defthm env-update-redundant-split
           (implies (case-split (iff val (env-lookup n env)))
                    (equal (env-update n val env)
                           (nfix env)))))

  (local (defthm truth-eval-when-norm-equals-norm-minus1
           (implies (equal (truth-norm x numvars) (truth-norm -1 numvars))
                    (truth-eval x env numvars))
           :hints (("goal" :use ((:instance truth-eval-of-truth-norm
                                  (truth x))
                                 (:instance truth-eval-of-truth-norm
                                  (truth -1)))
                    :in-theory (disable truth-eval-of-truth-norm)))))

  (local (defthm truth-eval-when-norm-equals-0
           (implies (equal (truth-norm x numvars) 0)
                    (not (truth-eval x env numvars)))
           :hints (("goal" :use ((:instance truth-eval-of-truth-norm
                                  (truth x)))
                    :in-theory (disable truth-eval-of-truth-norm)))))

  (defret lit-eval-of-aignet-build-truth4-simple
    (implies (and (index-listp indices 4)
                  (only-depends-on x indices 4)
                  (<= 4 (aignet::num-ins aignet)))
             (equal (aignet::lit-eval lit invals regvals new-aignet)
                    (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4))))
    :hints(("Goal" :in-theory (enable bool->bit acl2::b-not acl2::b-and index-listp)
            :induct <call>
            :expand ((:free (in) (aignet::lit-eval (aignet::mk-lit in 0) invals regvals aignet))
                     (:free (x) (aignet::id-eval (aignet::fanin-count x) invals regvals aignet)))
            :do-not-induct t)
           (acl2::use-termhint
            (b* (((when (atom indices))
                  ''(:use ((:instance only-depends-on-atom-when-truth-not-constant
                            (numvars 4)))
                     :in-theory (disable only-depends-on-atom-when-truth-not-constant))))
              nil)))))



(define full-perm-p-aux ((n natp)
                         (vars true-listp)
                         (numvars natp))
  :guard (<= n numvars)
  :measure (nfix (- (nfix numvars) (nfix n)))
  (b* (((when (mbe :logic (zp (- (nfix numvars) (nfix n)))
                   :exec (eql n numvars)))
        t))
    (and (member (lnfix n) vars)
         (full-perm-p-aux (1+ (lnfix n)) vars numvars)))
  ///
  (defthm full-perm-p-aux-implies-only-depends-on
    (implies (full-perm-p-aux n vars numvars)
             (only-depends-on-aux n truth vars numvars))
    :hints(("Goal" :in-theory (enable only-depends-on-aux)))))

(define full-perm-p ((vars true-listp)
                     (numvars natp))
  (full-perm-p-aux 0 vars numvars)
  ///
  (defthm full-perm-p-implies-only-depends-on
    (implies (full-perm-p vars numvars)
             (only-depends-on truth vars numvars))
    :hints(("Goal" :in-theory (enable only-depends-on)))))



(defines aignet-build-truth4-decomp-single
  :prepwork ((local
              (defthm depends-on-when-positive-cofactor-not-equal-x
                (implies (and (< (nfix n) (nfix numvars))
                              (not (equal (positive-cofactor n x numvars) (truth-norm x numvars))))
                         (depends-on n x numvars)))))
  (define aignet-build-truth4-decomp-single-try ((n natp)
                                                 (x truth4-p)
                                                 strash
                                                 aignet
                                                 (full-indices (and (index-listp full-indices 4)
                                                               (full-perm-p full-indices 4))))
    :returns (mv successp
                 (lit aignet::litp :rule-classes :type-prescription)
                 (new-strash)
                 (new-aignet))
    :guard (and (< n 4)
                (<= 4 (aignet::num-ins aignet)))
    :well-founded-relation acl2::nat-list-<
    :measure (list (count-truth4-deps x) 0)
    :verify-guards nil
    (b* ((aignet (aignet::aignet-fix aignet))
         ((unless (mbt (< (nfix n) 4)))
          (mv nil 0 strash aignet))
         (cof1 (positive-cofactor4 n x))
         ((when (eql cof1 (truth4-fix x)))
          ;; x is independent of n -- no decomp
          (mv nil 0 strash aignet))
         (cof0 (negative-cofactor4 n x))
         ((acl2::symlet recur0)
          ((mv cof0-lit strash aignet)
           (aignet-build-truth4-decomp-single-or-simple cof0 strash aignet full-indices)))
         ((acl2::symlet recur1)
          ((mv cof1-lit strash aignet)
           (aignet-build-truth4-decomp-single-or-simple cof1 strash aignet full-indices)))
         
         ((when (eql cof0 0))
          (b* (recur1
               ((mv lit strash aignet) (aignet::aignet-hash-and
                                        (aignet::mk-lit (innum->id n aignet) 0)
                                        cof1-lit
                                        9 strash aignet)))
            (mv t lit strash aignet)))

         ((when (eql cof0 #xffff))
          (b* (recur1
               ((mv lit strash aignet) (aignet::aignet-hash-or
                                        (aignet::mk-lit (innum->id n aignet) 1)
                                        cof1-lit
                                        9 strash aignet)))
            (mv t lit strash aignet)))

         ((when (eql cof1 0))
          (b* (recur0
               ((mv lit strash aignet) (aignet::aignet-hash-and
                                        (aignet::mk-lit (innum->id n aignet) 1)
                                        cof0-lit
                                        9 strash aignet)))
            (mv t lit strash aignet)))

         ((when (eql cof1 #xffff))
          (b* (recur0
               ((mv lit strash aignet) (aignet::aignet-hash-or
                                        (aignet::mk-lit (innum->id n aignet) 0)
                                        cof0-lit
                                        9 strash aignet)))
            (mv t lit strash aignet)))

         ((when (eql cof0 (truth-norm4 (lognot cof1))))
          (b* (recur0
               ((mv lit strash aignet) (aignet::aignet-hash-xor
                                        (aignet::mk-lit (innum->id n aignet) 0)
                                        cof0-lit
                                        9 strash aignet)))
            (mv t lit strash aignet))))
      (mv nil 0 strash aignet)))

  (define aignet-build-truth4-decomp-single-or-simple ((x truth4-p)
                                                       strash
                                                       aignet
                                                       (full-indices (and (index-listp full-indices 4)
                                                                     (full-perm-p full-indices 4))))
    :guard (<= 4 (aignet::num-ins aignet))
    :measure (list (count-truth4-deps x) (+ 1 (len full-indices)))
    :returns (mv (lit aignet::litp :rule-classes :type-prescription)
                 (new-strash)
                 (new-aignet))
    (b* (((mv ok lit strash aignet)
          (aignet-build-truth4-decomp-single full-indices x strash aignet full-indices))
         ((when ok) (mv lit strash aignet)))
      (aignet-build-truth4-simple full-indices x strash aignet)))

  (define aignet-build-truth4-decomp-single ((indices (index-listp indices 4))
                                             (x truth4-p)
                                             strash
                                             aignet
                                             (full-indices (and (index-listp full-indices 4)
                                                                (full-perm-p full-indices 4))))
    :guard (<= 4 (aignet::num-ins aignet))
    :measure (list (count-truth4-deps x) (len indices))
    :returns (mv (successp)
                 (lit aignet::litp :rule-classes :type-prescription)
                 (new-strash)
                 (new-aignet))
    (b* ((aignet (aignet::aignet-fix aignet))
         ((when (atom indices))
          (mv nil 0 strash aignet))
         ((mv ok lit strash aignet)
          (aignet-build-truth4-decomp-single-try (car indices) x strash aignet full-indices))
         ((when ok) (mv ok lit strash aignet)))
      (aignet-build-truth4-decomp-single (cdr indices) x strash aignet full-indices)))
  ///
  (std::defret-mutual aignet-extension-p-of-aignet-build-truth4-decomp-single
    (defret aignet-extension-p-of-aignet-build-truth4-decomp-single-try
      (aignet::aignet-extension-p new-aignet aignet)
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single-try)
    (defret aignet-extension-p-of-aignet-build-truth4-decomp-single-or-simple
      (aignet::aignet-extension-p new-aignet aignet)
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single-or-simple)
    (defret aignet-extension-p-of-aignet-build-truth4-decomp-single
      (aignet::aignet-extension-p new-aignet aignet)
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single))

  (std::defret-mutual stype-counts-preserved-of-aignet-build-truth4-single
    (defret stype-counts-preserved-of-aignet-build-truth4-single-try
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (aignet::stype-count stype new-aignet)
                      (aignet::stype-count stype aignet)))
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single-try)
    (defret stype-counts-preserved-of-aignet-build-truth4-single-or-simple
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (aignet::stype-count stype new-aignet)
                      (aignet::stype-count stype aignet)))
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single-or-simple)
    (defret stype-counts-preserved-of-aignet-build-truth4-single
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (aignet::stype-count stype new-aignet)
                      (aignet::stype-count stype aignet)))
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single))

  (std::defret-mutual aignet-litp-of-aignet-build-truth4-single
    (defret aignet-litp-of-aignet-build-truth4-single-try
      (implies (and (<= 4 (aignet::num-ins aignet))
                    (index-listp full-indices 4))
               (aignet::aignet-litp lit new-aignet))
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single-try)
    (defret aignet-litp-of-aignet-build-truth4-single-or-simple
      (implies (and (<= 4 (aignet::num-ins aignet))
                    (index-listp full-indices 4))
               (aignet::aignet-litp lit new-aignet))
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single-or-simple)
    (defret aignet-litp-of-aignet-build-truth4-single
      (implies (and (<= 4 (aignet::num-ins aignet))
                    (index-listp full-indices 4))
               (aignet::aignet-litp lit new-aignet))
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single))

  (verify-guards aignet-build-truth4-decomp-single
    :hints (("goal" :expand ((index-listp indices 4)))))


  (local (defthm env-update-redundant-split
           (implies (case-split (iff val (env-lookup n env)))
                    (equal (env-update n val env)
                           (nfix env)))))

  (local (defthm not-equal-of-negative-cofactor
           (implies (and (bind-free '((env . (aignet::truth4-env-from-aignet-invals invals))) (env))
                         (not (equal (truth-eval cof env numvars)
                                     (truth-eval truth (env-update n nil env) numvars)))
                         (< (nfix n) (nfix numvars)))
                    (not (equal (negative-cofactor n truth numvars) cof)))
           :hints (("goal" :use negative-cofactor-correct
                    :in-theory (disable negative-cofactor-correct)))))

  (local (defthm not-equal-of-positive-cofactor
           (implies (and (bind-free '((env . (aignet::truth4-env-from-aignet-invals invals))) (env))
                         (not (equal (truth-eval cof env numvars)
                                     (truth-eval truth (env-update n t env) numvars)))
                         (< (nfix n) (nfix numvars)))
                    (not (equal (positive-cofactor n truth numvars) cof)))
           :hints (("goal" :use positive-cofactor-correct
                    :in-theory (disable positive-cofactor-correct)))))

  (std::defret-mutual lit-eval-of-aignet-build-truth4-single
    (defret lit-eval-of-aignet-build-truth4-single-try
      (implies (and successp
                    (index-listp full-indices 4)
                    (full-perm-p full-indices 4)
                    (<= 4 (aignet::num-ins aignet)))
               (equal (aignet::lit-eval lit invals regvals new-aignet)
                      (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4))))
      :hints ('(:expand (<call>
                         (:free (in neg) (aignet::lit-eval (aignet::mk-lit in neg) invals regvals aignet))
                         (:free (x) (aignet::id-eval (aignet::fanin-count x) invals regvals aignet)))
                :do-not-induct t
                :in-theory (enable bool->bit b-not b-and b-xor)))
      :fn aignet-build-truth4-decomp-single-try)
    (defret lit-eval-of-aignet-build-truth4-single-or-simple
      (implies (and (<= 4 (aignet::num-ins aignet))
                    (index-listp full-indices 4)
                    (full-perm-p full-indices 4))
               (equal (aignet::lit-eval lit invals regvals new-aignet)
                      (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4))))
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single-or-simple)
    (defret lit-eval-of-aignet-build-truth4-single
      (implies (and successp
                    (index-listp full-indices 4)
                    (full-perm-p full-indices 4)
                    (<= 4 (aignet::num-ins aignet)))
               (equal (aignet::lit-eval lit invals regvals new-aignet)
                      (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4))))
      :hints ('(:expand (<call>)))
      :fn aignet-build-truth4-decomp-single))

  (fty::deffixequiv-mutual aignet-build-truth4-decomp-single))



                                
(local (defthm truth-norm-lognot-truth-norm
         (equal (truth-norm (lognot (truth-norm x numvars)) numvars)
                (truth-norm (lognot x) numvars))
         :hints(("Goal" :in-theory (enable truth-norm)))))

(define truth4-is-z-or-negation ((x truth4-p)
                                 (z truth4-p)
                                 (~z (equal ~z (truth-norm4 (lognot z)))))
  (b* ((x (truth4-fix x))
       (z (truth4-fix z))
       (~z (mbe :logic (truth-norm4 (lognot z))
                :exec ~z)))
    (or (eql x 0) (eql x #xffff) (eql x z) (eql x ~z)))
  ///
  (defthm truth4-is-z-or-negation-normalize-~z
    (implies (syntaxp (not (equal ~z ''nil)))
             (equal (truth4-is-z-or-negation x z ~z)
                    (truth4-is-z-or-negation x z nil)))))

(define truth4-decomp-cofactor-lit ((x truth4-p)
                                    (z truth4-p)
                                    (z-lit aignet::litp))
  :returns (x-lit aignet::litp)
  
  (cond ((eql (truth4-fix x) 0)              0)
        ((eql (truth4-fix x) #xffff)         1)
        ((eql (truth4-fix x) (truth4-fix z)) (aignet::lit-fix z-lit))
        (t                                   (aignet::lit-negate z-lit)))
  ///
  (defret aignet-litp-of-truth4-decomp-cofactor-lit
    (implies (aignet::aignet-litp z-lit aignet)
             (aignet::aignet-litp x-lit aignet)))

  (local (defthm truth-eval-when-norm-equals-norm-minus1
           (implies (equal (truth-norm x numvars) (truth-norm -1 numvars))
                    (truth-eval x env numvars))
           :hints (("goal" :use ((:instance truth-eval-of-truth-norm
                                  (truth x))
                                 (:instance truth-eval-of-truth-norm
                                  (truth -1)))
                    :in-theory (disable truth-eval-of-truth-norm)))))

  (local (defthm truth-eval-when-norm-equals-0
           (implies (equal (truth-norm x numvars) 0)
                    (not (truth-eval x env numvars)))
           :hints (("goal" :use ((:instance truth-eval-of-truth-norm
                                  (truth x)))
                    :in-theory (disable truth-eval-of-truth-norm)))))

  (local (defthm truth-eval-when-truth-norm-equal
           (implies (and (equal (truth-norm x numvars)
                                (truth-norm z numvars))
                         (syntaxp (and (equal x 'x)
                                       (equal z 'z))))
                    (equal (truth-eval x env numvars)
                           (truth-eval z env numvars)))
           :hints(("Goal" :use ((:instance truth-eval-of-truth-norm
                                 (truth x))
                                (:instance truth-eval-of-truth-norm
                                 (truth z)))
                   :in-theory (disable truth-eval-of-truth-norm)))))

  (local (defthm truth-norm-not-equal-lognot
           (implies (natp numvars)
                    (not (equal (truth-norm x numvars)
                                (truth-norm (lognot x) numvars))))
           :hints(("Goal" :in-theory (enable truth-norm)
                   :expand ((:free (x) (loghead (ash 1 numvars) x)))))))

  (local (defthm truth-eval-when-truth-norm-equal-lognot
           (implies (and (equal (truth-norm x numvars)
                                (truth-norm (lognot z) numvars))
                         (syntaxp (and (equal x 'x)
                                       (equal z 'z))))
                    (equal (truth-eval x env numvars)
                           (not (truth-eval z env numvars))))
           :hints(("Goal" :use ((:instance truth-eval-of-truth-norm
                                 (truth x))
                                (:instance truth-eval-of-truth-norm
                                 (truth (lognot z))))
                   :in-theory (disable truth-eval-of-truth-norm
                                       truth-eval-when-truth-norm-equal)))))

  (local (defthmd loghead-of-lognot-equal
           (implies (natp n)
                    (iff (equal (loghead n (lognot x)) y)
                         (and (unsigned-byte-p n y)
                              (equal (loghead n x) (loghead n (lognot y))))))
           :hints(("Goal" :in-theory (enable* ihsext-inductions
                                              ihsext-recursive-redefs)))))

  (local (defthm truth-norm-lognot-equals-const
           (implies (and (syntaxp (quotep q))
                         (natp numvars))
                    (equal (equal (truth-norm (lognot x) numvars) q)
                           (and (unsigned-byte-p (ash 1 numvars) q)
                                (equal (truth-norm x numvars) (truth-norm (lognot q) numvars)))))
           :hints(("Goal" :in-theory (enable truth-norm)
                   :use ((:instance loghead-of-lognot-equal
                          (y q) (n (ash 1 numvars))))))))


  (defret truth4-decomp-cofactor-lit-correct
    (implies (and (equal (aignet::lit-eval z-lit invals regvals aignet)
                         (bool->bit (truth-eval z (truth4-env-from-aignet-invals invals) 4)))
                  (truth4-is-z-or-negation x z nil))
             (equal (aignet::lit-eval x-lit invals regvals aignet)
                    (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4))))
    :hints(("Goal" :in-theory (enable truth4-is-z-or-negation b-not)))))
  

(define truth4-decomp-find-non-const-cofactor ((f00 truth4-p)
                                               (f01 truth4-p)
                                               (f10 truth4-p)
                                               (f11 truth4-p))
  :returns (z (iff (truth4-p z) z))
  (b* ((f00 (truth4-fix f00))
       (f01 (truth4-fix f01))
       (f10 (truth4-fix f10))
       (f11 (truth4-fix f11)))
    (cond ((not (or (eql f00 0) (eql f00 #xffff))) f00)
          ((not (or (eql f01 0) (eql f01 #xffff))) f01)
          ((not (or (eql f10 0) (eql f10 #xffff))) f10)
          ((not (or (eql f11 0) (eql f11 #xffff))) f11)
          (t nil))))


    

;; (define truth4-decomp-check-decomposable ((f00 truth4-p)
;;                                           (f01 truth4-p)
;;                                           (f10 truth4-p)
;;                                           (f11 truth4-p)
;;                                           (z   truth4-p))
;;   (b* ((f00 (truth4-fix f00))
;;        (f01 (truth4-fix f01))
;;        (f10 (truth4-fix f10))
;;        (f11 (truth4-fix f11))
;;        (z   (truth4-fix z))
;;        (~z (truth-norm4 (lognot z))))
;;     (and (or (eql f00 0) (eql f00 #xffff) (eql f00 z) (eql f00 ~z))
;;          (or (eql f01 0) (eql f01 #xffff) (eql f01 z) (eql f01 ~z))
;;          (or (eql f10 0) (eql f10 #xffff) (eql f10 z) (eql f10 ~z))
;;          (or (eql f11 0) (eql f11 #xffff) (eql f11 z) (eql f11 ~z)))))
  
(define aignet-build-truth4-decomp-try ((n natp)
                                        (m natp)
                                        (truth truth4-p)
                                        strash
                                        aignet
                                        (full-indices (and (index-listp full-indices 4)
                                                           (full-perm-p full-indices 4))))
  :returns (mv success
               (lit aignet::litp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  :guard (and (< n 4) (< m 4)
              (<= 4 (num-ins aignet)))
  (b* ((truth (truth4-fix truth))
       (f0 (negative-cofactor4 n truth))
       (f1 (positive-cofactor4 n truth))
       ;; ((cond (eql f0 f1))
       ;;  ;; no dependency on n
       ;;  nil)
       (f00 (negative-cofactor4 m f0))
       (f01 (positive-cofactor4 m f0))
       (f10 (negative-cofactor4 m f1))
       (f11 (positive-cofactor4 m f1))

       (aignet (aignet::aignet-fix aignet))

       ((when (or (and (eql f00 f01)
                       (eql f10 f11))
                  (and (eql f00 f10)
                       (eql f01 f11))))
        ;; independent of n or m -- use single/simple instead
        (mv nil 0 strash aignet))

       ;; z is some non-constant cofactor
       (z (truth4-decomp-find-non-const-cofactor f00 f01 f10 f11))

       ((unless z)
        ;; no dependency on other two vars -- should use single/simple instead
        (mv nil 0 strash aignet))
       
       (~z (truth-norm4 (lognot z)))

       ((unless (and (truth4-is-z-or-negation f00 z ~z)
                     (truth4-is-z-or-negation f01 z ~z)
                     (truth4-is-z-or-negation f10 z ~z)
                     (truth4-is-z-or-negation f11 z ~z)))
        ;; not decomposable by n, m -- unrelated nonconstant cofactors.  Fall back on simple.
        (mv nil 0 strash aignet))

       
       ;; Everything below succeeds.
       ((mv lit strash aignet)
        (b* ((n-lit (aignet::mk-lit (aignet::innum->id n aignet) 0))
             (m-lit (aignet::mk-lit (aignet::innum->id m aignet) 0))
             ((mv zlit strash aignet) (aignet-build-truth4-decomp-single-or-simple z strash aignet full-indices))
             
             (f00-lit (truth4-decomp-cofactor-lit f00 z zlit))
             (f01-lit (truth4-decomp-cofactor-lit f01 z zlit))
             (f10-lit (truth4-decomp-cofactor-lit f10 z zlit))
             (f11-lit (truth4-decomp-cofactor-lit f11 z zlit))

             ;; ((when x)
             ;;  (b* (((mv f1-lit strash aignet)
             ;;        (aignet::aignet-hash-mux m-lit f11-lit f10-lit 9 strash aignet))
             ;;       ((mv f0-lit strash aignet)
             ;;        (aignet::aignet-hash-mux m-lit f01-lit f00-lit 9 strash aignet))
             ;;       ((mv truth-lit strash aignet)
             ;;        (aignet::aignet-hash-mux n-lit f1-lit f0-lit 9 strash aignet)))
             ;;    (mv t truth-lit strash aignet)))

             ;; All cofactors are z or y.  Check all combos
             ((when (and (eql f01 f10)
                         (eql f01 f11)))
              (b* (((mv m-or-n-lit strash aignet)
                    (aignet::aignet-hash-or n-lit m-lit 9 strash aignet)))
                (aignet::aignet-hash-mux m-or-n-lit f01-lit f00-lit 9 strash aignet)))

             ;; f01 differs from other 3
             ((when (and (eql f00 f10)
                         (eql f00 f11)))
              (b* (((mv ~n-and-m-lit strash aignet)
                    (aignet::aignet-hash-and (aignet::lit-negate n-lit) m-lit 9 strash aignet)))
                (aignet::aignet-hash-mux ~n-and-m-lit f01-lit f00-lit 9 strash aignet)))

             ;; f10 differs from other 3
             ((when (and (eql f00 f01)
                         (eql f00 f11)))
              (b* (((mv n-and-~m-lit strash aignet)
                    (aignet::aignet-hash-and n-lit (aignet::lit-negate m-lit) 9 strash aignet)))
                (aignet::aignet-hash-mux n-and-~m-lit f10-lit f00-lit 9 strash aignet)))

             ;; f11 differs from other 3
             ((when (and (eql f00 f01)
                         (eql f00 f10)))
              (b* (((mv n-and-m-lit strash aignet)
                    (aignet::aignet-hash-and n-lit m-lit 9 strash aignet)))
                (aignet::aignet-hash-mux n-and-m-lit f11-lit f00-lit 9 strash aignet)))
             
             ;; f00, f11 | f01, f10
             ((when (and (eql f00 f11)
                         (eql f01 f10)))
              (b* (((mv n-xor-m-lit strash aignet)
                    (aignet::aignet-hash-xor n-lit m-lit 9 strash aignet)))
                (aignet::aignet-hash-mux n-xor-m-lit f01-lit f00-lit 9 strash aignet)))

             ;; 3-way decomposition -- just do double Shannon expansion.

             ((mv f1-lit strash aignet)
              (aignet::aignet-hash-mux m-lit f11-lit f10-lit 9 strash aignet))
             ((mv f0-lit strash aignet)
              (aignet::aignet-hash-mux m-lit f01-lit f00-lit 9 strash aignet)))
          (aignet::aignet-hash-mux n-lit f1-lit f0-lit 9 strash aignet))))

    (mv t lit strash aignet))
  ///
  (aignet::def-aignet-preservation-thms aignet-build-truth4-decomp-try :stobjname aignet)

  (defret stype-counts-preserved-of-aignet-build-truth4-decomp-try
    (let ((aignet::new-aignet new-aignet)
          (aignet::aignet aignet))
      #!aignet
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (stype-count stype new-aignet)
                      (stype-count stype aignet)))))

  (defret aignet-litp-of-aignet-build-truth4-decomp-try
    (implies (and (<= 4 (aignet::num-ins aignet))
                  (< (nfix n) 4)
                  (< (nfix m) 4)
                  (index-listp full-indices 4))
             (aignet::aignet-litp lit new-aignet)))


  ;; (local (defthm env-update-redundant-split
  ;;          (implies (case-split (iff val (env-lookup n env)))
  ;;                   (equal (env-update n val env)
  ;;                          (nfix env)))))

  ;; (local (defthm truth-eval-when-norm-equals-norm-minus1
  ;;          (implies (equal (truth-norm x numvars) (truth-norm -1 numvars))
  ;;                   (truth-eval x env numvars))
  ;;          :hints (("goal" :use ((:instance truth-eval-of-truth-norm
  ;;                                 (truth x))
  ;;                                (:instance truth-eval-of-truth-norm
  ;;                                 (truth -1)))
  ;;                   :in-theory (disable truth-eval-of-truth-norm)))))

  ;; (local (defthm truth-eval-when-norm-equals-0
  ;;          (implies (equal (truth-norm x numvars) 0)
  ;;                   (not (truth-eval x env numvars)))
  ;;          :hints (("goal" :use ((:instance truth-eval-of-truth-norm
  ;;                                 (truth x)))
  ;;                   :in-theory (disable truth-eval-of-truth-norm)))))


  (local
   (progn
     (defthmd not-equal-of-negative-negative-cofactor
       (implies (and (syntaxp (or (acl2::rewriting-negative-literal-fn
                                   `(equal (negative-cofactor ,m (negative-cofactor ,n ,truth ,numvars) ,numvars) ,cof)
                                   mfc state)
                                  (acl2::rewriting-negative-literal-fn
                                   `(equal ,cof (negative-cofactor ,m (negative-cofactor ,n ,truth ,numvars) ,numvars))
                                   mfc state)))
                     (bind-free '((env . (aignet::truth4-env-from-aignet-invals invals))) (env))
                     (< (nfix n) (nfix numvars))
                     (< (nfix m) (nfix numvars)))
                (iff (equal (negative-cofactor m (negative-cofactor n truth numvars) numvars) cof)
                     (and (hide (equal (negative-cofactor m (negative-cofactor n truth numvars) numvars) cof))
                          (equal (truth-eval cof env numvars)
                                 (truth-eval truth (env-update n nil (env-update m nil env)) numvars)))))
       :hints (("goal" :expand ((:free (x) (hide x))))))

     (defthmd not-equal-of-negative-positive-cofactor
       (implies (and (syntaxp (or (acl2::rewriting-negative-literal-fn
                                   `(equal (negative-cofactor ,m (positive-cofactor ,n ,truth ,numvars) ,numvars) ,cof)
                                   mfc state)
                                  (acl2::rewriting-negative-literal-fn
                                   `(equal ,cof (negative-cofactor ,m (positive-cofactor ,n ,truth ,numvars) ,numvars))
                                   mfc state)))
                     (bind-free '((env . (aignet::truth4-env-from-aignet-invals invals))) (env))
                     (< (nfix n) (nfix numvars))
                     (< (nfix m) (nfix numvars)))
                (iff (equal (negative-cofactor m (positive-cofactor n truth numvars) numvars) cof)
                     (and (hide (equal (negative-cofactor m (positive-cofactor n truth numvars) numvars) cof))
                          (equal (truth-eval cof env numvars)
                                 (truth-eval truth (env-update n t (env-update m nil env)) numvars)))))
       :hints (("goal" :expand ((:free (x) (hide x))))))

     (defthmd not-equal-of-positive-negative-cofactor
       (implies (and (syntaxp (or (acl2::rewriting-negative-literal-fn
                                   `(equal (positive-cofactor ,m (negative-cofactor ,n ,truth ,numvars) ,numvars) ,cof)
                                   mfc state)
                                  (acl2::rewriting-negative-literal-fn
                                   `(equal ,cof (positive-cofactor ,m (negative-cofactor ,n ,truth ,numvars) ,numvars))
                                   mfc state)))
                     (bind-free '((env . (aignet::truth4-env-from-aignet-invals invals))) (env))
                     (< (nfix n) (nfix numvars))
                     (< (nfix m) (nfix numvars)))
                (iff (equal (positive-cofactor m (negative-cofactor n truth numvars) numvars) cof)
                     (and (hide (equal (positive-cofactor m (negative-cofactor n truth numvars) numvars) cof))
                          (equal (truth-eval cof env numvars)
                                 (truth-eval truth (env-update n nil (env-update m t env)) numvars)))))
       :hints (("goal" :expand ((:free (x) (hide x))))))

     (defthmd not-equal-of-positive-positive-cofactor
       (implies (and (syntaxp (or (acl2::rewriting-negative-literal-fn
                                   `(equal (positive-cofactor ,m (positive-cofactor ,n ,truth ,numvars) ,numvars) ,cof)
                                   mfc state)
                                  (acl2::rewriting-negative-literal-fn
                                   `(equal ,cof (positive-cofactor ,m (positive-cofactor ,n ,truth ,numvars) ,numvars))
                                   mfc state)))
                     (bind-free '((env . (aignet::truth4-env-from-aignet-invals invals))) (env))
                     (< (nfix n) (nfix numvars))
                     (< (nfix m) (nfix numvars)))
                (iff (equal (positive-cofactor m (positive-cofactor n truth numvars) numvars) cof)
                     (and (hide (equal (positive-cofactor m (positive-cofactor n truth numvars) numvars) cof))
                          (equal (truth-eval cof env numvars)
                                 (truth-eval truth (env-update n t (env-update m t env)) numvars)))))
       :hints (("goal" :expand ((:free (x) (hide x))))))))

  (local (defthmd env-update-redundant-split
           (implies (case-split (iff val (env-lookup n env)))
                    (equal (env-update n val env)
                           (nfix env)))))

  ;; (local (defthm eval-of-env-update-when-other-update-1
  ;;          (implies (and (acl2::rewriting-negative-literal
  ;;                         `(truth-eval ,x (env-update ,n ,val ,env) ,numvars))
  ;;                        (truth-eval x (env-update n (not val) env) numvars))
  ;;                   (equal (truth-eval x (env-update n val env) numvars)
  ;;                          (and (hide (truth-eval x (env-update n val env) numvars))
  ;;                               (truth-eval x env numvars))))
  ;;          :hints(("Goal" :in-theory (enable env-update-redundant-split)
  ;;                  :expand ((:free (x) (hide x)))))))

  ;; (local (defthm eval-of-env-update-when-other-update-2
  ;;          (implies (and (acl2::rewriting-positive-literal
  ;;                         `(truth-eval ,x (env-update ,n ,val ,env) ,numvars))
  ;;                        (not (truth-eval x (env-update n (not val) env) numvars)))
  ;;                   (equal (truth-eval x (env-update n val env) numvars)
  ;;                          (or (hide (truth-eval x (env-update n val env) numvars))
  ;;                              (truth-eval x env numvars))))
  ;;          :hints(("Goal" :in-theory (enable env-update-redundant-split)
  ;;                  :expand ((:free (x) (hide x)))))))

  ;; (local (defthm eval-of-env-update-when-other-update-1-2
  ;;          (implies (and (acl2::rewriting-negative-literal
  ;;                         `(truth-eval ,x (env-update ,m ,val1 (env-update ,n ,val ,env)) ,numvars))
  ;;                        (truth-eval x (env-update m val1 (env-update n (not val) env)) numvars))
  ;;                   (equal (truth-eval x (env-update m val1 (env-update n val env)) numvars)
  ;;                          (and (hide (truth-eval x (env-update m val1 (env-update n val env)) numvars))
  ;;                               (truth-eval x (env-update m val1 env) numvars))))
  ;;          :hints(("Goal" :in-theory (enable env-update-redundant-split)
  ;;                  :expand ((:free (x) (hide x)))))))

  ;; (local (defthm eval-of-env-update-when-other-update-2-2
  ;;          (implies (and (acl2::rewriting-positive-literal
  ;;                         `(truth-eval ,x (env-update ,m ,val1 (env-update ,n ,val ,env)) ,numvars))
  ;;                        (not (truth-eval x (env-update m val1 (env-update n (not val) env)) numvars)))
  ;;                   (equal (truth-eval x (env-update m val1 (env-update n val env)) numvars)
  ;;                          (or (hide (truth-eval x (env-update m val1 (env-update n val env)) numvars))
  ;;                              (truth-eval x (env-update m val1 env) numvars))))
  ;;          :hints(("Goal" :in-theory (enable env-update-redundant-split)
  ;;                  :expand ((:free (x) (hide x)))))))

  ;; (local (defthm eval-when-both-env-updates-true
  ;;          (implies (and (truth-eval x (env-update n t env) numvars)
  ;;                        (truth-eval x (env-update n nil env) numvars))
  ;;                   (truth-eval x env numvars))
  ;;          :hints(("Goal" :in-theory (enable env-update-redundant-split)))))

  ;; (local (defthm eval-when-both-env-updates-false
  ;;          (implies (and (not (truth-eval x (env-update n t env) numvars))
  ;;                        (not (truth-eval x (env-update n nil env) numvars)))
  ;;                   (not (truth-eval x env numvars)))
  ;;          :hints(("Goal" :in-theory (enable env-update-redundant-split)))))

  ;; (local (defthm eval-when-all-four-env-updates-true
  ;;          (implies (and (truth-eval x (env-update m t (env-update n t env)) numvars)
  ;;                        (truth-eval x (env-update m t (env-update n nil env)) numvars)
  ;;                        (truth-eval x (env-update m nil (env-update n t env)) numvars)
  ;;                        (truth-eval x (env-update m nil (env-update n nil env)) numvars))
  ;;                   (truth-eval x env numvars))
  ;;          :hints(("Goal" :in-theory (enable env-update-redundant-split)))))

  ;; (local (defthm eval-when-all-four-env-updates-false
  ;;          (implies (and (not (truth-eval x (env-update m t (env-update n t env)) numvars))
  ;;                        (not (truth-eval x (env-update m t (env-update n nil env)) numvars))
  ;;                        (not (truth-eval x (env-update m nil (env-update n t env)) numvars))
  ;;                        (not (truth-eval x (env-update m nil (env-update n nil env)) numvars)))
  ;;                   (not (truth-eval x env numvars)))
  ;;          :hints(("Goal" :in-theory (enable env-update-redundant-split)))))

  (local (defthm equal-of-truth-evals
           (equal (equal (truth-eval x env numvars)
                         (truth-eval x1 env1 numvars1))
                  (iff (truth-eval x env numvars)
                       (truth-eval x1 env1 numvars1)))))

  (defret lit-eval-of-aignet-build-truth4-decomp-try
    (implies (and (<= 4 (aignet::num-ins aignet))
                  (< (nfix n) 4)
                  (< (nfix m) 4)
                  (not (equal (nfix n) (nfix m)))
                  (index-listp full-indices 4)
                  (full-perm-p full-indices 4)
                  success)
             (equal (aignet::lit-eval lit invals regvals new-aignet)
                    (bool->bit (truth-eval truth (truth4-env-from-aignet-invals invals) 4))))
    :hints(("Goal" ;; :in-theory (enable bool->bit acl2::b-not acl2::b-and b-ior bfix)
            :expand ((:free (in val) (aignet::lit-eval (aignet::mk-lit in val) invals regvals aignet))
                     (:free (x) (aignet::id-eval (aignet::fanin-count x) invals regvals aignet)))
            :do-not-induct t)
            (and stable-under-simplificationp
                 '(:in-theory (enable not-equal-of-negative-negative-cofactor
                                      not-equal-of-negative-positive-cofactor
                                      not-equal-of-positive-negative-cofactor
                                      not-equal-of-positive-positive-cofactor)))
            (and stable-under-simplificationp
                 '(:computed-hint-replacement
                   ('(:cases ((equal (nth m invals) 1))))
                   :cases ((equal (nth n invals) 1))
                   :in-theory (enable b-not bool->bit bfix b-ior)))))

  (defret stobjs-preserved-when-unsuccessful-of-aignet-build-truth4-decomp-try
    (implies (not success)
             (and (equal new-aignet (aignet::node-list-fix aignet))
                  (equal new-strash strash)))))




(define aignet-build-truth4-decomp-rec1 ((n natp)
                                         (indices (index-listp indices 4))
                                         (x truth4-p)
                                         strash
                                         aignet
                                         (full-indices (and (index-listp full-indices 4)
                                                            (full-perm-p full-indices 4))))
  ;; Should only be called on truth tables with 4 dependencies.
  :guard (and (< n 4)
              (<= 4 (num-ins aignet)))
  :returns (mv (successp)
               (lit aignet::litp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  :well-founded-relation acl2::nat-list-<
  :measure (len indices)
  :guard-hints (("goal" :expand ((index-listp indices 4))))
  (b* ((aignet (aignet::aignet-fix aignet))
       ((when (atom indices))
        (mv nil 0 strash aignet))
       (m (lnfix (car indices)))
       ((when (eql (lnfix n) (lnfix m)))
        (aignet-build-truth4-decomp-rec1 n (cdr indices) x strash aignet full-indices))
       ((mv success lit strash aignet)
        (aignet-build-truth4-decomp-try n m x strash aignet full-indices))
       ((when success)
        (mv t lit strash aignet)))
    (aignet-build-truth4-decomp-rec1 n (cdr indices) x strash aignet full-indices))
  ///
  (aignet::def-aignet-preservation-thms aignet-build-truth4-decomp-rec1 :stobjname aignet)

  (defret stype-counts-preserved-of-aignet-build-truth4-decomp-rec1
    (let ((aignet::new-aignet new-aignet)
          (aignet::aignet aignet))
      #!aignet
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (stype-count stype new-aignet)
                      (stype-count stype aignet)))))

  (defret aignet-litp-of-aignet-build-truth4-decomp-rec1
    (implies (and (<= 4 (aignet::num-ins aignet))
                  (< (nfix n) 4)
                  (index-listp full-indices 4)
                  (index-listp indices 4))
             (aignet::aignet-litp lit new-aignet))
    :hints (("goal" :induct t :expand ((index-listp indices 4)))))

  (defret lit-eval-of-aignet-build-truth4-decomp-rec1
    (implies (and (<= 4 (aignet::num-ins aignet))
                  (< (nfix n) 4)
                  (index-listp indices 4)
                  (index-listp full-indices 4)
                  (full-perm-p full-indices 4)
                  successp)
             (equal (aignet::lit-eval lit invals regvals new-aignet)
                    (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4))))
    :hints (("goal" :induct t :expand ((index-listp indices 4))))))


(define aignet-build-truth4-decomp-rec ((indices (index-listp indices 4))
                                        (x truth4-p)
                                        strash
                                        aignet
                                        (full-indices (and (index-listp full-indices 4)
                                                           (full-perm-p full-indices 4))))
  ;; Should only be called on truth tables with 4 dependencies.
  :guard (and (<= 4 (num-ins aignet))
              (consp indices))
  :returns (mv (successp)
               (lit aignet::litp :rule-classes :type-prescription)
               (new-strash)
               (new-aignet))
  :well-founded-relation acl2::nat-list-<
  :measure (len indices)
  :guard-hints (("goal" :expand ((index-listp indices 4))))
  (b* ((aignet (aignet::aignet-fix aignet))
       ((when (atom (cdr indices)))
        (mv nil 0 strash aignet))
       ((mv success lit strash aignet)
        (aignet-build-truth4-decomp-rec1 (car indices) (cdr indices) x strash aignet full-indices))
       ((when success)
        (mv t lit strash aignet)))
    (aignet-build-truth4-decomp-rec (cdr indices) x strash aignet full-indices))
  ///
  (aignet::def-aignet-preservation-thms aignet-build-truth4-decomp-rec :stobjname aignet)

  (defret stype-counts-preserved-of-aignet-build-truth4-decomp-rec
    (let ((aignet::new-aignet new-aignet)
          (aignet::aignet aignet))
      #!aignet
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (stype-count stype new-aignet)
                      (stype-count stype aignet)))))

  (defret aignet-litp-of-aignet-build-truth4-decomp-rec
    (implies (and (<= 4 (aignet::num-ins aignet))
                  (index-listp full-indices 4)
                  (index-listp indices 4))
             (aignet::aignet-litp lit new-aignet))
    :hints (("goal" :induct t :expand ((index-listp indices 4)))))

  (defret lit-eval-of-aignet-build-truth4-decomp-rec
    (implies (and (<= 4 (aignet::num-ins aignet))
                  (index-listp indices 4)
                  (index-listp full-indices 4)
                  (full-perm-p full-indices 4)
                  successp)
             (equal (aignet::lit-eval lit invals regvals new-aignet)
                    (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4))))
    :hints (("goal" :induct t :expand ((index-listp indices 4))))))


(aignet::defstatsmgr dsd4stats
  (simple)
  (single)
  (double)
  (both)
  (node-simple)
  (node-single)
  (node-double)
  (node-both))

(define dsd4stats-snap (dsd4stats)
  :returns (lst eqlable-listp)
  (list (lnfix (dsd4stats-simple dsd4stats))
        (lnfix (dsd4stats-single dsd4stats))
        (lnfix (dsd4stats-double dsd4stats))
        (lnfix (dsd4stats-both dsd4stats))))

(define dsd4stats-fanin-count ((snap eqlable-listp) dsd4stats)
  (b* (((list ssimple ssingle sdouble sboth) snap)
       (dsd4stats (incr-dsd4stats-node-simple-cond (not (eql ssimple (dsd4stats-simple dsd4stats))) dsd4stats))
       (dsd4stats (incr-dsd4stats-node-single-cond (not (eql ssingle (dsd4stats-single dsd4stats))) dsd4stats))
       (dsd4stats (incr-dsd4stats-node-double-cond (not (eql sdouble (dsd4stats-double dsd4stats))) dsd4stats))
       (dsd4stats (incr-dsd4stats-node-both-cond (not (eql sboth (dsd4stats-both dsd4stats))) dsd4stats)))
    dsd4stats))

(define dsd4stats-count (single-ok double-ok dsd4stats)
  (if single-ok
      (if double-ok
          (incr-dsd4stats-both dsd4stats)
        (incr-dsd4stats-single dsd4stats))
    (if double-ok
        (incr-dsd4stats-double dsd4stats)
      (incr-dsd4stats-simple dsd4stats))))

(define aignet-build-truth4-decomp ((x truth4-p)
                                    strash
                                    aignet
                                    dsd4stats
                                    (full-indices (and (index-listp full-indices 4)
                                                       (full-perm-p full-indices 4))))
  :returns (mv (lits aignet::lit-listp)
               (new-strash)
               (new-aignet)
               (new-dsd4stats))
  :guard (<= 4 (num-ins aignet))
  ;; (b* ((num-deps (count-truth4-deps x))
  ;;      ((when (< num-deps 4))
  ;;       (aignet-build-truth4-decomp-single-or-simple x strash aignet full-indices))
  ;;      ((mv simple-ok lit strash aignet)
  ;;       (aignet-build-truth4-decomp-single full-indices x strash aignet full-indices))
  ;;      ((when simple-ok) (mv lit strash aignet))
  ;;      ((mv nonsimple-ok lit strash aignet)
  ;;       (aignet-build-truth4-decomp-rec full-indices x strash aignet full-indices))
  ;;      ((when nonsimple-ok) (mv lit strash aignet)))
  ;;   (aignet-build-truth4-simple full-indices x strash aignet))
  (b* (;; (num-deps (count-truth4-deps x))
       ((mv single-ok single-lit strash aignet)
        (aignet-build-truth4-decomp-single full-indices x strash aignet full-indices))
       ((mv double-ok double-lit strash aignet)
        (aignet-build-truth4-decomp-rec full-indices x strash aignet full-indices))
       (dsd4stats (dsd4stats-count single-ok double-ok dsd4stats)))
    (if single-ok
        (if (and double-ok
                 (not (eql single-lit double-lit)))
            (mv (list single-lit double-lit) strash aignet dsd4stats)
          (mv (list single-lit) strash aignet dsd4stats))
      (if double-ok
          (mv (list double-lit) strash aignet dsd4stats)
        (b* (((mv simple-lit strash aignet)
              (aignet-build-truth4-simple full-indices x strash aignet)))
          (mv (list simple-lit) strash aignet dsd4stats)))))
  ///
  
  (aignet::def-aignet-preservation-thms aignet-build-truth4-decomp :stobjname aignet)

  (defret stype-counts-preserved-of-aignet-build-truth4-decomp
    (let ((aignet::new-aignet new-aignet)
          (aignet::aignet aignet))
      #!aignet
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (stype-count stype new-aignet)
                      (stype-count stype aignet)))))

  (defret aignet-lit-listp-of-aignet-build-truth4-decomp
    (implies (and (<= 4 (aignet::num-ins aignet))
                  (index-listp full-indices 4))
             (aignet::aignet-lit-listp lits new-aignet)))

  (defret aignet-litp-member-of-aignet-build-truth4-decomp
    (implies (and (member lit lits)
                  (index-listp full-indices 4)
                  (<= 4 (aignet::num-ins aignet)))
             (aignet::aignet-litp lit new-aignet)))

  (defret eval-member-of-aignet-build-truth4-decomp
    (implies (and (member lit lits)
                  (index-listp full-indices 4)
                  (full-perm-p full-indices 4)
                  (<= 4 (aignet::num-ins aignet)))
             (equal (aignet::lit-eval lit invals regvals new-aignet)
                    (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4)))))

  (defret true-listp-of-aignet-build-truth4-decomp
    (true-listp lits) :rule-classes :type-prescription)

  ;; (defret aignet-litp-of-aignet-build-truth4-decomp
  ;;   (implies (and (<= 4 (aignet::num-ins aignet))
  ;;                 (index-listp full-indices 4))
  ;;            (aignet::aignet-litp lit new-aignet)))

  ;; (defret lit-eval-of-aignet-build-truth4-decomp
  ;;   (implies (and (<= 4 (aignet::num-ins aignet))
  ;;                 (index-listp full-indices 4)
  ;;                 (full-perm-p full-indices 4))
  ;;            (equal (aignet::lit-eval lit invals regvals new-aignet)
  ;;                   (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4)))))
  )

(fty::deflist truth4-list :elt-type truth4)


(define permutations4p (x)
  (if (atom x)
      (eq x nil)
    (and (index-listp (car x) 4)
         (full-perm-p (car x) 4)
         (permutations4p (cdr x)))))

(local (defthm lit-listp-of-append
         (implies (and (aignet::lit-listp x)
                       (aignet::lit-listp y))
                  (aignet::lit-listp (append x y)))
         :hints(("Goal" :in-theory (enable append)))))

(local (defthm aignet-lit-listp-of-append
         (implies (and (aignet::aignet-lit-listp x aignet)
                       (aignet::aignet-lit-listp y aignet))
                  (aignet::aignet-lit-listp (append x y) aignet))
         :hints(("Goal" :in-theory (enable append)))))

(local (defthm member-append
         (iff (member x (append a b))
              (or (member x a) (member x b)))))

(define aignet-build-truth4-decomp-perms ((x truth4-p)
                                          (perms permutations4p)
                                          strash
                                          aignet
                                          dsd4stats)
  :returns (mv (lits aignet::lit-listp)
               (new-strash)
               (new-aignet)
               (new-dsd4stats))
  :guard (<= 4 (num-ins aignet))  
  :verify-guards nil
  (b* ((aignet (aignet::aignet-fix aignet))
       ((when (atom perms)) (mv nil strash aignet dsd4stats))
       ((mv lits1 strash aignet dsd4stats)
        (aignet-build-truth4-decomp x strash aignet dsd4stats (car perms)))
       ((mv rest strash aignet dsd4stats)
        (aignet-build-truth4-decomp-perms x (cdr perms) strash aignet dsd4stats)))
    (mv (append lits1 rest) strash aignet dsd4stats))
  ///

  (aignet::def-aignet-preservation-thms aignet-build-truth4-decomp-perms :stobjname aignet)

  (defret stype-counts-preserved-of-aignet-build-truth4-decomp-perms
    (let ((aignet::new-aignet new-aignet)
          (aignet::aignet aignet))
      #!aignet
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (stype-count stype new-aignet)
                      (stype-count stype aignet)))))

  (verify-guards aignet-build-truth4-decomp-perms
    :hints (("goal" :expand ((permutations4p perms)))))

  (defret aignet-lit-listp-of-aignet-build-truth4-decomp-perms
    (implies (and (<= 4 (aignet::num-ins aignet))
                  (permutations4p perms))
             (aignet::aignet-lit-listp lits new-aignet))
    :hints(("Goal" :in-theory (enable permutations4p))))

  (defret true-listp-of-aignet-build-truth4-decomp-perms
    (true-listp lits)
    :rule-classes :type-prescription)

  (defret aignet-litp-member-of-aignet-build-truth4-decomp-perms
    (implies (and (member lit lits)
                  (permutations4p perms)
                  (<= 4 (aignet::num-ins aignet)))
             (aignet::aignet-litp lit new-aignet))
    :hints(("Goal" :in-theory (enable permutations4p))))

  (defret eval-member-of-aignet-build-truth4-decomp-perms
    (implies (and (member lit lits)
                  (permutations4p perms)
                  (<= 4 (aignet::num-ins aignet)))
             (equal (aignet::lit-eval lit invals regvals new-aignet)
                    (bool->bit (truth-eval x (truth4-env-from-aignet-invals invals) 4))))
    :hints(("Goal" :in-theory (enable permutations4p)))))


(include-book "centaur/misc/smm" :dir :system)
(include-book "perm4")

(defsection perm4-rev-indices
  (local (set-default-hints
          '('(:in-theory (enable index-swap perm4-index-list)
              :expand ((:free (n perm x) (index-perm-rev n perm x 4))
                       (:free (n perm x) (index-perm n perm x 4)))))))

  (define perm4-rev-index0 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) 0 4)
         :exec (perm4-idx0 x)))
  
  (define perm4-rev-index1 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) 1 4)
       :exec (b* (((the (unsigned-byte 2) idx1) (perm4-idx1 x)))
               (if (eql idx1 (the (unsigned-byte 2) (perm4-idx0 x))) 0 idx1))))

  (define perm4-rev-index2 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) 2 4)
       :exec (b* (((the (unsigned-byte 2) idx2) (perm4-idx2 x))
                  ((the (unsigned-byte 2) idx0) (perm4-idx0 x)))
               (if (eql idx2 (the (unsigned-byte 2) (perm4-idx1 x)))
                   (if (eql idx0 1) 0 1)
                 (if (eql idx0 idx2) 0 idx2)))))

  (define perm4-rev-index3 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) 3 4)
         :exec (b* (((the (unsigned-byte 2) idx1) (perm4-idx1 x))
                    ((the (unsigned-byte 2) idx0) (perm4-idx0 x)))
                 (if (eql (the (unsigned-byte 2) (perm4-idx2 x)) 3)
                     (if (eql idx1 2)
                         (if (eql idx0 1) 0 1)
                       (if (eql idx0 2) 0 2))
                   (if (eql idx1 3)
                       (if (eql idx0 1) 0 1)
                     (if (eql idx0 3) 0 3))))))

  (define perm4-rev-index ((n natp) (x perm4p))
    :enabled t
    :inline t
    :guard (< n 4)
    (mbe :logic (index-perm-rev 0 (perm4-index-list x) n 4)
         :exec (case n
                 (0 (perm4-rev-index0 x))
                 (1 (perm4-rev-index1 x))
                 (2 (perm4-rev-index2 x))
                 (t (perm4-rev-index3 x)))))


  
  (define perm4-perm-index0 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm 0 (perm4-index-list x) 0 4)
         :exec ;; (b* ((k (perm4-idx0 x))
               ;;      (k (if (eql k 1)
               ;;             (perm4-idx1 x)
               ;;           (if (eql k (perm4-idx1 x))
               ;;               1
               ;;             k))))
               ;;   (if (eql k 2)
               ;;       (perm4-idx2 x)
               ;;     (if (eql k (perm4-idx2 x))
               ;;         2
               ;;       k)))
         (b* (((the (unsigned-byte 2) idx0) (perm4-idx0 x))
              ((the (unsigned-byte 2) idx1) (perm4-idx1 x)))
           (cond ((eql idx0 0) 0)
                 ((eql idx1 idx0) 1)
                 (t (b* ((k (if (eql idx0 1)
                                idx1
                              idx0)))
                      (if (eql k (the (unsigned-byte 2) (perm4-idx2 x)))
                          2
                        3)))))))
  
  (define perm4-perm-index1 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm 0 (perm4-index-list x) 1 4)
         :exec ;; (b* ((k (if (eql (perm4-idx0 x) 1) 0 1))
         ;;      (k (if (eql k 1)
         ;;               (perm4-idx1 x)
         ;;           (if (eql k (perm4-idx1 x))
         ;;               1
         ;;             k))))
         ;;   (if (eql k 2)
         ;;         (perm4-idx2 x)
         ;;       (if (eql k (perm4-idx2 x))
         ;;           2
         ;;         k)))
         (b* (((the (unsigned-byte 2) idx1) (perm4-idx1 x)))
           (cond ((eql (the (unsigned-byte 2) (perm4-idx0 x)) 1) 0)
                 ((eql idx1 1) 1)
                 ;; (t 
                 ;; x is idx1 going in,
                 ;; both idx1 and idx2 must be 2 or 3
                 ;;   idx2 \ idx1   2   3
                 ;;    2            2   3
                 ;;    3            3   2
                 ((eql idx1
                       (the (unsigned-byte 2) (perm4-idx2 x))) 2)
                 (t 3)
                 ;; ((eql (perm4-idx1 x) 2) (perm4-idx2 x))
                 ;; (t (perm4-idx1 x))
                 ))
         ))

  (define perm4-perm-index2 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm 0 (perm4-index-list x) 2 4)
       :exec ;; (b* ((k (if (eql (perm4-idx0 x) 2) 0 2))
             ;;      (k (if (eql k (perm4-idx1 x))
             ;;             1
             ;;           k)))
             ;;   (if (eql k 2)
             ;;       (perm4-idx2 x)
             ;;     (if (eql k (perm4-idx2 x))
             ;;         2
             ;;       k)))
       (cond ((eql (the (unsigned-byte 2) (perm4-idx0 x)) 2) 0)
             ((eql (the (unsigned-byte 2) (perm4-idx1 x)) 2) 1)
             (t (the (unsigned-byte 2) (perm4-idx2 x))))
       ))

  (define perm4-perm-index3 ((x perm4p))
    :enabled t
    :inline t
    (mbe :logic (index-perm 0 (perm4-index-list x) 3 4)
         :exec ;; (b* ((k (if (eql (perm4-idx0 x) 3) 0 3))
               ;;      (k (if (eql k (perm4-idx1 x))
               ;;             1
               ;;           k)))
               ;;   (if (eql k (perm4-idx2 x))
               ;;       2
               ;;     k))
         (cond ((eql (the (unsigned-byte 2) (perm4-idx0 x)) 3) 0)
               ((eql (the (unsigned-byte 2) (perm4-idx1 x)) 3) 1)
               ((eql (the (unsigned-byte 2) (perm4-idx2 x)) 3) 2)
               (t 3))))

  (define perm4-index ((n natp) (x perm4p))
    :enabled t
    :inline t
    :guard (< n 4)
    (mbe :logic (index-perm 0 (perm4-index-list x) n 4)
         :exec (case n
                 (0 (perm4-perm-index0 x))
                 (1 (perm4-perm-index1 x))
                 (2 (perm4-perm-index2 x))
                 (t (perm4-perm-index3 x)))))

)

(define perm4-to-index-list ((x perm4p))
  :returns (perm true-listp :rule-classes :type-prescription)
  :guard-hints (("goal" :in-theory (enable index-perm-rev index-swap perm4-index-list)
                 :expand ((:free (n perm x) (index-perm-rev n perm x 4)))))
  ;; (mbe :logic
  ;;      (b* ((lst '(0 1 2 3))
  ;;           (lst (update-nth 0 (nth (perm4-idx0 x) lst)
  ;;                            (update-nth (perm4-idx0 x) (nth 0 lst) lst)))
  ;;           (lst (update-nth 1 (nth (perm4-idx1 x) lst)
  ;;                            (update-nth (perm4-idx1 x) (nth 1 lst) lst)))
  ;;           (lst (update-nth 2 (nth (perm4-idx2 x) lst)
  ;;                            (update-nth (perm4-idx2 x) (nth 2 lst) lst))))
  ;;        lst)
  ;;      :exec
  (mbe :logic (b* ((perm (perm4-index-list x)))
                (list (index-perm-rev 0 perm 0 4)
                      (index-perm-rev 0 perm 1 4)
                      (index-perm-rev 0 perm 2 4)
                      (index-perm-rev 0 perm 3 4)))
       :exec (b* (((the (unsigned-byte 2) idx0) (perm4-idx0 x))
                  ((the (unsigned-byte 2) idx1) (perm4-idx1 x))
                  ((the (unsigned-byte 2) idx2) (perm4-idx2 x)))
               (list idx0
                     (if (eql idx0 idx1) 0 idx1)
                     (if (eql idx2 idx1)
                         (if (eql idx0 1) 0 1)
                       (if (eql idx0 idx2) 0 idx2))
                     (if (eql idx2 3)
                         (if (eql idx1 2)
                             (if (eql idx0 1) 0 1)
                           (if (eql idx0 2) 0 2))
                       (if (eql idx1 3)
                           (if (eql idx0 1) 0 1)
                         (if (eql idx0 3) 0 3))))))
  ///

  (defret index-listp-of-perm4-to-index-list
    (index-listp perm 4)
    :hints(("Goal" :in-theory (enable index-listp))))

  (defret full-perm-p-of-perm4-to-index-list
    (full-perm-p perm 4)
    :hints(("Goal" :in-theory (enable full-perm-p
                                      index-perm-rev
                                      index-swap
                                      perm4-index-list))))

  (defret len-of-perm4-to-index-list
    (equal (len (perm4-to-index-list x)) 4))

  (defthm nth-of-perm4-to-index-list
    (implies (< (nfix n) 4)
             (equal (nth n (perm4-to-index-list x))
                    (index-perm-rev 0 (perm4-index-list x) n 4)))
    :hints(("Goal" ;; :in-theory (enable index-perm-rev perm4-index-list nth)
            :cases ((equal (nfix n) 0)
                    (equal (nfix n) 1)
                    (equal (nfix n) 2)
                    (equal (nfix n) 3))))))

(define perm4s-to-permutations4 ((x perm4-list-p))
  (if (atom x)
      nil
    (cons (perm4-to-index-list (car x))
          (perm4s-to-permutations4 (cdr x)))))

(defconst *all-permutations4* (perm4s-to-permutations4 *all-perms4*))

(make-event
 `(define all-permutations4 ()
    :returns (perms permutations4p)
    ',*all-permutations4*
    ///
    (in-theory (disable (all-permutations4)))))

(acl2::defstobj-clone smm acl2::smm :strsubst (("ABCDE" . "ABCDE")))

(define smm-write-lit ((block natp)
                       (idx natp)
                       (lit aignet::litp)
                       (smm))
  :guard (and (< block (smm-nblocks smm))
              (< idx (smm-block-size block smm)))
  :guard-hints (("goal" :in-theory (enable unsigned-byte-p)))
  :enabled t
  (mbe :logic (smm-write block idx (aignet::lit-fix lit) smm)
       :exec (if (<= lit #xffffffff)
                 (smm-write block idx lit smm)
               (ec-call (smm-write block idx lit smm)))))

(define smm-write-lits ((block natp)
                        (idx natp)
                        (lits aignet::lit-listp)
                        (smm))
  :guard (and (< block (smm-nblocks smm))
              (<= (+ idx (len lits)) (smm-block-size block smm)))
  :prepwork ((local (defthm true-listp-when-u32-list-listp
                      (implies (acl2::u32-list-listp smm)
                               (true-listp smm))
                      :hints(("Goal" :in-theory (enable acl2::u32-list-listp))))))
  :returns (new-smm)
  (b* (((when (atom lits))
        (mbe :logic (non-exec (list-fix smm))
             :exec smm))
       (smm (smm-write-lit block idx (car lits) smm)))
    (smm-write-lits block (+ 1 (lnfix idx)) (cdr lits) smm))
  ///
  (defret read-diff-block-of-smm-write-lits
    (implies (not (equal (nfix block) (nfix n)))
             (equal (nth n new-smm)
                    (nth n smm))))

  (local (defret read-lesser-idx-of-smm-write-lits
           (implies (< (nfix n) (nfix idx))
                    (equal (nth n (nth block new-smm))
                           (nth n (nth block smm))))))

  (defret read-in-block-of-smm-write-lits
    (equal (nth n (nth block new-smm))
           (cond ((< (nfix n) (nfix idx)) (nth n (nth block smm)))
                 ((< (nfix n) (+ (nfix idx) (len lits)))
                  (aignet::lit-fix (nth (- (nfix n) (nfix idx)) lits)))
                 (t (nth n (nth block smm)))))
    :hints (("goal" :induct t)
            (and stable-under-simplificationp
                 '(:expand ((nth (+ n (- (nfix idx))) lits))))))

  (defret len-of-smm-write-lits
    (implies (< (nfix block) (len smm))
             (equal (len new-smm) (len smm))))

  (defret len-of-smm-write-lits-nondecreasing
    (<= (len smm) (len new-smm))
    :rule-classes :linear)

  (defret block-size-of-smm-write-lits
    (implies (<= (+ (nfix idx) (len lits)) (len (nth block smm)))
             (equal (len (nth block new-smm))
                    (len (nth block smm)))))

  ;; (local (include-book "std/lists/nth" :dir :system))

  ;; (defret true-listp-of-smm-write-lits
  ;;   (implies (true-listp smm)
  ;;            (true-listp new-smm)))

  ;; (defret block-of-smm-write-lits
  ;;   (implies (and (equal (len (nth block smm))
  ;;                        (len lits))
  ;;                 (< (nfix block) (len smm)))
  ;;            (equal (smm-write-lits block 0 lits smm)
  ;;                   (update-nth block (aignet::lit-list-fix lits)
  ;;                               (list-fix smm))))
  ;;   :hints (("goal" :do-not-induct t :in-theory (disable smm-write-lits))
  ;;           (and stable-under-simplificationp
  ;;                (acl2::equal-by-nths-hint))
  ;;           (and stable-under-simplificationp
  ;;                (acl2::equal-by-nths-hint))))
  )

(local (include-book "std/lists/repeat" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

(local (defthm lit-listp-of-remove-dups
         (implies (aignet::lit-listp x)
                  (aignet::lit-listp (remove-duplicates-equal x)))
         :hints(("Goal" :in-theory (enable remove-duplicates-equal)))))



(define aignet-build-truth4arr-decomps ((canonical-count natp)
                                        (truth4arr)
                                        (smm "storage for output literals")
                                        strash
                                        aignet
                                        dsd4stats)
  :guard (and (<= (acl2::smm-nblocks smm) canonical-count)
              (<= canonical-count (truth4s-length truth4arr))
              (<= 4 (num-ins aignet)))
  :measure (nfix (- (nfix canonical-count) (acl2::smm-nblocks smm)))
  :returns (mv new-smm new-strash new-aignet new-dsd4stats)
  :prepwork ((local (defthm eqlable-listp-when-lit-listp
                      (implies (aignet::lit-listp x)
                               (eqlable-listp x)))))
  (b* ((n (acl2::smm-nblocks smm))
       (aignet (aignet::aignet-fix aignet))
       ((when (mbe :logic (zp (- (nfix canonical-count) n))
                   :exec (eql n canonical-count)))
        (mv smm strash aignet dsd4stats))
       (truth (get-truth4 n truth4arr))
       (snap (dsd4stats-snap dsd4stats))
       ((mv lits strash aignet dsd4stats)
        (aignet-build-truth4-decomp-perms truth
                                          (all-permutations4)
                                          strash
                                          aignet
                                          dsd4stats))
       (dsd4stats (dsd4stats-fanin-count snap dsd4stats))
       (lits (remove-duplicates lits))
       (smm (acl2::smm-addblock (len lits) smm))
       (smm (smm-write-lits n 0 lits smm)))
    (aignet-build-truth4arr-decomps canonical-count truth4arr smm strash aignet dsd4stats))
  ///
  (defret smm-nblocks-of-aignet-build-truth4arr-decomps
    (implies (<= (len smm) (nfix canonical-count))
             (equal (len new-smm)
                    (nfix canonical-count))))

  (aignet::def-aignet-preservation-thms aignet-build-truth4arr-decomps :stobjname aignet)

  (defret stype-counts-preserved-of-aignet-build-truth4arr-decomps
    (let ((aignet::new-aignet new-aignet)
          (aignet::aignet aignet))
      #!aignet
      (implies (and (not (equal (aignet::stype-fix stype) (aignet::and-stype)))
                    (not (equal (aignet::stype-fix stype) (aignet::xor-stype))))
               (equal (stype-count stype new-aignet)
                      (stype-count stype aignet)))))

  (defret smm-blocks-preserved-of-aignet-build-truth4arr-decomps
    (implies (< (nfix block) (len smm))
             (equal (nth block new-smm)
                    (nth block smm))))

  (local (defthm nth-of-append
           (equal (nth n (append x y))
                  (if (< (nfix n) (len x))
                      (nth n x)
                    (nth (- (nfix n) (len x)) y)))))
  (local (in-theory (disable acl2::nth-of-append)))

  (local (defthm member-remove-dups
           (iff (member k (remove-duplicates-equal x))
                (member k x))))

  (local (defthm nth-of-remove-duplicates-is-member
           (implies (< (nfix n) (len (remove-duplicates-equal x)))
                    (member (nth n (remove-duplicates-equal x)) x))
           :hints (("goal" :use ((:instance acl2::member-of-nth
                                  (x (remove-duplicates-equal x))
                                  (n n)))
                    :in-theory (disable acl2::member-of-nth)
                    :do-not-induct t))))

  (defret aignet-litp-smm-lookup-of-aignet-build-truth4arr-decomps
    (implies (and (< (nfix n) (nfix canonical-count))
                  (<= (len smm) (nfix n))
                  (< (nfix idx) (len (nth n new-smm)))
                  (<= 4 (aignet::num-ins aignet)))
             (aignet::aignet-litp (nth idx (nth n new-smm)) new-aignet))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))
                  
  (defret eval-smm-lookup-of-aignet-build-truth4arr-decomps
    (implies (and (< (nfix n) (nfix canonical-count))
                  (<= (len smm) (nfix n))
                  (< (nfix idx) (len (nth n new-smm)))
                  (<= 4 (aignet::num-ins aignet)))
             (equal (aignet::lit-eval (nth idx (nth n new-smm)) invals regvals new-aignet)
                    (bool->bit (truth-eval (nth n truth4arr) (truth4-env-from-aignet-invals invals) 4))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))

(define aignet-build-truth4arr-decomps-top ((canonical-count natp "number of canonical truth tables")
                                            (truth4arr "canonical truth tables, already built")
                                            (smm "storage for output literals -- emptied")
                                            aignet)
  :returns (mv new-smm new-aignet)
  :guard (<= canonical-count (truth4s-length truth4arr))
  (b* (((acl2::local-stobjs strash dsd4stats)
        (mv smm strash aignet dsd4stats))
       (aignet (aignet::aignet-init 0 0 4 5000 aignet))
       (aignet (aignet::aignet-add-in aignet))
       (aignet (aignet::aignet-add-in aignet))
       (aignet (aignet::aignet-add-in aignet))
       (aignet (aignet::aignet-add-in aignet))
       (smm (smm-clear smm))
       ((mv smm strash aignet dsd4stats)
        (aignet-build-truth4arr-decomps canonical-count truth4arr smm strash aignet dsd4stats)))
    (print-dsd4stats dsd4stats)
    (mv smm strash aignet dsd4stats))
       
    
  ///
  
  (defret smm-nblocks-of-aignet-build-truth4arr-decomps-top
    (equal (len new-smm)
           (nfix canonical-count)))

  (defret num-ins-of-aignet-build-truth4arr-decomps-top
    (equal (aignet::stype-count :pi new-aignet) 4))

  (defret num-regs-of-aignet-build-truth4arr-decomps-top
    (equal (aignet::stype-count :reg new-aignet) 0))

  (defret aignet-litp-smm-lookup-of-aignet-build-truth4arr-decomps-top
    (implies (and (< (nfix n) (nfix canonical-count))
                  (< (nfix idx) (len (nth n new-smm))))
             (aignet::aignet-litp (nth idx (nth n new-smm)) new-aignet))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))
                  
  (defret eval-smm-lookup-of-aignet-build-truth4arr-decomps-top
    (implies (and (< (nfix n) (nfix canonical-count))
                  (< (nfix idx) (len (nth n new-smm))))
             (equal (aignet::lit-eval (nth idx (nth n new-smm)) invals regvals new-aignet)
                    (bool->bit (truth-eval (nth n truth4arr) (truth4-env-from-aignet-invals invals) 4))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding)))))
        
                    
  



(define setup-dsd4-lib (npn4arr
                        truth4arr
                        aignet
                        smm) ;; all emptied
  :returns (mv new-npn4arr
               new-truth4arr
               new-smm
               new-aignet)
  (b* (((mv count npn4arr truth4arr) (record-all-npn4-perms-top npn4arr truth4arr))
       ((mv smm aignet) (aignet-build-truth4arr-decomps-top count truth4arr smm aignet)))
    (mv npn4arr truth4arr smm aignet))
  ///
  (defret npn4arr-length-of-setup-dsd4-lib
    (equal (len new-npn4arr) #x10000))

  (defret npn4arr-indices-bounded-of-setup-dsd4-lib
    (npn4arr-indices-bounded (len new-smm) new-npn4arr))

  (defret npn4arr-correct-of-setup-dsd4-lib
    (npn4arr-correct new-npn4arr new-truth4arr))

  (defret num-ins-of-setup-dsd4-lib-aignet
    (equal (aignet::stype-count :pi new-aignet) 4))

  (defret num-regs-of-setup-dsd4-lib-aignet
    (equal (aignet::stype-count :reg new-aignet) 0))

  (defret aignet-litp-smm-lookup-of-setup-dsd4-lib
    (implies (and (< (nfix n) (len new-smm))
                  (< (nfix idx) (len (nth n new-smm))))
             (aignet::aignet-litp (nth idx (nth n new-smm)) new-aignet))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret smm-contains-aignet-lits-of-setup-dsd4-lib
    (smm-contains-aignet-lits new-smm new-aignet)
    :hints (("goal" :in-theory (e/d (smm-contains-aignet-lits) (setup-dsd4-lib)))))

  (defret truth4arr-length-of-setup-dsd4-lib
    (<= (len new-smm) (len new-truth4arr))
    :rule-classes :linear)

  (defret eval-smm-lookup-of-setup-dsd4-lib
    (implies (and (< (nfix n) (len new-smm))
                  (< (nfix idx) (len (nth n new-smm))))
             (equal (aignet::lit-eval (nth idx (nth n new-smm)) invals regvals new-aignet)
                    (bool->bit (truth-eval (nth n new-truth4arr) (truth4-env-from-aignet-invals invals) 4))))
    :hints(("Goal" :in-theory (enable* acl2::arith-equiv-forwarding))))

  (defret aignet::aignet-truth-impls-correct-of-setup-dsd4-lib
    (aignet::aignet-truth-impls-correct new-smm new-aignet new-truth4arr)
    :hints(("Goal" :in-theory (enable aignet::aignet-truth-impls-correct))))

  (defret npn4arr-indices-all-bound-of-setup-dsd4-lib
    (npn4arr-indices-all-bound new-npn4arr)))

(acl2::defstobj-clone rwlib aignet::rwlib :strsubst (("a" . "a")))
;; (defstobj rwlib
;;   (rwlib->npns :type npn4arr)
;;   (rwlib->truths :type truth4arr)
;;   (rwlib->aigs :type aignet)
;;   (rwlib->cands :type smm))

;; (include-book "std/stobjs/nested-stobjs" :dir :system)

;; (local (in-theory (disable nth update-nth
;;                            acl2::nth-when-zp)))

;; ;; (defsection update-rwlib->npns
;; ;;   (defthm nth-of-update-rwlib->npns
;; ;;     (equal (nth n (update-rwlib->npns npns rwlib))
;; ;;            (if (equal (nfix n) *rwlib->npns*)
;; ;;                npns
;; ;;              (nth n rwlib))))

;; ;;   (defthm rwlib->npns-of-update-rwlib->npns
;; ;;     (equal (rwlib->npns (update-rwlib->npns npns rwlib))
;; ;;            npns))

;; ;;   (in-theory (disable update-rwlib->npns)))
;; (define rwlib-wfp (rwlib)
;;   (b* (((acl2::stobj-get ok)
;;         ((npn4arr (rwlib->npns rwlib))
;;          (truth4arr (rwlib->truths rwlib))
;;          (aignet (rwlib->aigs rwlib))
;;          (smm (rwlib->cands rwlib)))
;;         (and (eql (npn4s-length npn4arr) #x10000)
;;              (ec-call (npn4arr-indices-all-bound npn4arr))
;;              (ec-call (npn4arr-indices-bounded (acl2::smm-nblocks smm) npn4arr))
;;              (<= (smm-nblocks smm) (truth4s-length truth4arr))
;;              (equal (aignet::num-ins aignet) 4)
;;              (ec-call (smm-contains-aignet-lits smm aignet)))))
;;     ok)
;;   ///
;;   (defthm rwlib-wfp-implies
;;     (implies (rwlib-wfp rwlib)
;;              (b* ((npn4arr (rwlib->npns rwlib))
;;                   (truth4arr (rwlib->truths rwlib))
;;                   (aignet (rwlib->aigs rwlib))
;;                   (smm (rwlib->cands rwlib)))
;;                (and (equal (len npn4arr) #x10000)
;;                     (npn4arr-indices-all-bound npn4arr)
;;                     (npn4arr-indices-bounded (len smm) npn4arr)
;;                     (<= (len smm) (len truth4arr))
;;                     (equal (aignet::stype-count :pi aignet) 4)
;;                     (smm-contains-aignet-lits smm aignet)))))

;;   (defthm rwlib-wfp-implies-linear
;;     (implies (rwlib-wfp rwlib)
;;              (b* ((truth4arr (rwlib->truths rwlib))
;;                   (smm (rwlib->cands rwlib)))
;;                (<= (len smm) (len truth4arr))))
;;     :rule-classes :linear)

;;   (defthm rwlib-wfp-implies-aignet-litp
;;     (b* ((smm (rwlib->cands rwlib))
;;          (aignet (rwlib->aigs rwlib)))
;;       (implies (and (rwlib-wfp rwlib)
;;                     (< (nfix n) (len smm))
;;                     (< (nfix idx) (len (nth n smm))))
;;                (aignet::aignet-litp (nth idx (nth n smm)) aignet))))

;;   (defthm rwlib-wfp-implies-npn4arr-indices-exist
;;     (b* ((npn4arr (rwlib->npns rwlib)))
;;       (implies (and (rwlib-wfp rwlib)
;;                     (truth4-p n))
;;                (equal (maybe-npn4-fix (nth n npn4arr))
;;                       (npn4-fix (nth n npn4arr)))))
;;     :hints(("Goal" :in-theory (enable truth4-p unsigned-byte-p))))

;;   (defthm rwlib-wfp-implies-npn4arr-index-upper-bound
;;     (b* ((npn4arr (rwlib->npns rwlib))
;;          (smm (rwlib->cands rwlib)))
;;       (implies (and (rwlib-wfp rwlib)
;;                     (truth4-p n))
;;                (< (npn4->truth-idx (nth n npn4arr)) (len smm))))
;;     :hints(("Goal" :in-theory (e/d (truth4-p unsigned-byte-p)
;;                                    (npn4arr-indices-bounded-necc))
;;             :use ((:instance npn4arr-indices-bounded-necc
;;                    (bound (len (rwlib->cands rwlib)))
;;                    (npn4arr (rwlib->npns rwlib))
;;                    (idx n)))))
;;     :rule-classes (:rewrite :linear))) 

;; (define permuted-env-from-aignet-invals ((npn npn4-p)
;;                                          (aignet::invals))
;;   :guard (<= 4 (aignet::bits-length aignet::invals))
;;   :returns (env natp :rule-classes :type-prescription)
;;   (b* (((npn4 npn))
;;        (env (truth4-env-from-aignet-invals aignet::invals))
;;        (env (env-permute-polarity 0 npn.polarity env 4)))
;;     (env-perm 0 (perm4-index-list npn.perm) env 4))
;;   ///
;;   (defret lookup-in-permuted-env-from-aignet-invals
;;     (implies (< (nfix n) 4)
;;              (equal (env-lookup n env)
;;                     (b* (((npn4 npn))
;;                          (idx (index-perm-rev 0 (perm4-index-list npn.perm) n 4)))
;;                       (acl2::bit->bool
;;                        (b-xor
;;                         (logbit idx npn.polarity)
;;                         (nth idx aignet::invals))))))
;;     :hints(("Goal" :in-theory (enable b-xor bool->bit)))))

;; (define rwlib-correct (rwlib)
;;   (b* (((acl2::stobj-get ok)
;;         ((npn4arr (rwlib->npns rwlib))
;;          (truth4arr (rwlib->truths rwlib))
;;          (aignet (rwlib->aigs rwlib))
;;          (smm (rwlib->cands rwlib)))
;;         (and (ec-call (npn4arr-correct npn4arr truth4arr))
;;              (ec-call (aignet::aignet-truth-impls-correct smm aignet truth4arr)))))
;;     ok)
;;   ///
;;   (local
;;    (defthm rwlib-correct-implies-eval-smm-lookup
;;      (b* ((truth4arr (rwlib->truths rwlib))
;;           (aignet (rwlib->aigs rwlib))
;;           (smm (rwlib->cands rwlib)))
;;        (implies (and (rwlib-correct rwlib)
;;                      (< (nfix n) (len smm))
;;                      (< (nfix idx) (len (nth n smm))))
;;                 (equal (aignet::lit-eval (nth idx (nth n smm)) invals regvals aignet)
;;                        (bool->bit (truth-eval (nth n truth4arr) (truth4-env-from-aignet-invals invals) 4)))))))

;;   (defthm rwlib-correct-implies-npn4-truth-value-ok
;;     (b* ((npn4arr (rwlib->npns rwlib))
;;          (truth4arr (rwlib->truths rwlib)))
;;       (implies (and (rwlib-correct rwlib)
;;                     (truth4-p idx))
;;                (b* ((val (nth idx npn4arr)))
;;                  (and (equal (maybe-npn4-fix val)
;;                              (npn4-fix val))
;;                       (b* (((npn4 val)))
;;                         (equal (npn4-truth-value val (nth val.truth-idx truth4arr))
;;                                idx))))))
;;     :hints(("Goal" :in-theory (enable truth4-p unsigned-byte-p))))

;;   (defthm rwlib-correct-implies-eval-smm-lookup-of-truth-idx
;;     (b* ((?truth4arr (rwlib->truths rwlib))
;;          (aignet (rwlib->aigs rwlib))
;;          (smm (rwlib->cands rwlib))
;;          (npn4arr (rwlib->npns rwlib))
;;          ((npn4 npn) (nth truth npn4arr))
;;          (env (permuted-env-from-aignet-invals npn invals)))
;;       (implies (and (rwlib-correct rwlib)
;;                     (rwlib-wfp rwlib)
;;                     (truth4-p truth)
;;                     (< (nfix idx) (len (nth npn.truth-idx smm))))
;;                (equal (aignet::lit-eval (nth idx (nth npn.truth-idx smm)) invals regvals aignet)
;;                       (b-xor npn.negate
;;                              (bool->bit (truth-eval truth env 4))))))
;;     :hints(("Goal" :in-theory (e/d (permuted-env-from-aignet-invals)
;;                                    (rwlib-correct
;;                                     rwlib->truths
;;                                     rwlib->aigs
;;                                     rwlib->cands
;;                                     rwlib->npns
;;                                     eval-of-npn4-truth-value-with-permuted-env
;;                                     eval-of-npn4-truth-value))
;;             :use ((:instance eval-of-npn4-truth-value-with-permuted-env
;;                    (npn (nth truth (rwlib->npns rwlib)))
;;                    (truth (nth (npn4->truth-idx (nth truth (rwlib->npns rwlib)))
;;                                (rwlib->truths rwlib)))
;;                    (orig-env (truth4-env-from-aignet-invals invals)))))))

;;   (defthm rwlib-correct-implies-id-eval-smm-lookup-of-truth-idx
;;     (b* ((?truth4arr (rwlib->truths rwlib))
;;          (aignet (rwlib->aigs rwlib))
;;          (smm (rwlib->cands rwlib))
;;          (npn4arr (rwlib->npns rwlib))
;;          ((npn4 npn) (nth truth npn4arr))
;;          (env (permuted-env-from-aignet-invals npn invals)))
;;       (implies (and (rwlib-correct rwlib)
;;                     (rwlib-wfp rwlib)
;;                     (truth4-p truth)
;;                     (< (nfix idx) (len (nth npn.truth-idx smm))))
;;                (equal (aignet::id-eval (aignet::lit-id (nth idx (nth npn.truth-idx smm))) invals regvals aignet)
;;                       (b-xor (aignet::lit-neg (nth idx (nth npn.truth-idx smm)))
;;                              (b-xor npn.negate
;;                                     (bool->bit (truth-eval truth env 4)))))))
;;     :hints (("goal" :use rwlib-correct-implies-eval-smm-lookup-of-truth-idx
;;              :in-theory (e/d (aignet::lit-eval b-xor bool->bit)
;;                              (rwlib-correct
;;                               rwlib-correct-implies-eval-smm-lookup-of-truth-idx
;;                               rwlib-correct-implies-eval-smm-lookup))))))
               
             
(local (in-theory (enable aignet::rwlib->truths
                          aignet::rwlib->npns
                          aignet::rwlib->aigs
                          aignet::rwlib->cands)))

(local (in-theory (disable acl2::nth-when-zp)))

(define dsd4-library-init (rwlib)
  :returns (initialized-rwlib)
  (b* (((acl2::stobj-get npn4arr truth4arr smm aignet)
        ((npn4arr (rwlib->npns rwlib))
         (truth4arr (rwlib->truths rwlib))
         (aignet (rwlib->aigs rwlib))
         (smm (rwlib->cands rwlib)))
        (setup-dsd4-lib npn4arr truth4arr aignet smm)))
    rwlib)
  ///
  (defret rwlib-wfp-of-dsd4-library-init
    (rwlib-wfp initialized-rwlib)
    :hints(("Goal" :in-theory (enable rwlib-wfp))))

  (defret rwlib-correct-of-dsd4-library-init
    (rwlib-correct initialized-rwlib)
    :hints(("Goal" :in-theory (enable rwlib-correct)))))



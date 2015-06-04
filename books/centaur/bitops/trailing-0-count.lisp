

(in-package "BITOPS")
(include-book "std/bitsets/bignum-extract" :dir :system)
(include-book "centaur/fty/fixequiv" :dir :system)
(include-book "centaur/misc/arith-equiv-defs" :dir :system)
(local (include-book "ihsext-basics"))
;; (local (include-book "equal-by-logbitp"))
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (in-theory (disable (tau-system)
                           acl2::loghead-identity
                           acl2::logtail-identity))) 
(local (in-theory (disable acl2::cancel_times-equal-correct
                           acl2::cancel_plus-equal-correct
                           ; acl2::logior-natp-type
                           bitops::logxor-natp-type-2
                           bitops::logior-<-0-linear-2
                           bitops::lognot-negp)))

;; (local (defthm logior-same-2
;;          (equal (logior x (logior x y))
;;                 (logior x y))
;;          :hints((bitops::logbitp-reasoning))))

;; (local (defthm logand-same-2
;;          (equal (logand x (logand x y))
;;                 (logand x y))
;;          :hints((bitops::logbitp-reasoning))))


;; (local (defthm logxor-self
;;          (equal (logxor x x) 0)))

;; (def-svex-rewrite unsigned-not-less-than-0
;;   :lhs (< (concat n x 0) 0)
;;   :rhs (xdet (bitxor (concat n x 0) (concat n x 0)))
;;   :hints(("Goal" :in-theory (enable svex-apply 4vec-< 4vec-concat
;;                                     4vec-bitxor 4vec-xdet))))


(define find-bit ((x :type (unsigned-byte 32)))
  :inline t
  (b* ((x (lnfix x))
       ((the (unsigned-byte 5) x16) (ash (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x0000FFFF))) 1 0)) 4))
       ((the (unsigned-byte 4) x8)  (ash (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x00FF00FF))) 1 0)) 3))
       ((the (unsigned-byte 3) x4)  (ash (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x0F0F0F0F))) 1 0)) 2))
       ((the (unsigned-byte 2) x2)  (ash (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x33333333))) 1 0)) 1))
       ((the (unsigned-byte 1) x1)  (the bit (if (eql 0 (the (unsigned-byte 32) (logand x #x55555555))) 1 0))))
    (the (unsigned-byte 32)
         (logior
          (the (unsigned-byte 32) x16)
          (the (unsigned-byte 32)
               (logior
                (the (unsigned-byte 32) x8)
                (the (unsigned-byte 32)
                     (logior
                      (the (unsigned-byte 32) x4)
                      (the (unsigned-byte 32)
                           (logior
                            (the (unsigned-byte 32) x2)
                            (the (unsigned-byte 32) x1))))))))))
  ///
  (local (defun test-find-bit (limit)
           (if (zp limit)
               t
             (and (let ((x (1- limit)))
                    (equal (find-bit (ash 1 x)) x))
                  (test-find-bit (1- limit))))))

  (local (defthm find-bit-by-test-find-bit
           (implies (and (test-find-bit limit)
                         (natp n)
                         (< n (nfix limit)))
                    (equal (find-bit (ash 1 n)) n))
           :hints(("Goal" :in-theory (disable find-bit)))))
    

  (defthm find-bit-of-ash-1
    (implies (and (natp n)
                  (< n 32))
             (equal (find-bit (ash 1 n))
                    n))
    :hints (("goal" :in-theory (disable find-bit test-find-bit)
             :use ((:instance find-bit-by-test-find-bit
                    (limit 32)))))))



(local (defthm integer-length-when-loghead/logtail
         (implies (and (not (equal 0 (logtail n x)))
                       (equal 0 (loghead m (logtail n x)))
                       (posp m) (natp n))
                  (<= (+ m n) (integer-length x)))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                 :induct (logtail n x)))))
(local (defthm logtail-nonzero-lemma
         (implies (and (not (equal 0 (logtail n x)))
                       (equal 0 (loghead m (logtail n x)))
                       (posp m) (natp n))
                  (not (equal 0 (logtail (+ m n) x))))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                 :induct (logtail n x)))))
(local (defthm integer-length-when-bignum-extract
         (implies (and (not (equal 0 (logtail (* 32 (nfix idx)) x)))
                       (equal 0 (bitsets::bignum-extract x idx)))
                  (<= (+ 32 (* 32 (nfix idx))) (integer-length x)))
         :hints(("Goal" :in-theory (enable bitsets::bignum-extract)))
         :rule-classes :linear))
(local (defthm logtail-nonzero-bignum-extract
         (implies (and (not (equal 0 (logtail (* 32 idx) x)))
                       (equal 0 (bitsets::bignum-extract x idx))
                       (natp idx))
                  (not (equal 0 (logtail (+ 32 (* 32 idx)) x))))
         :hints(("Goal" :in-theory (enable bitsets::bignum-extract)))))
(local (defthm loghead-zero-compose
         (implies (and (equal 0 (loghead n x))
                       (equal 0 (loghead m (logtail n x)))
                       (natp m) (natp n))
                  (equal (loghead (+ m n) x) 0))
         :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                 :induct (logtail n x)))))


(define trailing-0-count-32 ((x :type (unsigned-byte 32)))
  ;; :prepwork ((local (in-theory (disable unsigned-byte-p
  ;;                                       signed-byte-p)))
  ;;            (local (include-book "centaur/bitops/signed-byte-p" :dir :system)))
  ;; :guard (not (eql 0 x))
  (b* ((x (lnfix x))
       ((the (unsigned-byte 32) x)
        (the (unsigned-byte 32) (logand x (the (signed-byte 33) (- x))))))
    (find-bit x))
  ///
  (fty::deffixequiv trailing-0-count-32 :args ((x natp))))




(fty::deffixequiv bitsets::bignum-extract :args ((x integerp) (bitsets::slice natp)))

(define trailing-0-count-rec ((x integerp)
                              (slice-idx natp))
  :guard (not (equal 0 (logtail (* 32 slice-idx) x)))
  :measure (nfix (- (integer-length x) (* 32 (nfix slice-idx))))
  :prepwork ()
  (b* (((unless (mbt (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))))
        0)
       (slice-idx (lnfix slice-idx))
       (slice (bitsets::bignum-extract x slice-idx))
       ((when (eql 0 slice))
        (trailing-0-count-rec x (+ 1 slice-idx)))
       (slice-trailing-0-count (trailing-0-count-32 slice)))
    (+ slice-trailing-0-count (* 32 slice-idx))))

;; (define trailing-0-count-rec ((x integerp)
;;                               (slice-idx natp
;;                                          :type (unsigned-byte 27)))
;;   :guard (not (equal 0 (logtail (* 32 slice-idx) x)))
;;   :measure (nfix (- (integer-length x) (* 32 (nfix slice-idx))))
;;   :prepwork ()
;;   (b* (((unless (mbt (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))))
;;         0)
;;        ((the (unsigned-byte 27) slice-idx) (lnfix slice-idx))
;;        ((the (unsigned-byte 32) slice) (bitsets::bignum-extract x slice-idx))
;;        ((when (eql 0 slice))
;;         (mbe :logic (trailing-0-count-rec x (+ 1 slice-idx))
;;              :exec (if (eql slice-idx #x7ffffff)
;;                        (trailing-0-count-rec-slow x (+ 1 slice-idx))
;;                      (trailing-0-count-rec x (+ 1 slice-idx)))))
;;        (slice-trailing-0-count (trailing-0-count-32 slice)))
;;     (+ slice-trailing-0-count (* 32 slice-idx))))






(define trailing-0-count ((x integerp))
  :short "Optimized trailing 0 count for integers."
  :long "<p>To make this fast, be sure and include the
\"std/bitsets/bignum-extract-opt\" book (reqires a ttag), which prevents
this (at least on CCL64) from needing to create new bignums when run on
bignums.</p>"
  :verify-guards nil
  :measure (integer-length x)
  :hints(("Goal" :in-theory (enable integer-length**)))
  (mbe :logic
       (if (or (zip x)
               (logbitp 0 x))
           0
         (+ 1 (trailing-0-count (logcdr x))))
       :exec (if (eql 0 x)
                 0
               (trailing-0-count-rec x 0)))
  ///

  (defthm trailing-0-count-properties
    (implies (not (zip x))
             (let ((count (trailing-0-count x)))
               (and (logbitp count x)
                    (equal (loghead count x) 0)
                    (implies (< (nfix idx) count)
                             (not (logbitp idx x))))))
    :hints(("Goal" :in-theory (enable* bitops::ihsext-recursive-redefs
                                       bitops::ihsext-inductions)
            :induct (logbitp idx x))))

  (local (in-theory (disable unsigned-byte-p)))

  (defthm logand-of-minus-in-terms-of-trailing-0-count
    (implies (not (zip x))
             (equal (logand x (- x))
                    (ash 1 (trailing-0-count x))))
    :hints(("Goal" :induct (trailing-0-count x)
            :in-theory (enable bitops::ash** bitops::minus-to-lognot)
            :expand ((:with bitops::logand** (logand x (+ 1 (lognot x))))))))

  (defthm trailing-0-count-bound
    (implies (posp x)
             (< (trailing-0-count x) (integer-length x)))
    :hints(("Goal" :induct (trailing-0-count x)
            :expand ((:with bitops::integer-length** (integer-length x)))))
    :rule-classes :linear)



  (local (defthm integer-length-when-unsigned-byte-p
           (implies (unsigned-byte-p n x)
                    (<= (integer-length x) n))
           :hints(("Goal" :in-theory (e/d* (bitops::ihsext-inductions
                                            bitops::ihsext-recursive-redefs)
                                           (unsigned-byte-p))))
           :rule-classes :linear))

  (local (defthm trailing-0-count-32-correct
           (implies (and (unsigned-byte-p 32 x)
                         (not (equal x 0)))
                    (equal (trailing-0-count-32 x)
                           (trailing-0-count x)))
           :hints(("Goal" :in-theory (e/d (trailing-0-count-32)
                                          (unsigned-byte-p))))))

  (local (in-theory (enable trailing-0-count-rec)))


  (local (defthm trailing-0-count-of-loghead
           (implies (not (equal 0 (loghead n x)))
                    (equal (trailing-0-count (loghead n x))
                           (trailing-0-count x)))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              trailing-0-count)))))

  (local (defthm trailing-0-count-of-logtail
           (implies (and (equal 0 (loghead n x))
                         (not (equal 0 (logtail n x))))
                    (equal (trailing-0-count (logtail n x))
                           (- (trailing-0-count x) (nfix n))))
           :hints(("Goal" :in-theory (enable* bitops::ihsext-inductions
                                              bitops::ihsext-recursive-redefs
                                              trailing-0-count)))))

  (local (defthm not-zip-when-logtail
           (implies (not (equal 0 (logtail n x)))
                    (not (zip x)))
           :rule-classes :forward-chaining))

  (local (defthm trailing-0-count-rec-properties
           (implies (and (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))
                         (equal 0 (loghead (* 32 (nfix slice-idx)) x)))
                    (let ((ans (trailing-0-count-rec x slice-idx)))
                      (and (logbitp ans x)
                           (equal (loghead ans x) 0)
                           (implies (< (nfix idx) ans)
                                    (not (logbitp idx x))))))
           :hints(("Goal" :in-theory (enable bitsets::bignum-extract)))))

  (local (defthm trailing-0-count-rec-correct
           (implies (and (not (equal 0 (logtail (* 32 (nfix slice-idx)) x)))
                         (equal 0 (loghead (* 32 (nfix slice-idx)) x)))
                    (equal (trailing-0-count-rec x slice-idx)
                           (trailing-0-count x)))
           :hints (("goal" :in-theory (disable trailing-0-count-rec
                                               trailing-0-count-rec-properties
                                               trailing-0-count-properties)
                    :use ((:instance trailing-0-count-rec-properties
                           (idx (trailing-0-count x)))
                          (:instance trailing-0-count-properties
                           (idx (trailing-0-count-rec x slice-idx))))))))

  (verify-guards trailing-0-count))



#||
(include-book
 "std/util/defconsts" :dir :system)

(include-book
 "centaur/misc/memory-mgmt" :dir :system)

(define gen-trailing-0-count-numbers ((n natp) (width posp) acc state)
  :prepwork ((local (in-theory (enable random$))))
  (b* (((when (zp n)) (mv acc state))
       ((mv nzeros state) (random$ width state))
       (acc (cons (loghead width (ash -1 nzeros)) acc)))
    (gen-trailing-0-count-numbers (1- n) width acc state)))

(defconsts (*tests* state) (gen-trailing-0-count-numbers 100000 3000 nil state))

(define take-trailing-0-counts ((tests integer-listp) acc)
  (if (atom tests)
      acc
    (take-trailing-0-counts
     (cdr tests)
     (let ((x (car tests)))
       (cons (if (eql x 0) 0 (trailing-0-count (car tests)))
             acc)))))

(value-triple (acl2::set-max-mem
               (* 10 (Expt 2 30))))

;; without optimization: 1.1 sec
(defconsts *res1* (take-trailing-0-counts *tests* nil))

(include-book
 "std/bitsets/bignum-extract-opt" :dir :system)

;; with optimization: 0.06 sec
(defconsts *res2* (take-trailing-0-counts *tests* nil))

||#


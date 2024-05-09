#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book);$ACL2s-Preamble$|#


(in-package "DEFDATA")
(set-verify-guards-eagerness 2)
(include-book "std/util/bstar" :dir :system)
(include-book "acl2s/utilities" :dir :system)
(include-book "ihs/basic-definitions" :dir :system)
(local (include-book "ihs/logops-definitions" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

(make-event
 (er-progn
  (assign random-seed 1382728371)
  (value '(value-triple (@ random-seed))))
 :check-expansion t)

(defun getseed (state)
  (declare (xargs :stobjs (state)))
  (if (f-boundp-global 'random-seed state)
    (b* ((s (@ random-seed)))
      (if (unsigned-byte-p 63 s)
        (the (unsigned-byte 63) s)
        0))
    0))

(defthm getseed-unsigned-byte63 
  (unsigned-byte-p 63 (getseed state))
  :rule-classes (:rewrite :type-prescription))

(defthm getseed-nat 
  (natp (getseed state))
  :rule-classes :type-prescription)

(in-theory (disable getseed))
 
(defun putseed (s state)
  (declare (xargs :stobjs (state)
                  :guard (unsigned-byte-p 63 s)))
  (declare (type (unsigned-byte 63) s))
  (acl2::f-put-global 'random-seed s state))

;; This is the Thrust PRNG. I used it here as it only requires 63 bits
;; of seed/state, and ACL2s is currently using seeds of that length.
;;
;; I (Andrew Walter) converted this from Tommy Ettinger's C implementation:
;; https://gist.github.com/tommyettinger/e6d3e8816da79b45bfe582384c2fe14a#file-thrust-c
;; The C implementation was released into the public domain using the CC0 Deed:
;; http://creativecommons.org/publicdomain/zero/1.0/
;;
;; Internally, there are a number of places where full 64-bit unsigned
;; values are used. However, on my machine this still ends up being
;; faster than the previous implementation. Performance will likely
;; vary depending on the Lisp implementation used.
(defun genrandom-seed (max raw-seed)
    "generates a pseudo-random number less than max, given that the
current random seed is seed. and also returns the new seed."
  (declare (type (unsigned-byte 63) max)
           (type (unsigned-byte 63) raw-seed))
  (declare (xargs :guard (and (unsigned-byte-p 63 max)
                              (unsigned-byte-p 63 raw-seed)
                              (posp max))))
  ;; reconstitute the real seed
  (b* (((the (unsigned-byte 64) seed) (acl2::logcons 1 raw-seed))
       ((the (unsigned-byte 64) next-seed) (acl2::loghead 64 (+ seed #x6A5D39EAE12657AA)))
       ((the (unsigned-byte 64) z) (acl2::loghead 64 (* (logxor seed (acl2::loghead 64 (ash seed -25))) next-seed)))
       ((the (unsigned-byte 64) z) (logxor z (acl2::loghead 64 (ash z -22)))))
    ;; lop off the low-order bit of the seed, since it should always be odd.
    (mv (acl2::loghead 63 (mod z max)) (acl2::loghead 63 (ash next-seed -1)))))

(defthm genrandom-seed-res-size
  (implies (and (unsigned-byte-p 63 max) (posp max)
                (unsigned-byte-p 63 seed))
           (unsigned-byte-p 63 (mv-nth 0 (genrandom-seed max seed))))
  :rule-classes :type-prescription)

(defun genrandom-state (max state)
  "generates a pseudo-random number less than max"
  (declare (type (unsigned-byte 63) max))
  (declare (xargs :stobjs (state)
                  :guard (and (unsigned-byte-p 63 max) (posp max))))
  (b* ((raw-seed (getseed state))
       ((mv res next-seed) (genrandom-seed max raw-seed))
       (state (putseed next-seed state)))
    (mv res state)))

(defthm genrandom-state-res-size
  (implies (and (unsigned-byte-p 63 max) (posp max))
           (unsigned-byte-p 63 (mv-nth 0 (genrandom-state max state))))
  :rule-classes :type-prescription)

(encapsulate nil

 (local (defthm lemma1
   (IMPLIES (and (posp max)
                 (natp x))
              
         (<= 0 (MOD x MAX)))
   :rule-classes :linear))

 
(local (defthm lemma2
 (IMPLIES (AND (posp MAX)
               (< MAX 2147483648)
              (natp x))
         (< (MOD x MAX)
            2147483648))
 :rule-classes :linear))
 
(defthm genrandom-natural1
  (implies (and (posp max)) ;(natp seed))
           (and (integerp (mv-nth 0 (genrandom-seed max seed)))
                (>= (mv-nth 0 (genrandom-seed max seed)) 0))
           )
   :rule-classes :type-prescription)

(defthm genrandom-natural2-type
  (implies (and (natp seed))
           (and (integerp (mv-nth 1 (genrandom-seed max seed)))
                (<= 0 (mv-nth 1 (genrandom-seed max seed)))))
   :rule-classes :type-prescription)

(defthm genrandom-ub63-1
  (implies (and (<= 1 max)
                (unsigned-byte-p 63 max) 
                (natp seed))
           (unsigned-byte-p 63 (mv-nth 0 (genrandom-seed max seed))))
   :rule-classes (:type-prescription))


(defthm genrandom-ub63-2
  (implies (and (<= 1 max)
                (unsigned-byte-p 63 max)
                (natp seed))
           (unsigned-byte-p 63 (mv-nth 1 (genrandom-seed max seed))))
  :rule-classes :type-prescription)
 
(defthm genrandom-minimum1
   (implies (and (posp max) (natp seed))
            (<= 0 (mv-nth 0 (genrandom-seed max seed))))
   :rule-classes :linear)

(defthm genrandom-minimum2
   (implies (and (natp seed))
            (<= 0 (mv-nth 1 (genrandom-seed max seed))))
   :rule-classes :linear)

(local (defthm loghead-lt-help
         (implies (and (natp x) (natp y) (posp size)
                       (< x y))
                  (< (acl2::loghead size x) y))
         :hints (("Goal" :in-theory (enable acl2::loghead)))))

 (defthm genrandom-maximum1
   (implies (and (posp max))
                 
            (< (mv-nth 0 (genrandom-seed max seed)) max))
   :rule-classes (:linear))

  (defthm genrandom-maximum2
   (implies (and (posp max)
                 (unsigned-byte-p 63 seed))
            (<= (mv-nth 1 (genrandom-seed max seed)) (1- (expt 2 63))))
   :rule-classes :linear)

 (defthm genrandom-state-natural
   (natp (mv-nth 0 (genrandom-state max state)))
   :rule-classes :type-prescription)

 (defthm genrandom-state-minimum 
   (<= 0 (mv-nth 0 (genrandom-state max state)))
   :rule-classes :linear)

 (local (defthm loghead-lte-help
         (implies (and (natp x) (natp y) (posp size)
                       (<= x y))
                  (<= (acl2::loghead size x) y))
         :hints (("Goal" :in-theory (enable acl2::loghead)))))
 
 (defthm genrandom-state-maximum
   (implies (posp max)
            (<= (mv-nth 0 (genrandom-state max state)) (1- max)))
   :rule-classes :linear)
 
 )

 
(in-theory (disable genrandom-seed genrandom-state))#|ACL2s-ToDo-Line|#



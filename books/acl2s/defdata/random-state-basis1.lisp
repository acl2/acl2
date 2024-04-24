#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book);$ACL2s-Preamble$|#


(in-package "DEFDATA")
(set-verify-guards-eagerness 2)
(include-book "std/util/bstar" :dir :system)
(include-book "acl2s/utilities" :dir :system)
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
;(local (include-book "arithmetic-5/top" :dir :system))

(def-const *M63* (1- (expt 2 63))) ;1 less than 2^63
(def-const *P1* 16807)

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

(defthm getseed-<-*m63*
  (<= (getseed state) *M63*)
  :rule-classes :linear)

(in-theory (disable getseed))
 
(defun putseed (s state)
  (declare (xargs :stobjs (state)
                  :guard (unsigned-byte-p 63 s)))
  (declare (type (unsigned-byte 63) s))
  (acl2::f-put-global 'random-seed s state))


(defun genrandom-seed (max seed.)
  "generates a pseudo-random number less than max, given that the
current random seed is seed. and also returns the new seed."
  (declare (type (unsigned-byte 63) max)
           (type (unsigned-byte 63) seed.))
  (declare (xargs :guard (and (unsigned-byte-p 63 seed.)
                              (unsigned-byte-p 63 max)
                              (posp max))))
  (mbe :logic (if (and (posp max)
                       (unsigned-byte-p 63 seed.))
                       
                  (b* (((the (unsigned-byte 63) seed.) (mod (* *P1* seed.) *M63*)))
                    (mv (the (unsigned-byte 63) (mod seed. max)) seed.))
                (mv 0 1382728371))
       :exec (b* (((the (unsigned-byte 63) seed.) (mod (* *P1* seed.) *M63*)))
               (mv (the (unsigned-byte 63) (mod seed. max)) (the (unsigned-byte 63) seed.)))))


(defun genrandom-state (max state)
  "generates a pseudo-random number less than max"
  (declare (type (unsigned-byte 63) max))
  (declare (xargs :stobjs (state)
                  :guard (and  (unsigned-byte-p 63 max)
                               (posp max))))
  (b* (((the (unsigned-byte 63) old-seed) (getseed state))
       ((the (unsigned-byte 63) new-seed) (mod (* *P1* old-seed) *M63*))
       (state (acl2::f-put-global 'random-seed new-seed state)))
    (mv (if (zp max)
          0
          (the (unsigned-byte 63) (mod new-seed max)))
        state)))

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
           (and (integerp (car (genrandom-seed max seed)))
                (>= (car (genrandom-seed max seed)) 0))
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
           (unsigned-byte-p 63 (car (genrandom-seed max seed))))
   :rule-classes (:type-prescription))


(defthm genrandom-ub63-2
  (implies (and (<= 1 max)
                (unsigned-byte-p 63 max)
                (natp seed))
           (unsigned-byte-p 63 (mv-nth 1 (genrandom-seed max seed))))
  :rule-classes :type-prescription)
 
(defthm genrandom-minimum1
   (implies (and (posp max) (natp seed))
            (<= 0 (car (genrandom-seed max seed))))
   :rule-classes :linear)

(defthm genrandom-minimum2
   (implies (and (natp seed))
            (<= 0 (mv-nth 1 (genrandom-seed max seed))))
   :rule-classes :linear)

 (defthm genrandom-maximum1
   (implies (and (posp max))
                 
            (< (car (genrandom-seed max seed)) max))
   :rule-classes (:linear))
 
 (defthm genrandom-maximum2
   (implies (and (posp max)
                 (unsigned-byte-p 63 seed))
            (< (mv-nth 1 (genrandom-seed max seed)) *M63*))
   :rule-classes :linear)
 
 



 (defthm genrandom-state-natural
   (natp (car (genrandom-state max state)))
   :rule-classes :type-prescription)

 (defthm genrandom-state-minimum 
   (<= 0 (car (genrandom-state max state)))
   :rule-classes :linear)
 
 (defthm genrandom-state-maximum
   (implies (posp max)
            (<= (car (genrandom-state max state)) (1- max)))
   :rule-classes :linear)
 
 )

 
(in-theory (disable genrandom-seed genrandom-state))#|ACL2s-ToDo-Line|#



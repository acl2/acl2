#|$ACL2s-Preamble$;
(ld "pkg.lsp")
(acl2::begin-book);$ACL2s-Preamble$|#


(in-package "DEFDATA")
(set-verify-guards-eagerness 2)
(include-book "tools/bstar" :dir :system)

(defconst *M31* 2147483647);1 less than 2^31
(defconst *P1* 16807)

(make-event
 (er-progn
  (assign random-seed 1382728371)
  (value '(value-triple (@ random-seed))))
 :check-expansion t)


(defun getseed (state)
  (declare (xargs :stobjs (state)))
  (if (f-boundp-global 'random-seed state)
    (b* ((s (@ random-seed)))
      (if (unsigned-byte-p 31 s)
        (the (unsigned-byte 31) s)
        0))
    0))

(local (include-book "arithmetic-2/floor-mod/floor-mod" :dir :system))

(defthm getseed-unsigned-byte31 
  (unsigned-byte-p 31 (getseed state))
  :rule-classes :type-prescription)

(defthm getseed-nat 
  (natp (getseed state))
  :rule-classes :type-prescription)

(defthm getseed-<-*m31*
  (<= (getseed state) *M31*)
  :rule-classes :linear)

(in-theory (disable getseed))
 
(defun genrandom (max seed.)
  "generates a pseudo-random number less than max, given that the
current random seed is seed. and also returns the new seed."
  (declare (type (unsigned-byte 31) max)
           (type (unsigned-byte 31) seed.))
  (declare (xargs :guard (and (unsigned-byte-p 31 seed.)
                              (unsigned-byte-p 31 max)
                              (posp max))))
  (b* (((the (unsigned-byte 31) seed.) (mod (* *P1* seed.) *M31*)))
   (mv (the (unsigned-byte 31) (mod seed. max)) seed.)))


(defun genrandom-state (max state)
  "generates a pseudo-random number less than max"
  (declare (type (unsigned-byte 31) max))
  (declare (xargs :stobjs (state)
                  :guard (and  (unsigned-byte-p 31 max)
                               (posp max))))
  (b* (((the (unsigned-byte 31) old-seed) (getseed state))
       ((the (unsigned-byte 31) new-seed) (mod (* *P1* old-seed) *M31*))
       (state (acl2::f-put-global 'random-seed new-seed state)))
    (mv (if (zp max)
          0
          (the (unsigned-byte 31) (mod new-seed max)))
        state)))

(encapsulate nil
 (local (include-book "arithmetic-2/floor-mod/floor-mod" :dir :system))

 
 (defthm lemma1
   (IMPLIES (and (posp max)
                 (natp x))
              
         (<= 0 (MOD x MAX)))
   :rule-classes :linear)

 
(defthm lemma2
 (IMPLIES (AND (posp MAX)
               (< MAX 2147483648)
              (natp x))
         (< (MOD x MAX)
            2147483648))
 :rule-classes :linear)
 
(defthm genrandom-natural1
  (implies (and (posp max) (natp seed))
           (natp (car (genrandom max seed)))
           )
   :rule-classes :type-prescription)

(defthm genrandom-natural2
  (implies (and (natp seed))
           (natp (mv-nth 1 (genrandom max seed))))
   :rule-classes :type-prescription)



(defthm genrandom-ub31-1
  (implies (and (<= 1 max)
                (unsigned-byte-p 31 max) 
                (natp seed))
           (unsigned-byte-p 31 (car (genrandom max seed))))
   :rule-classes :type-prescription)


(defthm genrandom-ub31-2
  (implies (and (natp seed))
           (unsigned-byte-p 31 (mv-nth 1 (genrandom max seed))))
   :rule-classes :type-prescription)
 
(defthm genrandom-minimum1
   (implies (and (posp max) (natp seed))
            (<= 0 (car (genrandom max seed))))
   :rule-classes :linear)

(defthm genrandom-minimum2
   (implies (and (natp seed))
            (<= 0 (mv-nth 1 (genrandom max seed))))
   :rule-classes :linear)

 (defthm genrandom-maximum1
   (implies (and (posp max)
                 (natp seed))
            (< (car (genrandom max seed)) max))
   :rule-classes :linear)
 
 (defthm genrandom-maximum2
   (implies (and (natp seed))
            (< (mv-nth 1 (genrandom max seed)) *M31*))
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

 
(in-theory (disable genrandom genrandom-state))#|ACL2s-ToDo-Line|#



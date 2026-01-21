(in-package "ACL2")

; See read-over-write-proofs.lisp for the proofs.

(include-book "x86-state")
(local (include-book "read-over-write-proofs"))

(set-enforce-redundancy t)

(defthmd rgfi-!rgfi-same
  (equal (rgfi i (!rgfi i v x86-32))
         v))

(defthmd rgfi-!rgfi-different
  (implies (and (force (n03p i))
                (force (n03p j))
                (not (equal i j)))
           (equal (rgfi i (!rgfi j v x86-32))
                  (rgfi i x86-32))))

(defthm rgfi-!rgfi
  (implies (and (force (n03p i))
                (force (n03p j))
                (not (equal i j)))
           (equal (rgfi i (!rgfi j v x86-32))
                  (if (equal i j)
                      v
                    (rgfi i x86-32)))))

(defthmd memi-!memi-same
  (equal (memi i (!memi i v x86-32))
         v))

(defthmd memi-!memi-different
  (implies (and (force (n32p i))
                (force (n32p j))
                (not (equal i j)))
           (equal (memi i (!memi j v x86-32))
                  (memi i x86-32)))
  :hints (("Goal" :in-theory (enable memi !memi))))

(defthm memi-!memi
  (implies (and (force (n32p i))
                (force (n32p j)))
           (equal (memi i (!memi j v x86-32))
                  (if (equal i j)
                      v
                    (memi i x86-32)))))

(defthm !memi-!memi-same
  (implies (and (force (x86-32p x86-32))
                (force (n30p addr)))
           (equal (!memi addr word1
                         (!memi addr word2 x86-32))
                  (!memi addr word1 x86-32))))

(defthmd rm08-wm08-same
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n08p v)))
           (equal (rm08 i (wm08 i v x86-32))
                  v)))

(defthmd rm08-wm08-different
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p j))
                (not (equal i j))
                (force (n08p v)))
           (equal (rm08 i (wm08 j v x86-32))
                  (rm08 i x86-32))))

(defthm rm08-wm08
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p j))
                (force (n08p v)))
           (equal (rm08 i (wm08 j v x86-32))
                  (if (equal i j)
                      v
                    (rm08 i x86-32)))))

(defthmd rm16-wm16-same
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n16p v)))
           (equal (rm16 i (wm16 i v x86-32))
                  v)))

(defthmd rm16-wm16-different
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p j))
                (force (n16p v))

; See the analogous comment in rm32-wm32-different for discussion of the
; hypothesis corresponding to that just below.

                (or (and (<= (+ 2 i) j)
                         (<= (+ 2 j) 4294967296))
                    (and (<= (+ 2 j) i)
                         (<= (+ 2 i) 4294967296)))) ; (expt 2 32)
           (equal (rm16 i (wm16 j v x86-32))
                  (rm16 i x86-32))))

(defthmd rm16-wm16-write-high-byte
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p j))
                (force (n16p v))
                (equal (+ i 1) j)
                (force (<= (+ 2 j) 4294967296))) ; (expt 2 32)
           (equal (rm16 i (wm16 j v x86-32))
                  (logior (ash (logand v #xff)
                               8)
                          (rm08 i x86-32)))))

(defthmd rm16-wm16-write-low-byte
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p j))
                (force (n16p v))
                (equal (+ j 1) i)
                (force (<= (+ 2 i) 4294967296))) ; (expt 2 32)
           (equal (rm16 i (wm16 j v x86-32))
                  (logior (ash (rm08 (+ i 1) x86-32)
                               8)
                          (ash v -8)))))

(defthm rm16-wm16
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (<= (+ 2 i) 4294967296)) ; (expt 2 32)
                (force (n32p j))
                (force (<= (+ 2 j) 4294967296)) ; (expt 2 32)
                (force (n16p v)))
           (equal (rm16 i (wm16 j v x86-32))
                  (cond ((equal i j)
                         v)
                        ((equal (+ i 1) j)
                         (logior (ash (logand v #xff)
                                      8)
                                 (rm08 i x86-32)))
                        ((equal (+ j 1) i)
                         (logior (ash (rm08 (+ i 1) x86-32)
                               8)
                          (ash v -8)))
                        (t
                         (rm16 i x86-32))))))

(defthmd rm32-wm32-same
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p v)))
           (equal (rm32 i (wm32 i v x86-32))
                  v)))

(defthmd rm32-wm32-different
  (implies (and (force (x86-32p x86-32))
                (force (n32p v))
                (force (n32p i))
                (force (n32p j))

; Note that (not (= i j)) is not a strong enough hypothesis, because the dwords
; starting at i and at j might overlap.  Moreover, we can't tolerate
; wrap-around: for example, for the first case below, if j is 2^32-1 and i is
; 0, then (<= (+ 4 i) j) holds but the dwords overlap because of wm32 will wrap
; around; hence the conjunct (<= (+ 4 j) 2^32).

                (or (and (<= (+ 4 i) j)
                         (<= (+ 4 j) 4294967296)) ; (expt 2 32)
                    (and (<= (+ 4 j) i)
                         (<= (+ 4 i) 4294967296))))
           (equal (rm32 i (wm32 j v x86-32))
                  (rm32 i x86-32))))

(defthm rm32-wm32
  (implies (and (force (x86-32p x86-32))
                (force (n32p v))
                (force (n32p i))
                (force (n32p j))
                (force (<= (+ 4 i) 4294967296))
                (force (<= (+ 4 j) 4294967296)))
           (equal (rm32 i (wm32 j v x86-32))
                  (cond ((equal i j)
                         v)
                        ((equal (+ 1 j) i)
                         (logior (ash v -8)
                                 (ash (rm08 (+ 3 i) x86-32) 24)))
                        ((equal (+ 2 j) i)
                         (logior (ash v -16)
                                 (ash (rm08 (+ 2 i) x86-32) 16)
                                 (ash (rm08 (+ 3 i) x86-32) 24)))
                        ((equal (+ 3 j) i)
                         (logior (ash v -24)
                                 (ash (rm08 (+ 1 i) x86-32) 8)
                                 (ash (rm08 (+ 2 i) x86-32) 16)
                                 (ash (rm08 (+ 3 i) x86-32) 24)))
                        ((equal j (+ 1 i))
                         (logior (rm08 i x86-32)
                                 (ash (logand v #xffffff) 8)))
                        ((equal j (+ 2 i))
                         (logior (rm08 i x86-32)
                                 (ash (rm08 (+ 1 i) x86-32) 8)
                                 (ash (logand v #xffff) 16)))
                        ((equal j (+ 3 i))
                         (logior (rm08 i x86-32)
                                 (ash (rm08 (+ 1 i) x86-32) 8)
                                 (ash (rm08 (+ 2 i) x86-32) 16)
                                 (ash (logand v #xff) 24)))
                        (t (rm32 i x86-32))))))

; a mixed read-write theorem
(defthm rm08-wm32
  (implies (and (force (x86-32p x86-32))
                (force (n32p v))
                (force (n32p i))
                (force (n32p j))
                (force (<= (+ 4 j) 4294967296)))
           (equal (rm08 i (wm32 j v x86-32))
                  (cond ((< i j)
                         (rm08 i x86-32))
                        ((equal i j)
                         (logand v #xff))
                        ((equal i (+ 1 j))
                         (logand (ash v -8) #xff))
                        ((equal i (+ 2 j))
                         (logand (ash v -16) #xff))
                        ((equal i (+ 3 j))
                         (ash v -24))
                        (t (rm08 i x86-32))))))

; other theorems of interest

(defthmd rm32-rm08
  (implies (and (force (x86-32p x86-32))
                (force (n32p addr))
                (force (<= (+ 4 addr) 4294967296))) ; (expt 2 32)
           (equal (rm32 addr x86-32)
                  (logior (ash (rm08 (+ 3 addr) x86-32)
                               24)
                          (ash (rm08 (+ 2 addr) x86-32)
                               16)
                          (ash (rm08 (+ 1 addr) x86-32)
                               8)
                          (rm08 addr x86-32)))))


(in-package "ACL2")

#||

; [Jared and Sol]: fool make_cert_help.pl into allowing more memory for this
; book. We would just include centaur/misc/memory-mgmt, but that has a ttag.

(set-max-mem (* 6 (expt 2 30)))

||#

; All theorems in this file are local except for those that are to be exported,
; which are labeled with the comment "; Exported theorem:".  We use def-gl-thm
; (actually a local version) so dispatch lemmas that were seen to be needed
; upon analysis of simplification checkpoints.  Without def-gl-thm, we would
; consider using one of these libraries:

; (local (include-book "arithmetic-5/top" :dir :system))
; (local (include-book "rtl/rel9/lib/top" :dir :system))

; That would perhaps take considerable work, however, because wm08 uses lognot,
; which doesn't appear in many lemmas in the above libraries.  Less important
; is that we might have to disable some rules, e.g. ash-rewrite in the latter
; case.  Fortunately, finding lemmas in either of the above books isn't hard,
; for example using the find-lemmas utility:

; (local (include-book "misc/find-lemmas" :dir :system))

(include-book "x86-state")

; Exported theorem:
(defthm rgfi-!rgfi-same
  (equal (rgfi i (!rgfi i v x86-32))
         v)
  :hints (("Goal" :in-theory (enable rgfi !rgfi))))

; Exported theorem:
(defthm rgfi-!rgfi-different
  (implies (and (force (n03p i))
                (force (n03p j))
                (not (equal i j)))
           (equal (rgfi i (!rgfi j v x86-32))
                  (rgfi i x86-32)))
  :hints (("Goal" :in-theory (enable rgfi !rgfi))))

; Exported theorem:
(defthm rgfi-!rgfi
  (implies (and (force (n03p i))
                (force (n03p j))
                (not (equal i j)))
           (equal (rgfi i (!rgfi j v x86-32))
                  (if (equal i j)
                      v
                    (rgfi i x86-32)))))

(local (in-theory (disable rgfi-!rgfi-same rgfi-!rgfi-different)))

; Exported theorem:
(defthm memi-!memi-same
  (equal (memi i (!memi i v x86-32))
         v)
  :hints (("Goal" :in-theory (enable memi !memi))))

; Exported theorem:
(defthm memi-!memi-different
  (implies (and (force (n32p i))
                (force (n32p j))
                (not (equal i j)))
           (equal (memi i (!memi j v x86-32))
                  (memi i x86-32)))
  :hints (("Goal" :in-theory (enable memi !memi))))

; Exported theorem:
(defthm memi-!memi
  (implies (and (force (n32p i))
                (force (n32p j)))
           (equal (memi i (!memi j v x86-32))
                  (if (equal i j)
                      v
                    (memi i x86-32)))))

(in-theory (disable memi-!memi-same memi-!memi-different))

(local (include-book "centaur/gl/gl" :dir :system))

(defmacro def-local-gl-thm (&rest args)
  `(local (def-gl-thm ,@args)))

(def-local-gl-thm rm08-wm08-same-lemma-1
  :hyp (force (and (n08p v)
                   (n32p mem-val)
                   (n02p i02)))
  :concl (equal
          (logand (ash (logior (logand (+ -1 (- (ash 255 (ash i02 3))))
                                       mem-val)
                               (ash v (ash i02 3)))
                       (- (ash i02 3)))
                  255)
          v)
  :g-bindings
  `((mem-val (:g-number ,(gl-int 0 1 33)))
    (v (:g-number ,(gl-int 33 1 9)))
    (i02 (:g-number ,(gl-int 42 1 3)))))

; From x86-state.lisp:
(def-local-gl-thm ash-addr--2-is-less
    :hyp (n32p addr)
    :concl (< (ash addr -2) 1073741824)
    :rule-classes :linear
    :g-bindings
    `((addr (:g-number ,(gl-int 0 1 33)))))

; Exported theorem:
(defthm rm08-wm08-same
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n08p v)))
           (equal (rm08 i (wm08 i v x86-32))
                  v))
  :hints (("Goal" :in-theory (enable rm08 wm08))))

(def-local-gl-thm rm08-wm08-different-same-dword-lemma
  :hyp (force (and (n32p mem-val)
                   (n02p i02)
                   (n02p j02)
                   (not (equal i02 j02))
                   (n08p v)))
  :concl (equal
          (logand (ash (logior (logand (+ -1 (- (ash 255 (ash j02 3))))
                                       mem-val)
                               (ash v (ash j02 3)))
                       (- (ash i02 3)))
                  255)
          (logand (ash mem-val
                       (- (ash i02 3)))
                  255))
  :g-bindings
  `((mem-val
     (:g-number ,(gl-int 0 1 33)))
    (i02
     (:g-number ,(gl-int 33 1 3)))
    (j02
     (:g-number ,(gl-int 36 1 3)))
    (v
     (:g-number ,(gl-int 39 1 9)))))

(def-local-gl-thm n32p-concat-ash-logand
  :hyp (n32p i)
  :concl (equal (logior (ash (ash i -2) 2)
                        (logand i 3))
                i)
  :rule-classes nil
  :g-bindings
  `((i (:g-number ,(gl-int 0 1 33)))))

(local
 (defthm rm08-wm08-different-same-dword
   (implies (and (x86-32p x86-32)
                 (n32p i)
                 (n32p j)
                 (equal (ash i -2) (ash j -2))
                 (not (equal i j))
                 (n08p v))
            (equal (rm08 i (wm08 j v x86-32))
                   (rm08 i x86-32)))
   :hints (("Goal"
            :in-theory (enable rm08 wm08))
           ("[1]Subgoal 1''"
            :use ((:instance n32p-concat-ash-logand (i i))
                  (:instance n32p-concat-ash-logand (i j)))))
   :rule-classes nil))

(local (in-theory (disable rm08-wm08-different-same-dword-lemma)))

(local
 (defthm rm08-wm08-different-different-dword
   (implies (and (x86-32p x86-32)
                 (n32p i)
                 (n32p j)
                 (not (equal (ash i -2) (ash j -2)))
                 (not (equal i j))
                 (n08p v))
            (equal (rm08 i (wm08 j v x86-32))
                   (rm08 i x86-32)))
   :hints (("Goal" :in-theory (enable rm08 wm08)))
   :rule-classes nil))

; Exported theorem:
(defthm rm08-wm08-different
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p j))
                (not (equal i j))
                (force (n08p v)))
           (equal (rm08 i (wm08 j v x86-32))
                  (rm08 i x86-32)))
  :hints (("Goal" :use (rm08-wm08-different-different-dword
                        rm08-wm08-different-same-dword))))

; Exported theorem:
(defthm rm08-wm08
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p j))
                (force (n08p v)))
           (equal (rm08 i (wm08 j v x86-32))
                  (if (equal i j)
                      v
                    (rm08 i x86-32)))))

(in-theory (disable rm08-wm08-same rm08-wm08-different))

; Start proof of rm16-wm16-same.

(def-local-gl-thm rm16-wm16-same-lemma-1
  :hyp (n16p v)
  :concl (equal (logior (ash (logand (ash v -8) 255) 8)
                        (logand v 255))
                v)
  :g-bindings
  `((v (:g-number ,(gl-int 0 1 17)))))

(def-local-gl-thm rm16-wm16-same-lemma-2
  :hyp (n32p i)
  :concl (not (equal i (logand (+ 1 i) 4294967295)))
  :g-bindings
  `((i (:g-number ,(gl-int 0 1 33)))))

(def-local-gl-thm rm16-wm16-same-lemma-3
  :hyp (and (n32p addr)
            (not (equal (logand addr 3) 3)))
  :concl (<= (ash (logand addr 3) 3) 16)
  :g-bindings
  `((addr (:g-number ,(gl-int  0 1 33))))
  :rule-classes :linear)

(def-local-gl-thm rm16-wm16-same-lemma-4
  :hyp (and (natp shift)
            (<= shift 16)
            (n32p dword)
            (n16p v))
  :concl (equal (logand (ash (logior (logand (+ -1 (- (ash 65535 shift)))
                                             dword)
                                     (ash v shift))
                             (- shift))
                        65535)
                v)
  :g-bindings
  `((shift (:g-number ,(gl-int 0 1 6)))
    (dword (:g-number ,(gl-int 6 1 33)))
    (v     (:g-number ,(gl-int 39 1 17)))))

; Exported theorem:
(defthm rm16-wm16-same
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n16p v)))
           (equal (rm16 i (wm16 i v x86-32))
                  v))
  :hints (("Goal" :in-theory (enable rm16 wm16))))

; We defer the proof of rm16-wm16-different to after the corresponding result
; for rm32 and wm32, so that lemmas proved for the latter can help with the
; former.

; Start proof of rm32-wm32-same.

(def-local-gl-thm hack1
  :hyp (AND (n32p i)
            (n32p v)
            (n32p dword0)
            (n32p dword1))
  :concl (equal
          (logior
           (ash (logior (logand dword0
                                (+ -1 (ash 1 (ash (logand i 3) 3))))
                        (ash (logand v
                                     (+ -1
                                        (ash 1 (ash (+ 4 (- (logand i 3))) 3))))
                             (ash (logand i 3) 3)))
                (- (ash (logand i 3) 3)))
           (ash
            (logand (logior (ash v (- (ash (+ 4 (- (logand i 3))) 3)))
                            (logand dword1
                                    (ash (+ -1
                                            (ash 1 (ash (+ 4 (- (logand i 3))) 3)))
                                         (ash (logand i 3) 3))))
                    (+ -1 (ash 1 (ash (logand i 3) 3))))
            (ash (+ 4 (- (logand i 3))) 3)))
          v)
  :g-bindings
  `((dword0 (:g-number ,(gl-int  0 1 33)))
    (dword1 (:g-number ,(gl-int 34 1 33)))
    (i (:g-number ,(gl-int 68 1 33)))
    (v (:g-number ,(gl-int 102 1 33)))))

(def-local-gl-thm hack2
  :hyp (n32p i)
  :concl (not (equal (logand (+ 1 (ash i -2)) 1073741823)
                     (ash i -2)))
  :g-bindings
  `((i (:g-number ,(gl-int 0 1 33)))))

; Exported theorem:
(defthm rm32-wm32-same
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p v)))
           (equal (rm32 i (wm32 i v x86-32))
                  v))
  :hints (("Goal" :in-theory (enable rm32 wm32))))

; Start proof of rm32-wm32-different.  That theorem really consists of two
; cases: one for i<j and the other for j<i.  See the comment in that theorem.
; We prove each case separately.

; Start proof of rm32-wm32-different-i<j.

(def-local-gl-thm hack3
  :hyp (and (n32p i)
            (n32p j)
            (<= (+ 4 i) j))
  :concl (equal (equal (ash i -2)
                       (ash j -2))
                nil)
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))))

(def-local-gl-thm hack4
  :hyp (and (n32p i)
            (n32p j)
            (< i j)
            (equal (logand j 3) 0))
  :concl (equal (equal (ash i -2)
                       (ash j -2))
                nil)
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))))

(def-local-gl-thm hack5
  :hyp (AND (n32p i)
            (n32p j)
            (<= (+ 4 i) j)
            (<= (+ 4 j) 4294967296)
            (not (equal (logand j 3) 0)))
  :concl (not (equal (ash i -2)
                     (logand (+ 1 (ash j -2)) 1073741823)))
   :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))))

(def-local-gl-thm hack6
  :hyp (and (n32p i)
            (n32p j)
            (<= (+ 4 i) j)
            (equal (logand j 3) 0)
            (not (equal (logand i 3) 0)))
  :concl (not (equal (logand (+ 1 (ash i -2)) 1073741823)
                     (ash j -2)))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))))

(def-local-gl-thm hack7
  :hyp (and (n32p i)
            (n32p j)
            (<= (+ 4 i) j))
  :concl (not (equal (logand (+ 1 (ash i -2)) 1073741823)
                     (logand (+ 1 (ash j -2)) 1073741823)))
   :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))))

(def-local-gl-thm hack8
  :hyp (and (n32p i)
            (n32p j)
            (<= (+ 4 i) j)
            (n32p v)
            (equal (logand (+ 1 (ash i -2)) 1073741823)
                   (ash j -2))
            (n32p dword))
  :concl (equal
          (ash
           (logand (logior (logand dword
                                   (+ -1 (ash 1 (ash (logand j 3) 3))))
                           (ash (logand v
                                        (+ -1
                                           (ash 1 (ash (+ 4 (- (logand j 3))) 3))))
                                (ash (logand j 3) 3)))
                   (+ -1 (ash 1 (ash (logand i 3) 3))))
           (ash (+ 4 (- (logand i 3))) 3))
          (ash (logand dword
                       (+ -1 (ash 1 (ash (logand i 3) 3))))
               (ash (+ 4 (- (logand i 3))) 3)))
   :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (dword (:g-number ,(gl-int 68 2 33)))
    (v (:g-number ,(gl-int 69 2 33)))))

(local
 (defthm rm32-wm32-different-i<j
   (implies (and (x86-32p x86-32)
                 (n32p i)
                 (n32p j)
                 ;; Note that (not (= i j)) is not strong enough:
                 (<= (+ 4 i) j)
                 (<= (+ 4 j) 4294967296) ; (expt 2 32)
                 (n32p v))
            (equal (rm32 i (wm32 j v x86-32))
                   (rm32 i x86-32)))
   :hints (("Goal" :in-theory (enable rm32 wm32)

; Note: We originally needed the following :cases hint, but that is no longer
; necessary because memi-!memi induces a case split.  To see the need, first
; execute:
; (in-theory (e/d (memi-!memi-same memi-!memi-different) (memi-!memi)))

;           :cases ((equal (logand (+ 1 (ash i -2)) 1073741823) (ash j -2)))
            ))
   :rule-classes nil))

; Start proof of rm32-wm32-different-j<i.

(def-local-gl-thm hack9
  :hyp (AND (n32p i)
            (n32p j)
            (<= (+ 4 j) i))
  :concl (not (equal (ash i -2) (ash j -2)))
   :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))))

(def-local-gl-thm hack10
  :hyp (and (n32p i)
            (n32p j)
            (<= (+ 4 j) i)
            (n32p v)
            (equal (ash i -2)
                   (logand (+ 1 (ash j -2)) 1073741823))
            (n32p dword))
  :concl (equal
          (ash (logior (ash v (- (ash (+ 4 (- (logand j 3))) 3)))
                       (logand dword
                               (ash (+ -1
                                       (ash 1 (ash (+ 4 (- (logand j 3))) 3)))
                                    (ash (logand j 3) 3))))
               (- (ash (logand i 3) 3)))
          (ash dword
               (- (ash (logand i 3) 3))))
   :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (dword (:g-number ,(gl-int 68 2 33)))
    (v (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm hack11
  :hyp (and (n32p i)
            (n32p j)
            (<= (+ 4 j) i))
  :concl (not (equal (logand (+ 1 (ash i -2)) 1073741823)
                     (logand (+ 1 (ash j -2)) 1073741823)))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))))

(local
 (defthm rm32-wm32-different-j<i
   (implies (and (x86-32p x86-32)
                 (n32p i)
                 (n32p j)
                 ;; Note that (not (= i j)) is not strong enough:
                 (<= (+ 4 j) i)
                 (<= (+ 4 i) 4294967296) ; (expt 2 32)
                 (n32p v)
                 )
            (equal (rm32 i (wm32 j v x86-32))
                   (rm32 i x86-32)))
   :hints (("Goal"
            :in-theory (enable rm32 wm32)

; Note: We originally needed the following :cases hint, but that is no longer
; necessary because memi-!memi induces a case split.  To see the need, first
; execute:
; (in-theory (e/d (memi-!memi-same memi-!memi-different) (memi-!memi)))

;           :cases ((equal (ash i -2) (logand (+ 1 (ash j -2)) 1073741823)))
            ))
   :rule-classes nil))

; Exported theorem:
(defthm rm32-wm32-different
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
                  (rm32 i x86-32)))
  :hints (("Goal" :use (rm32-wm32-different-i<j
                        rm32-wm32-different-j<i))))

(defthm rm32-wm32-no-overlap
  (implies (and (force (x86-32p x86-32))
                (force (n32p v))
                (force (n32p i))
                (force (n32p j))
                (or (and (<= (+ 4 i) j)
                         (<= (+ 4 j) 4294967296)) ; (expt 2 32)
                    (and (<= (+ 4 j) i)
                         (<= (+ 4 i) 4294967296))))
           (equal (rm32 i (wm32 j v x86-32))
                  (rm32 i x86-32)))
  :hints (("Goal" :expand ((hide (rm32 i (wm32 j v x86-32)))))))

; Finally, to prove all the various cases in which the 32-bit read and write
; regions overlap, we first reduce 32-bit reads and writes to concenations
; involving 8-bit reads and writes.

(def-local-gl-thm hack12
  :hyp (and (n32p addr)
            (<= (+ 4 addr) 4294967296)
            (equal (logand addr 3) 0)
            (n02p k))
  :concl (equal (ash (+ k addr) -2)
                (ash addr -2))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))
    (k (:g-number ,(gl-int 33 1 36)))))

(def-local-gl-thm hack13
  :hyp (and (n32p addr)
            (<= (+ 4 addr) 4294967296)
            (equal (logand addr 3) 0)
            (n02p k))
  :concl (equal (logand (+ k addr) 3)
                k)
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))
    (k (:g-number ,(gl-int 33 1 36)))))

(def-local-gl-thm hack14
  :hyp (n32p dword)
  :concl (equal (logior (ash (logand (ash dword -24)
                                     255)
                             24)
                        (ash (logand (ash dword -16)
                                     255)
                             16)
                        (ash (logand (ash dword -8)
                                     255)
                             8)
                        (logand (ash dword 0)
                                255))
                dword)
  :g-bindings
  `((dword (:g-number ,(gl-int 0 1 33)))))

(def-local-gl-thm hack15
  :hyp (and (n32p addr)
            (<= (+ 4 addr) 4294967296) ; (expt 2 32)
            (not (equal (logand addr 3) 0)))
  :concl (equal (logand (+ 1 (ash addr -2)) 1073741823)
                (+ 1 (ash addr -2)))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))))

(def-local-gl-thm hack16
  :hyp (and (n32p addr)
            (<= (+ 4 addr) 4294967296) ; (expt 2 32)
            (not (equal (logand addr 3) 0))
            (integerp k)
            (< 0 k)
            (< k 4))
  :concl (equal (ash (+ k addr) -2)
                (case k
                  (1 (case (logand addr 3)
                       (3 (+ 1 (ash addr -2)))
                       (otherwise (ash addr -2))))
                  (2 (case (logand addr 3)
                       ((2 3) (+ 1 (ash addr -2)))
                       (otherwise (ash addr -2))))
                  (3 (+ 1 (ash addr -2)))))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))
    (k (:g-number ,(gl-int 33 1 3)))))

(def-local-gl-thm hack17
  :hyp (and (integerp addr)
            (<= 0 addr)
            (<= (+ 4 addr) 4294967296) ; (expt 2 32)
            (equal 2 (logand addr 3))
            (n32p dword0)
            (n32p dword1))
  :concl (equal (logior (ash (logand (ash dword1
                                          (- (ash (logand (+ 3 addr) 3) 3)))
                                     255)
                             24)
                        (ash (logand (ash dword1
                                          (- (ash (logand (+ 2 addr) 3) 3)))
                                     255)
                             16)
                        (ash (logand (ash dword0
                                          (- (ash (logand (+ 1 addr) 3) 3)))
                                     255)
                             8)
                        (logand (ash dword0 -16)
                                255))
                (logior (ash dword0 -16)
                        (ash (logand dword1
                                     65535)
                             16)))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))
    (dword0 (:g-number ,(gl-int 34 1 33)))
    (dword1 (:g-number ,(gl-int 68 1 33)))))

(def-local-gl-thm hack18
  :hyp (and (integerp addr)
            (<= 0 addr)
            (<= (+ 4 addr) 4294967296) ; (expt 2 32)
            (equal 1 (logand addr 3))
            (n32p dword0)
            (n32p dword1))
  :concl (equal (logior (ash dword0 -8)
                        (ash (logand dword1
                                     255)
                             24))
                (logior (ash (logand (ash dword1
                                          (- (ash (logand (+ 3 addr) 3) 3)))
                                     255)
                             24)
                        (ash (logand (ash dword0
                                          (- (ash (logand (+ 2 addr) 3) 3)))
                                     255)
                             16)
                        (ash (logand (ash dword0
                                          (- (ash (logand (+ 1 addr) 3) 3)))
                                     255)
                             8)
                        (logand (ash dword0 -8)
                                255)))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))
    (dword0 (:g-number ,(gl-int 34 1 33)))
    (dword1 (:g-number ,(gl-int 68 1 33)))))

(def-local-gl-thm hack19
  :hyp (and (integerp addr)
            (<= 0 addr)
            (<= (+ 4 addr) 4294967296) ; (expt 2 32)
            (equal 3 (logand addr 3))
            (n32p dword0)
            (n32p dword1))
  :concl (equal (logior (ash (logand (ash dword1
                                          (- (ash (logand (+ 3 addr) 3) 3)))
                                     255)
                             24)
                        (ash (logand (ash dword1
                                          (- (ash (logand (+ 2 addr) 3) 3)))
                                     255)
                             16)
                        (ash (logand (ash dword1
                                          (- (ash (logand (+ 1 addr) 3) 3)))
                                     255)
                             8)
                        (logand (ash dword0 -24)
                                255))
                (logior (ash dword0 -24)
                        (ash (logand dword1
                                     16777215)
                             8)))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))
    (dword0 (:g-number ,(gl-int 34 1 33)))
    (dword1 (:g-number ,(gl-int 68 1 33)))))

(def-local-gl-thm hack20
  :hyp (and (equal (ash addr -2) 1073741823)
            (integerp addr)
            (<= 0 addr)
            (<= (+ 4 addr) 4294967296))
  :concl (not (equal (logand addr 3) 3))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))))

(def-local-gl-thm hack21
  :hyp (and (equal (ash addr -2) 1073741823)
            (integerp addr)
            (<= 0 addr)
            (<= (+ 4 addr) 4294967296)) ; (expt 2 32)
  :concl (not (equal (logand addr 3) 1))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))))

(def-local-gl-thm hack22
  :hyp (and (equal (ash addr -2) 1073741823)
            (integerp addr)
            (<= 0 addr)
            (<= (+ 4 addr) 4294967296)) ; (expt 2 32)
  :concl (not (equal (logand addr 3) 2))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))))

; Reordering the rewrite-clause-type-alist: I added the uppercase text below to
; make this work.  See the comment in rewrite-clause-type-alist.
; JSM April 7, 2013.

(defthm rm32-rm08
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
                          (rm08 addr x86-32))))
  :hints (("Goal"
           :in-theory
           (e/d (rm32 rm08)
                ((:EXECUTABLE-COUNTERPART BINARY-LOGAND))))))

; In order to prove rules about the case of overlapping addresses for 32-bit
; read/write, our strategy is to reduce reads to 8-bit reads and to reason
; about 8-bit reads of 32-bit writes.

(def-local-gl-thm ash--2-monotone
  :hyp (and (n32p i)
            (n32p j)
            (<= i j))
  :concl (<= (ash i -2) (ash j -2))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33))))
  :rule-classes :linear)

(local
 (defthm +-assoc-constants
   (implies (and (syntaxp i) (syntaxp j))
            (equal (+ i (+ j k))
                   (+ (+ i j) k)))))

(local
 (with-arithmetic-help-5

  (defthm logior-commutative
    (equal (logior x y) (logior y x)))

  (defthm logior-associative
    (equal (logior (logior x y) z) (logior x y z)))

  (defthm logior-commutative-2
    (equal (logior x y z) (logior y x z)))))

; Working towards rm08-wm32:

(local (in-theory (disable natp)))

(def-local-gl-thm rm08-wm32-hack-1
  :hyp (and (n32p i)
            (n32p j)
            (n32p dword)
            (n32p v)
            (< i j)
            (equal (ash i -2) (ash j -2)))
  :concl (equal
          (logand
           (ash (logior (logand dword
                                (+ -1 (ash 1 (ash (logand j 3) 3))))
                        (ash (logand v
                                     (+ -1
                                        (ash 1 (ash (+ 4 (- (logand j 3))) 3))))
                             (ash (logand j 3) 3)))
                (- (ash (logand i 3) 3)))
           255)
          (logand (ash dword
                       (- (ash (logand i 3) 3)))
                  255))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm rm08-wm32-hack-2
  :hyp (and (n32p i)
            (n32p j)
            (n32p dword)
            (n32p v))
  :concl (equal
          (logand
           (ash (logior (logand dword
                                (+ -1 (ash 1 (ash (logand i 3) 3))))
                        (ash (logand v
                                     (+ -1
                                        (ash 1 (ash (+ 4 (- (logand i 3))) 3))))
                             (ash (logand i 3) 3)))
                (- (ash (logand i 3) 3)))
           255)
          (logand v 255))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm rm08-wm32-hack-3
  :hyp (and (n32p i)
            (n32p j)
            (equal (logand j 3) 3)
            (n32p dword)
            (n32p v))
  :concl (equal (logand (ash (logior (ash v -8)
                                     (logand dword
                                             4278190080))
                             (- (ash (logand (+ 1 j) 3) 3)))
                        255)
                (logand (ash v -8) 255))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm rm08-wm32-hack-4
  :hyp (and (n32p i)
            (n32p j)
            (not (equal (logand j 3) 3))
            (n32p dword)
            (n32p v))
  :concl (equal
          (logand
           (ash (logior (logand dword
                                (+ -1 (ash 1 (ash (logand j 3) 3))))
                        (ash (logand v
                                     (+ -1
                                        (ash 1 (ash (+ 4 (- (logand j 3))) 3))))
                             (ash (logand j 3) 3)))
                (- (ash (logand (+ 1 j) 3) 3)))
           255)
          (logand (ash v -8) 255))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm rm08-wm32-hack-5
  :hyp (and (n32p i)
            (n32p j)
            (equal 2 (logand j 3))
            (n32p dword)
            (n32p v))
  :concl (equal (logand (ash (logior (ash v -16)
                                     (logand dword
                                             4294901760))
                             (- (ash (logand (+ 2 j) 3) 3)))
                        255)
                (logand (ash v -16) 255))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm rm08-wm32-hack-6
  :hyp (and (n32p i)
            (n32p j)
            (equal (logand j 3) 1)
            (n32p dword)
            (n32p v))
  :concl (equal (logand (ash (logior (ash (logand v 16777215) 8)
                                     (logand dword 255))
                             (- (ash (logand (+ 2 j) 3) 3)))
                        255)
                (logand (ash v -16) 255))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm rm08-wm32-hack-7
  :hyp (and (n32p i)
            (n32p j)
            (equal 3 (logand j 3))
            (n32p dword)
            (n32p v))
  :concl (equal (logand (ash (logior (ash v -8)
                                     (logand dword
                                             4278190080))
                             (- (ash (logand (+ 2 j) 3) 3)))
                        255)
                (logand (ash v -16) 255))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm rm08-wm32-hack-8
  :hyp (and (n32p j)
            (not (equal (logand j 3) 0))
            (n32p dword)
            (n32p v))
  :concl (equal
          (logand (ash (logior (ash v (- (ash (+ 4 (- (logand j 3))) 3)))
                               (logand dword
                                       (ash (+ -1
                                               (ash 1 (ash (+ 4 (- (logand j 3))) 3)))
                                            (ash (logand j 3) 3))))
                       (- (ash (logand (+ 3 j) 3) 3)))
                  255)
          (ash v -24))
  :g-bindings
  `(;(i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm rm08-wm32-hack-8-a
  :hyp (and (n32p j)
            (<= (+ 4 j) 4294967296)
            (not (equal (logand j 3) 0)))
  :concl (< (+ 1 (ash j -2))
            1073741824)
  :g-bindings
  `((j (:g-number ,(gl-int 0 1 33))))
  :rule-classes :linear)

(local
 (with-arithmetic-help-5

  (defthm ash-0
    (implies (integerp x)
             (equal (ash x 0) x)))))

(def-local-gl-thm rm08-wm32-hack-9
  :hyp (n32p v)
  :concl (equal (logand (ash v -24) 255)
                (ash v -24))
  :g-bindings
  `((v (:g-number ,(gl-int 0 1 33))))
  :rule-classes :linear)

(def-local-gl-thm rm08-wm32-hack-10
  :hyp (and (n32p i)
            (n32p j)
            (not (equal i j))
            (not (equal i (+ 1 j)))
            (not (equal i (+ 2 j)))
            (not (equal i (+ 3 j)))
            (equal (logand j 3) 0))
  :concl (not (equal (ash i -2) (ash j -2)))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))))

(def-local-gl-thm rm08-wm32-hack-11
  :hyp (and (n32p i)
            (n32p j)
            (n32p v)
            (n32p dword)
            (not (equal i (+ 1 j)))
            (not (equal i (+ 2 j)))
            (not (equal i (+ 3 j)))
            (equal (ash i -2) (+ 1 (ash j -2))))
  :concl (equal
          (logand (ash (logior (ash v (- (ash (+ 4 (- (logand j 3))) 3)))
                               (logand dword
                                       (ash (+ -1
                                               (ash 1 (ash (+ 4 (- (logand j 3))) 3)))
                                            (ash (logand j 3) 3))))
                       (- (ash (logand i 3) 3)))
                  255)
          (logand (ash dword
                       (- (ash (logand i 3) 3)))
                  255))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

(def-local-gl-thm rm08-wm32-hack-12
  :hyp (and (n32p i)
            (n32p j)
            (n32p v)
            (n32p dword)
            (not (equal i j))
            (not (equal i (+ 1 j)))
            (not (equal i (+ 2 j)))
            (not (equal i (+ 3 j)))
            (equal (ash i -2) (ash j -2)))
  :concl (equal
          (logand
           (ash (logior (logand dword
                                (+ -1 (ash 1 (ash (logand j 3) 3))))
                        (ash (logand v
                                     (+ -1
                                        (ash 1 (ash (+ 4 (- (logand j 3))) 3))))
                             (ash (logand j 3) 3)))
                (- (ash (logand i 3) 3)))
           255)
          (logand (ash dword
                       (- (ash (logand i 3) 3)))
                  255))
  :g-bindings
  `((i (:g-number ,(gl-int 0 2 33)))
    (j (:g-number ,(gl-int 1 2 33)))
    (v (:g-number ,(gl-int 68 2 33)))
    (dword (:g-number ,(gl-int 69 2 33)))))

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
                        (t (rm08 i x86-32)))))
  :hints (("Goal" :in-theory (enable rm08 wm32))))

(def-local-gl-thm rm32-wm32-hack1
  :hyp (and (n32p v)
            (n08p byte0)
            (n08p byte1))
  :concl (equal (logior (ash (logand v 255) 16)
                        (ash (logand (ash v -8) 255) 24)
                        byte0
                        (ash byte1 8))
                (logior (ash (logand v 65535) 16)
                        byte0
                        (ash byte1 8)))
  :g-bindings
  `((v (:g-number ,(gl-int 0 1 33)))
    (byte0 (:g-number ,(gl-int 34 2 9)))
    (byte1 (:g-number ,(gl-int 35 2 9)))))

(def-local-gl-thm rm32-wm32-hack2
  :hyp (and (n32p v)
            (n08p byte0))
  :concl (equal (logior (ash (logand v 255) 8)
                        (ash (logand (ash v -8) 255) 16)
                        (ash (logand (ash v -16) 255) 24)
                        byte0)
                (logior (ash (logand v 16777215) 8)
                        byte0))
  :g-bindings
  `((v (:g-number ,(gl-int 0 1 33)))
    (byte0 (:g-number ,(gl-int 34 1 9)))))

(def-local-gl-thm rm32-wm32-hack3
  :hyp (n32p v)
  :concl (equal (logior (logand v 255)
                        (ash (ash v -24) 24)
                        (ash (logand (ash v -8) 255) 8)
                        (ash (logand (ash v -16) 255) 16))
                v)
  :g-bindings
  `((v (:g-number ,(gl-int 0 1 33)))))

(def-local-gl-thm rm32-wm32-hack4
  :hyp (and (n32p v)
            (n08p byte0))
  :concl (equal (logior (ash (ash v -24) 16)
                        (logand (ash v -8) 255)
                        (ash (logand (ash v -16) 255) 8)
                        (ash byte0 24))
                (logior (ash v -8)
                        (ash byte0 24)))
  :g-bindings
  `((v (:g-number ,(gl-int 0 1 33)))
    (byte0 (:g-number ,(gl-int 34 1 9)))))

(def-local-gl-thm rm32-wm32-hack5
  :hyp (and (n32p v)
            (n08p byte0)
            (n08p byte1))
  :concl (equal (logior (ash (ash v -24) 8)
                        (logand (ash v -16) 255)
                        (ash byte0 16)
                        (ash byte1 24))
                (logior (ash v -16)
                        (ash byte0 16)
                        (ash byte1 24)))
  :g-bindings
  `((v (:g-number ,(gl-int 0 1 33)))
    (byte0 (:g-number ,(gl-int 34 2 9)))
    (byte1 (:g-number ,(gl-int 35 2 9)))))

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

; Start proof of rm16-wm16-different, originally deferred to here (after the
; corresponding result for rm32 and wm32) so that lemmas proved for the latter
; can help with the former (though perhaps that's no longer necessary, given
; that we have since changed the definitions of rm32 and wm32).

; An initial proof exploration was messy, so we decided to reduce 16-bit reads
; and writes to 8-bit reads and writes.  It might be nice to do similarly for
; the analogous 32-bit theorem (already proved above).

; Below here, it helped during development to add the syntaxp hypothesis to
; lemma ash-negative-shift-makes-input-smaller in misc-events.lisp.

(local
 (with-arithmetic-help-5
  (defthm logand-+1-3
    (implies (natp x)
             (equal (logand (+ 1 x) 3)
                    (if (equal (logand x 3) 3)
                        0
                      (1+ (logand x 3))))))))

(def-local-gl-thm logand-<-expt-32-identity
  :hyp (and (natp j)
            (< j 4294967296) ; (expt 2 32)
            )
  :concl (equal (logand j 4294967295) ; (1- (expt 2 32))
                j)
  :g-bindings
  `((j (:g-number ,(gl-int 0 1 33)))))

(local
 (with-arithmetic-help-5
  (defthm ash-+1--2
    (implies (natp addr)
             (equal (ash (+ 1 addr) -2)
                    (if (equal (logand addr 3) 3)
                        (+ 1 (ash addr -2))
                      (ash addr -2)))))))

(def-local-gl-thm rm16-rm08-lemma-lemma
  :hyp (and (integerp addr)
            (<= 0 addr)
            (< (+ 1 addr) 4294967296)
            (not (equal (logand addr 3) 3))
            (n32p val))
  :concl (equal (logior (ash (logand (ash val (- (ash (+ 1 (logand addr 3)) 3)))
                                     255)
                             8)
                        (logand (ash val (- (ash (logand addr 3) 3)))
                                255))
                (logand (ash val (- (ash (logand addr 3) 3)))
                        65535))
  :g-bindings
  `((addr (:g-number ,(gl-int 0 1 33)))
    (val  (:g-number ,(gl-int 33 1 66)))))

(local
 (defthm rm16-rm08-lemma
   (implies (and (x86-32p x86-32)
                 (natp addr)
                 (n32p (1+ addr))
                 (not (equal (logand addr 3) 3)))
            (equal (rm16 addr x86-32)
                   (let* ((byte0 (rm08       addr    x86-32))
                          (byte1 (rm08 (n32+ addr 1) x86-32)))
                     (logior (ash byte1 8) byte0))))
   :hints (("Goal" :in-theory (enable rm16 rm08)))))

; Exported theorem, potentially:
(defthm rm16-rm08
  (implies (and (force (x86-32p x86-32))
                (integerp addr)
                (force (n32p (1+ addr))))
           (equal (rm16 addr x86-32)
                  (logior (ash (rm08 (+ 1 addr) x86-32)
                               8)
                          (rm08 addr x86-32))))
  :hints (("Goal"
           :in-theory (enable rm16 rm08)
           :use rm16-rm08-lemma)))

(def-local-gl-thm logand-ash--8 ; Move to some library?
  :hyp (n16p word)
  :concl (equal (logand (ash word -8) 255)
                (ash word -8))
  :g-bindings
  `((word (:g-number ,(gl-int 0 1 17)))))

(local ; Move to some library?
 (defthm update-nth-update-nth-same
   (equal (update-nth i val1
                      (update-nth i val2 lst))
          (update-nth i val1 lst))))

; Exported theorem:
(defthm !memi-!memi-same
  (implies (and (force (x86-32p x86-32))
                (force (n30p addr)))
           (equal (!memi addr word1
                         (!memi addr word2 x86-32))
                  (!memi addr word1 x86-32)))
  :hints (("Goal" :in-theory (enable !memi))))

(def-local-gl-thm wm16-wm08-lemma
  :hyp (and (integerp n2)
            (<= 0 n2)
            (< n2 3)
            (n16p word)
            (n32p dword))
  :concl (equal (logior (ash word (ash n2 3))
                        (logand (+ -1
                                   (- (ash 65535 (ash n2 3))))
                                dword))
                (logior (ash (ash word -8)
                             (ash (+ 1 n2) 3))
                        (logand (+ -1
                                   (- (ash 255 (ash (+ 1 n2) 3))))
                                (logior (ash (logand word 255)
                                             (ash n2 3))
                                        (logand (+ -1
                                                   (- (ash 255 (ash n2 3))))
                                                dword)))))
  :g-bindings
  `((word  (:g-number ,(gl-int  0 1 17)))
    (dword (:g-number ,(gl-int 17 1 33)))
    (n2    (:g-number ,(gl-int 50 1 3)))))

; Exported theorem, potentially:
(defthm wm16-wm08
  (implies (and (force (x86-32p x86-32))
                (natp addr)
                (force (n32p (1+ addr)))
                (force (n16p word)))
           (equal (wm16 addr word x86-32)
                  (wm08 (+ 1 addr) (ash word -8)
                        (wm08 addr (logand word #xff)
                              x86-32))))
  :hints (("Goal"
           :in-theory (enable wm16 wm08)
           :use rm16-rm08-lemma)))

(local
 (with-arithmetic-help-5
  (defthm ash--8-linear
    (implies (n16p x)
             (<= (ash x -8) 255))
    :rule-classes :linear)))

; Exported theorem:
(defthm rm16-wm16-different
  (implies (and (force (x86-32p x86-32))
                (force (n32p i))
                (force (n32p j))
                (force (n16p v))
                (or (and (<= (+ 2 i) j)
                         (<= (+ 2 j) 4294967296))
                    (and (<= (+ 2 j) i)
                         (<= (+ 2 i) 4294967296)))) ; (expt 2 32)
           (equal (rm16 i (wm16 j v x86-32))
                  (rm16 i x86-32))))

; Exported theorem:
(defthm rm16-wm16-write-high-byte
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

; Exported theorem:
(defthm rm16-wm16-write-low-byte
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

(def-local-gl-thm hack-last
  :hyp (n16p v)
  :concl (equal (logior (logand v 255)
                        (ash (ash v -8) 8))
                v)
  :g-bindings
  `((v (:g-number ,(gl-int 0 1 17)))))

; Exported theorem:
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

(local (in-theory (disable rm16-rm08 wm16-wm08)))

(in-theory (disable rm16-wm16-same rm16-wm16-different))

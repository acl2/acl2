; Phase 4 -- THE RECURRENCE BRIDGE:  kk-iter == Kestrel keyexpansion.
;
;   MAIN (kk-iter-is-keyexpansion):  (aes::inp key), r <= 10  =>
;     kk-iter(key, r) = round key r of (aes::keyexpansion key 4)
;                     = (append w[4r] w[4r+1] w[4r+2] w[4r+3])
;
; Structure:
;   (1) sbox-is / bvxor8-is-logxor / rcon-row: primitive bridges (the fixslice
;       side's *sbox* table = (aes::sbox); word xor = byte logxor on u8s; the
;       rcon table rows are make-word(kx r,0,0,0)).
;   (2) nth-of-loop1: the first four words are the key's bytes.
;   (3) l2-nth: THE characterization of keyexpansionloop2 -- entry j of the
;       completed loop is untouched below the start index and satisfies the
;       word recurrence  w[j] = wordxor(w[j-4], l2temp(j, w[j-1]))  above it.
;   (4) step-words-to-bytes: one word-level round step, flattened to bytes,
;       IS kr-spec-bytes (pure algebra over 16 symbolic bytes).
;   (5) MAIN by induction on r.
(in-package "ACL2")
(include-book "aes_fixslice_keyread")
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "kestrel/bv/logxor" :dir :system))
(local (in-theory (disable len-when-wstatep true-listp-when-wstatep nth-when-zp)))

;; ---------------------------------------------------------------------------
;; (1) primitive bridges.
(local (defthm sbox-is
  (equal (aes::sbox) *sbox*)
  :hints (("Goal" :use sbox-const-correct))))

(local (defthm bvchop8-id
  (implies (unsigned-byte-p 8 x) (equal (acl2::bvchop 8 x) x))
  :hints (("Goal" :in-theory (enable acl2::bvchop unsigned-byte-p)))))
(defthm bvxor8-is-logxor
  (implies (and (unsigned-byte-p 8 x) (unsigned-byte-p 8 y))
           (equal (acl2::bvxor 8 x y) (logxor x y)))
  :hints (("Goal" :in-theory (enable acl2::bvxor))))

;; the rcon table, one row at a time, in terms of the fixslice side's kx.
(defthm rcon-row
  (implies (and (natp r) (< r 10))
           (equal (nth (+ 1 r) aes::*rcon*)
                  (aes::make-word (kx r) 0 0 0)))
  :hints (("Goal" :in-theory (enable kx)
           :cases ((equal r 0) (equal r 1) (equal r 2) (equal r 3) (equal r 4)
                   (equal r 5) (equal r 6) (equal r 7) (equal r 8) (equal r 9)))))

;; ---------------------------------------------------------------------------
;; (2) the first four words: loop1 packs the key bytes.
(defthm nth-of-loop1
  (implies (aes::inp key)
           (and (equal (nth 0 (aes::keyexpansionloop1 0 4 key w))
                       (aes::make-word (nth 0 key) (nth 1 key) (nth 2 key) (nth 3 key)))
                (equal (nth 1 (aes::keyexpansionloop1 0 4 key w))
                       (aes::make-word (nth 4 key) (nth 5 key) (nth 6 key) (nth 7 key)))
                (equal (nth 2 (aes::keyexpansionloop1 0 4 key w))
                       (aes::make-word (nth 8 key) (nth 9 key) (nth 10 key) (nth 11 key)))
                (equal (nth 3 (aes::keyexpansionloop1 0 4 key w))
                       (aes::make-word (nth 12 key) (nth 13 key) (nth 14 key) (nth 15 key)))))
  :hints (("Goal" :do-not-induct t
           :expand ((:free (i w) (aes::keyexpansionloop1 i 4 key w)))
           :in-theory (e/d () (aes::make-word nth-when-zp)))))

;; ---------------------------------------------------------------------------
;; (3) the loop2 characterization.  l2temp is exactly the loop body's temp
;; computation at nk = 4 (the nk > 6 branch is dead).
(defund l2temp (i prev)
  (if (equal (mod i 4) 0)
      (aes::wordxor (aes::subword (aes::rotword prev)) (nth (/ i 4) aes::*rcon*))
    prev))

;; frame: entries below the start index are untouched.
(defthm l2-frame
  (implies (and (integerp i) (natp j) (< j i))
           (equal (nth j (aes::keyexpansionloop2 i 44 4 w)) (nth j w)))
  :hints (("Goal" :induct (aes::keyexpansionloop2 i 44 4 w)
           :in-theory (e/d (aes::keyexpansionloop2)
                           (aes::wordxor aes::subword aes::rotword aes::make-word
                            nth-when-zp)))))

;; the recurrence: every entry at or above the start index is
;; wordxor(entry 4 back, l2temp of the previous entry).
(defthm l2-rec
  (implies (and (integerp i) (<= 4 i) (<= i 44) (natp j) (<= i j) (< j 44))
           (equal (nth j (aes::keyexpansionloop2 i 44 4 w))
                  (aes::wordxor
                    (nth (- j 4) (aes::keyexpansionloop2 i 44 4 w))
                    (l2temp j (nth (+ -1 j) (aes::keyexpansionloop2 i 44 4 w))))))
  :rule-classes nil
  :hints (("Goal" :induct (aes::keyexpansionloop2 i 44 4 w)
           :in-theory (e/d (aes::keyexpansionloop2 l2temp)
                           (aes::wordxor aes::subword aes::rotword aes::make-word
                            nth-when-zp)))))

;; ---------------------------------------------------------------------------
;; (4) word shapes and typing.
(local (defthm u8-nth-all
  (implies (and (acl2::all-unsigned-byte-p 8 l) (natp i) (< i (len l)))
           (unsigned-byte-p 8 (nth i l)))
  :hints (("Goal" :in-theory (enable acl2::all-unsigned-byte-p nth)))))
(local (defthm u8-of-nth-sbox
  (implies (and (natp i) (< i 256))
           (unsigned-byte-p 8 (nth i *sbox*)))
  :hints (("Goal" :use (:instance u8-nth-all (l *sbox*))))))

(local (defthm len-when-wordp
  (implies (acl2::bv-arrayp 8 4 w) (equal (len w) 4))
  :hints (("Goal" :in-theory (enable acl2::bv-arrayp)))))
(local (defthm true-listp-when-wordp
  (implies (acl2::bv-arrayp 8 4 w) (true-listp w))
  :hints (("Goal" :in-theory (enable acl2::bv-arrayp)))))
(local (defthm u8-nth-of-wordp
  (implies (and (acl2::bv-arrayp 8 4 w) (natp k) (< k 4))
           (unsigned-byte-p 8 (nth k w)))
  :hints (("Goal" :in-theory (enable acl2::bv-arrayp)
           :use (:instance u8-nth-all (l w) (i k))))))

;; a length-4 true-list is the explicit list of its elements.
(defthmd expand-len-4
  (implies (and (true-listp x) (equal (len x) 4))
           (equal (list (nth 0 x) (nth 1 x) (nth 2 x) (nth 3 x)) x))
  :hints (("Goal" :in-theory (enable nth)
           :expand ((len x) (len (cdr x)) (len (cdr (cdr x))) (len (cdr (cdr (cdr x))))))))

;; ---------------------------------------------------------------------------
;; (5) STEP, WORDS TO BYTES: one word-level round step, flattened, IS
;; kr-spec-bytes.  Proved over 16 EXPLICIT symbolic bytes (everything computes
;; structurally, no shape splits), then lifted to symbolic words by the
;; expand-len-4 fold -- the project's standard -bytes/-general idiom.
(local (defthm step-bytes-explicit
  (implies (and (unsigned-byte-p 8 a0) (unsigned-byte-p 8 a1) (unsigned-byte-p 8 a2) (unsigned-byte-p 8 a3) (unsigned-byte-p 8 a4) (unsigned-byte-p 8 a5) (unsigned-byte-p 8 a6) (unsigned-byte-p 8 a7) (unsigned-byte-p 8 a8) (unsigned-byte-p 8 a9) (unsigned-byte-p 8 a10) (unsigned-byte-p 8 a11) (unsigned-byte-p 8 a12) (unsigned-byte-p 8 a13) (unsigned-byte-p 8 a14) (unsigned-byte-p 8 a15) (unsigned-byte-p 8 rv))
           (equal (append (aes::wordxor (list a0 a1 a2 a3) (aes::wordxor (aes::subword (aes::rotword (list a12 a13 a14 a15))) (aes::make-word rv 0 0 0)))
                          (aes::wordxor (list a4 a5 a6 a7) (aes::wordxor (list a0 a1 a2 a3) (aes::wordxor (aes::subword (aes::rotword (list a12 a13 a14 a15))) (aes::make-word rv 0 0 0))))
                          (aes::wordxor (list a8 a9 a10 a11) (aes::wordxor (list a4 a5 a6 a7) (aes::wordxor (list a0 a1 a2 a3) (aes::wordxor (aes::subword (aes::rotword (list a12 a13 a14 a15))) (aes::make-word rv 0 0 0)))))
                          (aes::wordxor (list a12 a13 a14 a15) (aes::wordxor (list a8 a9 a10 a11) (aes::wordxor (list a4 a5 a6 a7) (aes::wordxor (list a0 a1 a2 a3) (aes::wordxor (aes::subword (aes::rotword (list a12 a13 a14 a15))) (aes::make-word rv 0 0 0)))))))
                  (kr-spec-bytes (append (list a0 a1 a2 a3) (list a4 a5 a6 a7) (list a8 a9 a10 a11) (list a12 a13 a14 a15)) rv)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (kr-spec-bytes xorw aes::wordxor aes::subword aes::rotword
                            aes::make-word aes::wordbyte0 aes::wordbyte1 aes::wordbyte2 aes::wordbyte3)
                           (nth-when-zp))))))

(defthm step-words-to-bytes
  (implies (and (acl2::bv-arrayp 8 4 w0) (acl2::bv-arrayp 8 4 w1)
                (acl2::bv-arrayp 8 4 w2) (acl2::bv-arrayp 8 4 w3)
                (unsigned-byte-p 8 rv))
           (equal (append (aes::wordxor w0 (aes::wordxor (aes::subword (aes::rotword w3))
                                                         (aes::make-word rv 0 0 0)))
                          (aes::wordxor w1 (aes::wordxor w0 (aes::wordxor (aes::subword (aes::rotword w3))
                                                                          (aes::make-word rv 0 0 0))))
                          (aes::wordxor w2 (aes::wordxor w1 (aes::wordxor w0 (aes::wordxor (aes::subword (aes::rotword w3))
                                                                                           (aes::make-word rv 0 0 0)))))
                          (aes::wordxor w3 (aes::wordxor w2 (aes::wordxor w1 (aes::wordxor w0 (aes::wordxor (aes::subword (aes::rotword w3))
                                                                                                            (aes::make-word rv 0 0 0)))))))
                  (kr-spec-bytes (append w0 w1 w2 w3) rv)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance step-bytes-explicit (a0 (nth 0 w0)) (a1 (nth 1 w0)) (a2 (nth 2 w0)) (a3 (nth 3 w0)) (a4 (nth 0 w1)) (a5 (nth 1 w1)) (a6 (nth 2 w1)) (a7 (nth 3 w1)) (a8 (nth 0 w2)) (a9 (nth 1 w2)) (a10 (nth 2 w2)) (a11 (nth 3 w2)) (a12 (nth 0 w3)) (a13 (nth 1 w3)) (a14 (nth 2 w3)) (a15 (nth 3 w3)))
                 (:instance expand-len-4 (x w0)) (:instance expand-len-4 (x w1)) (:instance expand-len-4 (x w2)) (:instance expand-len-4 (x w3))
                 (:instance len-when-wordp (w w0)) (:instance true-listp-when-wordp (w w0)) (:instance len-when-wordp (w w1)) (:instance true-listp-when-wordp (w w1)) (:instance len-when-wordp (w w2)) (:instance true-listp-when-wordp (w w2)) (:instance len-when-wordp (w w3)) (:instance true-listp-when-wordp (w w3))
                 (:instance u8-nth-of-wordp (w w0) (k 0)) (:instance u8-nth-of-wordp (w w0) (k 1)) (:instance u8-nth-of-wordp (w w0) (k 2)) (:instance u8-nth-of-wordp (w w0) (k 3)) (:instance u8-nth-of-wordp (w w1) (k 0)) (:instance u8-nth-of-wordp (w w1) (k 1)) (:instance u8-nth-of-wordp (w w1) (k 2)) (:instance u8-nth-of-wordp (w w1) (k 3)) (:instance u8-nth-of-wordp (w w2) (k 0)) (:instance u8-nth-of-wordp (w w2) (k 1)) (:instance u8-nth-of-wordp (w w2) (k 2)) (:instance u8-nth-of-wordp (w w2) (k 3)) (:instance u8-nth-of-wordp (w w3) (k 0)) (:instance u8-nth-of-wordp (w w3) (k 1)) (:instance u8-nth-of-wordp (w w3) (k 2)) (:instance u8-nth-of-wordp (w w3) (k 3)))
           :in-theory (union-theories (theory 'ground-zero) '()))))

;; ---------------------------------------------------------------------------
;; (6) shapes of the expansion rows, and the top-level open.
(local (defthm wordp-of-make-word
  (implies (and (unsigned-byte-p 8 b0) (unsigned-byte-p 8 b1)
                (unsigned-byte-p 8 b2) (unsigned-byte-p 8 b3))
           (acl2::bv-arrayp 8 4 (aes::make-word b0 b1 b2 b3)))
  :hints (("Goal" :in-theory (enable aes::make-word acl2::bv-arrayp acl2::all-unsigned-byte-p)))))

(local (defthm wordp-of-nth-rcon
  (implies (and (natp m) (< m 11))
           (acl2::bv-arrayp 8 4 (nth m aes::*rcon*)))
  :hints (("Goal" :cases ((equal m 0) (equal m 1) (equal m 2) (equal m 3) (equal m 4) (equal m 5)
                          (equal m 6) (equal m 7) (equal m 8) (equal m 9) (equal m 10))))))

(defthm keyexpansion-open
  (equal (aes::keyexpansion key 4)
         (aes::keyexpansionloop2 4 44 4
           (aes::keyexpansionloop1 0 4 key (acl2::repeat 44 '(0 0 0 0)))))
  :hints (("Goal" :in-theory (e/d (aes::keyexpansion (:e acl2::repeat)) ()))))

;; every row of the expansion is a word (4 u8s): strong induction with IHs at
;; j-4 and j-1, driven by the l2 recurrence.
(defun row-ind4 (j)
  (declare (xargs :measure (nfix j)))
  (if (< (nfix j) 4) j (list (row-ind4 (- j 4)) (row-ind4 (- j 1)))))

(defthm exp-row-wordp
  (implies (and (aes::inp key) (natp j) (< j 44))
           (acl2::bv-arrayp 8 4 (nth j (aes::keyexpansion key 4))))
  :hints (("Goal" :induct (row-ind4 j)
           :in-theory (e/d (l2temp)
                           (aes::keyexpansion aes::keyexpansionloop2 aes::keyexpansionloop1
                            aes::wordxor aes::subword aes::rotword aes::make-word
                            acl2::bv-arrayp nth-when-zp nth)))
          ("Subgoal *1/2"
           :use ((:instance l2-rec (i 4) (w (aes::keyexpansionloop1 0 4 key (acl2::repeat 44 '(0 0 0 0)))))))
          ("Subgoal *1/1"
           :cases ((equal j 0) (equal j 1) (equal j 2) (equal j 3))
           :in-theory (e/d () (aes::keyexpansionloop2 aes::keyexpansionloop1
                               aes::make-word acl2::bv-arrayp nth-when-zp)))))

;; ---------------------------------------------------------------------------
;; (7) MAIN: the bridge.
(defund kk-of-w (w r)
  (append (nth (* 4 r) w) (nth (+ 1 (* 4 r)) w)
          (nth (+ 2 (* 4 r)) w) (nth (+ 3 (* 4 r)) w)))

(defun br-ind (r) (if (zp r) r (br-ind (1- r))))

(defthm kk-iter-is-keyexpansion
  (implies (and (aes::inp key) (natp r) (<= r 10))
           (equal (kk-of-w (aes::keyexpansion key 4) r)
                  (kk-iter key r)))
  :hints (("Goal" :induct (br-ind r)
           :in-theory (e/d (kk-of-w l2temp kk-iter)
                           (aes::keyexpansion aes::keyexpansionloop2 aes::keyexpansionloop1
                            aes::wordxor aes::subword aes::rotword aes::make-word
                            acl2::bv-arrayp kr-spec-bytes kx nth-when-zp nth
                            step-words-to-bytes)))
          ("Subgoal *1/2"
           :use ((:instance l2-rec (i 4) (j (+ 4 (* 4 (1- r))))
                            (w (aes::keyexpansionloop1 0 4 key (acl2::repeat 44 '(0 0 0 0)))))
                 (:instance l2-rec (i 4) (j (+ 5 (* 4 (1- r))))
                            (w (aes::keyexpansionloop1 0 4 key (acl2::repeat 44 '(0 0 0 0)))))
                 (:instance l2-rec (i 4) (j (+ 6 (* 4 (1- r))))
                            (w (aes::keyexpansionloop1 0 4 key (acl2::repeat 44 '(0 0 0 0)))))
                 (:instance l2-rec (i 4) (j (+ 7 (* 4 (1- r))))
                            (w (aes::keyexpansionloop1 0 4 key (acl2::repeat 44 '(0 0 0 0)))))
                 (:instance rcon-row (r (1- r)))
                 (:instance step-words-to-bytes
                            (w0 (nth (* 4 (1- r)) (aes::keyexpansion key 4)))
                            (w1 (nth (+ 1 (* 4 (1- r))) (aes::keyexpansion key 4)))
                            (w2 (nth (+ 2 (* 4 (1- r))) (aes::keyexpansion key 4)))
                            (w3 (nth (+ 3 (* 4 (1- r))) (aes::keyexpansion key 4)))
                            (rv (kx (1- r))))
                 (:instance exp-row-wordp (j (* 4 (1- r))))
                 (:instance exp-row-wordp (j (+ 1 (* 4 (1- r)))))
                 (:instance exp-row-wordp (j (+ 2 (* 4 (1- r)))))
                 (:instance exp-row-wordp (j (+ 3 (* 4 (1- r)))))
                 (:instance kx-byte (c (1- r)))
                 (:instance kk-iter-step (i (1- r)))))
          ("Subgoal *1/1"
           :in-theory (e/d (kk-of-w kk-iter expand-len-16 aes::make-word)
                           (aes::keyexpansionloop2 aes::keyexpansionloop1
                            acl2::bv-arrayp nth-when-zp nth)))))

; Phase 4 -- key-schedule CORE chaining: the schedule's 10 rcon-loop rounds
; compute Kestrel's key expansion (bitsliced), for ALL inputs.
;
; Strategy (structured rewriting; GL only for the per-round bit cruxes):
;  * Each schedule loop shape (memshift32, xor_columns) is proven equal to an
;    explicit window-update spec (ms/xc-spec) with a read-through (nth-of-*)
;    lemma -- this gives LOCALITY and FRAME for free; w8-spec is the window
;    WRITE spec the subslice vec-update-range borrows bridge to.
;  * One rcon-loop round is then a pure window transform krw8 on
;    rkeys[off..off+8), writing rkeys[off+8..off+16); off-independent (kround,
;    in aes_fixslice_keyround).
;  * The keystep cruxes give krw8(bitslice(b,b),c) = bitslice(kr-spec-bytes(b,
;    xpow c), same); chaining the 10 disjoint windows then yields
;    inv_bitslice(window r) = kk(r) for every round key.
(in-package "ACL2")
(include-book "aes_fixslice_correspondence")
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/update-nth" :dir :system))
(local (include-book "std/lists/nth" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))

;; This proof chain builds on the -gl extraction + centaur/gl (whose `fail`
;; FUNCTION rules out including range_for-proofs, which pulls in the `fail`
;; MACRO from rust-primitives).  rnext-on-range -- what the synthesized range
;; iterator's next does on a concrete range -- is re-derived here directly.
(defmacro rng (i e) `(core-ops-range-range-usize- ,i ,e))
(defmacro rnext (r)
  `(core-iter-range-impl-core-iter-traits-iterator-iterator-for-core-ops-range-range-usize-next-usize-
    ,r))
;; the reversed-range iterator (`for i in (a..b).rev()`, upstream memshift32):
;; `rev` is the identity on the (newtype-erased) range, and its `next` is the
;; reverse advance -- both backend-synthesized when the sysroot has no MIR
;; for them, with identical semantics either way.
(defmacro rrev (r)
  `(core-iter-traits-iterator-iterator-rev-core-ops-range-range-usize- ,r))
(defmacro rvnext (r)
  `(core-iter-adapters-rev-impl-core-iter-traits-iterator-iterator-for-core-iter-adapters-rev-rev-core-ops-range-range-usize-next-core-ops-range-range-usize-
    ,r))
(defthm rev-on-range
  (equal (rrev r) (ok r))
  :hints (("Goal" :in-theory
           (enable core-iter-traits-iterator-iterator-rev-core-ops-range-range-usize-))))
(defthm rvnext-on-range
  (equal (rvnext (rng s e))
         (if (< s e)
             (ok (cons (core-option-option-usize--some (- e 1)) (rng s (- e 1))))
           (ok (cons (core-option-option-usize--none) (rng s e)))))
  :hints (("Goal" :in-theory
           (enable core-iter-adapters-rev-impl-core-iter-traits-iterator-iterator-for-core-iter-adapters-rev-rev-core-ops-range-range-usize-next-core-ops-range-range-usize-))))
(defthm rnext-on-range
  (equal (rnext (rng i e))
         (if (< i e)
             (ok (cons (core-option-option-usize--some i) (rng (+ i 1) e)))
           (ok (cons (core-option-option-usize--none) (rng i e)))))
  :hints (("Goal" :in-theory
           (enable core-iter-range-impl-core-iter-traits-iterator-iterator-for-core-ops-range-range-usize-next-usize-))))
;; NOTE on ranges as constants vs constructors: when a generated body opens
;; in a proof, its (rng s e) literals EVALUATE to quoted alists, which the
;; (rng s e)-patterned loop lemmas cannot match.  Books that reason about an
;; OPEN body at a symbolic offset either disable this executable counterpart
;; locally in the hint, or (better) keep the caller closed and :use the
;; interface equation -- see keyround's kround readers.

;; Fixed shifts (<32) and the rotate never fail -- lets the b* ok-binders in the
;; loop bodies resolve while u32-shl / ror stay opaque to arithmetic-5.
(defthm result-kind-u32-shl-small
  (implies (and (natp n) (< n 32))
           (equal (result-kind (u32-shl x n)) :ok))
  :hints (("Goal" :in-theory (enable u32-shl))))
(defthm result-kind-ror
  (equal (result-kind (aes-fixslice-encrypt-ror x y)) :ok)
  :hints (("Goal" :in-theory (enable aes-fixslice-encrypt-ror u32-rotate-right))))

;; ============================ write8 ============================
(defun w8-spec (i e rkeys off s)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e))
      (w8-spec (+ i 1) e (update-nth (+ off i) (nth i s) rkeys) off s)
    rkeys))
(defthm len-of-w8-spec
  (implies (and (natp i) (natp e) (natp off) (<= (+ off e) (len rkeys)))
           (equal (len (w8-spec i e rkeys off s)) (len rkeys))))
(defthm nth-of-w8-spec
  (implies (and (natp i) (natp e) (natp off) (natp k))
           (equal (nth k (w8-spec i e rkeys off s))
                  (if (and (< i e) (<= (+ off i) k) (< k (+ off e))) (nth (- k off) s) (nth k rkeys)))))
;; ============================ memshift32 ============================
(defun ms-spec (i e buffer src dst)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e))
      (ms-spec (+ i 1) e (update-nth (+ dst i) (nth (+ src i) buffer) buffer) src dst)
    buffer))
(defthm msd-loop0-step-rec
  (implies (and (natp s) (natp e) (< s e) (not (zp n)) (natp src) (natp dst)
                (< (+ src (- e 1)) (len buffer)) (< (+ dst (- e 1)) (len buffer))
                (< (len buffer) 4294967296))
           (equal (aes-fixslice-encrypt-memshift32-loop0 n (rng s e) buffer src dst)
                  (aes-fixslice-encrypt-memshift32-loop0 (1- n) (rng s (- e 1))
                       (update-nth (+ dst (- e 1)) (nth (+ src (- e 1)) buffer) buffer) src dst)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-memshift32-loop0 n (rng s e) buffer src dst))
                  :in-theory (enable rvnext-on-range))))
(defthm msd-loop0-step-base
  (implies (and (natp s) (natp e) (<= e s) (not (zp n)))
           (equal (aes-fixslice-encrypt-memshift32-loop0 n (rng s e) buffer src dst) (ok buffer)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-memshift32-loop0 n (rng s e) buffer src dst))
                  :in-theory (enable rvnext-on-range))))
;; descending accumulator spec matching the loop's write order
(defun ms-spec-d (s e buffer src dst)
  (declare (xargs :measure (nfix (- (nfix e) (nfix s)))))
  (if (and (natp s) (natp e) (< s e))
      (ms-spec-d s (- e 1) (update-nth (+ dst (- e 1)) (nth (+ src (- e 1)) buffer) buffer) src dst)
    buffer))
(defun msd-ind (n s e buffer src dst)
  (declare (xargs :measure (nfix (- (nfix e) (nfix s)))))
  (if (and (natp s) (natp e) (< s e) (not (zp n)))
      (msd-ind (1- n) s (- e 1) (update-nth (+ dst (- e 1)) (nth (+ src (- e 1)) buffer) buffer) src dst)
    (list n s e buffer src dst)))
(defthm ms-loop0-is-msspec-d
  (implies (and (natp s) (natp e) (<= s e) (natp src) (natp dst)
                (<= (+ src e) (len buffer)) (<= (+ dst e) (len buffer))
                (< (len buffer) 4294967296) (< (- e s) (nfix n)))
           (equal (aes-fixslice-encrypt-memshift32-loop0 n (rng s e) buffer src dst)
                  (ok (ms-spec-d s e buffer src dst))))
  :hints (("Goal" :induct (msd-ind n s e buffer src dst)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (e/d (ms-spec-d)
                                  (aes-fixslice-encrypt-memshift32-loop0 rvnext-on-range
                                   (:executable-counterpart core-ops-range-range-usize-))))))
(defthm len-of-ms-spec-d
  (implies (and (natp s) (natp e) (natp dst) (<= (+ dst e) (len buffer)))
           (equal (len (ms-spec-d s e buffer src dst)) (len buffer))))
(defthm true-listp-of-ms-spec-d
  (implies (true-listp buffer) (true-listp (ms-spec-d s e buffer src dst))))
(defthm nth-of-ms-spec-d
  (implies (and (natp s) (natp e) (natp src) (natp dst) (natp k) (<= (+ src e) dst))
           (equal (nth k (ms-spec-d s e buffer src dst))
                  (if (and (< s e) (<= (+ dst s) k) (< k (+ dst e)))
                      (nth (+ src (- k dst)) buffer) (nth k buffer)))))
(defthm len-of-ms-spec
  (implies (and (natp i) (natp e) (natp dst) (<= (+ dst e) (len buffer)))
           (equal (len (ms-spec i e buffer src dst)) (len buffer))))
(defthm true-listp-of-ms-spec
  (implies (true-listp buffer) (true-listp (ms-spec i e buffer src dst))))
(defthm nth-of-ms-spec
  (implies (and (natp i) (natp e) (natp src) (natp dst) (natp k) (<= (+ src e) dst))
           (equal (nth k (ms-spec i e buffer src dst))
                  (if (and (< i e) (<= (+ dst i) k) (< k (+ dst e)))
                      (nth (+ src (- k dst)) buffer) (nth k buffer)))))
(defthm ms-spec-d-is-ms-spec
  (implies (and (natp src) (natp dst) (natp e) (<= (+ src e) dst)
                (<= (+ dst e) (len buffer)) (true-listp buffer))
           (equal (ms-spec-d 0 e buffer src dst) (ms-spec 0 e buffer src dst)))
  :hints ((acl2::equal-by-nths-hint)
          '(:in-theory (e/d (nth-of-ms-spec nth-of-ms-spec-d len-of-ms-spec len-of-ms-spec-d)
                            (ms-spec ms-spec-d nth)))))
;; the interface every later book uses: unchanged right-hand side (the
;; descending write order is invisible -- the windows are disjoint); the one
;; new hypothesis is upstream's own debug_assert (src 8-aligned).
(defthm memshift32-is-msspec
  (implies (and (natp src) (equal (rem src 8) 0)
                (<= (+ src 16) (len buffer)) (< (len buffer) 4294967296)
                (true-listp buffer))
           (equal (aes-fixslice-encrypt-memshift32 100 buffer src)
                  (ok (ms-spec 0 8 buffer src (+ src 8)))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-memshift32)
                                  (aes-fixslice-encrypt-memshift32-loop0 ms-spec ms-spec-d
                                   rev-on-range))
                  :use ((:instance ms-loop0-is-msspec-d (s 0) (e 8) (n 100) (dst (+ src 8)))
                        (:instance ms-spec-d-is-ms-spec (e 8) (dst (+ src 8)))))))

;; ============================ xor_columns ============================
(defun xc-word (left cur dror)
  (b* (((ok v1092) (aes-fixslice-encrypt-ror cur dror))
       (v1093 (u32-and 50529027 v1092))
       (rk (u32-xor left v1093))
       ((ok v1095) (u32-shl rk 2))
       (v1096 (u32-and 4244438268 v1095))
       (v1097 (u32-xor rk v1096))
       ((ok v1098) (u32-shl rk 4))
       (v1099 (u32-and 4042322160 v1098))
       (v1100 (u32-xor v1097 v1099))
       ((ok v1101) (u32-shl rk 6))
       (v1102 (u32-and 3233857728 v1101))
       (v1103 (u32-xor v1100 v1102)))
    v1103))
(defthm xc-loop0-step-rec
  (implies (and (natp i) (natp e) (< i e) (not (zp n)) (natp off) (natp dx)
                (<= dx off) (< (+ off i) (len rkeys)) (< (len rkeys) 4294967296))
           (equal (aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror)
                  (aes-fixslice-encrypt-xor-columns-loop0 (1- n) (rng (+ i 1) e)
                       (update-nth (+ off i)
                                   (xc-word (nth (+ off i (- dx)) rkeys) (nth (+ off i) rkeys) dror)
                                   rkeys) off dx dror)))
  :hints (("Goal" :do-not-induct t :do-not '(eliminate-destructors generalize)
                  :expand ((aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror))
                  :in-theory (e/d (rnext-on-range xc-word result-kind-u32-shl-small result-kind-ror)
                                  (u32-and u32-xor u32-shl u32-or aes-fixslice-encrypt-ror)))))
(defthm xc-loop0-step-base
  (implies (and (natp i) (natp e) (<= e i) (not (zp n)))
           (equal (aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror) (ok rkeys)))
  :hints (("Goal" :expand ((aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror))
                  :in-theory (enable rnext-on-range))))
(defun xc-spec (i e rkeys off dx dror)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e))
      (xc-spec (+ i 1) e
               (update-nth (+ off i)
                           (xc-word (nth (+ off i (- dx)) rkeys) (nth (+ off i) rkeys) dror) rkeys)
               off dx dror)
    rkeys))
(defun xc-ind (n i e rkeys off dx dror)
  (declare (xargs :measure (nfix (- (nfix e) (nfix i)))))
  (if (and (natp i) (natp e) (< i e) (not (zp n)))
      (xc-ind (1- n) (+ i 1) e
              (update-nth (+ off i)
                          (xc-word (nth (+ off i (- dx)) rkeys) (nth (+ off i) rkeys) dror) rkeys)
              off dx dror)
    (list n i e rkeys off dx dror)))
(defthm xc-loop0-is-xcspec
  (implies (and (natp i) (natp e) (<= i e) (natp off) (natp dx) (<= dx off)
                (<= (+ off e) (len rkeys)) (< (len rkeys) 4294967296) (< (- e i) (nfix n)))
           (equal (aes-fixslice-encrypt-xor-columns-loop0 n (rng i e) rkeys off dx dror)
                  (ok (xc-spec i e rkeys off dx dror))))
  :hints (("Goal" :induct (xc-ind n i e rkeys off dx dror)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (e/d (xc-spec)
                                  (aes-fixslice-encrypt-xor-columns-loop0 rnext-on-range xc-word
                                   (:executable-counterpart core-ops-range-range-usize-))))))
(defthm len-of-xc-spec
  (implies (and (natp i) (natp e) (natp off) (<= (+ off e) (len rkeys)))
           (equal (len (xc-spec i e rkeys off dx dror)) (len rkeys)))
  :hints (("Goal" :in-theory (disable xc-word))))
(defthm nth-of-xc-spec
  (implies (and (natp i) (natp e) (natp off) (natp dx) (natp k) (<= e dx) (< 0 off))
           (equal (nth k (xc-spec i e rkeys off dx dror))
                  (if (and (< i e) (<= (+ off i) k) (< k (+ off e)))
                      (xc-word (nth (+ k (- dx)) rkeys) (nth k rkeys) dror) (nth k rkeys))))
  :hints (("Goal" :induct (xc-spec i e rkeys off dx dror)
                  :do-not '(eliminate-destructors generalize)
                  :in-theory (disable xc-word))))
(defthm xor-columns-is-xcspec
  (implies (and (natp off) (natp dx) (<= dx off) (<= (+ off 8) (len rkeys))
                (< (len rkeys) 4294967296))
           (equal (aes-fixslice-encrypt-xor-columns 100 rkeys off dx dror)
                  (ok (xc-spec 0 8 rkeys off dx dror))))
  :hints (("Goal" :in-theory (e/d (aes-fixslice-encrypt-xor-columns)
                                  (aes-fixslice-encrypt-xor-columns-loop0 xc-spec))
                  :use (:instance xc-loop0-is-xcspec (i 0) (e 8) (n 100)))))

;; ============================ read8 ============================
(defun rd8 (rkeys off)
  (list (nth off rkeys) (nth (+ off 1) rkeys) (nth (+ off 2) rkeys) (nth (+ off 3) rkeys)
        (nth (+ off 4) rkeys) (nth (+ off 5) rkeys) (nth (+ off 6) rkeys) (nth (+ off 7) rkeys)))
;; ---- window bridges: the schedule's subslice borrows read and write
;; exactly the rd8 / w8-spec windows the Phase-4 proofs are stated over ----
(defthm true-listp-of-w8-spec
  (implies (true-listp rkeys) (true-listp (w8-spec i e rkeys off s))))
(defthm len-of-rd8-8 (equal (len (rd8 l off)) 8) :hints (("Goal" :in-theory (enable rd8))))
(defthm true-listp-of-rd8 (true-listp (rd8 l off)) :hints (("Goal" :in-theory (enable rd8))))
(defthm nth-of-rd8
  (implies (and (natp n) (< n 8)) (equal (nth n (rd8 l off)) (nth (+ off n) l)))
  :hints (("Goal" :in-theory (enable rd8)
           :cases ((equal n 0) (equal n 1) (equal n 2) (equal n 3)
                   (equal n 4) (equal n 5) (equal n 6) (equal n 7)))))
(defthm take8-nthcdr-is-rd8-k
  (implies (and (natp off) (<= (+ off 8) (len rk)) (true-listp rk))
           (equal (take 8 (nthcdr off rk)) (rd8 rk off)))
  :hints ((acl2::equal-by-nths-hint)
          '(:in-theory (e/d () (rd8 nth take nthcdr)))))
;; NB on rule shape: a (+ off 8) INSIDE a rule's left-hand side never matches
;; goal terms -- ACL2 normalizes sums constant-first ((+ 8 off)) and literal
;; windows compute ((vec-index-range rk 72 80)), and one-way unification is
;; purely syntactic.  So the window bridges bind the upper bound as a FREE
;; variable and pin it with an (equal hi (+ off 8)) hypothesis, which rewriting
;; discharges in every form (symbolic sums by arithmetic, literals by
;; evaluation).  The -k versions below are the fixed-shape originals the
;; generalized rules are derived from.
(defthm rk-of-window8-k
  (implies (and (natp off) (<= (+ off 8) (len rk)))
           (equal (result-kind (vec-index-range rk off (+ off 8))) :ok)))
(defthm val-of-window8-k
  (implies (and (natp off) (<= (+ off 8) (len rk)) (true-listp rk))
           (equal (result-ok->val (vec-index-range rk off (+ off 8)))
                  (rd8 rk off)))
  :hints (("Goal" :in-theory (e/d () (rd8 nth))
           :use ((:instance take8-nthcdr-is-rd8-k)))))
(defthm vur8-is-w8spec-k
  (implies (and (natp off) (<= (+ off 8) (len rk)) (true-listp rk)
                (true-listp s) (equal (len s) 8))
           (equal (vec-update-range rk off (+ off 8) s)
                  (w8-spec 0 8 rk off s)))
  :hints ((acl2::equal-by-nths-hint)
          '(:in-theory (e/d () (w8-spec vec-update-range nth)))))
(defthm rk-of-window8
  (implies (and (natp off) (equal hi (+ off 8)) (<= hi (len rk)))
           (equal (result-kind (vec-index-range rk off hi)) :ok))
  :hints (("Goal" :use rk-of-window8-k
           :in-theory (disable rk-of-window8-k vec-index-range))))
(defthm val-of-window8
  (implies (and (natp off) (equal hi (+ off 8)) (<= hi (len rk)) (true-listp rk))
           (equal (result-ok->val (vec-index-range rk off hi)) (rd8 rk off)))
  :hints (("Goal" :use val-of-window8-k
           :in-theory (disable val-of-window8-k vec-index-range rd8 nth))))
(defthm vur8-is-w8spec
  (implies (and (natp off) (equal hi (+ off 8)) (<= hi (len rk)) (true-listp rk)
                (true-listp s) (equal (len s) 8))
           (equal (vec-update-range rk off hi s) (w8-spec 0 8 rk off s)))
  :hints (("Goal" :use vur8-is-w8spec-k
           :in-theory (disable vur8-is-w8spec-k vec-update-range w8-spec nth))))

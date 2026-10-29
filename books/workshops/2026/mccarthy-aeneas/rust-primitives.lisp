; Stage 0 prototype of the Aeneas ACL2 primitives book.
; Mirrors backends/coq/Primitives.v: error = Failure | OutOfFuel;
; result a = Ok a | Fail error.  FTY style per design decision.
; Scope: only what the hand-translated demo/loops examples need.

(in-package "ACL2")

(include-book "centaur/fty/top" :dir :system)
(include-book "std/util/bstar" :dir :system)
(local (include-book "arithmetic-5/top" :dir :system))
(local (include-book "std/lists/take" :dir :system))
(local (include-book "std/lists/nthcdr" :dir :system))
(local (include-book "std/lists/append" :dir :system))
(local (include-book "std/lists/nth" :dir :system))

;; ---------------------------------------------------------------- errors

(fty::deftagsum rust-error
  (:failure ())
  (:out-of-fuel ()))

(defmacro err-failure () '(rust-error-failure))
(defmacro err-out-of-fuel () '(rust-error-out-of-fuel))

;; ---------------------------------------------------------------- result
;; Untyped payload (any-p): one result type serves every Rust type.

(fty::deftagsum result
  (:ok ((val any-p)))
  (:fail ((err rust-error-p))))

(defmacro ok (x) `(result-ok ,x))

;; Monadic bind as a b* binder:  (b* (((ok x) (u32-add a b))) ...)
;; short-circuits on :fail, binding the payload otherwise.

(def-b*-binder ok
  :decls ((declare (xargs :guard t)))
  :body
  `(b* ((patbind-ok-tmp-do-not-use ,(car forms)))
     (if (eq (result-kind patbind-ok-tmp-do-not-use) :ok)
         (b* ((,(car args) (result-ok->val patbind-ok-tmp-do-not-use)))
           ,rest-expr)
       patbind-ok-tmp-do-not-use)))

;; ---------------------------------------------------------------- integers
;; Checked machine-integer ops.  Uniform pattern: compute in Z, return
;; (ok r) iff r is in range, else (result-fail (err-failure)) -- matching
;; Aeneas's panic-on-overflow semantics.  Division/remainder use
;; truncate/rem (Rust rounds toward zero), never floor/mod.

(defconst *u32-max* (1- (expt 2 32)))
(defconst *i32-min* (- (expt 2 31)))
(defconst *i32-max* (1- (expt 2 31)))

(defun u32p (x)
  (declare (xargs :guard t))
  (and (natp x) (<= x *u32-max*)))

(defun i32p (x)
  (declare (xargs :guard t))
  (and (integerp x) (<= *i32-min* x) (<= x *i32-max*)))

(defun u32-add (x y)
  (let ((r (+ x y))) (if (u32p r) (ok r) (result-fail (err-failure)))))

(defun u32-sub (x y)
  (let ((r (- x y))) (if (u32p r) (ok r) (result-fail (err-failure)))))

(defun u32-mul (x y)
  (let ((r (* x y))) (if (u32p r) (ok r) (result-fail (err-failure)))))

(defun u32-div (x y)
  (if (eql y 0)
      (result-fail (err-failure))
    (let ((r (truncate x y))) (if (u32p r) (ok r) (result-fail (err-failure))))))

(defun u32-rem (x y)
  (if (eql y 0)
      (result-fail (err-failure))
    (let ((r (rem x y))) (if (u32p r) (ok r) (result-fail (err-failure))))))

(defun i32-add (x y)
  (let ((r (+ x y))) (if (i32p r) (ok r) (result-fail (err-failure)))))

(defun i32-sub (x y)
  (let ((r (- x y))) (if (i32p r) (ok r) (result-fail (err-failure)))))

;; i32::MIN / -1 overflows: captured uniformly by the range check on r.
(defun i32-div (x y)
  (if (eql y 0)
      (result-fail (err-failure))
    (let ((r (truncate x y))) (if (i32p r) (ok r) (result-fail (err-failure))))))

;; Casts for the hand-written u32/i32 (the macro supplies the rest).
;; Rust `as` between integer types TRUNCATES (two's-complement wrap); it
;; never fails.  (This deliberately diverges from the checked mk_scalar
;; model: `as` is total in Rust -- de-vendoring roadmap item 5.)
(defun u32-cast (x) (ok (mod (ifix x) 4294967296)))
(defun u32-cast-bool (x) (ok (if x 1 0)))
(defun i32-cast (x)
  (let ((r (mod (ifix x) 4294967296)))
    (ok (if (> r 2147483647) (- r 4294967296) r))))
(defun i32-cast-bool (x) (ok (if x 1 0)))
(defthm u32-cast-rk (equal (result-kind (u32-cast x)) :ok))
(defthm u32-cast-range (u32p (result-ok->val (u32-cast x))))
(defthm u32-cast-ok (implies (u32p x) (equal (u32-cast x) (ok x))))
(defthm i32-cast-rk (equal (result-kind (i32-cast x)) :ok))
(defthm i32-cast-range (i32p (result-ok->val (i32-cast x))))
(defthm i32-cast-ok (implies (i32p x) (equal (i32-cast x) (ok x))))
;; casts stay DISABLED: total truncating definitions would otherwise open on
;; symbolic arguments and spill mod/ifix arithmetic into every goal (ground
;; calls still compute via the executable counterparts; the -rk/-range/-ok
;; rules above are the reasoning interface).
(in-theory (disable u32-cast i32-cast))

;; --------------------------------------------- LE bytes (roadmap item 6)
;; u32::from_le_bytes / to_le_bytes (total; bytes little-endian first) and
;; <[T]>::copy_from_slice (panics -- fails -- unless the lengths agree;
;; the value is then just the source window).
;; logior/ash (not +/*): identical on byte inputs, and BDD-friendly -- the
;; GL cruxes bit-blast these through the whole cipher, and adders with
;; carries blow the node count where disjoint ORs are free.
(defun u32-from-le-bytes (bs)
  (logior (nth 0 bs) (ash (nth 1 bs) 8)
          (ash (nth 2 bs) 16) (ash (nth 3 bs) 24)))
(defun u32-to-le-bytes (w)
  (list (logand w 255) (logand (ash w -8) 255)
        (logand (ash w -16) 255) (logand (ash w -24) 255)))
(defun slice-copy-from-slice (self src)
  (if (equal (len self) (len src))
      (ok src)
    (result-fail (err-failure))))
(defthm len-of-u32-to-le-bytes
  (equal (len (u32-to-le-bytes w)) 4))
(defthm true-listp-of-u32-to-le-bytes
  (true-listp (u32-to-le-bytes w)))
(defthm rk-of-slice-copy-from-slice
  (implies (equal (len self) (len src))
           (equal (slice-copy-from-slice self src) (ok src))))

;; result-kind of the constructors, as rewrite rules (fty's own :kind
;; machinery does not export these in a form the rewriter picks up).
(defthm result-kind-of-result-ok (equal (result-kind (result-ok x)) :ok))
(defthm result-kind-of-result-fail
  (equal (result-kind (result-fail e)) :fail))

;; ---------------------------------------------------------------- misc
;; Rust unit value, and Aeneas's massert (used by extracted unit tests).

(defmacro unit () :unit)

(defun massert (b)
  (if b (ok (unit)) (result-fail (err-failure))))

;; ---------------------------------------------------- all integer types
;; Macro-generated recognizers and checked ops for the remaining Rust
;; integer types (u32/i32 above are hand-written and used by the earliest
;; proofs). usize/isize are modeled as 64-bit here; upstream Aeneas
;; currently pins usize to 32 bits in the F* primitives with a TODO --
;; revisit for consistency once upstream decides (plan section 5.4).

(defmacro def-rust-int-type (name min max)
  (let* ((s (symbol-name name)))
    (let ((pred (intern$ (concatenate 'string s "P") "ACL2"))
          (add (intern$ (concatenate 'string s "-ADD") "ACL2"))
          (sub (intern$ (concatenate 'string s "-SUB") "ACL2"))
          (mul (intern$ (concatenate 'string s "-MUL") "ACL2"))
          (dv (intern$ (concatenate 'string s "-DIV") "ACL2"))
          (rm (intern$ (concatenate 'string s "-REM") "ACL2"))
          (cast (intern$ (concatenate 'string s "-CAST") "ACL2"))
          (castb (intern$ (concatenate 'string s "-CAST-BOOL") "ACL2"))
          (add-ok (intern$ (concatenate 'string s "-ADD-OK") "ACL2"))
          (add-fail (intern$ (concatenate 'string s "-ADD-FAIL") "ACL2"))
          (sub-ok (intern$ (concatenate 'string s "-SUB-OK") "ACL2"))
          (sub-fail (intern$ (concatenate 'string s "-SUB-FAIL") "ACL2"))
          (mul-ok (intern$ (concatenate 'string s "-MUL-OK") "ACL2"))
          (cast-ok (intern$ (concatenate 'string s "-CAST-OK") "ACL2"))
          (cast-rk (intern$ (concatenate 'string s "-CAST-RK") "ACL2"))
          (cast-range (intern$ (concatenate 'string s "-CAST-RANGE") "ACL2")))
      `(progn
         (defun ,pred (x)
           (declare (xargs :guard t))
           (and (integerp x) (<= ,min x) (<= x ,max)))
         (defun ,add (x y)
           (let ((r (+ x y))) (if (,pred r) (ok r) (result-fail (err-failure)))))
         (defun ,sub (x y)
           (let ((r (- x y))) (if (,pred r) (ok r) (result-fail (err-failure)))))
         (defun ,mul (x y)
           (let ((r (* x y))) (if (,pred r) (ok r) (result-fail (err-failure)))))
         (defun ,dv (x y)
           (if (eql y 0) (result-fail (err-failure))
             (let ((r (truncate x y)))
               (if (,pred r) (ok r) (result-fail (err-failure))))))
         (defun ,rm (x y)
           (if (eql y 0) (result-fail (err-failure))
             (let ((r (rem x y)))
               (if (,pred r) (ok r) (result-fail (err-failure))))))
         ;; `x as <name>`: Rust `as` TRUNCATES (two's-complement wrap
         ;; into [min,max]); it is total and never fails (roadmap item 5).
         (defun ,cast (x)
           (let ((r (mod (ifix x) ,(+ 1 (- max min)))))
             (ok (if (> r ,max) (- r ,(+ 1 (- max min))) r))))
         ;; `b as <name>` for a bool b: mk_scalar name (if b 1 0); 0 and 1
         ;; are in range for every integer type, so it never fails.
         (defun ,castb (x) (ok (if x 1 0)))
         (defthm ,add-ok
           (implies (and (,pred x) (,pred y) (,pred (+ x y)))
                    (equal (,add x y) (ok (+ x y)))))
         (defthm ,add-fail
           (implies (and (,pred x) (,pred y) (not (,pred (+ x y))))
                    (equal (,add x y) (result-fail (err-failure)))))
         (defthm ,sub-ok
           (implies (and (,pred x) (,pred y) (,pred (- x y)))
                    (equal (,sub x y) (ok (- x y)))))
         (defthm ,sub-fail
           (implies (and (,pred x) (,pred y) (not (,pred (- x y))))
                    (equal (,sub x y) (result-fail (err-failure)))))
         (defthm ,mul-ok
           (implies (and (,pred x) (,pred y) (,pred (* x y)))
                    (equal (,mul x y) (ok (* x y)))))
         ;; Widening / in-range cast is the identity (the AES S-box index
         ;; case: a byte cast to usize); truncation is total and lands in
         ;; range.  All three fire without opening the cast definition.
         (defthm ,cast-ok
           (implies (,pred x) (equal (,cast x) (ok x))))
         (defthm ,cast-rk (equal (result-kind (,cast x)) :ok))
         (defthm ,cast-range (,pred (result-ok->val (,cast x))))
         ;; keep the truncating definition closed (see the u32-cast note)
         (in-theory (disable ,cast))))))

;; Bitwise, shift and wrapping ops for UNSIGNED Rust integer types.
;; - xor/and/or: total, plain value (bit width preserved).
;; - shl/shr: return result -- Rust panics if the shift amount is >= the
;;   bit width; the value shift itself is modulo 2^width (shl) or a
;;   logical right shift (shr, valid since the value is non-negative).
;; - wrapping_{add,sub,mul}: total, result-wrapped to match how Aeneas
;;   models the std methods (monadic, but never actually fail).
(defmacro def-rust-uint-bitops (name width)
  (let* ((s (symbol-name name))
         (m `(expt 2 ,width)))
    (let ((xor (intern$ (concatenate 'string s "-XOR") "ACL2"))
          (band (intern$ (concatenate 'string s "-AND") "ACL2"))
          (bor (intern$ (concatenate 'string s "-OR") "ACL2"))
          (shl (intern$ (concatenate 'string s "-SHL") "ACL2"))
          (shr (intern$ (concatenate 'string s "-SHR") "ACL2"))
          (wadd (intern$ (concatenate 'string s "-WRAPPING-ADD") "ACL2"))
          (wsub (intern$ (concatenate 'string s "-WRAPPING-SUB") "ACL2"))
          (wmul (intern$ (concatenate 'string s "-WRAPPING-MUL") "ACL2")))
      `(progn
         (defun ,xor (x y) (logxor x y))
         (defun ,band (x y) (logand x y))
         (defun ,bor (x y) (logior x y))
         (defun ,shl (x n)
           (if (< (nfix n) ,width)
               (ok (mod (ash x (nfix n)) ,m))
             (result-fail (err-failure))))
         (defun ,shr (x n)
           (if (< (nfix n) ,width)
               (ok (ash x (- (nfix n))))
             (result-fail (err-failure))))
         (defun ,wadd (x y) (ok (mod (+ x y) ,m)))
         (defun ,wsub (x y) (ok (mod (- x y) ,m)))
         (defun ,wmul (x y) (ok (mod (* x y) ,m)))))))

;; rotate_left / rotate_right (the AES key-schedule RotWord, and rotations
;; in several ciphers). Total -- they never panic -- but Aeneas models the
;; core::num methods monadically, so like the wrapping ops we return (ok).
;; rotate_left(x,n) = ((x << k) | (x >> (w-k))) mod 2^w, with k = n mod w;
;; rotate_right is the mirror. ACL2's ash is a total arithmetic shift, so
;; the (w-k) right shift needs no undefined-behavior special-casing at k=0.
(defmacro def-rust-uint-rotate (name width)
  (let* ((s (symbol-name name))
         (m `(expt 2 ,width)))
    (let ((rotl (intern$ (concatenate 'string s "-ROTATE-LEFT") "ACL2"))
          (rotr (intern$ (concatenate 'string s "-ROTATE-RIGHT") "ACL2")))
      `(progn
         (defun ,rotl (x n)
           (let ((k (mod (nfix n) ,width)))
             (ok (mod (logior (ash x k) (ash x (- k ,width))) ,m))))
         (defun ,rotr (x n)
           (let ((k (mod (nfix n) ,width)))
             (ok (mod (logior (ash x (- k)) (ash x (- ,width k))) ,m))))))))


(def-rust-int-type u8 0 255)
(def-rust-int-type u16 0 65535)
(def-rust-int-type u64 0 18446744073709551615)
(def-rust-int-type u128 0 340282366920938463463374607431768211455)
(def-rust-int-type usize 0 18446744073709551615)
(def-rust-int-type i8 -128 127)
(def-rust-int-type i16 -32768 32767)
(def-rust-int-type i64 -9223372036854775808 9223372036854775807)
(def-rust-int-type i128 -170141183460469231731687303715884105728
                        170141183460469231731687303715884105727)
(def-rust-int-type isize -9223372036854775808 9223372036854775807)

(def-rust-uint-bitops u8 8)
(def-rust-uint-bitops u16 16)
(def-rust-uint-bitops u32 32)
(def-rust-uint-bitops u64 64)
(def-rust-uint-bitops u128 128)
(def-rust-uint-bitops usize 64)

(def-rust-uint-rotate u8 8)
(def-rust-uint-rotate u16 16)
(def-rust-uint-rotate u32 32)
(def-rust-uint-rotate u64 64)
(def-rust-uint-rotate u128 128)
(def-rust-uint-rotate usize 64)

;; ---------------------------------------------------------------- arrays
;; Rust arrays [T; N] and slices &[T] are both modeled as true lists (the
;; same representation Kestrel bv-arrays use). Indexing/updating is
;; bounds-checked and returns a result; conversions between arrays and
;; slices are the identity. usize bounds are implicitly respected because
;; list lengths are.

(defun array-index (a i)
  (if (and (natp i) (< i (len a)))
      (ok (nth i a))
    (result-fail (err-failure))))

(defun array-update (a i v)
  (if (and (natp i) (< i (len a)))
      (ok (update-nth i v a))
    (result-fail (err-failure))))

(defun array-len (a) (len a))

(defun array-repeat (n x)
  (if (zp n) nil (cons x (array-repeat (1- n) x))))

;; Subslice [i..j) of a list, shared form.
(defun array-subslice (a i j)
  (if (and (natp i) (natp j) (<= i j) (<= j (len a)))
      (ok (nthcdr i (take j a)))
    (result-fail (err-failure))))

;; ------------------------------------------- subslice borrows (roadmap #7)
;; a[lo..hi] -- the bounds-checked window read every Index/IndexMut<RangeX>
;; instance synthesizes to (RangeTo/RangeFrom default the missing bound to
;; 0 / (len a) at the printer level).
(defun vec-index-range (v lo hi)
  (if (and (natp lo) (natp hi) (<= lo hi) (<= hi (len v)))
      (ok (take (- hi lo) (nthcdr lo v)))
    (result-fail (err-failure))))
;; The backward function of &mut a[lo..hi]: splice the updated window back.
;; TOTAL -- Aeneas backward functions are pure (the forward read already
;; performed the bounds check on the ok path where this is applied).
(defun vec-update-range (v lo hi sub)
  (append (take lo v) sub (nthcdr hi v)))

;; interface rules (the window-spec bridge the proofs use)
(defthm rk-of-vec-index-range
  (implies (and (natp lo) (natp hi) (<= lo hi) (<= hi (len v)))
           (equal (result-kind (vec-index-range v lo hi)) :ok)))
(defthm val-of-vec-index-range
  (implies (and (natp lo) (natp hi) (<= lo hi) (<= hi (len v)))
           (equal (result-ok->val (vec-index-range v lo hi))
                  (take (- hi lo) (nthcdr lo v)))))
(defthm vec-index-range-oob
  (implies (not (and (natp lo) (natp hi) (<= lo hi) (<= hi (len v))))
           (equal (vec-index-range v lo hi) (result-fail (err-failure)))))
(defthm len-of-vec-index-range-val
  (implies (and (natp lo) (natp hi) (<= lo hi) (<= hi (len v)))
           (equal (len (result-ok->val (vec-index-range v lo hi))) (- hi lo))))
(defthm true-listp-of-vec-index-range-val
  (true-listp (result-ok->val (vec-index-range v lo hi))))
(defthm len-of-vec-update-range
  (implies (and (natp lo) (natp hi) (<= lo hi) (<= hi (len v))
                (equal (len sub) (- hi lo)))
           (equal (len (vec-update-range v lo hi sub)) (len v))))
(defthm true-listp-of-vec-update-range
  (implies (and (true-listp v) (true-listp sub))
           (true-listp (vec-update-range v lo hi sub))))
(defthm nth-of-vec-index-range-val
  (implies (and (natp lo) (natp hi) (<= lo hi) (<= hi (len v)) (natp k)
                (< k (- hi lo)))
           (equal (nth k (result-ok->val (vec-index-range v lo hi)))
                  (nth (+ lo k) v))))
(defthm nth-of-vec-update-range
  (implies (and (natp lo) (natp hi) (<= lo hi) (<= hi (len v))
                (equal (len sub) (- hi lo)) (natp k) (< k (len v)))
           (equal (nth k (vec-update-range v lo hi sub))
                  (cond ((< k lo) (nth k v))
                        ((< k hi) (nth (- k lo) sub))
                        (t (nth k v))))))

;; A few rules the proofs want.
(defthm array-index-ok
  (implies (and (natp i) (< i (len a)))
           (equal (array-index a i) (ok (nth i a)))))

(defthm array-index-oob
  (implies (not (and (natp i) (< i (len a))))
           (equal (array-index a i) (result-fail (err-failure)))))

(defthm array-update-ok
  (implies (and (natp i) (< i (len a)))
           (equal (array-update a i v) (ok (update-nth i v a)))))

(defthm len-of-array-repeat
  (equal (len (array-repeat n x)) (nfix n)))

;; ------------------------------------------------------------------ Vec
;; Rust Vec<T> is a growable array, modeled (like arrays/slices) as a list.
;; push/insert take &mut self, so Aeneas returns the updated vector; new
;; and len cannot fail. Requires the crate extracted with --monomorphize.

(defun vec-new () (ok nil))
(defun vec-len (v) (ok (len v)))
(defun vec-push (v x) (ok (append v (list x))))
(defun vec-insert (v i x)
  (if (and (natp i) (<= i (len v)))
      (ok (append (take i v) (cons x (nthcdr i v))))
    (result-fail (err-failure))))

(defthm len-of-vec-push
  (equal (len (result-ok->val (vec-push v x))) (+ 1 (len v))))

(defthm true-listp-of-vec-push
  (implies (true-listp v) (true-listp (result-ok->val (vec-push v x)))))

;; ------------------------------------------------- characterization rules
;; The seed of the Stage-1 rule library: rewrite checked ops to ok/fail
;; under arithmetic side conditions, so proofs about extracted code never
;; open the op definitions.

(defthm u32-add-ok
  (implies (and (u32p x) (u32p y) (<= (+ x y) *u32-max*))
           (equal (u32-add x y) (ok (+ x y)))))

(defthm u32-add-overflow
  (implies (and (u32p x) (u32p y) (> (+ x y) *u32-max*))
           (equal (u32-add x y) (result-fail (err-failure)))))

(defthm u32-sub-ok
  (implies (and (u32p x) (u32p y) (<= y x))
           (equal (u32-sub x y) (ok (- x y)))))

(defthm u32-sub-underflow
  (implies (and (u32p x) (u32p y) (< x y))
           (equal (u32-sub x y) (result-fail (err-failure)))))

(defthm u32-mul-ok
  (implies (and (u32p x) (u32p y) (<= (* x y) *u32-max*))
           (equal (u32-mul x y) (ok (* x y)))))

(defthm i32-add-ok
  (implies (and (i32p x) (i32p y) (<= *i32-min* (+ x y)) (<= (+ x y) *i32-max*))
           (equal (i32-add x y) (ok (+ x y)))))

(defthm i32-sub-ok
  (implies (and (i32p x) (i32p y) (<= *i32-min* (- x y)) (<= (- x y) *i32-max*))
           (equal (i32-sub x y) (ok (- x y)))))

(defthm u32-cast-ok
  (implies (u32p x) (equal (u32-cast x) (ok x))))

(defthm i32-cast-ok
  (implies (i32p x) (equal (i32-cast x) (ok x))))

;; Sanity checks (concrete execution, incl. panic edges).
(assert-event (equal (u32-add 1 2) (ok 3)))
(assert-event (equal (u32-add *u32-max* 1) (result-fail (err-failure))))
(assert-event (equal (u32-sub 0 1) (result-fail (err-failure))))
(assert-event (equal (u32-div 7 2) (ok 3)))
(assert-event (equal (u32-rem 7 2) (ok 1)))
(assert-event (equal (u32-div 7 0) (result-fail (err-failure))))
(assert-event (equal (i32-div -7 2) (ok -3)))     ; truncation toward zero
(assert-event (equal (i32-div *i32-min* -1) (result-fail (err-failure)))) ; MIN / -1
;; Casts: Rust `as` truncates (two's-complement wrap) and never fails.
(assert-event (equal (usize-cast 200) (ok 200)))        ; u8 value as usize
(assert-event (equal (u8-cast 300) (ok 44)))            ; 300 as u8 = 300 mod 256
(assert-event (equal (u8-cast 255) (ok 255)))
(assert-event (equal (u32-cast 7) (ok 7)))
(assert-event (equal (i8-cast 255) (ok -1)))            ; 255u8 as i8 = -1
(assert-event (equal (u8-cast -1) (ok 255)))            ; -1i32 as u8 = 255
(assert-event (equal (i8-cast 128) (ok -128)))          ; 128 as i8 wraps
(assert-event (equal (u32-cast -1) (ok 4294967295)))    ; -1i32 as u32
(assert-event (equal (u8-cast-bool t) (ok 1)))
(assert-event (equal (u8-cast-bool nil) (ok 0)))
;; Rotations (RotWord and friends): wrap-around at the word boundary.
(assert-event (equal (u32-rotate-left 1 1) (ok 2)))
(assert-event (equal (u32-rotate-left #x80000000 1) (ok 1)))
(assert-event (equal (u32-rotate-right 1 1) (ok #x80000000)))
(assert-event (equal (u32-rotate-left 7 0) (ok 7)))
(assert-event (equal (u8-rotate-left #x80 1) (ok 1)))

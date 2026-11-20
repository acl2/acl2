; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "../interp")
(include-book "factorial") ; for the body-building macros

; Hand-written MIR bodies exercising, one at a time,
; the constructs that the AES workload needs
; beyond the factorial core:
; constant arrays, integer-to-integer casts, array indexing,
; references (same-frame and cross-frame, reads and writes),
; unsizing coercions and pointer metadata (slice lengths),
; array repetition,
; and enum construction/discriminant/downcast reads.
; Each body is run through the interpreter
; with known-answer assertions.

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro u32 ()
  '(ty-uint (uint-type-u32)))

(defmacro usize ()
  '(ty-uint (uint-type-usize)))

(defmacro const-u32 (n)
  `(operand-constant (const-uint ,n (uint-type-u32))))

(defmacro const-usize (n)
  `(operand-constant (const-uint ,n (uint-type-usize))))

(defmacro local-place (n &rest projection)
  `(make-place :local ,n :projection (list ,@projection)))

(define run-u64-fn ((name acl2::stringp)
                    (args value-listp)
                    (program mir-programp))
  :returns (out runoutp)
  (run-fn name args program 100000))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Probe 1: constant array + int-to-int cast + variable indexing --
; the S-box lookup shape:
;
;   fn sbox(i: u8) -> u32 { TABLE[i as usize] }
;
; Locals: _0: u32 (return), _1: u8 (i), _2: usize (i as usize),
;         _3: [u32; 4] (the table).

(defconst *sbox-body*
  (make-body
   :locals (list (u32)
                 (ty-uint (uint-type-u8))
                 (usize)
                 (ty-array (u32) 4))
   :arg-count 1
   :blocks
   (list
    (make-basic-block
     :statements
     (list (assign-local 3
                         (rvalue-use
                          (operand-constant
                           (const-array
                            (list (const-uint 10 (uint-type-u32))
                                  (const-uint 20 (uint-type-u32))
                                  (const-uint 30 (uint-type-u32))
                                  (const-uint 40 (uint-type-u32)))))))
           (assign-local 2
                         (rvalue-cast (cast-kind-int-to-int)
                                      (copy-local 1)
                                      (usize)))
           (assign-local 0
                         (rvalue-use
                          (operand-copy
                           (local-place 3 (proj-elem-index 2))))))
     :terminator (terminator-return)))))

(defconst *sbox-program*
  (make-mir-program :funs (omap::update "sbox" *sbox-body* nil)
                    :adts nil))

(assert-event (mir-programp *sbox-program*))

(assert-event
 (equal (run-u64-fn "sbox"
                    (list (value-uint 2 (uint-type-u8)))
                    *sbox-program*)
        (runout-done (value-uint 30 (uint-type-u32)))))

(assert-event
 (equal (run-u64-fn "sbox"
                    (list (value-uint 0 (uint-type-u8)))
                    *sbox-program*)
        (runout-done (value-uint 10 (uint-type-u32)))))

; An out-of-bounds index projection is undefined behavior
; (in real rustc output, a bounds-check assert precedes it).

(assert-event
 (equal (runout-kind (run-u64-fn "sbox"
                                 (list (value-uint 9 (uint-type-u8)))
                                 *sbox-program*))
        :ub))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Probe 2: same-frame reference, write through a dereference:
;
;   fn deref42() -> u64 { let mut x = 1; let r = &mut x; *r = 42; x }
;
; Locals: _0: u64 (return), _1: u64 (x), _2: &mut u64 (r).

(defconst *deref42-body*
  (make-body
   :locals (list (u64)
                 (u64)
                 (ty-ref (mutability-mut) (u64)))
   :arg-count 0
   :blocks
   (list
    (make-basic-block
     :statements
     (list (assign-local 1 (rvalue-use (const-u64 1)))
           (assign-local 2 (rvalue-ref (mutability-mut) (local-place 1)))
           (statement-assign (local-place 2 (proj-elem-deref))
                             (rvalue-use (const-u64 42)))
           (assign-local 0 (rvalue-use (copy-local 1))))
     :terminator (terminator-return)))))

(defconst *deref42-program*
  (make-mir-program :funs (omap::update "deref42" *deref42-body* nil)
                    :adts nil))

(assert-event
 (equal (run-u64-fn "deref42" nil *deref42-program*)
        (runout-done (value-uint 42 (uint-type-u64)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Probe 3: cross-frame reference -- the argument-passing shape:
;
;   fn add41(r: &mut u64) { *r = *r + 41; }
;   fn main41() -> u64 { let mut x = 1; add41(&mut x); x }
;
; The callee writes through a reference into the caller's frame.

(defconst *add41-body*
  (make-body
   :locals (list (ty-tuple nil)
                 (ty-ref (mutability-mut) (u64)))
   :arg-count 1
   :blocks
   (list
    (make-basic-block
     :statements
     (list (statement-assign
            (local-place 1 (proj-elem-deref))
            (rvalue-binary-op
             (bin-op-add)
             (operand-copy (local-place 1 (proj-elem-deref)))
             (const-u64 41)))
           (assign-local 0 (rvalue-use (operand-constant (const-unit)))))
     :terminator (terminator-return)))))

(defconst *main41-body*
  (make-body
   :locals (list (u64)
                 (u64)
                 (ty-ref (mutability-mut) (u64))
                 (ty-tuple nil))
   :arg-count 0
   :blocks
   (list
    (make-basic-block
     :statements
     (list (assign-local 1 (rvalue-use (const-u64 1)))
           (assign-local 2 (rvalue-ref (mutability-mut) (local-place 1))))
     :terminator (terminator-call
                  (operand-constant (const-fn "add41"))
                  (list (move-local 2))
                  (make-place :local 3 :projection nil)
                  1))
    (make-basic-block
     :statements
     (list (assign-local 0 (rvalue-use (copy-local 1))))
     :terminator (terminator-return)))))

(defconst *main41-program*
  (make-mir-program
   :funs (omap::update "main41"
                       *main41-body*
                       (omap::update "add41" *add41-body* nil))
   :adts nil))

(assert-event (mir-programp *main41-program*))

(assert-event
 (equal (run-u64-fn "main41" nil *main41-program*)
        (runout-done (value-uint 42 (uint-type-u64)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Probe 4: unsizing coercion + pointer metadata --
; the fat-pointer creation and slice-length shape:
;
;   fn len4() -> usize { let a = [1u32, 2, 3, 4]; let s: &[u32] = &a; s.len() }
;
; (with the length read as the PtrMetadata of the slice reference).
; Locals: _0: usize, _1: [u32; 4], _2: &[u32; 4], _3: &[u32].

(defconst *len4-body*
  (make-body
   :locals (list (usize)
                 (ty-array (u32) 4)
                 (ty-ref (mutability-not) (ty-array (u32) 4))
                 (ty-ref (mutability-not) (ty-slice (u32))))
   :arg-count 0
   :blocks
   (list
    (make-basic-block
     :statements
     (list (assign-local 1
                         (rvalue-aggregate (agg-kind-array (u32))
                                           (list (const-u32 1)
                                                 (const-u32 2)
                                                 (const-u32 3)
                                                 (const-u32 4))))
           (assign-local 2 (rvalue-ref (mutability-not) (local-place 1)))
           (assign-local 3
                         (rvalue-cast (cast-kind-unsize)
                                      (copy-local 2)
                                      (ty-ref (mutability-not)
                                              (ty-slice (u32)))))
           (assign-local 0
                         (rvalue-unary-op (un-op-ptr-metadata)
                                          (copy-local 3))))
     :terminator (terminator-return)))))

(defconst *len4-program*
  (make-mir-program :funs (omap::update "len4" *len4-body* nil)
                    :adts nil))

(assert-event
 (equal (run-u64-fn "len4" nil *len4-program*)
        (runout-done (value-uint 4 (uint-type-usize)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Probe 5: array repetition -- the state-initializer shape:
;
;   fn rep7() -> u32 { let a = [7u32; 5]; a[3] }
;
; Locals: _0: u32, _1: [u32; 5], _2: usize.

(defconst *rep7-body*
  (make-body
   :locals (list (u32)
                 (ty-array (u32) 5)
                 (usize))
   :arg-count 0
   :blocks
   (list
    (make-basic-block
     :statements
     (list (assign-local 1 (rvalue-repeat (const-u32 7) 5))
           (assign-local 2 (rvalue-use (const-usize 3)))
           (assign-local 0
                         (rvalue-use
                          (operand-copy
                           (local-place 1 (proj-elem-index 2))))))
     :terminator (terminator-return)))))

(defconst *rep7-program*
  (make-mir-program :funs (omap::update "rep7" *rep7-body* nil)
                    :adts nil))

(assert-event
 (equal (run-u64-fn "rep7" nil *rep7-program*)
        (runout-done (value-uint 7 (uint-type-u32)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Probe 6: enum construction, discriminant read, switch, and
; downcast field read -- the Option-match shape from iterators:
;
;   fn getsome() -> u64 {
;       let o = Some(99u64);
;       match o { Some(v) => v, None => 0 }
;   }
;
; Locals: _0: u64, _1: Option<u64> (as ADT "Option", variants None=0/Some=1),
;         _2: usize (the discriminant).

(defconst *getsome-body*
  (make-body
   :locals (list (u64)
                 (ty-adt "Option")
                 (usize))
   :arg-count 0
   :blocks
   (list
    ;; bb0:
    (make-basic-block
     :statements
     (list (assign-local 1
                         (rvalue-aggregate (agg-kind-adt "Option" 1)
                                           (list (const-u64 99))))
           (assign-local 2 (rvalue-discriminant (local-place 1))))
     :terminator (terminator-switch-int
                  (move-local 2)
                  (make-switch-targets :values (list 1)
                                       :targets (list 1)
                                       :otherwise 2)))
    ;; bb1: the Some arm
    (make-basic-block
     :statements
     (list (assign-local 0
                         (rvalue-use
                          (operand-copy
                           (local-place 1
                                        (proj-elem-downcast 1)
                                        (proj-elem-field 0))))))
     :terminator (terminator-return))
    ;; bb2: the None arm
    (make-basic-block
     :statements
     (list (assign-local 0 (rvalue-use (const-u64 0))))
     :terminator (terminator-return)))))

(defconst *getsome-program*
  (make-mir-program
   :funs (omap::update "getsome" *getsome-body* nil)
   :adts (omap::update
          "Option"
          (make-adt-def :name "Option"
                        :variants (list (make-variant :name "None"
                                                      :fields nil)
                                        (make-variant :name "Some"
                                                      :fields (list (u64)))))
          nil)))

(assert-event (mir-programp *getsome-program*))

(assert-event
 (equal (run-u64-fn "getsome" nil *getsome-program*)
        (runout-done (value-uint 99 (uint-type-u64)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Probe 7: reading an element through a slice reference --
; the shape rustc emits for s[i] with s: &[u32]
; (a dereference projection followed by an index projection):
;
;   fn pick3() -> u32 {
;     let a = [10u32, 20, 30, 40];
;     let s: &[u32] = &a;
;     let i = 2usize;
;     s[i]                     // MIR: _0 = (*_3)[_4]
;   }
;
; Locals: _0: u32 (return), _1: [u32; 4] (a),
;         _2: &[u32; 4] (&a), _3: &[u32] (s), _4: usize (i).

(defconst *pick3-body*
  (make-body
   :locals (list (u32)
                 (ty-array (u32) 4)
                 (ty-ref (mutability-not) (ty-array (u32) 4))
                 (ty-ref (mutability-not) (ty-slice (u32)))
                 (usize))
   :arg-count 0
   :blocks
   (list
    (make-basic-block
     :statements
     (list (assign-local 1
                         (rvalue-aggregate (agg-kind-array (u32))
                                           (list (const-u32 10)
                                                 (const-u32 20)
                                                 (const-u32 30)
                                                 (const-u32 40))))
           (assign-local 2 (rvalue-ref (mutability-not) (local-place 1)))
           (assign-local 3
                         (rvalue-cast (cast-kind-unsize)
                                      (copy-local 2)
                                      (ty-ref (mutability-not)
                                              (ty-slice (u32)))))
           (assign-local 4 (rvalue-use (const-usize 2)))
           (assign-local 0
                         (rvalue-use
                          (operand-copy
                           (local-place 3
                                        (proj-elem-deref)
                                        (proj-elem-index 4))))))
     :terminator (terminator-return)))))

(defconst *pick3-program*
  (make-mir-program :funs (omap::update "pick3" *pick3-body* nil)
                    :adts nil))

(assert-event
 (equal (run-u64-fn "pick3" nil *pick3-program*)
        (runout-done (value-uint 30 (uint-type-u32)))))

; Indexing at or past the slice window's length is
; undefined behavior at the machine level
; (in real rustc output, a bounds-check assert precedes the access).

(defconst *pick9-body*
  (change-body *pick3-body*
               :blocks
               (list
                (make-basic-block
                 :statements
                 (append (butlast (basic-block->statements
                                   (car (body->blocks *pick3-body*)))
                                  2)
                         (list (assign-local 4 (rvalue-use (const-usize 9)))
                               (assign-local 0
                                             (rvalue-use
                                              (operand-copy
                                               (local-place
                                                3
                                                (proj-elem-deref)
                                                (proj-elem-index 4)))))))
                 :terminator (terminator-return)))))

(defconst *pick9-program*
  (make-mir-program :funs (omap::update "pick9" *pick9-body* nil)
                    :adts nil))

(assert-event
 (equal (runout-kind (run-u64-fn "pick9" nil *pick9-program*))
        :ub))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Probe 8: the abort terminator --
; where rustc's terminating-panic forms land under panic=abort.

(defconst *boom-body*
  (make-body
   :locals (list (u32))
   :arg-count 0
   :blocks
   (list
    (make-basic-block
     :statements nil
     :terminator (terminator-abort "core::panicking::panic")))))

(defconst *boom-program*
  (make-mir-program :funs (omap::update "boom" *boom-body* nil)
                    :adts nil))

(assert-event
 (equal (run-u64-fn "boom" nil *boom-program*)
        (runout-panic (list :abort "core::panicking::panic"))))

; Leo Library
;
; Copyright (C) 2025 Provable Inc.
;
; License: See the LICENSE file distributed with this library.
;
; Authors: Alessandro Coglio (www.alessandrocoglio.info)
;          Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "LEO-EARLY")

(include-book "values")

;; for logand:
(local (include-book "ihs/logops-lemmas" :dir :system))
;; for logior and logxor:
(local (include-book "centaur/bitops/ihs-extensions" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ bitwise-operations
  :parents (dynamic-semantics)
  :short "Leo bitwise operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These operate on signed and unsigned integers, as well as on boolean
     values.  For the binary operations, both arguments are always evaluated,
     even in the case the arguments are boolean-valued, unlike the
     @(see logical-operations)
     (which return after evaluating the first argument
     if the result is known at that point).")
   (xdoc::p
    "These are not, bitwise-and, bitwise-inclusive-or,
     and bitwise-exclusive-or."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-not ((arg valuep))
  :returns (result value-resultp)
  :short "Leo logical or bitwise negation operation."
  (b* ((err (list :op-not (value-fix arg))))
    (cond ((value-case arg :bool)
           (value-bool (not (value-bool->get arg))))
          ((value-case arg :u8)
           (value-u8 (loghead 8 (lognot (value-u8->get arg)))))
          ((value-case arg :u16)
           (value-u16 (loghead 16 (lognot (value-u16->get arg)))))
          ((value-case arg :u32)
           (value-u32 (loghead 32 (lognot (value-u32->get arg)))))
          ((value-case arg :u64)
           (value-u64 (loghead 64 (lognot (value-u64->get arg)))))
          ((value-case arg :u128)
           (value-u128 (loghead 128 (lognot (value-u128->get arg)))))
          ((value-case arg :i8)
           (value-i8 (lognot (value-i8->get arg))))
          ((value-case arg :i16)
           (value-i16 (lognot (value-i16->get arg))))
          ((value-case arg :i32)
           (value-i32 (lognot (value-i32->get arg))))
          ((value-case arg :i64)
           (value-i64 (lognot (value-i64->get arg))))
          ((value-case arg :i128)
           (value-i128 (lognot (value-i128->get arg))))
          (t (reserrf err))))
  :guard-hints (("Goal"
                 :in-theory
                 (e/d (value-bool->get
                       ubyte8p   value-u8->get   acl2::ubyte8-fix
                       ubyte16p  value-u16->get  acl2::ubyte16-fix
                       ubyte32p  value-u32->get  acl2::ubyte32-fix
                       ubyte64p  value-u64->get  acl2::ubyte64-fix
                       ubyte128p value-u128->get acl2::ubyte128-fix
                       sbyte8p   value-i8->get   acl2::sbyte8-fix
                       sbyte16p  value-i16->get  acl2::sbyte16-fix
                       sbyte32p  value-i32->get  acl2::sbyte32-fix
                       sbyte64p  value-i64->get  acl2::sbyte64-fix
                       sbyte128p value-i128->get acl2::sbyte128-fix)
                      (signed-byte-p))))
  ///
  (fty::deffixequiv op-not
                    :args ((arg valuep))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-bitand ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo bitwise-and operation"
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('and') operation operates on integers in a bitwise fashion
     and on booleans where both arguments are evaluated."))
  (b* ((err (list :op-bitand (value-fix left) (value-fix right))))
    (cond ((and (value-case left :bool) (value-case right :bool))
           (let ((leftval (value-bool->get left))
                 (rightval (value-bool->get right)))
             (value-bool (and leftval rightval))))
          ((and (value-case left :u8) (value-case right :u8))
           (value-u8 (logand (value-u8->get left)
                             (value-u8->get right))))
          ((and (value-case left :u16) (value-case right :u16))
           (value-u16 (logand (value-u16->get left)
                              (value-u16->get right))))
          ((and (value-case left :u32) (value-case right :u32))
           (value-u32 (logand (value-u32->get left)
                              (value-u32->get right))))
          ((and (value-case left :u64) (value-case right :u64))
           (value-u64 (logand (value-u64->get left)
                              (value-u64->get right))))
          ((and (value-case left :u128) (value-case right :u128))
           (value-u128 (logand (value-u128->get left)
                               (value-u128->get right))))
          ((and (value-case left :i8) (value-case right :i8))
           (value-i8 (logand (value-i8->get left)
                             (value-i8->get right))))
          ((and (value-case left :i16) (value-case right :i16))
           (value-i16 (logand (value-i16->get left)
                              (value-i16->get right))))
          ((and (value-case left :i32) (value-case right :i32))
           (value-i32 (logand (value-i32->get left)
                              (value-i32->get right))))
          ((and (value-case left :i64) (value-case right :i64))
           (value-i64 (logand (value-i64->get left)
                              (value-i64->get right))))
          ((and (value-case left :i128) (value-case right :i128))
           (value-i128 (logand (value-i128->get left)
                               (value-i128->get right))))
          (t (reserrf err))))
  :guard-hints (("Goal"
                 :in-theory
                 (e/d (value-bool->get
                       ubyte8p   value-u8->get   acl2::ubyte8-fix
                       ubyte16p  value-u16->get  acl2::ubyte16-fix
                       ubyte32p  value-u32->get  acl2::ubyte32-fix
                       ubyte64p  value-u64->get  acl2::ubyte64-fix
                       ubyte128p value-u128->get acl2::ubyte128-fix
                       sbyte8p   value-i8->get   acl2::sbyte8-fix
                       sbyte16p  value-i16->get  acl2::sbyte16-fix
                       sbyte32p  value-i32->get  acl2::sbyte32-fix
                       sbyte64p  value-i64->get  acl2::sbyte64-fix
                       sbyte128p value-i128->get acl2::sbyte128-fix)
                      (signed-byte-p))))
  ///
  (fty::deffixequiv op-bitand
                    :args ((left valuep) (right valuep))))

(define op-bitior ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo bitwise-inclusive-or operation."
  :long
  (xdoc::topstring
   (xdoc::p
    "This @('or') operation operates on integers in a bitwise fashion
     and on booleans where both arguments are evaluated."))
  (b* ((err (list :op-bitior (value-fix left) (value-fix right))))
    (cond ((and (value-case left :bool) (value-case right :bool))
           (let ((leftval (value-bool->get left))
                 (rightval (value-bool->get right)))
             (value-bool (or leftval rightval))))
          ((and (value-case left :u8) (value-case right :u8))
           (value-u8 (logior (value-u8->get left)
                             (value-u8->get right))))
          ((and (value-case left :u16) (value-case right :u16))
           (value-u16 (logior (value-u16->get left)
                              (value-u16->get right))))
          ((and (value-case left :u32) (value-case right :u32))
           (value-u32 (logior (value-u32->get left)
                              (value-u32->get right))))
          ((and (value-case left :u64) (value-case right :u64))
           (value-u64 (logior (value-u64->get left)
                              (value-u64->get right))))
          ((and (value-case left :u128) (value-case right :u128))
           (value-u128 (logior (value-u128->get left)
                               (value-u128->get right))))
          ((and (value-case left :i8) (value-case right :i8))
           (value-i8 (logior (value-i8->get left)
                             (value-i8->get right))))
          ((and (value-case left :i16) (value-case right :i16))
           (value-i16 (logior (value-i16->get left)
                              (value-i16->get right))))
          ((and (value-case left :i32) (value-case right :i32))
           (value-i32 (logior (value-i32->get left)
                              (value-i32->get right))))
          ((and (value-case left :i64) (value-case right :i64))
           (value-i64 (logior (value-i64->get left)
                              (value-i64->get right))))
          ((and (value-case left :i128) (value-case right :i128))
           (value-i128 (logior (value-i128->get left)
                               (value-i128->get right))))
          (t (reserrf err))))
  :guard-hints (("Goal"
                 :in-theory
                 (e/d (value-bool->get
                       ubyte8p   value-u8->get   acl2::ubyte8-fix
                       ubyte16p  value-u16->get  acl2::ubyte16-fix
                       ubyte32p  value-u32->get  acl2::ubyte32-fix
                       ubyte64p  value-u64->get  acl2::ubyte64-fix
                       ubyte128p value-u128->get acl2::ubyte128-fix
                       sbyte8p   value-i8->get   acl2::sbyte8-fix
                       sbyte16p  value-i16->get  acl2::sbyte16-fix
                       sbyte32p  value-i32->get  acl2::sbyte32-fix
                       sbyte64p  value-i64->get  acl2::sbyte64-fix
                       sbyte128p value-i128->get acl2::sbyte128-fix)
                      (signed-byte-p))))
  ///
  (fty::deffixequiv op-bitior
                    :args ((left valuep) (right valuep))))

(define op-bitxor ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo bitwise-exclusive-or operation."
  (b* ((err (list :op-bitand (value-fix left) (value-fix right))))
    (cond ((and (value-case left :bool) (value-case right :bool))
           (let ((leftval (value-bool->get left))
                 (rightval (value-bool->get right)))
             (value-bool (not (equal leftval rightval)))))
          ((and (value-case left :u8) (value-case right :u8))
           (value-u8 (logxor (value-u8->get left)
                             (value-u8->get right))))
          ((and (value-case left :u16) (value-case right :u16))
           (value-u16 (logxor (value-u16->get left)
                              (value-u16->get right))))
          ((and (value-case left :u32) (value-case right :u32))
           (value-u32 (logxor (value-u32->get left)
                              (value-u32->get right))))
          ((and (value-case left :u64) (value-case right :u64))
           (value-u64 (logxor (value-u64->get left)
                              (value-u64->get right))))
          ((and (value-case left :u128) (value-case right :u128))
           (value-u128 (logxor (value-u128->get left)
                               (value-u128->get right))))
          ((and (value-case left :i8) (value-case right :i8))
           (value-i8 (logxor (value-i8->get left)
                             (value-i8->get right))))
          ((and (value-case left :i16) (value-case right :i16))
           (value-i16 (logxor (value-i16->get left)
                              (value-i16->get right))))
          ((and (value-case left :i32) (value-case right :i32))
           (value-i32 (logxor (value-i32->get left)
                              (value-i32->get right))))
          ((and (value-case left :i64) (value-case right :i64))
           (value-i64 (logxor (value-i64->get left)
                              (value-i64->get right))))
          ((and (value-case left :i128) (value-case right :i128))
           (value-i128 (logxor (value-i128->get left)
                               (value-i128->get right))))
          (t (reserrf err))))
  :guard-hints (("Goal"
                 :in-theory
                 (e/d (value-bool->get
                       ubyte8p   value-u8->get   acl2::ubyte8-fix
                       ubyte16p  value-u16->get  acl2::ubyte16-fix
                       ubyte32p  value-u32->get  acl2::ubyte32-fix
                       ubyte64p  value-u64->get  acl2::ubyte64-fix
                       ubyte128p value-u128->get acl2::ubyte128-fix
                       sbyte8p   value-i8->get   acl2::sbyte8-fix
                       sbyte16p  value-i16->get  acl2::sbyte16-fix
                       sbyte32p  value-i32->get  acl2::sbyte32-fix
                       sbyte64p  value-i64->get  acl2::sbyte64-fix
                       sbyte128p value-i128->get acl2::sbyte128-fix)
                      (signed-byte-p))))
  ///
  (fty::deffixequiv op-bitxor
                    :args ((left valuep) (right valuep))))

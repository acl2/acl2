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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ ordering-operations
  :parents (dynamic-semantics)
  :short "Leo ordering operations."
  :long
  (xdoc::topstring
   (xdoc::p
    "These are the usual strict and non-strict ordering relations:
     less than, less than or equal to, greater than, greater than or equal to.")
   (xdoc::p
    "We model them via ACL2 functions that return boolean values
     when applied on integer, field, or scalar values of the same type.
     They defensively return an error indication
     when they are applied to values of other types
     or to values of different types."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-lt ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo less-than operation."
  (cond ((and (value-case left :u8) (value-case right :u8))
         (value-bool (< (value-u8->get left) (value-u8->get right))))
        ((and (value-case left :u16) (value-case right :u16))
         (value-bool (< (value-u16->get left) (value-u16->get right))))
        ((and (value-case left :u32) (value-case right :u32))
         (value-bool (< (value-u32->get left) (value-u32->get right))))
        ((and (value-case left :u64) (value-case right :u64))
         (value-bool (< (value-u64->get left) (value-u64->get right))))
        ((and (value-case left :u128) (value-case right :u128))
         (value-bool (< (value-u128->get left) (value-u128->get right))))
        ((and (value-case left :i8) (value-case right :i8))
         (value-bool (< (value-i8->get left) (value-i8->get right))))
        ((and (value-case left :i16) (value-case right :i16))
         (value-bool (< (value-i16->get left) (value-i16->get right))))
        ((and (value-case left :i32) (value-case right :i32))
         (value-bool (< (value-i32->get left) (value-i32->get right))))
        ((and (value-case left :i64) (value-case right :i64))
         (value-bool (< (value-i64->get left) (value-i64->get right))))
        ((and (value-case left :i128) (value-case right :i128))
         (value-bool (< (value-i128->get left) (value-i128->get right))))
        ((and (value-case left :field) (value-case right :field))
         (value-bool (< (value-field->get left) (value-field->get right))))
        ((and (value-case left :scalar) (value-case right :scalar))
         (value-bool (< (value-scalar->get left) (value-scalar->get right))))
        (t (reserrf (list :op-lt (value-fix left) (value-fix right)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-le ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo less-than-or-equal-to operation."
  (cond ((and (value-case left :u8) (value-case right :u8))
         (value-bool (<= (value-u8->get left) (value-u8->get right))))
        ((and (value-case left :u16) (value-case right :u16))
         (value-bool (<= (value-u16->get left) (value-u16->get right))))
        ((and (value-case left :u32) (value-case right :u32))
         (value-bool (<= (value-u32->get left) (value-u32->get right))))
        ((and (value-case left :u64) (value-case right :u64))
         (value-bool (<= (value-u64->get left) (value-u64->get right))))
        ((and (value-case left :u128) (value-case right :u128))
         (value-bool (<= (value-u128->get left) (value-u128->get right))))
        ((and (value-case left :i8) (value-case right :i8))
         (value-bool (<= (value-i8->get left) (value-i8->get right))))
        ((and (value-case left :i16) (value-case right :i16))
         (value-bool (<= (value-i16->get left) (value-i16->get right))))
        ((and (value-case left :i32) (value-case right :i32))
         (value-bool (<= (value-i32->get left) (value-i32->get right))))
        ((and (value-case left :i64) (value-case right :i64))
         (value-bool (<= (value-i64->get left) (value-i64->get right))))
        ((and (value-case left :i128) (value-case right :i128))
         (value-bool (<= (value-i128->get left) (value-i128->get right))))
        ((and (value-case left :field) (value-case right :field))
         (value-bool (<= (value-field->get left) (value-field->get right))))
        ((and (value-case left :scalar) (value-case right :scalar))
         (value-bool (<= (value-scalar->get left) (value-scalar->get right))))
        (t (reserrf (list :op-lt (value-fix left) (value-fix right)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-gt ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo greater-than operation."
  (cond ((and (value-case left :u8) (value-case right :u8))
         (value-bool (> (value-u8->get left) (value-u8->get right))))
        ((and (value-case left :u16) (value-case right :u16))
         (value-bool (> (value-u16->get left) (value-u16->get right))))
        ((and (value-case left :u32) (value-case right :u32))
         (value-bool (> (value-u32->get left) (value-u32->get right))))
        ((and (value-case left :u64) (value-case right :u64))
         (value-bool (> (value-u64->get left) (value-u64->get right))))
        ((and (value-case left :u128) (value-case right :u128))
         (value-bool (> (value-u128->get left) (value-u128->get right))))
        ((and (value-case left :i8) (value-case right :i8))
         (value-bool (> (value-i8->get left) (value-i8->get right))))
        ((and (value-case left :i16) (value-case right :i16))
         (value-bool (> (value-i16->get left) (value-i16->get right))))
        ((and (value-case left :i32) (value-case right :i32))
         (value-bool (> (value-i32->get left) (value-i32->get right))))
        ((and (value-case left :i64) (value-case right :i64))
         (value-bool (> (value-i64->get left) (value-i64->get right))))
        ((and (value-case left :i128) (value-case right :i128))
         (value-bool (> (value-i128->get left) (value-i128->get right))))
        ((and (value-case left :field) (value-case right :field))
         (value-bool (> (value-field->get left) (value-field->get right))))
        ((and (value-case left :scalar) (value-case right :scalar))
         (value-bool (> (value-scalar->get left) (value-scalar->get right))))
        (t (reserrf (list :op-lt (value-fix left) (value-fix right)))))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define op-ge ((left valuep) (right valuep))
  :returns (result value-resultp)
  :short "Leo greater-than-or-equal-to operation."
  (cond ((and (value-case left :u8) (value-case right :u8))
         (value-bool (>= (value-u8->get left) (value-u8->get right))))
        ((and (value-case left :u16) (value-case right :u16))
         (value-bool (>= (value-u16->get left) (value-u16->get right))))
        ((and (value-case left :u32) (value-case right :u32))
         (value-bool (>= (value-u32->get left) (value-u32->get right))))
        ((and (value-case left :u64) (value-case right :u64))
         (value-bool (>= (value-u64->get left) (value-u64->get right))))
        ((and (value-case left :u128) (value-case right :u128))
         (value-bool (>= (value-u128->get left) (value-u128->get right))))
        ((and (value-case left :i8) (value-case right :i8))
         (value-bool (>= (value-i8->get left) (value-i8->get right))))
        ((and (value-case left :i16) (value-case right :i16))
         (value-bool (>= (value-i16->get left) (value-i16->get right))))
        ((and (value-case left :i32) (value-case right :i32))
         (value-bool (>= (value-i32->get left) (value-i32->get right))))
        ((and (value-case left :i64) (value-case right :i64))
         (value-bool (>= (value-i64->get left) (value-i64->get right))))
        ((and (value-case left :i128) (value-case right :i128))
         (value-bool (>= (value-i128->get left) (value-i128->get right))))
        ((and (value-case left :field) (value-case right :field))
         (value-bool (>= (value-field->get left) (value-field->get right))))
        ((and (value-case left :scalar) (value-case right :scalar))
         (value-bool (>= (value-scalar->get left) (value-scalar->get right))))
        (t (reserrf (list :op-lt (value-fix left) (value-fix right)))))
  :hooks (:fix))

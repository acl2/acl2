; Rust Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Eric McCarthy (bendyarm on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RUST")

(include-book "../abstract-syntax")

; A hand-written MIR body for an iterative factorial function,
; as a structural test of the MIR fixtypes
; (the interpreter that will run it is milestone M1):
;
;   fn factorial(n: u64) -> u64 {
;       let mut acc: u64 = 1;
;       let mut i: u64 = n;
;       while i > 1 {
;           acc = acc * i;
;           i = i - 1;
;       }
;       acc
;   }
;
; in the MIR shape rustc gives it with overflow checks off
; (with overflow checks on, the multiplication becomes
; mul-with-overflow plus an assert terminator).
;
; Locals: _0: u64 (return place), _1: u64 (n, the argument),
;         _2: u64 (acc), _3: u64 (i), _4: bool (loop condition).
;
;   bb0: _2 = const 1u64; _3 = copy _1; goto -> bb1
;   bb1: _4 = Gt(copy _3, const 1u64);
;        switchInt(move _4) -> [0: bb3, otherwise: bb2]
;   bb2: _2 = Mul(copy _2, copy _3);
;        _3 = Sub(copy _3, const 1u64);
;        goto -> bb1
;   bb3: _0 = copy _2; return

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro u64 ()
  '(ty-uint (uint-type-u64)))

(defmacro const-u64 (n)
  `(operand-constant (const-uint ,n (uint-type-u64))))

(defmacro copy-local (n)
  `(operand-copy (make-place :local ,n :projection nil)))

(defmacro move-local (n)
  `(operand-move (make-place :local ,n :projection nil)))

(defmacro assign-local (n rvalue)
  `(statement-assign (make-place :local ,n :projection nil) ,rvalue))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *factorial-body*
  (make-body
   :locals (list (u64) ; _0: return place
                 (u64) ; _1: n
                 (u64) ; _2: acc
                 (u64) ; _3: i
                 (ty-bool)) ; _4: loop condition
   :arg-count 1
   :blocks
   (list
    ;; bb0:
    (make-basic-block
     :statements (list (statement-storage-live 2)
                       (assign-local 2 (rvalue-use (const-u64 1)))
                       (statement-storage-live 3)
                       (assign-local 3 (rvalue-use (copy-local 1))))
     :terminator (terminator-goto 1))
    ;; bb1:
    (make-basic-block
     :statements (list (statement-storage-live 4)
                       (assign-local 4 (rvalue-binary-op (bin-op-gt)
                                                         (copy-local 3)
                                                         (const-u64 1))))
     :terminator (terminator-switch-int
                  (move-local 4)
                  (make-switch-targets :values (list 0)
                                       :targets (list 3)
                                       :otherwise 2)))
    ;; bb2:
    (make-basic-block
     :statements (list (assign-local 2 (rvalue-binary-op (bin-op-mul)
                                                         (copy-local 2)
                                                         (copy-local 3)))
                       (assign-local 3 (rvalue-binary-op (bin-op-sub)
                                                         (copy-local 3)
                                                         (const-u64 1)))
                       (statement-storage-dead 4))
     :terminator (terminator-goto 1))
    ;; bb3:
    (make-basic-block
     :statements (list (assign-local 0 (rvalue-use (copy-local 2)))
                       (statement-storage-dead 3)
                       (statement-storage-dead 2))
     :terminator (terminator-return)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert-event (bodyp *factorial-body*))
(assert-event (equal (len (body->locals *factorial-body*)) 5))
(assert-event (equal (body->arg-count *factorial-body*) 1))
(assert-event (equal (len (body->blocks *factorial-body*)) 4))

; The entry block ends in a goto to block 1.

(assert-event
 (equal (basic-block->terminator (car (body->blocks *factorial-body*)))
        (terminator-goto 1)))

; A whole (one-function, no-ADTs) MIR program.

(defconst *factorial-program*
  (make-mir-program :funs (omap::update "factorial" *factorial-body* nil)
                    :adts nil))

(assert-event (mir-programp *factorial-program*))
(assert-event
 (equal (omap::lookup "factorial" (mir-program->funs *factorial-program*))
        *factorial-body*))

; A small ADT table entry, exercising the type side:
; enum Sign { Neg, Zero, Pos(u64) }

(defconst *sign-adt*
  (make-adt-def :name "Sign"
                :variants (list (make-variant :name "Neg" :fields nil)
                                (make-variant :name "Zero" :fields nil)
                                (make-variant :name "Pos"
                                              :fields (list (u64))))))

(assert-event (adt-defp *sign-adt*))
(assert-event
 (mir-programp
  (make-mir-program :funs (omap::update "factorial" *factorial-body* nil)
                    :adts (omap::update "Sign" *sign-adt* nil))))

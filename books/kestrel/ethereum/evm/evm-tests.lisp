; Tests of the EVM model.
;
; Copyright (C) 2019-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ETHEREUM")

(include-book "evm")
(include-book "evm-rules")
(include-book "std/testing/assert" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defconst *add-program* (list *add* *stop*))

;; Note that simple-run deals with programs that only use the stack, and it
;; projects out the stack after running.

;; Proves that the following 2 operations are equivalent:
;; 1. Pushing X and then Y onto the stack and then runing the add-program.
;; 2. Pushing the sum (modulo 2^256) of X and Y onto the stack.
(defthm add-program-correct
  (equal (simple-run *add-program*
                     (stack-push y (stack-push x (empty-stack))))
         (stack-push (acl2::bvplus 256 x y)
                     (empty-stack)))
  :hints (("Goal" :in-theory (append *semantic-function-rules*
                                     (enable current-operation stack-item)))))

;; Adding X and Y is equivalent to adding Y and X:
(defthm add-commutative
  (equal (simple-run *add-program* (stack-push y (stack-push x (empty-stack))))
         (simple-run *add-program* (stack-push x (stack-push y (empty-stack)))))
  :hints (("Goal" :in-theory (append *semantic-function-rules*
                                     (enable current-operation stack-item)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Adds the top 2 numbers on the stack and then subtracts the number below them.
(defconst *add-sub-program* (list *add* *sub* *stop*))

;; Test the disassembly:
(assert-equal (disassemble-evm-code *add-sub-program*)
              '((0 :add) (1 :sub) (2 :stop)))

;; Concrete test: Add 700 and 7, then subtract 3.  The result is 704.
(assert-equal (simple-run *add-sub-program*
                          (stack-push 700 (stack-push 7 (stack-push 3 (empty-stack)))))
              (stack-push 704 (empty-stack)))

(defthm symbolic-execution-test
  (equal (simple-run (list *add* *sub* *stop*)
                     (stack-push 700 (stack-push x (stack-push 3 (empty-stack)))))
         (stack-push (acl2::bvminus 256 (acl2::bvplus 256 700 x)
                                    3)
                     (empty-stack)))
  :hints (("Goal" :in-theory (append *semantic-function-rules*
                                     (enable current-operation stack-item)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

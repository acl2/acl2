; A proof of a very simple WASM program
;
; Copyright (C) 2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "WASM")

(include-book "proof-support")

;; todo: get this by parsing add.wasm:
(defconst *add-program*
  '((:local.get 1)
    (:local.get 0)
    (:i32.add)))

;; verify that add program correctly adds x and y:
;; executing the add program until it returns has the effect of pushing the sum of x and y onto the operand-stack of the caller
(defthm add-correct
  (implies (and (u32p x)
                (u32p y)
                (consp rest-of-call-stack)
                )
           (equal (top-operand
                    (current-operand-stack
                      (run 4 ; run 4 steps (currently, the implicit return is a step)
                           (make-state :store :fake ; todo!
                                       :call-stack (push-call-stack (make-frame :return-arity 1
                                                                                :locals (list (make-i32-val x) (make-i32-val y)) ; the params
                                                                                :operand-stack (empty-operand-stack)
                                                                                :instrs *add-program*)
                                                                    rest-of-call-stack)))))
                  (make-i32-val (bvplus 32 x y))))
  :hints (("Goal" :in-theory (enable current-instrs
                                     ;top-frame
                                     execute-instr return-from-function current-frame
                                     top-n-operands
                                     i32.add-vals
                                     make-i32-val ;todo
                                     i32-valp))))

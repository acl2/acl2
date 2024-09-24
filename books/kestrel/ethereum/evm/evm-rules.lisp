; Rules about the EVM model
;
; Copyright (C) 2019-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "EVM")

(include-book "evm")
(include-book "kestrel/utilities/defopeners" :dir :system)
(acl2::defopeners run-machine)

(defthm stacks-size-of-stack-push
  (equal (stack-size (stack-push item stack))
         (+ 1 (stack-size stack)))
  :hints (("Goal" :in-theory (enable stack-size stack-push))))

(defthm popn-of-stack-push
  (implies (posp n)
           (equal (popn n (stack-push item stack))
                  (popn (+ -1 n) stack)))
  :hints (("Goal" :in-theory (enable popn stack-push))))

(defthm stack-top-of-stack-push
  (equal (stack-top (stack-push item stack))
         item)
  :hints (("Goal" :in-theory (enable stack-top stack-push))))

(defthm popn-of-0
  (equal (popn 0 stack)
         stack)
  :hints (("Goal" :in-theory (enable popn))))

;todo: add more
(defconst *semantic-function-rules*
  '(execute-STOP
    execute-ADD
    execute-MUL
    execute-SUB
    execute-DIV
    execute-SDIV
    execute-MOD
;;    execute-SMOD
    execute-ADDMOD
    execute-MULMOD
    execute-EXP
;;    execute-SIGNEXTEND
    execute-LT
    execute-GT
    execute-SLT
    execute-SGT
    execute-EQ
    execute-ISZERO
    execute-AND
    execute-OR
    execute-XOR
    execute-NOT
    execute-BYTE
    ;; execute-SHA3
    ;; execute-ADDRESS
    ;; execute-BALANCE
    ;; execute-ORIGIN
    ;; execute-CALLER
    ;; execute-CALLVALUE
    ;; execute-CALLDATALOAD
    ;; execute-CALLDATASIZE
    ;; execute-CALLDATACOPY
    ;; execute-CODESIZE
    ;; execute-CODECOPY
    ;; execute-GASPRICE
    ;; execute-EXTCODESIZE
    ;; execute-EXTCODECOPY
    ;; execute-RETURNDATASIZE
    ;; execute-RETURNDATACOPY
    ;; execute-BLOCKHASH
    ;; execute-COINBASE
    ;; execute-TIMESTAMP
    ;; execute-NUMBER
    ;; execute-DIFFICULTY
    ;; execute-GASLIMIT
    ;; execute-POP
    ;; execute-MLOAD
    ;; execute-MSTORE
    ;; execute-MSTORE8
    ;; execute-SLOAD
    ;; execute-SSTORE
    ;; execute-JUMP
    ;; execute-JUMPI
    ;; execute-PC
    ;; execute-MSIZE
    ;; execute-GAS
    ;; execute-JUMPDEST
    ;; execute-PUSH1
    ;; execute-PUSH2
    ;; execute-PUSH3
    ;; execute-PUSH4
    ;; execute-PUSH5
    ;; execute-PUSH6
    ;; execute-PUSH7
    ;; execute-PUSH8
    ;; execute-PUSH9
    ;; execute-PUSH10
    ;; execute-PUSH11
    ;; execute-PUSH12
    ;; execute-PUSH13
    ;; execute-PUSH14
    ;; execute-PUSH15
    ;; execute-PUSH16
    ;; execute-PUSH17
    ;; execute-PUSH18
    ;; execute-PUSH19
    ;; execute-PUSH20
    ;; execute-PUSH21
    ;; execute-PUSH22
    ;; execute-PUSH23
    ;; execute-PUSH24
    ;; execute-PUSH25
    ;; execute-PUSH26
    ;; execute-PUSH27
    ;; execute-PUSH28
    ;; execute-PUSH29
    ;; execute-PUSH30
    ;; execute-PUSH31
    ;; execute-PUSH32
    ;; execute-DUP1
    ;; execute-DUP2
    ;; execute-DUP3
    ;; execute-DUP4
    ;; execute-DUP5
    ;; execute-DUP6
    ;; execute-DUP7
    ;; execute-DUP8
    ;; execute-DUP9
    ;; execute-DUP10
    ;; execute-DUP11
    ;; execute-DUP12
    ;; execute-DUP13
    ;; execute-DUP14
    ;; execute-DUP15
    ;; execute-DUP16
    ;; execute-SWAP1
    ;; execute-SWAP2
    ;; execute-SWAP3
    ;; execute-SWAP4
    ;; execute-SWAP5
    ;; execute-SWAP6
    ;; execute-SWAP7
    ;; execute-SWAP8
    ;; execute-SWAP9
    ;; execute-SWAP10
    ;; execute-SWAP11
    ;; execute-SWAP12
    ;; execute-SWAP13
    ;; execute-SWAP14
    ;; execute-SWAP15
    ;; execute-SWAP16
    ;; execute-LOG0
    ;; execute-LOG1
    ;; execute-LOG2
    ;; execute-LOG3
    ;; execute-LOG4
    ;; execute-CREATE
    ;; execute-CALL
    ;; execute-CALLCODE
    ;; execute-RETURN
    ;; execute-DELEGATECALL
    ;; execute-STATICCALL
    ;; execute-REVERT
    ;; execute-INVALID
    ;; execute-SELFDESTRUCT
    ))

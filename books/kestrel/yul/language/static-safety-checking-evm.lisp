; Yul Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "YUL")

(include-book "static-safety-checking")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc+ static-safety-checking-evm
  :parents (static-semantics)
  :short "Static safety checking of the EVM dialect of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "We specialize the static safety checks for generic Yul to the EVM dialect
     by defining a function table for the EVM functions
     and by using that as the initial function table
     to check the safety of the top-level block.")
   (xdoc::p
    "The EVM functions are listed at
     [Solidity: Yul: Specification of Yul: EVM Dialect].
     As noted in the text before the table,
     they return either no or one value."))
  :order-subtopics t
  :default-parent t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define evm-funtable ()
  :returns (funtab funtablep)
  :short "Function table for the EVM dialect of Yul."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is based on the table in [Solidity],
     referenced in @(see static-safety-checking-evm).")
   (xdoc::p
    "In order to enter the information concisely,
     we introduce a macro that builds a nest of @(tsee omap::update)s."))
  (evm-funtable-build "stop" 0 0
                      "add" 2 1
                      "sub" 2 1
                      "mul" 2 1
                      "div" 2 1
                      "sdiv" 2 1
                      "mod" 2 1
                      "smod" 2 1
                      "exp" 2 1
                      "not" 1 1
                      "lt" 2 1
                      "gt" 2 1
                      "slt" 2 1
                      "sgt" 2 1
                      "eq" 2 1
                      "iszero" 1 1
                      "and" 2 1
                      "or" 2 1
                      "xor" 2 1
                      "byte" 2 1
                      "shl" 2 1
                      "shr" 2 1
                      "sar" 2 1
                      "addmod" 3 1
                      "mulmod" 3 1
                      "signextend" 2 1
                      "keccak256" 2 1
                      "pc" 0 1
                      "pop" 1 0
                      "mload" 1 1
                      "mstore" 2 0
                      "mstore8" 2 0
                      "sload" 1 1
                      "sstore" 2 0
                      "msize" 0 1
                      "gas" 0 1
                      "address" 0 1
                      "balance" 1 1
                      "selfbalance" 0 1
                      "caller" 0 1
                      "callvalue" 0 1
                      "calldataload" 1 1
                      "calldatasize" 0 1
                      "calldatacopy" 3 0
                      "codesize" 0 1
                      "codecopy" 3 0
                      "extcodesize" 1 1
                      "extcodecopy" 4 0
                      "returndatasize" 0 1
                      "returndatacopy" 3 0
                      "extcodehash" 1 1
                      "create" 3 1
                      "create2" 4 1
                      "call" 7 1
                      "callcode" 7 1
                      "delegatecall" 6 1
                      "staticcall" 6 1
                      "return" 2 0
                      "revert" 2 0
                      "selfdestruct" 1 0
                      "invalid" 0 0
                      "log0" 2 0
                      "log1" 3 0
                      "log2" 4 0
                      "log3" 5 0
                      "log4" 6 0
                      "chainid" 0 1
                      "basefee" 0 1
                      "origin" 0 1
                      "gasprice" 0 1
                      "blockhash" 1 1
                      "coinbase" 0 1
                      "timestamp" 0 1
                      "number" 0 1
                      "difficulty" 0 1
                      "gaslimit" 0 1)

  :prepwork

  ((defun evm-funtable-build-fn (args)
     (if (endp args)
         nil
       `(omap::update (identifier ,(first args))
                      (make-funtype :in ,(second args) :out ,(third args))
                      ,(evm-funtable-build-fn (cdddr args)))))

   (defmacro evm-funtable-build (&rest args)
     (evm-funtable-build-fn args))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define check-safe-top-block-evm ((block blockp))
  :returns (_ resulterr-optionp)
  :short "Check if the top block is safe, in the EVM dialect."
  :long
  (xdoc::topstring
   (xdoc::p
    "This is like @(tsee check-safe-top-block) for generic Yul,
     except that the initial function table is
     the one with the EVM functions."))
  (b* (((ok modes) (check-safe-block block nil (evm-funtable))))
    (if (equal modes (set::insert (mode-regular) nil))
        nil
      (err (list :top-block-mode modes))))
  :hooks (:fix))

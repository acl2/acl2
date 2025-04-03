; A formal model of the EVM (Ethereum Virtual Machine)
;
; Copyright (C) 2019-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "EVM")

;; STATUS: IN-PROGRESS

;; TODO: Finish adding instructions.
;; TODO: Check existing instructions wrt the latest version of the Yellow Paper.
;; TODO: Add documentation.
;; TODO: Add tests.
;; TODO: Some notions defined here, like wordp and transactionp, are also defined in the ETHEREUM package.

(include-book "kestrel/bv/unsigned-byte-p" :dir :system)
(include-book "kestrel/bv/bvplus" :dir :system)
(include-book "kestrel/bv/bvminus" :dir :system)
(include-book "kestrel/bv/bvmult" :dir :system)
(include-book "kestrel/bv/bvdiv" :dir :system)
(include-book "kestrel/bv/sbvdiv" :dir :system)
(include-book "kestrel/bv/bvmod" :dir :system)
(include-book "kestrel/bv/bvand" :dir :system)
(include-book "kestrel/bv/bvor" :dir :system)
(include-book "kestrel/bv/bvxor" :dir :system)
(include-book "kestrel/bv/bitxor" :dir :system)
(include-book "kestrel/bv/bvnot" :dir :system)
(include-book "kestrel/bv/bvsx" :dir :system)
(include-book "kestrel/bv/bool-to-bit" :dir :system)
(include-book "kestrel/bv/sbvlt-def" :dir :system)
;(include-book "../bv/conversions-es")
(include-book "kestrel/sequences/defforall" :dir :system)
(include-book "kestrel/lists-light/subrange" :dir :system)
(include-book "kestrel/lists-light/memberp" :dir :system)
(include-book "kestrel/bv-lists/all-unsigned-byte-p" :dir :system)
(include-book "kestrel/bv-lists/packbv" :dir :system)
(include-book "kestrel/bv-lists/unpackbv" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "std/util/defaggregate" :dir :system)
(include-book "support")
(local (include-book "kestrel/bv/bvcat" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))
(local (include-book "kestrel/lists-light/nthcdr" :dir :system))
(local (include-book "kestrel/arithmetic-light/expt" :dir :system))
(local (include-book "kestrel/arithmetic-light/mod2" :dir :system))
(local (include-book "kestrel/arithmetic-light/times" :dir :system))
(local (include-book "kestrel/arithmetic-light/times-and-divide" :dir :system))
(local (include-book "kestrel/arithmetic-light/minus" :dir :system))

(local (in-theory (disable mv-nth)))

;; Recognize a natural number less than 2^64
(defund n64p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 64 x))

;; Recognize a natural number less than 2^256
(defund n256p (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 256 x))

(defthm n256p-forward-to-natp
  (implies (n256p x)
           (natp x))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable n256p))))

;helps with the bv ops
(defthm n256p-when-unsigned-byte-p
  (implies (unsigned-byte-p 256 x)
           (n256p x))
  :hints (("Goal" :in-theory (enable n256p))))

;for bool-to-bit
(defthm n256p-when-bitp
  (implies (unsigned-byte-p 1 x)
           (n256p x))
  :hints (("Goal" :in-theory (enable n256p))))

(defthm n256p-of-if
  (equal (n256p (if test x y))
         (if test
             (n256p x)
           (n256p y))))


(acl2::defforall-simple n256p :name all-n256p :guard t)

;; ;;maybe define a wordplus, etc.
;; (defthm n256p-of-bvplus
;;   (N256P (BVPLUS 256 x y))
;;   :hints (("Goal" :in-theory (enable N256P))))

;; (defthm n256p-of-bvmult
;;   (n256p (bvmult 256 x y))
;;   :hints (("Goal" :in-theory (enable n256p))))

;; (defthm n256p-of-bvdiv
;;   (n256p (bvdiv 256 x y))
;;   :hints (("Goal" :in-theory (enable n256p))))

;; (defthm n256p-of-bvmod
;;   (n256p (bvmod 256 x y))
;;   :hints (("Goal" :in-theory (enable n256p))))

;; (defthm n256p-of-sbvdiv
;;   (n256p (acl2::sbvdiv 256 x y))
;;   :hints (("Goal" :in-theory (enable n256p))))

(defthm n256p-of-bvminus
  (n256p (bvminus 256 x y))
  :hints (("Goal" :in-theory (enable n256p))))

;; (defthm n256p-of-bvchop
;;   (n256p (bvchop 256 x))
;;   :hints (("Goal" :in-theory (enable n256p))))

(defthm bvchop-identity-when-256p
  (implies (n256p x)
           (equal (bvchop 256 x)
                  x))
  :hints (("Goal" :in-theory (enable n256p))))

;
;; (thm
;;  (implies (N256P x)
;;           (natp x)))

(defun wordp (x)
  (declare (xargs :guard t))
  (unsigned-byte-p 256 x) ;todo: or should we use a B_32?
  )

(acl2::defforall-simple wordp :name all-wordp :guard t)

(defun word-arrayp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (all-wordp x)))

(defun byte-arrayp (b)
  (declare (xargs :guard t))
  (and (true-listp b)
       (acl2::all-unsigned-byte-p 8 b)))

;; Recognize a sequence of bytes of length 20
(defun b20p (x)
  (declare (xargs :guard t))
  (and (byte-arrayp x)
       (= 20 (len x))))

;; Recognize a sequence of bytes of length 32
(defun b32p (x)
  (declare (xargs :guard t))
  (and (byte-arrayp x)
       (= 32 (len x))))

;;160 bits. YP4.1.  Note that (11) implies that this is a list of 20 bytes.
(defund addressp (x)
  (declare (xargs :guard t))
  (b20p x))

(defun 0-address ()
  (declare (xargs :guard t))
  (repeat 20 0))

(defthm addressp-of-0-address
  (addressp (0-address)))

(defund noncep (x)
  (declare (xargs :guard t))
  (n256p x))

;; turn an address (list of 20 bytes) into an n256.
(defund pack-address (address)
  (declare (xargs :guard (addressp address)
                  :guard-hints (("Goal" :in-theory (enable addressp)))))
  (acl2::packbv 20 8 address))

(defthm n256p-of-pack-address
  (implies (addressp address)
           (n256p (pack-address address)))
  :hints (("Goal" :in-theory (enable pack-address))))

;; turn an address-number (nat less than 2^160) into an address (list of 20 bytes)
(defund unpack-address (address-num)
  (declare (xargs :guard (and (natp address-num)
                              (< address-num (expt 2 160)))
                  :guard-hints (("Goal" :in-theory (enable addressp)))))
  (acl2::unpackbv 20 8 address-num))

(defthm addressp-of-unpack-address
  (implies (and (natp address-num)
                (< address-num (expt 2 160)))
           (addressp (unpack-address address-num)))
  :hints (("Goal" :in-theory (enable unpack-address addressp))))


(acl2::defforall-simple addressp :name all-addressp :guard t) ;todo fix defforall-simple to use the right package

;; YP4.1
;; The types here come from (12).
(std::defaggregate account-state
  ((nonce noncep)                       ;; _n
   (balance n256p)                      ;; _b
   (storage-root b32p)                  ;; _s
   (codehash b32p)                      ;; _c
   )
  :pred account-statep)

(acl2::defforall-simple account-statep :name all-account-statep :guard t)

;; small sigma.  YP4.1.
;; A map from addresses to account states.
(defund world-statep (sigma)
  (declare (xargs :guard t))
  (and (alistp sigma)
       (all-addressp (strip-cars sigma))
       (all-account-statep (strip-cdrs sigma))))

(defund empty-world-state ()
  (declare (xargs :guard t))
  nil)

(defthm world-statep-forward-to-alistp
  (implies (world-statep sigma)
           (alistp sigma))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable world-statep))))

(defthm world-statep-forward-to-true-listp
  (implies (world-statep sigma)
           (true-listp sigma))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable world-statep))))

;; sigma[a]
;; Returns an account-state or :empty-set.
(defund get-account (sigma address)
  (declare (xargs :guard (and (addressp address)
                              (world-statep sigma))))
  (let ((entry (assoc-equal address sigma)))
    (if entry
        (cdr entry)
      :empty-set)))

(defthm get-account-type
  (implies (and (addressp address)
                (world-statep sigma)
                (not (equal (get-account sigma address)
                            :empty-set)))
           (account-statep (get-account sigma address)))
  :hints (("Goal" :in-theory (enable get-account WORLD-STATEP))))

(defthm empty-not-an-account-state
  (not (account-statep :empty-set)))

;; TODO: Lots more here, starting at (6).

(defstub kec-of-empty () t)

(defund empty-accountp (sigma address)
  (declare (xargs :guard (and (world-statep sigma)
                              (addressp address))))
  (let ((account-state (get-account sigma address)))
    (and (not (equal account-state :empty-set)) ;implicit ;todo: or add to guard
         (and (equal (account-state->codehash account-state)
                     (kec-of-empty))
              (equal (account-state->nonce account-state)
                     0)
              (equal (account-state->balance account-state)
                     0)))))

(defund dead-accountp (sigma address)
  (declare (xargs :guard (and (world-statep sigma)
                              (addressp address))))
  (let ((account-state (get-account sigma address)))
    (or (equal :empty-set account-state)
        (empty-accountp sigma address))))

;any limit?
;n256p?
(defun weip (x)
  (declare (xargs :guard t))
  (natp x))

(defun maybe-addressp (x)
  (declare (xargs :guard t))
  (or (addressp x)
      (eq x :empty-set) ;todo: this is discussed as being the only member of B_0
      ))

;; See YP Section 4.2.
(std::defaggregate transaction
  ((nonce noncep) ;T_n
   (gas-price weip) ;T_p
   (gas-limit n256p) ;T_g
   (to maybe-addressp) ;T_t
   (value weip) ;T_v
   (sig-v) ;T_w ;type is wrong in YP
   (sig-r n256p) ;T_r
   (sig-s n256p) ;T_s
   (init-or-data byte-arrayp) ;only sometimes ;T_i
   )
  :pred transactionp)

(acl2::defforall-simple transactionp :name all-transactionp :guard t)

;; transaction substate
(std::defaggregate substate
  ((self-destruct-set all-addressp) ;addresses, not accounts, right?
   (log-series)
   (touched-accounts all-addressp)
   (refund-balance weip))
  :pred substatep)

;; YP6.1.
(defund initial-substate ()
  (declare (xargs :guard t))
  (substate nil ;no self-destructs (todo: oveuse of empty set in YP)
            nil ;no logs
            nil ;no touched accounts
            0 ;refund balance
            ))

;todo: what are the types of all these fields?
(std::defaggregate block-header
  ((parent-hash)
   (ommers-hash)
   (beneficiary addressp)
   (state-root n256p)
   (transactions-root n256p)
   (receipts-root n256p)
   (logs-bloom) ;todo type?
   (difficulty) ;todo type?
   (number natp) ;todo type?
   (gas-limit)
   (gas-used)
   (timestamp)
   (extra-data byte-arrayp) ;todo max len
   (mix-hash n256p)
   (nonce n64p) ;there are other nonces
   )
  :pred block-headerp)

(acl2::defforall-simple block-headerp :name all-block-headerp :guard t)

(std::defaggregate block$ ;todo: remove-block-p from the package imports
                   ((header block-headerp)
                    (transations all-transactionp)
                    (ommer-headers all-block-headerp)))

; "I"
(std::defaggregate execution-environment
  ((owner-address addressp)      ;I_a
   (sender-address addressp)     ;I_o
   (gas-price natp)              ;I_p ;todo: type?
   (input-data byte-arrayp)      ;I_d
   (causer-account addressp)     ;I_s ;todo: what is this?
   (value n256p)                 ;I_v type?  ;this has to be an n256 or we can't push it onto the stack
   (bytecode byte-arrayp)        ;I_b
   (block-header block-headerp)  ;I_H
   (depth natp)                  ;I_e
   (permission)                  ;I_w todo: type?
   )
  :pred execution-environmentp)

(defthm natp-of-pc-when-execution-environmentp
  (implies (execution-environmentp mu)
           (true-listp (execution-environment->bytecode mu)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable execution-environmentp execution-environment->bytecode))))

;anything beyond the end up to x^256-1 is a zero.
(defund memoryp (x)
  (declare (xargs :guard t))
  (word-arrayp x))

;;;
;;; the stack
;;;

(defund stackp (stack)
  (declare (xargs :guard t))
  (and (all-n256p stack)
       (true-listp stack)
       (<= (len stack) 1024)))

(defund empty-stack ()
  (declare (xargs :guard t))
  nil)

(defund stack-size (stack)
  (declare (xargs :guard (stackp stack)))
  (len stack))

;drop?
;; (defthm n256p-of-nth-when-stackp
;;   (implies (and (stackp stack)
;;                 (<= 0 n)
;;                 (< n (stack-size stack)))
;;            (n256p (nth n stack)))
;;   :hints (("Goal" :in-theory (e/d (stackp nth)
;;                                   nil))))


(defund stack-top (stack)
  (declare (xargs :guard (and (stackp stack)
                              (< 0 (stack-size stack)))
                  :guard-hints (("Goal" :in-theory (enable stack-size)))))
  (car stack))

(defund popn (n stack)
  (declare (xargs :guard (and (natp n)
                              (stackp stack)
                              (<= n (stack-size stack)))
                  :guard-hints (("Goal" :in-theory (enable stackp)))))
  (nthcdr n stack))

(defthm stackp-of-popn
  (implies (stackp stack)
           (stackp (popn delta stack)))
  :hints (("Goal" :in-theory (enable popn stackp))))

(defthm popn-of-0
  (equal (popn 0 stack)
         stack)
  :hints (("Goal" :in-theory (enable popn))))

(defthm stacks-size-of-popn
  (implies (and (<= n (stack-size stack))
                (natp n))
           (equal (stack-size (popn n stack))
                  (- (stack-size stack) n)))
  :hints (("Goal" :in-theory (enable popn stackp stack-size))))

;todo: remove push from the ethereum package and call this push
(defund stack-push (item stack)
  (declare (xargs :guard (and (n256p item)
                              (stackp stack)
                              (< (stack-size stack) 1024))))
  (cons item stack))

(defthm stackp-of-stack-push
  (equal (stackp (stack-push item stack))
         (and (stackp stack)
              (< (stack-size stack) 1024)
              (n256p item)))
  :hints (("Goal" :in-theory (enable stack-push stackp stack-size))))

(defthm n256p-of-stack-top-when-stackp
  (implies (and (stackp stack)
                (< 0 (stack-size stack)))
           (n256p (stack-top stack)))
  :hints (("Goal" :in-theory (e/d (stackp stack-top)
                                  nil))))

(defthm integerp-of-stack-top-when-stackp
  (implies (and (stackp stack)
                (< 0 (stack-size stack)))
           (integerp (stack-top stack)))
  :hints (("Goal" :in-theory (e/d (stackp stack-top)
                                  nil))))

(defthm natp-of-stack-top-when-stackp-forced
  (implies (and (force (stackp stack))
                (force (< 0 (stack-size stack))))
           (natp (stack-top stack)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (e/d (stackp stack-top)
                                  nil))))

(defthm unsigned-byte-p-of-stack-top-when-stackp-forced
  (implies (and (force (stackp stack))
                (force (< 0 (stack-size stack)))
                (<= 256 n)
                (integerp n)
                )
           (unsigned-byte-p n (stack-top stack)))
  :hints (("Goal" :use n256p-of-stack-top-when-stackp
           :in-theory (e/d (n256p) ( n256p-of-stack-top-when-stackp)))))

(defthm acl2-numberp-of-stack-top-when-stackp
  (implies (and (stackp stack)
                (< 0 (stack-size stack)))
           (acl2-numberp (stack-top stack)))
  :hints (("Goal" :in-theory (e/d (stackp stack-top)
                                  nil))))

(defthm nonneg-of-stack-top-when-stackp
  (implies (and (stackp stack)
                (< 0 (stack-size stack)))
           (not (< (stack-top stack) 0)))
  :hints (("Goal" :use n256p-of-stack-top-when-stackp
           :in-theory (disable n256p-of-stack-top-when-stackp))))

(defthm stack-size-bound-linear
  (implies (stackp stack)
           (<= (stack-size stack)
               1024))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable stack-size stackp))))

(defthm stack-top-of-stack-push
  (equal (stack-top (stack-push item stack))
         item)
  :hints (("Goal" :in-theory (enable stack-top stack-push))))

;;;
;;; the machine-state (mu)
;;;

;; small "mu"
;todo types
(std::defaggregate machine-state
  ((gas-available natp) ;"mu_g"
   (pc natp ;n256p todo: but how big is the max program?
       ) ;"mu_pc"
   (memory memoryp) ;"mu_m"
   (active-words) ;type? n256p not quite big enough ;"mu_i"
   (stack stackp) ;"mu_s"
   )
  :pred machine-statep)

(defthm natp-of-gas-available-when-machine-statep
  (implies (machine-statep mu)
           (natp (machine-state->gas-available mu)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable machine-statep machine-state->gas-available n256p))))

;; (defthm n256p-of-pc-when-machine-statep
;;   (implies (machine-statep mu)
;;            (n256p (machine-state->pc mu)))
;;   :rule-classes :type-prescription
;;   :hints (("Goal" :in-theory (enable machine-statep machine-state->pc))))

(defthm natp-of-pc-when-machine-statep
  (implies (machine-statep mu)
           (natp (machine-state->pc mu)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable machine-statep machine-state->pc n256p))))

;;todo: slow to get the stack over and over when stack-item is called
;todo: make a version that directly takes the stack
;repeatedly?
(defund stack-item (n mu)
  (declare (xargs :guard (and (natp n)
                              ;;(< n 1024)
                              (machine-statep mu)
                              (< n (stack-size (machine-state->stack mu))))
                  :guard-hints (("Goal" :use (:instance return-type-of-machine-state->stack
                                                        (x mu))
                                 :in-theory (e/d (stackp)
                                                 (return-type-of-machine-state->stack))))))
  (stack-top (popn n (machine-state->stack mu))))

(defthm n256p-of-stack-item ;tighten
  (implies (and (machine-statep mu)
                (< n (stack-size (machine-state->stack mu)))
                (natp n))
           (n256p (stack-item n mu)))
  :hints (("Goal" :in-theory (enable stack-size stack-item machine-statep machine-state->stack))))

(defthm unsigned-byte-p-when-n256p
  (implies (n256p x)
           (unsigned-byte-p 256 x))
  :hints (("Goal" :in-theory (enable n256p))))

(defthm unsigned-byte-p-of-stack-item ;tighten
  (implies (and (machine-statep mu)
                (< n (stack-size (machine-state->stack mu))) ;move to rhs?
                (natp n))
           (unsigned-byte-p 256 (stack-item n mu)))
  :hints (("Goal" :use n256p-of-stack-item
           :in-theory (disable n256p-of-stack-item))))
  ;; :hints (("Goal" :in-theory (enable stack-size stack-item machine-statep machine-state->stack ;POPN stack-top ACL2::NTH-WHEN-<=-LEN
  ;;                                    ))))

(defthm natp-of-stack-item ;tighten
  (implies (and (machine-statep mu)
                (< n (stack-size (machine-state->stack mu)))
                (natp n))
           (natp (stack-item n mu)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :use n256p-of-stack-item
           :in-theory (e/d (n256p) (n256p-of-stack-item
                                    UNSIGNED-BYTE-P-OF-STACK-ITEM)))))

(defund initial-memory ()
  (declare (xargs :guard t))
  nil ;omit trailing zeros
  )


;"C"
(defun instruction-cost (sigma mu i)
  (declare (xargs :guard (and (world-statep sigma)
                              (machine-statep mu)
                              (execution-environmentp i))))
  (declare (ignore sigma mu i)) ;todo
  0 ;fixme
  )

;; Each entry is a list of the form (value mnemonic delta alpha), where value
;; is the opcode, delta is the number of items removed from the stack, and
;; alpha is the number of items added to the stack.
;todo: check all of these!
(defconst *instructions*
  '((#x00 :STOP 0 0)
    (#x01 :ADD 2 1)
    (#x02 :MUL 2 1)
    (#x03 :SUB 2 1)
    (#x04 :DIV 2 1)
    (#x05 :SDIV 2 1)
    (#x06 :MOD 2 1)
    (#x07 :SMOD 2 1)
    (#x08 :ADDMOD 3 1)
    (#x09 :MULMOD 3 1)
    (#x0a :EXP 2 1)
    (#x0b :SIGNEXTEND 2 1)
    (#x10 :LT 2 1)
    (#x11 :GT 2 1)
    (#x12 :SLT 2 1)
    (#x13 :SGT 2 1)
    (#x14 :EQ 2 1)
    (#x15 :ISZERO 1 1)
    (#x16 :AND 2 1)
    (#x17 :OR 2 1)
    (#x18 :XOR 2 1)
    (#x19 :NOT 1 1)
    (#x1a :BYTE 2 1)
    (#x20 :SHA3 2 1)
    (#x30 :ADDRESS 0 1)
    (#x31 :BALANCE 1 1)
    (#x32 :ORIGIN 0 1)
    (#x33 :CALLER 0 1)
    (#x34 :CALLVALUE 0 1)
    (#x35 :CALLDATALOAD 1 1)
    (#x36 :CALLDATASIZE 0 1)
    (#x37 :CALLDATACOPY 3 0)
    (#x38 :CODESIZE 0 1)
    (#x39 :CODECOPY 3 0)
    (#x3a :GASPRICE 0 1)
    (#x3b :EXTCODESIZE 1 1)
    (#x3c :EXTCODECOPY 4 0)
    (#x3d :RETURNDATASIZE 0 1)
    (#x3e :RETURNDATACOPY 3 0)
    (#x40 :BLOCKHASH 1 1)
    (#x41 :COINBASE 0 1)
    (#x42 :TIMESTAMP 0 1)
    (#x43 :NUMBER 0 1)
    (#x44 :DIFFICULTY 0 1)
    (#x45 :GASLIMIT 0 1)
    (#x50 :POP 1 0)
    (#x51 :MLOAD 1 1)
    (#x52 :MSTORE 2 0)
    (#x53 :MSTORE8 2 0)
    (#x54 :SLOAD 1 1)
    (#x55 :SSTORE 2 0)
    (#x56 :JUMP 1 0)
    (#x57 :JUMPI 2 0)
    (#x58 :PC 0 1)
    (#x59 :MSIZE 0 1)
    (#x5a :GAS 0 1)
    (#x5b :JUMPDEST 0 0)
    (#x60 :PUSH1 0 1)
    (#x61 :PUSH2 0 1)
    (#x62 :PUSH3 0 1)
    (#x63 :PUSH4 0 1)
    (#x64 :PUSH5 0 1)
    (#x65 :PUSH6 0 1)
    (#x66 :PUSH7 0 1)
    (#x67 :PUSH8 0 1)
    (#x68 :PUSH9 0 1)
    (#x69 :PUSH10 0 1)
    (#x6a :PUSH11 0 1)
    (#x6b :PUSH12 0 1)
    (#x6c :PUSH13 0 1)
    (#x6d :PUSH14 0 1)
    (#x6e :PUSH15 0 1)
    (#x6f :PUSH16 0 1)
    (#x70 :PUSH17 0 1)
    (#x71 :PUSH18 0 1)
    (#x72 :PUSH19 0 1)
    (#x73 :PUSH20 0 1)
    (#x74 :PUSH21 0 1)
    (#x75 :PUSH22 0 1)
    (#x76 :PUSH23 0 1)
    (#x77 :PUSH24 0 1)
    (#x78 :PUSH25 0 1)
    (#x79 :PUSH26 0 1)
    (#x7a :PUSH27 0 1)
    (#x7b :PUSH28 0 1)
    (#x7c :PUSH29 0 1)
    (#x7d :PUSH30 0 1)
    (#x7e :PUSH31 0 1)
    (#x7f :PUSH32 0 1)
    (#x80 :DUP1 1 2)
    (#x81 :DUP2 2 3)
    (#x82 :DUP3 3 4)
    (#x83 :DUP4 4 5)
    (#x84 :DUP5 5 6)
    (#x85 :DUP6 6 7)
    (#x86 :DUP7 7 8)
    (#x87 :DUP8 8 9)
    (#x88 :DUP9 9 10)
    (#x89 :DUP10 10 11)
    (#x8a :DUP11 11 12)
    (#x8b :DUP12 12 13)
    (#x8c :DUP13 13 14)
    (#x8d :DUP14 14 15)
    (#x8e :DUP15 15 16)
    (#x8f :DUP16 16 17)
    (#x90 :SWAP1 2 2)
    (#x91 :SWAP2 3 3)
    (#x92 :SWAP3 4 4)
    (#x93 :SWAP4 5 5)
    (#x94 :SWAP5 6 6)
    (#x95 :SWAP6 7 7)
    (#x96 :SWAP7 8 8)
    (#x97 :SWAP8 9 9)
    (#x98 :SWAP9 10 10)
    (#x99 :SWAP10 11 11)
    (#x9a :SWAP11 12 12)
    (#x9b :SWAP12 13 13)
    (#x9c :SWAP13 14 14)
    (#x9d :SWAP14 15 15)
    (#x9e :SWAP15 16 16)
    (#x9f :SWAP16 17 17)
    (#xa0 :LOG0 2 0)
    (#xa1 :LOG1 3 0)
    (#xa2 :LOG2 4 0)
    (#xa3 :LOG3 5 0)
    (#xa4 :LOG4 6 0)
    (#xf0 :CREATE 3 1)
    (#xf1 :CALL 7 1)
    (#xf2 :CALLCODE 7 1)
    (#xf3 :RETURN 2 0)
    (#xf4 :DELEGATECALL 6 1)
    (#xfa :STATICCALL 6 1)
    (#xfd :REVERT 2 0)
    (#xfe :INVALID :empty-set :empty-set)
    (#xff :SELFDESTRUCT 1 0)
    ))

(defconst *mnemonics*
  (strip-cadrs *instructions*))

(defconst *valid-mnemonics*
  (remove-eq :invalid *mnemonics*))

(defund get-opcode (mnemonic insts)
  (declare (xargs :guard (and (member-eq mnemonic *mnemonics*)
                              (true-listp insts))))
  (if (endp insts)
      (er hard? 'get-opcode "Not found :~x0." mnemonic)
    (let ((entry (first insts)))
      (if (not (= 4 (len entry)))
          (er hard? 'get-opcode "bad entry :~x0." entry)
        (if (eq mnemonic (second entry))
            (first entry)
          (get-opcode mnemonic (rest insts)))))))

(defun get-mnemonic (opcode insts)
  (declare (xargs :guard (and (unsigned-byte-p 8 opcode)
                              (true-listp insts))))
  (if (endp insts)
      (er hard? 'get-mnemonic "Not found :~x0." opcode)
    (let ((entry (first insts)))
      (if (not (= 4 (len entry)))
          (er hard? 'get-mnemonic "bad entry :~x0." entry)
        (if (eql opcode (first entry))
            (second entry)
          (get-mnemonic opcode (rest insts)))))))

;todo: auto-gen?
(defconst *stop* (get-opcode :stop *instructions*))
(defconst *selfdestruct* (get-opcode :selfdestruct *instructions*))
(defconst *add* (get-opcode :add *instructions*))
(defconst *sub* (get-opcode :sub *instructions*))
(defconst *revert* (get-opcode :revert *instructions*))
(defconst *return* (get-opcode :return *instructions*))
(defconst *jump* (get-opcode :jump *instructions*))
(defconst *jumpi* (get-opcode :jumpi *instructions*))
(defconst *jumpdest* (get-opcode :jumpdest *instructions*))
(defconst *returndatacopy* (get-opcode :returndatacopy *instructions*))
(defconst *push1* (get-opcode :push1 *instructions*))
(defconst *push32* (get-opcode :push32 *instructions*))


;; Returns the numeric opcode
;"w"
(defund current-operation (mu i)
  (declare (xargs :guard (and (machine-statep mu)
                              (execution-environmentp i))))
  (let ((mu_pc (machine-state->pc mu))
        (i_b (execution-environment->bytecode i)))
    (if (< mu_pc (len i_b))
        (nth mu_pc i_b)
      *stop*)))

(defthm unsigned-byte-p-of-nth-when-byte-arrayp
  (implies (and (byte-arrayp lst)
                (<= 0 n)
                (< n (len lst)))
           (unsigned-byte-p 8 (nth n lst)))
  :hints (("Goal" :in-theory (e/d (byte-arrayp (:i nth))
                                  nil))))

(defthm unsigned-byte-p-of-current-operation
  (implies (and (execution-environmentp i)
                (machine-statep mu))
           (unsigned-byte-p 8 (current-operation mu i)))
  :hints (("Goal" :in-theory (e/d ( CURRENT-OPERATION)
                                  nil))))

;; number of stack items removed by the instruction
(defund delta (opcode)
  (declare (xargs :guard (unsigned-byte-p 8 opcode)))
  (let ((match (assoc opcode *instructions*)))
    (if match
        (third match)
      :empty-set)))

(defthm natp-of-delta
  (implies (not (equal (delta opcode) :empty-set))
           (natp (delta opcode)))
  :hints (("Goal" :in-theory (enable delta))))

(defthm rationalp-of-delta
  (implies (not (equal (delta opcode) :empty-set))
           (rationalp (delta opcode)))
  :hints (("Goal" :in-theory (enable delta))))

(defund alpha (opcode)
  (declare (xargs :guard (unsigned-byte-p 8 opcode)))
  (let ((match (assoc opcode *instructions*)))
    (if match
        (fourth match)
      :empty-set)))

(defthm natp-of-alpha
  (implies (not (equal (alpha opcode) :empty-set))
           (natp (alpha opcode)))
  :hints (("Goal" :in-theory (enable alpha))))

(defthm rationalp-of-alpha
  (implies (not (equal (alpha opcode) :empty-set))
           (rationalp (alpha opcode)))
  :hints (("Goal" :in-theory (enable alpha))))

(defthm equal-of-alpha-and-empty-set
  (equal (equal (alpha opcode) :empty-set)
         (equal (delta opcode) :empty-set))
  :hints (("Goal" :in-theory (enable alpha delta))))

;;todo: compare to :empty-set
(defun empty-set () (declare (xargs :guard t)) nil)

;; The length of the instruction, including the opcode and any push data
(defund inst-len (w)
  (declare (xargs :guard (unsigned-byte-p 8 w)))
  (if (and (<= *push1* w)
           (<= w *push32*))
      (+ (+ 1 (- w *push1*)) ;num bytes pushed
         1                   ;one for the opcode
         )
    1))

(defthm pos-of-inst-len
  (< 0 (inst-len w))
  :rule-classes (:rewrite :type-prescription :linear)
  :hints (("Goal" :in-theory (enable inst-len))))

(defthm integerp-of-inst-len
  (implies (integerp w)
           (integerp (inst-len w)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable inst-len))))

(defund next-inst (i w)
  (declare (xargs :guard (and (natp i) ;strengthen?
                              (unsigned-byte-p 8 w))))
  (+ i (inst-len w)))

  ;; (if (and (<= *push1* w)
  ;;          (<= w *push32*))
  ;;     (+ i w (- *push1*) 2)
  ;;   (+ i 1)))

(defthm next-inst-bound
  (implies (and (natp i)
                ;(unsigned-byte-p 8 w)
                )
           (< i (next-inst i w)))
  :rule-classes (:rewrite :linear)
  :hints (("Goal" :in-theory (enable next-inst))))

(defthm integerp-of-next-inst
  (implies (and (natp i)
                (unsigned-byte-p 8 w)
                )
           (integerp (next-inst i w)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable next-inst))))

(defund valid-jump-dests-aux (c i)
  (declare (xargs :guard (and (byte-arrayp c)
                              (natp i) ;strengthen?
                              )
                  :measure (+ 1 (nfix (- (len c) i)))
                  :hints (("Goal" :use ((:instance next-inst-bound
                                                   (w (nth i c)))
                                        (:instance integerp-of-next-inst
                                                  (w (nth i c))))
                           :in-theory (disable next-inst-bound integerp-of-next-inst)))))
  (if (or (not (mbt (natp i)))
          (>= i (len c))) ;todo: optimize by caching
      (empty-set)
    (if (eql *jumpdest* (nth i c))
        (cons i
              (valid-jump-dests-aux c (next-inst i (nth i c))))
      (valid-jump-dests-aux c (next-inst i (nth i c))))))

(defthm nat-listp-of-valid-jump-dests-aux
  (implies (natp i)
           (nat-listp (valid-jump-dests-aux c i)))
  :hints (("Goal" :in-theory (enable valid-jump-dests-aux))))

;; "D"
;; Find the valid jump destinations for the code C.
(defund valid-jump-dests (c)
  (declare (xargs :guard (byte-arrayp c)))
  (valid-jump-dests-aux c 0))

(defthm nat-listp-of-valid-jump-dests
  (nat-listp (valid-jump-dests c))
  :hints (("Goal" :in-theory (enable valid-jump-dests))))


;; "Z"
(defun exceptional-haltp (sigma mu i)
  (declare (xargs :guard (and (world-statep sigma)
                              (machine-statep mu)
                              (execution-environmentp i))
                  :guard-hints (("Goal" :use (:instance natp-of-alpha (opcode (current-operation mu i)))
                                 :in-theory (disable natp-of-alpha)))))
  (let ((w (current-operation mu i)))
    (or (< (machine-state->gas-available mu)
           (instruction-cost sigma mu i))
        (equal (delta w) :empty-set)
        (< (stack-size (machine-state->stack mu)) (delta w)) ;;stack underflow
        (and (eql w *jump*)
             (not (member (stack-item 0 mu) ;todo: be more abstract than nth
                          (valid-jump-dests ;todo: dont recompute?
                           (execution-environment->bytecode i)))))
        (and (eql w *jumpi*)
             (not (equal 0 (stack-item 1 mu)))
             (not (member (stack-item 0 mu) ;todo: be more abstract than nth
                          (valid-jump-dests ;todo: dont recompute?
                           (execution-environment->bytecode i)))))
        (and (eql w *returndatacopy*)
             (> (+ (stack-item 1 mu)
                   (stack-item 2 mu))
                0; fixme YP in contradictory on mu_o
                ))
        ;;stack overflow:
        (> (+ (stack-size (machine-state->stack mu))
              (- (delta w))
              (alpha w))
           1024)
        ;;fixme more
        )))

(defstub h-return (mu) t) ;fixme

; "H" (normal halting)
;; a byte array or :empty-set?
(defun output-data (mu i)
  (declare (xargs :guard (and (machine-statep mu)
                              (execution-environmentp i))))
  (let ((w (current-operation mu i)))
    (if (member w (list *return* *revert*))
        (h-return mu)
      (if (member w (list *stop* *selfdestruct*))
          nil
        :empty-set))))


;; These return (mv sigma mu a i).

(defun inc-pc (mu)
  (declare (xargs :guard (machine-statep mu)))
  (change-machine-state mu :pc (+ 1 (machine-state->pc mu))))

;todo: what if it overflows the 2^256 boundary?
(defthm machine-statep-of-inc-pc
  (implies (machine-statep mu)
           (machine-statep (inc-pc mu)))
  :hints (("Goal" :in-theory (enable inc-pc))))


;; This is for one-byte ops that are not jumps and that push a single result
;; onto the stack.
(defun def-simple-op-fn (mnemonic
                         result-to-push ;removal of the operands is handled according to delta
                         guard-hints
                         )
  (declare (xargs :guard (and (member-eq mnemonic *valid-mnemonics*))
                  :guard-hints (("Goal" :in-theory (enable acl2::memberp-of-cons-when-constant)))))
  (let* ((name (symbol-name mnemonic))
         (fn (acl2::pack-in-package-of-symbol 'def-simple-op-fn 'execute- name))
         (opcode (get-opcode mnemonic *instructions*))
         (delta (delta opcode))
         (alpha (alpha opcode))
         (guard-expr `(and (world-statep sigma)
                           (machine-statep mu)
                           (substatep a)
                           (execution-environmentp i)
                           (<= ,delta
                               (stack-size (machine-state->stack mu)))
                           (<= (stack-size (machine-state->stack mu))
                               ,(+ 1024 delta (- alpha))))))
    `(progn
       ;; Returns (mv sigma mu a i)
       (defund ,fn (sigma mu a i)
         (declare (xargs :guard ,guard-expr
                         ,@(and guard-hints
                                `(:guard-hints ,guard-hints))))
         (let* ((stack (machine-state->stack mu))
                (stack (popn ,delta stack))
                (stack (stack-push ,result-to-push stack))
                (mu (change-machine-state mu :stack stack))
                (mu (inc-pc mu)))
           (mv sigma mu a i)))

       (defthm ,(acl2::pack$ 'world-statep-of-mv-nth-0-of- fn)
         (implies ,guard-expr
                  (world-statep (mv-nth 0 (,fn sigma mu a i))))
         :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(acl2::pack$ 'machine-statep-of-mv-nth-1-of- fn)
         (implies ,guard-expr
                  (machine-statep (mv-nth 1 (,fn sigma mu a i))))
         :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(acl2::pack$ 'substatep-of-mv-nth-2-of- fn)
         (implies ,guard-expr
                  (substatep (mv-nth 2 (,fn sigma mu a i))))
         :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(acl2::pack$ 'execution-environmentp-of-mv-nth-3-of- fn)
         (implies ,guard-expr
                  (execution-environmentp (mv-nth 3 (,fn sigma mu a i))))
         :hints (("Goal" :in-theory (enable ,fn)))))))

(defmacro def-simple-op (mnemonic result-stack &key (guard-hints 'nil))
  (def-simple-op-fn mnemonic result-stack guard-hints))

;;;
;;; Semantic functions for each instruction
;;;

;; The semantic function for :stop.
;; no change to the stack.  the function output-data will detect the stop
;; instruction and cause execution to stop.
(defun execute-stop (sigma mu a i)
  (declare (xargs :guard (and (world-statep sigma)
                              (machine-statep mu)
                              (substatep a)
                              (execution-environmentp i))))
  (let* ((mu (inc-pc mu)))
    (mv sigma mu a i)))

;; The semantic function for :add.
(def-simple-op :add
  (bvplus 256
                (stack-item 0 mu)
                (stack-item 1 mu)))

;; The semantic function for :mul.
(def-simple-op :mul
  (bvmult 256
                (stack-item 0 mu)
                (stack-item 1 mu)))

;; The semantic function for :sub.
(def-simple-op :sub
  (bvminus 256
                 (stack-item 0 mu)
                 (stack-item 1 mu)))

;; The semantic function for :div.
(def-simple-op :div
  (if (equal 0 (stack-item 1 mu)) ;todo: consider chopping before comparing to 0
      0
    (bvdiv 256
                 (stack-item 0 mu)
                 (stack-item 1 mu))))

;; The semantic function for :sdiv.
;todo check
(def-simple-op :sdiv
  (if (equal 0 (stack-item 1 mu))
      0
    (acl2::sbvdiv 256
                  (stack-item 0 mu)
                  (stack-item 1 mu))))

;; The semantic function for :mod.
(def-simple-op :mod
  (if (equal 0 (stack-item 1 mu))
      0
    (bvmod 256
                 (stack-item 0 mu)
                 (stack-item 1 mu))))

;; Bit-vector version of the signum (sgn) function.  Returns 0, 1, or -1
;; according to whether X is zero, positive, or negative.
(defun bvsgn (size x)
  (declare (xargs :guard (and (integerp x)
                              (natp size))))
  (if (bvlt size x 0)
      -1
    (if (bvlt size 0 x)
        1
      0)))

(local (in-theory (enable acl2::bvp)))

(defthm equal-of-bv-to-sint-and-0
  (equal (equal (bv-to-sint 256 x) 0)
         (equal (bvchop 256 x) 0))
  :hints (("Goal" :in-theory (enable acl2::bv-to-sint))))

(defthm unsigned-byte-p-of-sint-to-bv
  (unsigned-byte-p 256 (acl2::sint-to-bv 256 x))
  :hints (("Goal" :in-theory (enable acl2::sint-to-bv))))

;(in-theory (disable acl2::mod-=-0))

(in-theory (disable signed-byte-p))

(defthm logext-256-when-non-negative
  (implies (<= 0 (acl2::logext 256 x))
           (equal (acl2::logext 256 x)
                  (bvchop 255 x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable acl2::logext-cases))))

(defthm logext-256-when-non-negative-2
  (implies (equal 0 (acl2::getbit 255 x))
           (equal (acl2::logext 256 x)
                  (bvchop 255 x)))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :hints (("Goal" :in-theory (enable acl2::logext-cases))))

;gen
(defthm <-of-logext-and-0
  (equal (< (ACL2::LOGEXT 256 x) 0)
         (not (equal 0 (acl2::getbit 255 x))))
  :hints (("Goal" :in-theory (enable acl2::logext-cases))))

;; (thm
;;  (implies (and (unsigned-byte-p 256 x)
;;                (not (equal 0 x)))
;;           (equal (< 0 (BVCHOP '255 x))
;;                  (not (equal

(defthm logext-negative-type
  (implies (EQUAL (ACL2::GETBIT 255 x) 1)
           (< (ACL2::LOGEXT 256 x) 0))
  :rule-classes :type-prescription)

;; The semantic function for :smod.
;todo: check
;todo: compare to sbvrem.
(def-simple-op :smod
  (if (equal 0 (bvchop 256 (stack-item 1 mu))) ;the chop should do nothing
      0
    (acl2::sint-to-bv
     256
     (* (bvsgn 256 (stack-item 0 mu))
        (mod (abs (bv-to-sint 256 (stack-item 0 mu)))
             (abs (bv-to-sint 256 (stack-item 1 mu)))))))
  :guard-hints (("Goal" :in-theory (e/d (n256p
                                         acl2::sintp
                                         acl2::bv-to-sint
                                         signed-byte-p
                                         acl2::<-of-mod
                                         ACL2::BVCAT
                                         acl2::logapp
                                         acl2::getbit
                                         acl2::logext-cases
                                         abs)
                                        (acl2::mod-of-minus-arg1
                                         acl2::mod-of-minus-arg2
                                         acl2::bvcat-of-getbit-and-x-adjacent
                                         acl2::bvcat-equal-rewrite-alt
                                         acl2::bvcat-equal-rewrite
                                         ACL2::BVCAT-RECOMBINE))
                 :use (:instance acl2::split-bv (x (stack-item 1 mu))
                                 (n 256)
                                 (m 255)))))


;; The semantic function for :addmod.
(def-simple-op :addmod
  (if (equal 0 (stack-item 2 mu))
      0
    (bvmod 256
                 (+ (stack-item 0 mu)
                    (stack-item 1 mu))
                 (stack-item 2 mu))))

;; The semantic function for :mulmod.
(def-simple-op :mulmod
  (if (equal 0 (stack-item 2 mu))
      0
    (bvmod 256
                 (* (stack-item 0 mu)
                    (stack-item 1 mu))
                 (stack-item 2 mu))))

;; The semantic function for :mulmod.
(def-simple-op :exp
  (bvchop 256
                 (expt (stack-item 0 mu)
                       (stack-item 1 mu))))

(defthm arith-helper-divide-by-8
  (equal (< '248 (BINARY-* '8 x))
         (< 31 x)))

(defthm <-when-bvlt
  (implies (and (bvlt 256 x k2)
                (<= k2 (+ -1 k))
                (unsigned-byte-p 256 x)
                (unsigned-byte-p 256 k2)
                (unsigned-byte-p 256 k1))
           (not (< k x)))
  :hints (("Goal" :in-theory (enable acl2::bvlt))))

;; This models the YP's subscript notation to extract bits. Note that the bit
;; numbering is the reverse of normal.  For this function, bit 0 is the most
;; significant bit and bit 255 the least significant.
(defun wordbit (n word)
  (declare (xargs :guard (and (natp n)
                              (< n 256)
                              (n256p word))))
  (acl2::getbit (- 255 n)
                word))

;; Convert a 256-bit value into a list of 32 bytes, in big-endian fashion, with
;; the most significant byte of the word listed first in the result, and so on.
;; todo: use the term "word" more instead of n256p?
(defun word-to-bytes (word)
  (declare (xargs :guard (n256p word)))
  (acl2::unpackbv 32 8 word))

;; Convert an array of 32 bytes into a 256-bit word, in big-endian fashoon,
;; with the first byte occupying the most significant bits of the result, and
;; so on.
(defun bytes-to-word (bytes)
  (declare (xargs :guard (b32p bytes)))
  (acl2::packbv 32 8 bytes))

;; The semantic function for :signextend.
;todo: check
;; Note that bit index 0 is the most significant
(def-simple-op :signextend
  (let* (;; i guess we add 1 because there must be at least 1 byte in order to
         ;; have a sign bit:
         (old-num-bytes (+ (stack-item 0 mu) 1)))
    (if (< 32 old-num-bytes) ;; no effect (exactly 32 also has no effect, but let's include it in the other case)
        (stack-item 1 mu)
      (let* (
             ;; This is index of the sign bit of the value in (stack-item 0 mu),
             ;; which is presumably less than 256-bits wide.
;             (t-var (- 256 (* 8 old-num-bytes))) ;; "t" ;; this can be at most 248 (the sign bit of the least significant byte), if it is 0 there is no effect
 ;            (sign-bit (- 256 t-var)) ;using our standard numbering system
             )
        (bvsx 256 (* 8 old-num-bytes) (stack-item 1 mu)))))
  ;; (if (bvle 256 31 (stack-item 0 mu))
  ;;     (stack-item 1 mu)
  ;;   (bvsx 256
  ;;               (* 8 (+ 1 (stack-item 0 mu)))
  ;;               (stack-item 1 mu)))
  :guard-hints (("Goal" :in-theory (enable n256p acl2::bvlt))))

(defthm execute-signextend-correct
  (implies (and (natp i)
                (<= i 255)
                (MACHINE-STATEP MU)
                (<= 2 (stack-size (machine-state->stack mu))))
           (let ((mu-prime (mv-nth 1 (execute-signextend sigma mu a i)))
                 (t-var (- 256 (* 8 (+ (stack-item 0 mu) 1)))))
             (equal (wordbit i (stack-item 0 mu-prime))
                    (if (<= i t-var)
                        (wordbit t-var (stack-item 1 mu))
                      (wordbit i (stack-item 1 mu))))))
  :hints (("Goal" :in-theory (enable execute-signextend stack-item
                                     ACL2::GETBIT-TOO-HIGH))))

;; The semantic function for :lt.
(def-simple-op :lt
  (acl2::bool-to-bit (bvlt 256 (stack-item 0 mu) (stack-item 1 mu))))

;; The semantic function for :gt.
(def-simple-op :gt
  (acl2::bool-to-bit (bvgt 256 (stack-item 0 mu) (stack-item 1 mu))))

;; The semantic function for :slt.
(def-simple-op :slt
  (acl2::bool-to-bit (acl2::sbvlt 256 (stack-item 0 mu) (stack-item 1 mu))))

;; The semantic function for :sgt.
(def-simple-op :sgt
  (acl2::bool-to-bit (acl2::sbvgt 256 (stack-item 0 mu) (stack-item 1 mu))))

;; The semantic function for :eq.
(def-simple-op :eq
  (acl2::bool-to-bit (equal (stack-item 0 mu) (stack-item 1 mu))))

;; The semantic function for :iszero.
(def-simple-op :iszero
  (acl2::bool-to-bit (equal 0 (stack-item 0 mu))))

;; The semantic function for :and.
(def-simple-op :and
  (bvand 256 (stack-item 0 mu) (stack-item 1 mu)))

;; The semantic function for :or.
(def-simple-op :or
  (bvor 256 (stack-item 0 mu) (stack-item 1 mu)))

;; The semantic function for :xor.
(def-simple-op :xor
  (bvxor 256 (stack-item 0 mu) (stack-item 1 mu)))

;; Correctness of the :xor operation
;; todo: add more validation theorems like this
(defthm execute-xor-correct
  (implies (and (natp i)
                (<= i 255))
           (let ((mu-prime (mv-nth 1 (execute-xor sigma mu a i))))
             (equal (wordbit i (stack-item 0 mu-prime))
                    (acl2::bitxor (wordbit i (stack-item 0 mu))
                                  (wordbit i (stack-item 1 mu))))))
  :hints (("Goal" :in-theory (enable execute-xor stack-item))))

;; The semantic function for :not.
(def-simple-op :not
  (bvnot 256 (stack-item 0 mu)))

;; Correctness of the :not operation
(defthm execute-not-correct
  (implies (and (natp i)
                (<= i 255))
           (let ((mu-prime (mv-nth 1 (execute-not sigma mu a i))))
             (equal (wordbit i (stack-item 0 mu-prime))
                    (if (equal (wordbit i (stack-item 0 mu)) 0)
                        1
                      0))))
  :hints (("Goal" :in-theory (enable execute-not stack-item))))

;; The semantic function for :byte.
(def-simple-op :byte
  (let ((byte-num (stack-item 0 mu)))
    (if (< byte-num 32)
        ;; The result goes into the most-significant byte (why?):
        (bvcat 8 (nth byte-num (word-to-bytes (stack-item 1 mu)))
                     248 0)
      0)))

(defthm execute-byte-correct
  (implies (and (natp i)
                (<= i 255)
                ;;todo: have def-simple-op generate a precondition and call it here?
                (machine-statep mu)
                (<= 2 (stack-size (machine-state->stack mu)))
                )
           (let ((mu-prime (mv-nth 1 (execute-byte sigma mu a i))))
             (equal (wordbit i (stack-item 0 mu-prime))
                    (if (and (< i 8)
                             (< (stack-item 0 mu) 32))
                        (wordbit (+ i (* 8 (stack-item 0 mu)))
                                      (stack-item 1 mu))
                      0))))
  :hints (("Goal" :in-theory (enable execute-byte stack-item
                                     ACL2::GETBIT-OF-SLICE-TOO-HIGH))))

;; The semantic function for :address.
(def-simple-op :address
  (pack-address (execution-environment->owner-address i)))

;; The semantic function for :balance.
(def-simple-op :balance
  (let* ((address-number (mod (stack-item 0 mu) (expt 2 160)))
         (address (unpack-address address-number))
         (maybe-account (get-account sigma address)))
    (if (eq maybe-account :empty-set)
        0
      (account-state->balance maybe-account))))

;; The semantic function for :origin.
(def-simple-op :origin
  (pack-address (execution-environment->sender-address i)))

;; The semantic function for :caller.
(def-simple-op :caller
  (pack-address (execution-environment->causer-account i))) ;todo rename this thing to caller-address?

;; The semantic function for :callvalue.
(def-simple-op :callvalue
  (execution-environment->value i))

;; ;todo: make this more abstract
;; ;todo: we know what delta is, from the table
;; (defun execute-add (sigma mu a i ;delta ;alpha
;;                           )
;;   (declare (xargs :guard (and (world-statep sigma)
;;                               (machine-statep mu)
;;                               (substatep a)
;;                               (execution-environmentp i)
;;                               ;(natp delta)
;;                               ;;(natp alpha)
;;                               (<= 2 ;delta
;;                                   (stack-size (machine-state->stack mu)))
;;                               )))
;;   (let* ((stack (machine-state->stack mu)) ;boilerplate
;;          (stack (popn 2 ;delta
;;                       stack)) ;boilerplate
;;          (stack (stack-push (bvplus 256
;;                                           (stack-item 0 mu)
;;                                           (stack-item 1 mu))
;;                             stack))
;;          (mu (change-machine-state mu :stack stack))
;;          (mu (inc-pc mu)))
;;     (mv sigma mu a i)))

;; "O"
;; Returns (mv world-state machine-state substate execution-environment)
(defun step-machine (sigma mu a i)
  (declare (xargs :guard (and (world-statep sigma)
                              (machine-statep mu)
                              (substatep a)
                              (execution-environmentp i)
                              (not (equal (delta (current-operation mu i)) :empty-set)) ;valid instruction
                              (<= (delta (current-operation mu i)) (stack-size (machine-state->stack mu)))
                              (<= (stack-size (machine-state->stack mu))
                                  (+ 1024 (+ (delta (current-operation mu i)))
                                     (- (alpha (current-operation mu i))))))))
  (let* ((opcode (current-operation mu i)))
    (case opcode
      ;;todo: auto gen these cases?:
      (#x00 (execute-stop sigma mu a i))
      (#x01 (execute-add sigma mu a i))
      (#x02 (execute-mul sigma mu a i))
      (#x03 (execute-sub sigma mu a i))
      (#x04 (execute-DIV sigma mu a i))
      (#x05 (execute-SDIV sigma mu a i))
      (#x06 (execute-MOD sigma mu a i))
      (#x07 (execute-SMOD sigma mu a i))
      (#x08 (execute-ADDMOD sigma mu a i))
      (#x09 (execute-MULMOD sigma mu a i))
      (#x0a (execute-EXP sigma mu a i))
      ;; (#x0b (execute-SIGNEXTEND sigma mu a i))
      (#x10 (execute-LT sigma mu a i))
      (#x11 (execute-GT sigma mu a i))
      (#x12 (execute-SLT sigma mu a i))
      (#x13 (execute-SGT sigma mu a i))
      (#x14 (execute-EQ sigma mu a i))
      (#x15 (execute-ISZERO sigma mu a i))
      (#x16 (execute-AND sigma mu a i))
      (#x17 (execute-OR sigma mu a i))
      (#x18 (execute-XOR sigma mu a i))
      (#x19 (execute-NOT sigma mu a i))
      (#x1a (execute-BYTE sigma mu a i))
      ;; (#x20 (execute-sha3 sigma mu a i))
      (#x30 (execute-address sigma mu a i))
      (#x31 (execute-balance sigma mu a i))
      (#x32 (execute-ORIGIN sigma mu a i))
      (#x33 (execute-CALLER sigma mu a i))
      (#x34 (execute-CALLVALUE sigma mu a i))
      ;; (#x35 (execute-CALLDATALOAD sigma mu a i))
      ;; (#x36 (execute-CALLDATASIZE sigma mu a i))
      ;; (#x37 (execute-CALLDATACOPY sigma mu a i))
      ;; (#x38 (execute-CODESIZE sigma mu a i))
      ;; (#x39 (execute-CODECOPY sigma mu a i))
      ;; (#x3a (execute-GASPRICE sigma mu a i))
      ;; (#x3b (execute-EXTCODESIZE sigma mu a i))
      ;; (#x3c (execute-EXTCODECOPY sigma mu a i))
      ;; (#x3d (execute-RETURNDATASIZE sigma mu a i))
      ;; (#x3e (execute-RETURNDATACOPY sigma mu a i))
      ;; (#x40 (execute-BLOCKHASH sigma mu a i))
      ;; (#x41 (execute-COINBASE sigma mu a i))
      ;; (#x42 (execute-TIMESTAMP sigma mu a i))
      ;; (#x43 (execute-NUMBER sigma mu a i))
      ;; (#x44 (execute-DIFFICULTY sigma mu a i))
      ;; (#x45 (execute-GASLIMIT sigma mu a i))
      ;; (#x50 (execute-POP sigma mu a i))
      ;; (#x51 (execute-MLOAD sigma mu a i))
      ;; (#x52 (execute-MSTORE sigma mu a i))
      ;; (#x53 (execute-MSTORE8 sigma mu a i))
      ;; (#x54 (execute-SLOAD sigma mu a i))
      ;; (#x55 (execute-SSTORE sigma mu a i))
      ;; (#x56 (execute-JUMP sigma mu a i))
      ;; (#x57 (execute-JUMPI sigma mu a i))
      ;; (#x58 (execute-PC sigma mu a i))
      ;; (#x59 (execute-MSIZE sigma mu a i))
      ;; (#x5a (execute-GAS sigma mu a i))
      ;; (#x5b (execute-JUMPDEST sigma mu a i))
      ;; (#x60 (execute-PUSH1 sigma mu a i))
      ;; (#x61 (execute-PUSH2 sigma mu a i))
      ;; (#x62 (execute-PUSH3 sigma mu a i))
      ;; (#x63 (execute-PUSH4 sigma mu a i))
      ;; (#x64 (execute-PUSH5 sigma mu a i))
      ;; (#x65 (execute-PUSH6 sigma mu a i))
      ;; (#x66 (execute-PUSH7 sigma mu a i))
      ;; (#x67 (execute-PUSH8 sigma mu a i))
      ;; (#x68 (execute-PUSH9 sigma mu a i))
      ;; (#x69 (execute-PUSH10 sigma mu a i))
      ;; (#x6a (execute-PUSH11 sigma mu a i))
      ;; (#x6b (execute-PUSH12 sigma mu a i))
      ;; (#x6c (execute-PUSH13 sigma mu a i))
      ;; (#x6d (execute-PUSH14 sigma mu a i))
      ;; (#x6e (execute-PUSH15 sigma mu a i))
      ;; (#x6f (execute-PUSH16 sigma mu a i))
      ;; (#x70 (execute-PUSH17 sigma mu a i))
      ;; (#x71 (execute-PUSH18 sigma mu a i))
      ;; (#x72 (execute-PUSH19 sigma mu a i))
      ;; (#x73 (execute-PUSH20 sigma mu a i))
      ;; (#x74 (execute-PUSH21 sigma mu a i))
      ;; (#x75 (execute-PUSH22 sigma mu a i))
      ;; (#x76 (execute-PUSH23 sigma mu a i))
      ;; (#x77 (execute-PUSH24 sigma mu a i))
      ;; (#x78 (execute-PUSH25 sigma mu a i))
      ;; (#x79 (execute-PUSH26 sigma mu a i))
      ;; (#x7a (execute-PUSH27 sigma mu a i))
      ;; (#x7b (execute-PUSH28 sigma mu a i))
      ;; (#x7c (execute-PUSH29 sigma mu a i))
      ;; (#x7d (execute-PUSH30 sigma mu a i))
      ;; (#x7e (execute-PUSH31 sigma mu a i))
      ;; (#x7f (execute-PUSH32 sigma mu a i))
      ;; (#x80 (execute-DUP1 sigma mu a i))
      ;; (#x81 (execute-DUP2 sigma mu a i))
      ;; (#x82 (execute-DUP3 sigma mu a i))
      ;; (#x83 (execute-DUP4 sigma mu a i))
      ;; (#x84 (execute-DUP5 sigma mu a i))
      ;; (#x85 (execute-DUP6 sigma mu a i))
      ;; (#x86 (execute-DUP7 sigma mu a i))
      ;; (#x87 (execute-DUP8 sigma mu a i))
      ;; (#x88 (execute-DUP9 sigma mu a i))
      ;; (#x89 (execute-DUP10 sigma mu a i))
      ;; (#x8a (execute-DUP11 sigma mu a i))
      ;; (#x8b (execute-DUP12 sigma mu a i))
      ;; (#x8c (execute-DUP13 sigma mu a i))
      ;; (#x8d (execute-DUP14 sigma mu a i))
      ;; (#x8e (execute-DUP15 sigma mu a i))
      ;; (#x8f (execute-DUP16 sigma mu a i))
      ;; (#x90 (execute-SWAP1 sigma mu a i))
      ;; (#x91 (execute-SWAP2 sigma mu a i))
      ;; (#x92 (execute-SWAP3 sigma mu a i))
      ;; (#x93 (execute-SWAP4 sigma mu a i))
      ;; (#x94 (execute-SWAP5 sigma mu a i))
      ;; (#x95 (execute-SWAP6 sigma mu a i))
      ;; (#x96 (execute-SWAP7 sigma mu a i))
      ;; (#x97 (execute-SWAP8 sigma mu a i))
      ;; (#x98 (execute-SWAP9 sigma mu a i))
      ;; (#x99 (execute-SWAP10 sigma mu a i))
      ;; (#x9a (execute-SWAP11 sigma mu a i))
      ;; (#x9b (execute-SWAP12 sigma mu a i))
      ;; (#x9c (execute-SWAP13 sigma mu a i))
      ;; (#x9d (execute-SWAP14 sigma mu a i))
      ;; (#x9e (execute-SWAP15 sigma mu a i))
      ;; (#x9f (execute-SWAP16 sigma mu a i))
      ;; (#xa0 (execute-LOG0 sigma mu a i))
      ;; (#xa1 (execute-LOG1 sigma mu a i))
      ;; (#xa2 (execute-LOG2 sigma mu a i))
      ;; (#xa3 (execute-LOG3 sigma mu a i))
      ;; (#xa4 (execute-LOG4 sigma mu a i))
      ;; (#xf0 (execute-CREATE sigma mu a i))
      ;; (#xf1 (execute-CALL sigma mu a i))
      ;; (#xf2 (execute-CALLCODE sigma mu a i))
      ;; (#xf3 (execute-RETURN sigma mu a i))
      ;; (#xf4 (execute-DELEGATECALL sigma mu a i))
      ;; (#xfa (execute-STATICCALL sigma mu a i))
      ;; (#xfd (execute-REVERT sigma mu a i))
      ;; (#xfe (execute-INVALID sigma mu a i))
      ;; (#xff (execute-SELFDESTRUCT sigma mu a i))
      (otherwise (prog2$ (er hard? 'step-machine "Unrecognzied instruction ~x0." opcode)
                         (mv sigma mu a i))))))

(defun initial-machine-state (gas)
  (declare (xargs :guard (natp gas)))
  (machine-state gas
                 0
                 (initial-memory)
                 0
                 (empty-stack)
                 ;todo: (130) talks about mu_o -- what is that?
                 ))

;"X"
;; Returns (mv sigma mu a i o)
;todo: don't return i if we willl just ignore it.
(defun run-machine (steps ;force termination
                    sigma mu a i)
  (declare (xargs :guard (and (natp steps)
                              (world-statep sigma)
                              (machine-statep mu)
                              (substatep a)
                              (execution-environmentp i))))
  (if (zp steps)
      (prog2$ (er hard? 'run-machine "No steps left!")
              (mv sigma mu a i nil))
    (if (exceptional-haltp sigma mu i)
        (mv :empty-set mu (initial-substate) i
            :empty-set ; type?
            )
      (let ((w (current-operation mu i))
            (o (output-data mu i)))
        (if (equal w *revert*)
            (mv :empty-set
                (change-machine-state mu :gas-available (- (machine-state->gas-available mu)
                                                           (instruction-cost sigma mu i)))
                (initial-substate)
                i
                o)
          (if (not (eq :empty-set o)) ;output data present
              (mv-let (sigma mu a i)  ;todo: YP is confusing here
                (step-machine sigma mu a i)
                (mv sigma mu a i o))
            (mv-let (sigma mu a i) ;todo: YP is confusing here
              (step-machine sigma mu a i)
              (run-machine (+ -1 steps) sigma mu a i))))))))

(defthm machine-statep-of-mv-nth-1-of-run-machine
  (implies (and (machine-statep mu)
                (execution-environmentp i)
                (world-statep sigma)
                (substatep a))
           (machine-statep (mv-nth 1 (run-machine steps sigma mu a i)))))


;; TODO in (121) xi only has 3 args!
;; Returns (mv world-state remaining-gas substate output)
(defun xi (world-state gas execution-environment transaction)
  (declare (xargs :guard (and (world-statep world-state)
                              (natp gas) ;??
                              (execution-environmentp execution-environment)
                              (transactionp transaction))))
  (declare (ignore transaction)) ;todo
  (mv-let (sigma mu a i o)
    (run-machine 10000000 ;todo
                 world-state
                 (initial-machine-state gas)
                 (initial-substate)
                 execution-environment)
    (declare (ignore i))
    (mv sigma
        (machine-state->gas-available mu)
        a
        o)))


;;;;;;;;;;;;;;;;;;;

;; TODO: formalize (2-4)

;; large upsilon
;; Returns a new world-state.
;; TODO
(defstub next-state (world-state transaction) t)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Runs CODE on STACK.
;; Returns (mv sigma mu a i o).
(defun simple-run-core (code stack)
  (declare (xargs :guard (and (byte-arrayp code)
                              (stackp stack))))
  (run-machine 1000000 ;todo
               (empty-world-state)
               (machine-state 100000 0 nil 0
                              stack
                              )
               (initial-substate)
               (execution-environment (0-address)
                                      (0-address)
                                      0
                                      nil
                                      (0-address)
                                      0
                                      code
                                      (block-header 0 0 (0-address) 0 0 0 nil 0 0 0 0 0 nil 0 0)
                                      0
                                      nil)))

;; Projects out the stack after running CODE on STACK.
(defun simple-run (code stack)
  (declare (xargs :guard (and (byte-arrayp code)
                              (stackp stack))))
  (mv-let (sigma mu a i o)
    (simple-run-core code stack)
    (declare (ignore sigma a i o))
    (machine-state->stack mu)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun disassemble-evm-code-aux (i c)
  (declare (xargs :guard (and (natp i)
                              (byte-arrayp c))
                  :measure (len c)))
  (if (or (not (mbt (byte-arrayp c)))
          (endp c))
      nil
    (let* ((opcode (first c))
           (mnemonic (get-mnemonic opcode *instructions*))
           (inst-len (inst-len opcode))
           (info (if (and (<= *push1* opcode)
                          (<= opcode *push32*))
                     (list mnemonic (take (+ -1 inst-len) (cdr c)))
                   mnemonic)))
      (cons (list i info)
            (disassemble-evm-code-aux (+ 1 i) (nthcdr inst-len c))))))

;; Given the program as a list of bytes, return an array mapping program locations to instruction mnemonics.
(defun disassemble-evm-code (c)
  (declare (xargs :guard (byte-arrayp c)))
  (disassemble-evm-code-aux 0 c))

;(disassemble-evm-code '(#x60 #x01 #x60 #x17 #x03 #x60 #x00 #x55))

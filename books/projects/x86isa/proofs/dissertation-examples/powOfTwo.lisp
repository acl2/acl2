;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "programmer-level-mode/programmer-level-memory-utils" :dir :proof-utils :ttags :all)

(include-book "centaur/gl/gl" :dir :system)
(include-book "centaur/bitops/ihs-extensions" :dir :system)
(local (include-book "centaur/bitops/signed-byte-p" :dir :system))

;; ======================================================================

;; bool isPowerOfTwo? (unsigned int v) {
;;   bool f;
;;   f = v && !(v & (v - 1));
;;   return f;
;; }


;; GCC O2 Optimization
;; 0000000100000ec0 <_isPowerOfTwo?>:
;;    100000ec0:	55                      push   %rbp
;;    100000ec1:	48 89 e5                mov    %rsp,%rbp
;;    100000ec4:	85 ff                   test   %edi,%edi
;;    100000ec6:	74 0a                   je     100000ed2 <_isPowerOfTwo?+0x12>
;;    100000ec8:	8d 47 ff                lea    -0x1(%rdi),%eax
;;    100000ecb:	85 c7                   test   %eax,%edi
;;    100000ecd:	0f 94 c0                sete   %al
;;    100000ed0:	eb 02                   jmp    100000ed4 <_isPowerOfTwo?+0x14>
;;    100000ed2:	31 c0                   xor    %eax,%eax
;;    100000ed4:	5d                      pop    %rbp
;;    100000ed5:	c3                      retq
;;    100000ed6:	66 2e 0f 1f 84 00 00    nopw   %cs:0x0(%rax,%rax,1)
;;    100000edd:	00 00 00

(defconst *program*
  '(
    #x55           ;; push   %rbp
    #x48 #x89 #xe5 ;; mov    %rsp,%rbp
    #x85 #xff      ;; test   %edi,%edi
    #x74 #x0a      ;; je     <_isPowerOfTwo?+0x12>
    #x8d #x47 #xff ;; lea    -0x1(%rdi),%eax
    #x85 #xc7      ;; test   %eax,%edi
    #x0f #x94 #xc0 ;; sete   %al
    #xeb #x02      ;; jmp    <_isPowerOfTwo?+0x14>
    #x31 #xc0      ;; xor    %eax,%eax
    #x5d           ;; pop    %rbp
    #xc3           ;; retq
    ))

(encapsulate
  ()
  (local (include-book "arithmetic-5/top" :dir :system))

  (defun power-of-2-p (x)
    (if (zp x)
        nil
      (if (equal x 1)
          t
        (if (zp (mod x 2))
            (power-of-2-p (floor x 2))
          nil))))

  (defthm power-of-2-p-returns-t-for-x=2^n
    ;; Every number x == 2^n, where n is a natural number,
    ;; satisfies power-of-2-p.
    (implies (and (natp n)
                  (equal x (expt 2 n)))
             (power-of-2-p x))
    :hints (("Goal" :in-theory (e/d* (expt) ())))))

(def-gl-thm program-effects-helper-1
  :hyp (and (unsigned-byte-p 32 x)
            (power-of-2-p x))
  :concl (equal (logand x (+ -1 x)) 0)
  :g-bindings
  `((x    (:g-number ,(gl-int 0 1 33)))))

(def-gl-thm program-effects-helper-2
  :hyp (and (unsigned-byte-p 32 x)
            (not (equal x 0))
            (not (power-of-2-p x)))
  :concl (equal (equal (logand x (+ -1 x)) 0) nil)
  :g-bindings
  `((x    (:g-number ,(gl-int 0 1 33)))))

(def-gl-thm power-of-2-p-result-helper
  :hyp (and (unsigned-byte-p 32 x)
            (power-of-2-p x))
  :concl (equal (loghead 8 (logior 1 (logext 64 (bitops::logsquash 8 (+ -1 x)))))
                1)
  :g-bindings
  `((x    (:g-number ,(gl-int 0 1 33)))))

;; ======================================================================

(defun-nx preconditions (x86)
  (and
   ;; The x86 state is well-formed.
   (x86p x86)
   ;; Alignment checking is turned off.
   (not (alignment-checking-enabled-p x86))
   ;; The model is operating in the programmer-level mode.
   (programmer-level-mode x86)
   ;; The program is located at linear addresses ranging from (rip
   ;; x86) to (+ -1 (len *program*) (rip x86)).
   (program-at (create-canonical-address-list (len *program*) (rip x86))
               *program* x86)
   ;; The addresses where the program is located are canonical.
   (canonical-address-p (rip x86))
   (canonical-address-p (+ (len *program*) (rip x86)))
   ;; The initial state is error-free.
   (equal (ms x86) nil)
   (equal (fault x86) nil)
   ;; Stack addresses are canonical.
   (canonical-address-p (+ -8 (xr :rgf *rsp* x86)))
   (canonical-address-p (xr :rgf *rsp* x86))
   (canonical-address-p (+ 8 (xr :rgf *rsp* x86)))
   ;; Return address is canonical.
   (canonical-address-p
    (logext
     64
     (combine-bytes
      (mv-nth 1
              (rb (create-canonical-address-list 8 (xr :rgf *rsp* x86))
                  :r x86)))))
   ;; Stack and program are disjoint.
   (disjoint-p
    (create-canonical-address-list
     (len *program*) (xr :rip 0 x86))
    (create-canonical-address-list
     8 (+ -8 (xr :rgf *rsp* x86))))
   (unsigned-byte-p 32 (rgfi *rdi* x86))))

(defun is-power-of-2-clock () 10)

(defun is-not-power-of-2-clock (x)
  (if (zp x) 7 10))

(defthm power-of-2-p-result
  (implies (and (preconditions x86)
                (power-of-2-p (rgfi *rdi* x86)))
           (equal (loghead 8 (xr :rgf *rax* (x86-run (is-power-of-2-clock) x86)))
                  1))
  :hints (("Goal"
           :do-not-induct t
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             jcc/cmovcc/setcc-spec
                             gpr-and-spec-4
                             gpr-xor-spec-4

                             top-level-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr08
                             wr32
                             wr64
                             rr32
                             rr64
                             rm32
                             rm64
                             wm32
                             wm64
                             rr32
                             x86-operand-from-modr/m-and-sib-bytes
                             rim-size
                             rim32
                             n32-to-i32
                             n64-to-i64
                             rim08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             ;; Flags
                             write-user-rflags
                             zf-spec)
                            (create-canonical-address-list
                             (create-canonical-address-list))))))

(defthm not-power-of-2-p-result
  (implies (and (preconditions x86)
                (not (power-of-2-p (rgfi *rdi* x86))))
           (equal (loghead
                   8
                   (xr :rgf *rax*
                       (x86-run (is-not-power-of-2-clock (rgfi *rdi* x86)) x86)))
                  0))
  :hints (("Goal"
           :do-not-induct t
           :cases (equal (rgfi *rdi* x86) 0)
           :in-theory (e/d* (instruction-decoding-and-spec-rules

                             jcc/cmovcc/setcc-spec
                             gpr-and-spec-4
                             gpr-xor-spec-4

                             top-level-opcode-execute
                             !rgfi-size
                             x86-operand-to-reg/mem
                             wr08
                             wr32
                             wr64
                             rr32
                             rr64
                             rm32
                             rm64
                             wm32
                             wm64
                             rr32
                             x86-operand-from-modr/m-and-sib-bytes
                             rim-size
                             rim32
                             n32-to-i32
                             n64-to-i64
                             rim08
                             two-byte-opcode-decode-and-execute
                             x86-effective-addr
                             ;; Flags
                             write-user-rflags
                             zf-spec)
                            (create-canonical-address-list
                             (create-canonical-address-list))))))

;; ======================================================================

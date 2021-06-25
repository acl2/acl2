;; Original Author: Dmitry Nadezhin

(in-package "X86ISA")
(include-book "std/util/defrule" :dir :system)
(include-book "projects/x86isa/proofs/utilities/app-view/top" :dir :system)

(include-book "tools/with-arith5-help" :dir :system)
(local (acl2::allow-arith5-help))

;; ======================================================================

; Local lemma

(local
 (acl2::with-arith5-help
  (defrule n64-to-i64-as-logext
    (equal (n64-to-i64 (n64 addr))
           (logext 64 addr)))))

(local
 (defrule logand-0
   (equal (logand x 0) 0)
   :enable logand))

; This is an instruction which has both 1-byte displacement and 1-byte
; immediate. Suppose that 1-byte immediate is-not at canonical-address.
; Then model should raise an exception about immediate.
; Let's check it.

(defconst *test_code*
  '(#x80 #x45 #x02)) ; #x?? ; addb [rbp+2],?? 

(defun test-state (x86)
  (declare (xargs :stobjs (x86)))
  (let ((rip (rip x86)))
    (and (x86p x86)
         (equal (ms x86) nil)
         (equal (fault x86) nil)
         (app-view x86)
         (canonical-address-p rip)
         (canonical-address-p (+ -1 rip (len *test_code*)))
         (not (canonical-address-p (+ rip (len *test_code*))))
         (program-at (create-canonical-address-list
                      (len *test_code*) rip)
                     *test_code*
                     x86))))

(defun test-state-1 (x86)
  (declare (xargs :stobjs (x86)))
  (and (test-state x86)
       (canonical-address-p (logext 64 (+ 2 (rgfi *rbp* x86))))))

(defun test-state-2 (x86)
  (declare (xargs :stobjs (x86)))
  (and (test-state x86)
       (not (canonical-address-p (logext 64 (+ 2 (rgfi *rbp* x86)))))))

; Suppose that [rbp+2] is a canonical-address-p.
; Model aborts with a message "temp-rip-not-canonical" as expected.

(defrule test-1-thm
  (b* ((start-rip (xr :rip nil x86))
       (temp-rip (+ 3 start-rip))
       (x86-new (x86-fetch-decode-execute x86)))
    (implies
     (test-state-1 x86)
     (equal
      x86-new
      (xw :ms nil
          `((X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP-TEST-E-I
             :rip ,start-rip
             :temp-rip-not-canonical ,temp-rip))
          x86))))
  :enable (x86-fetch-decode-execute
           x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
           x86-operand-from-modr/m-and-sib-bytes
           x86-effective-addr)
  :disable (n64 n64-to-i64 logext)
  :rule-classes ())

; Suppose that [rbp+2] is a not canonical-address-p.
; Model aborts with a message
; "x86-operand-from-modr/m-and-sib-bytes-non-canonical-address-encountered".
; I expect here the same message "temp-rip-not-canonical" as in previous theorem.

(defrule test-2-thm
  (b* ((start-rip (xr :rip nil x86))
       (x86-new (x86-fetch-decode-execute x86)))
    (implies
     (test-state-2 x86)
     (equal
      x86-new
      (xw :ms nil
          `((x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
             :rip ,start-rip
             :x86-operand-from-modr/m-and-sib-bytes
             x86-operand-from-modr/m-and-sib-bytes-non-canonical-address-encountered))
          x86))))
  :enable (x86-fetch-decode-execute
           x86-add/adc/sub/sbb/or/and/xor/cmp-test-E-I
           x86-operand-from-modr/m-and-sib-bytes
           x86-effective-addr)
  :disable (n64 n64-to-i64 logext)
  :rule-classes ())

;; ======================================================================

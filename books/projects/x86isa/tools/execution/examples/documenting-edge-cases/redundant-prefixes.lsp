;; Original Author: Dmitry Nadezhin
;; Some edits by Shilpi Goel

(in-package "X86ISA")
(include-book "std/util/defrule" :dir :system)
(include-book "projects/x86isa/proofs/utilities/app-view/top" :dir :system)

;; ======================================================================

(defconst *test_code*
  '(#xf0 #xf0 #xf0 #xf0 #xf0 #x00 #x00))

(defrule get-prefixes-opener-lemma-group-1-prefix-redundant
  (implies (and (app-view x86)
                (let* ((flg (mv-nth 0 (rm08 start-rip :x x86)))
                       (prefix-byte-group-code
                        (get-one-byte-prefix-array-code
                         (mv-nth 1 (rm08 start-rip :x x86)))))
                  (and (not flg) ;; No error in reading a byte
                       (equal prefix-byte-group-code 1)))
                (equal (prefixes-slice :group-1-prefix prefixes)
                       (mv-nth 1 (rm08 start-rip :x x86)))
                (not (zp cnt))
                (canonical-address-p (1+ start-rip)))
           (equal (get-prefixes start-rip prefixes cnt x86)
                  (get-prefixes (1+ start-rip)
                                (!prefixes-slice :group-1-prefix
                                                 (mv-nth 1 (rm08 start-rip :x x86))
                                                 prefixes)
                                (1- cnt) x86)))
  :in-theory (e/d (rb) ())
  :expand (get-prefixes start-rip prefixes cnt x86))

(defrule test-thm
  (implies
   (and (x86p x86)
        (equal (ms x86) nil)
        (equal (fault x86) nil)
        (app-view x86)
        (canonical-address-p (rip x86))
        (canonical-address-p (+ (rip x86) (len *test_code*)))
        (program-at (create-canonical-address-list
                     (len *test_code*) (rip x86))
                    *test_code*
                    x86))
   (equal (x86-fetch-decode-execute x86)
          (X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G 0 (XR :RIP 0 X86)
                                                       (+ 7 (XR :RIP 0 X86))
                                                       3845 0 0 0 0 X86)))
  :enable (x86-fetch-decode-execute)
  :rule-classes ())

;; ======================================================================

;; Concrete execution examples:

(b*
    ;; Poised to execute: #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #x00 #x00
    ;; (legal instruction with 13 redundant lock prefixes, #x00 modr/m byte, and #x00 opcode)
    ((start-rip 0)
     (x86 (!ms nil x86))
     (x86 (!fault nil x86))
     (x86 (!app-view t x86))
     (x86 (!rip start-rip x86))
     ((mv flg0 x86)
      (wm64      start-rip  (combine-bytes '(#xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0)) x86))
     ((mv flg1 x86)
      (wm64 (+ 8 start-rip) (combine-bytes '(#xF0 #xF0 #xF0 #xF0 #xF0               )) x86))
     ((when (or flg0 flg1)) x86)
     (x86 (x86-fetch-decode-execute x86))
     (- (cw "~% rip: ~x0 ms: ~x1~%" (rip x86) (ms x86))))
  x86)
;; Prints: rip: 15 ms: NIL

(b*
    ;; Poised to execute: #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #x00 #x00
    ;; (illegal instruction with 14 redundant lock prefixes)
    ((start-rip 0)
     (x86 (!ms nil x86))
     (x86 (!fault nil x86))
     (x86 (!app-view t x86))
     (x86 (!rip start-rip x86))
     ((mv flg0 x86)
      (wm64      start-rip  (combine-bytes '(#xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0 #xF0)) x86))
     ((mv flg1 x86)
      (wm64 (+ 8 start-rip) (combine-bytes '(#xF0 #xF0 #xF0 #xF0 #xF0 #xF0          )) x86))
     ((when (or flg0 flg1)) x86)
     (x86 (x86-fetch-decode-execute x86))
     (- (cw "~% rip: ~x0 ms: ~x1~%" (rip x86) (ms x86))))
  x86)
;; Prints: rip: 0 ms: ((X86-ADD/ADC/SUB/SBB/OR/AND/XOR/CMP/TEST-E-G :RIP 0 :INSTRUCTION-LENGTH 16))

(b*
    ;; Poised to execute: #xF0 #xF3 #x00 #x00
    ;; (instruction with two group 1 prefixes --- the x86 model doesn't handle these kinds of situations)
    ((start-rip 0)
     (x86 (!ms nil x86))
     (x86 (!fault nil x86))
     (x86 (!app-view t x86))
     (x86 (!rip start-rip x86))
     ((mv flg0 x86)
      (wm64      start-rip  (combine-bytes '(#xF0 #xF3)) x86))
     ((when flg0) x86)
     (x86 (x86-fetch-decode-execute x86))
     (- (cw "~% rip: ~x0 ms: ~x1~%" (rip x86) (ms x86))))
  x86)
;; Prints: rip: 0 ms: ((X86-FETCH-DECODE-EXECUTE :RIP 0 :ERROR-IN-READING-PREFIXES T))

;; ======================================================================

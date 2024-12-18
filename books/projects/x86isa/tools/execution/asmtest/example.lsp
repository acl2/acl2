
(in-package "X86ISA")

(include-book "asmtest")
(include-book "../top" :ttags (:undef-flg :other-non-det :instrument))

(def-snippet-data real-snippet-data)


(init-x86-state-64
 nil
 0
 nil         ;; GPRs
 nil         ;; CRs
 nil         ;; MSRs
 nil         ;; SRs (visible)
 nil nil nil ;; (hidden)
 0           ;; rflags
 nil         ;;memory
 x86)

(binary-file-load "asmtest" :elf t)

(test-snippet "blsi32"
              :input-file "in.bin"
              :output-file "blsi32.bin")


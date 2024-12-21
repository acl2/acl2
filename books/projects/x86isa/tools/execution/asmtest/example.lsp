
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

; head -c 1000 /dev/urandom > in.bin
; ./asmtest -i in.bin -o blsi32.bin blsi32
(test-snippet-event "blsi32"
              :input-file "in.bin"
              :output-file "blsi32.bin")

; ./asmtest -i in.bin -o blsi64.bin blsi64
(test-snippet-event "blsi64"
              :input-file "in.bin"
              :output-file "blsi64.bin")

; head -c 200000 /dev/urandom > inbig.bin
; ./asmtest -i inbig.bin -o blsi32big.bin blsi32
(test-snippet-event "blsi32"
              :input-file "inbig.bin"
              :output-file "blsi32big.bin")

; ./asmtest -i inbig.bin -o blsi64big.bin blsi64
(test-snippet-event "blsi64"
              :input-file "inbig.bin"
              :output-file "blsi64big.bin")

; ./asmtest -i in.bin -o adcx64.bin adcx64
(test-snippet-event "adcx64"
              :input-file "in.bin"
              :output-file "adcx64.bin")

; ./asmtest -i in.bin -o adcx32.bin adcx32
(test-snippet-event "adcx32"
              :input-file "in.bin"
              :output-file "adcx32.bin")

; ./asmtest -i in.bin -o adox64.bin adox64
(test-snippet-event "adox64"
              :input-file "in.bin"
              :output-file "adox64.bin")

; ./asmtest -i in.bin -o adox32.bin adox32
(test-snippet-event "adox32"
              :input-file "in.bin"
              :output-file "adox32.bin")


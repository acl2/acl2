
(in-package "X86ISA")

(include-book "../asmtest")
(include-book "../../execloaders")

;; Read the actual snippet data (function addresses and input/output sizes)
;; from snippets.lsp and attach it to the snippet-data stub
(def-snippet-data real-snippet-data :fname "../snippets.lsp")


;; Initialize the x86 state into 64-bit mode
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

;; Load the asmtest executable into memory
(binary-file-load "../asmtest" :elf t)



#|

head -c 1000 /dev/urandom > in.bin
../asmtest -i in.bin -n blsi32 blsi32
../asmtest -i in.bin -n blsi64 blsi64
../asmtest -i in.bin -n adcx64 adcx64
../asmtest -i in.bin -n adcx32 adcx32
../asmtest -i in.bin -n adox64 adox64
../asmtest -i in.bin -n adox32 adox32
../asmtest -i in.bin -n cmpxchg8b cmpxchg8b
../asmtest -i in.bin -n cmpxchg16b cmpxchg16b

head -c 200000 /dev/urandom > inbig.bin
../asmtest -i inbig.bin -n blsi32big blsi32
../asmtest -i inbig.bin -n blsi64big blsi64
../asmtest -i inbig.bin -n adcx64big adcx64
../asmtest -i inbig.bin -n adcx32big adcx32
../asmtest -i inbig.bin -n adox64big adox64
../asmtest -i inbig.bin -n adox32big adox32

../text_to_binary.py adox_adcx_32bit_ins.txt adox_adcx_32bit_ins.bin
../asmtest -i adox_adcx_32bit_ins.bin -n adcx32custom adcx32
../asmtest -i adox_adcx_32bit_ins.bin -n adox32custom adox32

../text_to_binary.py blsi32_ins.txt blsi32_ins.bin
../asmtest -i blsi32_ins.bin -n blsi32custom blsi32

../text_to_binary.py cmpxchg8b_ins.txt cmpxchg8b_ins.bin
../asmtest -i cmpxchg8b_ins.bin -n cmpxchg8b_custom cmpxchg8b

../text_to_binary.py cmpxchg16b_ins.txt cmpxchg16b_ins.bin
../asmtest -i cmpxchg16b_ins.bin -n cmpxchg16b_custom cmpxchg16b

../text_to_binary.py popcnt16_ins.txt popcnt16_ins.bin
../asmtest -n popcnt16 popcnt16

../text_to_binary.py popcnt32_ins.txt popcnt32_ins.bin
../asmtest -n popcnt32 popcnt32

../text_to_binary.py popcnt64_ins.txt popcnt64_ins.bin
../asmtest -n popcnt64 popcnt64

|#

(test-snippetconf-event "blsi32.conf")
(test-snippetconf-event "blsi64.conf")
(test-snippetconf-event "adcx64.conf")

(test-snippetconf-event "adcx32.conf")
(test-snippetconf-event "adox64.conf")
(test-snippetconf-event "adox32.conf")
(test-snippetconf-event "cmpxchg8b.conf")
(test-snippetconf-event "cmpxchg16b.conf")

(test-snippetconf-event "blsi32big.conf")
(test-snippetconf-event "blsi64big.conf")
(test-snippetconf-event "adcx64big.conf")
(test-snippetconf-event "adcx32big.conf")
(test-snippetconf-event "adox64big.conf")
(test-snippetconf-event "adox32big.conf")

(test-snippetconf-event "adcx32custom.conf")
(test-snippetconf-event "adox32custom.conf")

(test-snippetconf-event "blsi32custom.conf")

(test-snippetconf-event "cmpxchg8b_custom.conf")
(test-snippetconf-event "cmpxchg16b_custom.conf")

(test-snippetconf-event "popcnt16.conf")
(test-snippetconf-event "popcnt32.conf")
(test-snippetconf-event "popcnt64.conf")

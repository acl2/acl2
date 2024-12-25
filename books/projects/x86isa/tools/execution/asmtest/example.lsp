
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



#|

head -c 1000 /dev/urandom > in.bin
./asmtest -i in.bin -o blsi32.bin blsi32
./asmtest -i in.bin -o blsi64.bin blsi64
./asmtest -i in.bin -o adcx64.bin adcx64
./asmtest -i in.bin -o adcx32.bin adcx32
./asmtest -i in.bin -o adox64.bin adox64
./asmtest -i in.bin -o adox32.bin adox32
./asmtest -i in.bin -o cmpxchg8b.bin cmpxchg8b
./asmtest -i in.bin -o cmpxchg16b.bin cmpxchg16b

head -c 200000 /dev/urandom > inbig.bin
./asmtest -i inbig.bin -o blsi32big.bin blsi32
./asmtest -i inbig.bin -o blsi64big.bin blsi64
./asmtest -i inbig.bin -o adcx64big.bin adcx64
./asmtest -i inbig.bin -o adcx32big.bin adcx32
./asmtest -i inbig.bin -o adox64big.bin adox64
./asmtest -i inbig.bin -o adox32big.bin adox32

./text_to_binary.py adox_adcx_32bit_ins.txt adox_adcx_32bit_ins.bin
./asmtest -i adox_adcx_32bit_ins.bin -o adcx32custom.bin adcx32
./asmtest -i adox_adcx_32bit_ins.bin -o adox32custom.bin adox32

./text_to_binary.py blsi32_ins.txt blsi32_ins.bin
./asmtest -i blsi32_ins.bin -o blsi32custom.bin blsi32

./text_to_binary.py cmpxchg8b_ins.txt cmpxchg8b_ins.bin
./asmtest -i cmpxchg8b_ins.bin -o cmpxchg8b_custom.bin cmpxchg8b

./text_to_binary.py cmpxchg16b_ins.txt cmpxchg16b_ins.bin
./asmtest -i cmpxchg16b_ins.bin -o cmpxchg16b_custom.bin cmpxchg16b
|#

(test-snippet-event "blsi32" :input-file "in.bin" :output-file "blsi32.bin")
(test-snippet-event "blsi64" :input-file "in.bin" :output-file "blsi64.bin")
(test-snippet-event "adcx64" :input-file "in.bin" :output-file "adcx64.bin")
(test-snippet-event "adcx32" :input-file "in.bin" :output-file "adcx32.bin")
(test-snippet-event "adox64" :input-file "in.bin" :output-file "adox64.bin")
(test-snippet-event "adox32" :input-file "in.bin" :output-file "adox32.bin")
(test-snippet-event "cmpxchg8b" :input-file "in.bin" :output-file "cmpxchg8b.bin")
(test-snippet-event "cmpxchg16b" :input-file "in.bin" :output-file "cmpxchg16b.bin")

(test-snippet-event "blsi32" :input-file "inbig.bin" :output-file "blsi32big.bin")
(test-snippet-event "blsi64" :input-file "inbig.bin" :output-file "blsi64big.bin")
(test-snippet-event "adcx64" :input-file "inbig.bin" :output-file "adcx64big.bin")
(test-snippet-event "adcx32" :input-file "inbig.bin" :output-file "adcx32big.bin")
(test-snippet-event "adox64" :input-file "inbig.bin" :output-file "adox64big.bin")
(test-snippet-event "adox32" :input-file "inbig.bin" :output-file "adox32big.bin")

(test-snippet-event "adcx32" :input-file "adox_adcx_32bit_ins.bin" :output-file "adcx32custom.bin")
(test-snippet-event "adox32" :input-file "adox_adcx_32bit_ins.bin" :output-file "adox32custom.bin")

(test-snippet-event "blsi32" :input-file "blsi32_ins.bin" :output-file "blsi32custom.bin")

(test-snippet-event "cmpxchg8b" :input-file "cmpxchg8b_ins.bin" :output-file "cmpxchg8b_custom.bin")
(test-snippet-event "cmpxchg16b" :input-file "cmpxchg16b_ins.bin" :output-file "cmpxchg16b_custom.bin")

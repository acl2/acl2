(in-package 3bz)

#++
(ql:quickload '(salza2 flexi-streams chipz))
#++
(defun dump-deflate (octets &rest options)
  (let ((uiop:*default-stream-element-type* '(unsigned-byte 8)))
    (flex:with-input-from-sequence (s octets)
      (sb-ext:run-program
       ;; -r = raw deflate data, -d = print dynamic header, -s = print stats
       #p"~/src/infgen/infgen.exe" (or options '("-rds"))
       :input s
       :output *standard-output*))))

#++
(let* ((v (salza2:compress-data (coerce #(1 2 3 4 1 2 3 4 1 2) 'octet-vector) 'salza2:deflate-compressor))
       (c (make-instance 'octet-vector-context
                         :octet-vector v
                         :boxes (make-context-boxes :end (length v))))
       (state (make-deflate-state)))
  (dump-deflate v)
  (print (length (time (chipz:decompress nil 'chipz:deflate v))))
  (time
   (decompress c state)))



;; test streams from https://github.com/nayuki/Simple-DEFLATE-decompressor/blob/master/java/test/DecompressorTest.java


(defun deflate-test (in out &optional err)
  (declare (ignorable err))
  (let* ((in (remove #\space in))
         (out (remove #\space out))
         (octets (make-array (* (ceiling (length in) 8))
                             :element-type 'octet :initial-element 0)))
    (declare (ignorable out))
    (loop for c across in
          for x from 0
          for bit = (mod x 8)
          for byte = (floor x 8)
          do (setf (ldb (byte 1 bit) (aref octets byte))
                   (digit-char-p c)))
    (format t "~&test ~s~% -> ~x~%" in octets)
    (dump-deflate octets)
    (let* ((c (make-instance 'octet-vector-context
                             :octet-vector octets
                             :boxes (make-context-boxes :end (length octets))))
           (state (make-deflate-state))
           (d #++(with-output-to-string (*standard-output*)
                   (decompress c state)
                   #++(loop for b = (read-struct 'deflate-block c)
                            when (data b)
                              do (loop for a across (data b)
                                       do (format s "~2,'0x" a))
                            until (plusp (bfinal b))))
              (let* ((tmp (make-array 1024 :element-type 'octet))
                     (d1 (decompress c state :into tmp)))
                (setf d1 (list (subseq tmp 0 d1)))
                (with-output-to-string (s)
                  (loop for v in d1
                        do (loop for x across v
                                 do (format s "~2,'0x" x)))))))
      (format t "got <~a>~%" d)
      (format t "expected <~a>~%" out)
      (unless err (assert (string= d out))))))

 ;; No blocks
(deflate-test "" "" 'eof)

;; Reserved block type
(deflate-test "1 11 00000" "" 'format)

;; Partial block type
(deflate-test "1 0" "" 'eof) ;;

;; Uncompressed block len=0: (empty)
(deflate-test "1 00 00000   0000000000000000 1111111111111111" "")

;; Uncompressed block len=3: 05 14 23
(deflate-test "1 00 00000   1100000000000000 0011111111111111   10100000 00101000 11000100" "05 14 23") ;

;; Uncompressed block len=1: 05
;; Uncompressed block len=2: 14 23
(deflate-test "0 00 00000   0100000000000000 1011111111111111   10100000 00101000   1 00 00000   1000000000000000 0111111111111111   11000100" "05 14 23") ;

;; Uncompressed block (partial padding) (no length)
(deflate-test "1 00 000" "" 'eof)       ;


;; Uncompressed block (partial length)
(deflate-test "1 00 00000 0000000000" "" 'eof)


;; Uncompressed block (mismatched len and nlen)
(deflate-test "1 00 00000 0010000000010000 1111100100110101" "" 'format)


;; Uncompressed block len=6: 55 EE (End)
(deflate-test "1 00 11111 0110000000000000 1001111111111111 10101010 01110111" "" 'eof) ;

;; Uncompressed block len=0: (empty)
;; No final block
(deflate-test "0 00 00000   0000000000000000 1111111111111111" "" 'eof)

;; Fixed Huffman block: 90 A1 FF End
;; Uncompressed block len=2: AB CD
(deflate-test "0 10 110010000 110100001 111111111 0000000  1 00 0100000000000000 1011111111111111 11010101 10110011" "90 A1 FF AB CD") ;

;; Fixed Huffman block: End
(deflate-test "1 10 0000000" "")        ;

;; Fixed Huffman block: 00 80 8F 90 C0 FF End
(deflate-test "1 10 00110000 10110000 10111111 110010000 111000000 111111111 0000000" "00 80 8F 90 C0 FF") ;


;; Fixed Huffman block: 00 01 02 (33) End
(deflate-test "1 10 00110000 00110001 00110010 0000001 00010 0000000" "00 01 02 00 01 02") ;

;; Fixed Huffman block: 01 (14) End
(deflate-test "1 10 00110001 0000010 00000 0000000" "01 01 01 01 01") ;

;; Fixed Huffman block: 8E 8F (25) End
(deflate-test "1 10 10111110 10111111 0000011 00001 0000000" "8E 8F 8E 8F 8E 8F 8E") ;

;; Fixed Huffman block: #286
(deflate-test "1 10 11000110" "" 'format) ;

;; Fixed Huffman block: #287
(deflate-test "1 10 11000111" "" 'format) ;

;; Fixed Huffman block: 00 #257 #30
(deflate-test "1 10 00110000 0000001 11110" "" 'format) ;

;; Fixed Huffman block: 00 #257 #31
(deflate-test "1 10 00110000 0000001 11111" "" 'format) ;

;; Fixed Huffman block: (partial symbol)
(deflate-test "1 10 00000" "" 'eof)     ;

;; Fixed Huffman block: 00 #269+1(partial)
(deflate-test "1 10 00110000 0001101 1" "" 'eof) ;

;; Fixed Huffman block: 00 #285 #0 #257 #8+00(partial)
(deflate-test "1 10 00110000 11000101 00000 0000001 01000 00" "" 'eof) ;

;; Dynamic Huffman block:
;;   numCodeLen=19
;;     codeLenCodeLen = 0:0 1:1 2:0 ... 15:0 16:0 17:0 18:1
;;   numLitLen=257 numDist=2
;;     litLenCodeLen = 0:1 1:0 ... 255:0 256:1
;;     distCodeLen = 0:1 1:1
;;   Data: End
(let ((blockHeader "1 01")
      (codeCounts  "00000 10000 1111")
      (codeLenCodeLens  "000 000 100 000 000 000 000 000 000 000 000 000 000 000 000 000 000 100 000")
      (codeLens  "0 11111111 10101011 0 0 0")
      (data  "1"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens codeLens data) ""))

;; Dynamic Huffman block:
;;   numCodeLen=18
;;     codeLenCodeLen = 0:2 1:2 2:0 ... 15:0 16:0 17:0 18:1
;;   numLitLen=257 numDist=1
;;     litLenCodeLen = 0:0 ... 254:0 255:1 256:1
;;     distCodeLen = 0:0
;;   Data: End

(let ((blockHeader  "1 01")
      (codeCounts  "00000 00000 0111")
      (codeLenCodeLens  "000 000 100 010 000 000 000 000 000 000 000 000 000 000 000 000 000 010")
      (codeLens  "01111111 00101011 11 11 10")
      (data  "1"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens codeLens data) ""))



;; Dynamic Huffman block:
;;   numLitLen=257 numDist=1 numCodeLen=18
;;   codeLenCodeLen = 0:0 1:1 2:0 ... 15:0 16:1 17:0 18:0
;;   Literal/length/distance code lengths: #16+00
(let ((blockHeader "1 01")
      (codeCounts "00000 00000 0111")
      (codeLenCodeLens "100 000 000 000 000 000 000 000 000 000 000 000 000 000 000 000 000 100")
      (codeLens "1"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens codeLens) "" 'format))



;; Dynamic Huffman block:
;;   numLitLen=257 numDist=1 numCodeLen=18
;;   codeLenCodeLen = 0:0 1:1 2:0 ... 15:0 16:0 17:0 18:1
;;   Literal/length/distance code lengths: 1 1 #18+1111111 #18+1101100
(let ((blockHeader "1 01")              ;
      (codeCounts "00000 00000 0111")   ;
      (codeLenCodeLens "000 000 100 000 000 000 000 000 000 000 000 000 000 000 000 000 000 100") ;
      (codeLens "0 0 11111111 10011011")) ;
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens codeLens) "" 'format))



;; Dynamic Huffman block:
;;   numLitLen=257 numDist=1 numCodeLen=4
;;   codeLenCodeLen = 0:1 1:1 2:1 3:0
(let ((blockHeader "1 01")
      (codeCounts "00000 00000 0000")
      (codeLenCodeLens "100 100 100 000")
      (padding "0000000000000000000"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens padding) "" 'format)) ;



;; Dynamic Huffman block:
;;   numLitLen=257 numDist=1 numCodeLen=4
;;   codeLenCodeLen = 0:1 1:1 2:1 3:1
(let ((blockHeader "1 01")
      (codeCounts "00000 00000 0000")
      (codeLenCodeLens "100 100 100 100")
      (padding "0000000000000000000"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens padding) "" 'format)) ;



;; Dynamic Huffman block:
;;   numLitLen=257 numDist=1 numCodeLen=4
;;   codeLenCodeLen = 0:1 1:2 2:3 3:0
(let ((blockHeader "1 01")
      (codeCounts "00000 00000 0000")
      (codeLenCodeLens "100 010 110 000")
      (padding "0000000000000000000"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens padding) "" 'format)) ;



;; Dynamic Huffman block:
;;   numLitLen=257 numDist=1 numCodeLen=4
;;   codeLenCodeLen = 0:0 1:0 2:0 3:0
(let ((blockHeader "1 01")
      (codeCounts "00000 00000 0000")
      (codeLenCodeLens "000 000 000 000")
      (padding "0000000000000000000"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens padding) "" 'format)) ;


;; Dynamic Huffman block:
;;   numLitLen=257 numDist=1 numCodeLen=4
;;   codeLenCodeLen = 0:0 1:0 2:1 3:0
(let ((blockHeader "1 01")
      (codeCounts "00000 00000 0000")
      (codeLenCodeLens "000 000 100 000")
      (padding "0000000000000000000"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens padding) "" 'format)) ;


;; Dynamic Huffman block:
;;   numLitLen=257 numDist=1 numCodeLen=4
;;   codeLenCodeLen = 0:2 1:1 2:0 3:0
(let ((blockHeader "1 01")
      (codeCounts "00000 00000 0000")
      (codeLenCodeLens "010 100 000 000")
      (padding "0000000000000000000"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens padding) "" 'format)) ;


;; Dynamic Huffman block:
;;   numLitLen=258 numDist=1 numCodeLen=18
;;   codeLenCodeLen = 0:2 1:2 2:2 ... 15:0 16:0 17:0 18:2
;;   Literal/length/distance code lengths: 0 2 #18+1111111 #18+1101001 1 2 1
;;   Data: 01 #257 #0 #256
(let ((blockHeader "1 01")
      (codeCounts "10000 00000 0111")
      (codeLenCodeLens "000 000 010 010 000 000 000 000 000 000 000 000 000 000 000 010 000 010")
      (codeLens "00 10 111111111 111001011 01 10 01")
      (data "10 11 0 0"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens codeLens data) "01 01 01 01")) ;


;; Dynamic Huffman block:
;;   numLitLen=258 numDist=1 numCodeLen=18
;;   codeLenCodeLen = 0:2 1:2 2:2 ... 15:0 16:0 17:0 18:2
;;   Literal/length/distance code lengths: 0 2 #18+1111111 #18+1101001 1 2 1
;;   Data: 01 #257 #31 #256
(let ((blockHeader "1 01")
      (codeCounts "10000 00000 0111")
      (codeLenCodeLens "000 000 010 010 000 000 000 000 000 000 000 000 000 000 000 010 000 010")
      (codeLens "00 10 111111111 111001011 01 10 01")
      (data "10 11 1 0"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens codeLens data) "01 01 01 01" 'format)) ;


;; Dynamic Huffman block:
;;   numLitLen=258 numDist=1 numCodeLen=18
;;   codeLenCodeLen = 0:2 1:2 2:2 ... 15:0 16:0 17:0 18:2
;;   Literal/length/distance code lengths: 2 #18+1111111 #18+1101010 1 2 0
;;   Data: 00 #257
(let ((blockHeader "1 01")
      (codeCounts "10000 00000 0111")
      (codeLenCodeLens "000 000 010 010 000 000 000 000 000 000 000 000 000 000 000 010 000 010")
      (codeLens "10 111111111 110101011 01 10 00")
      (data "10 11")
      (padding "0000000000000000"))
  (deflate-test (concatenate 'string blockHeader codeCounts codeLenCodeLens codeLens data padding) "" 'format)) ;


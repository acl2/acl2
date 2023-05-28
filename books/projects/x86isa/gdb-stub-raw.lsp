(in-package "X86ISA")

(defun write-packet (str stream)
  (format stream "$~a#~2,'0x" str   
          (mod (loop for i from 0 below (length str)
                     for ch = (char str i)
                     sum (char-code ch)) 256))
  (force-output stream))

(defun read-packet (stream)
  (if (equal #\$ (read-char stream))
    (let*
      ((str (with-output-to-string (str-stream) (loop for ch = (read-char stream)
                                                      until (equal ch #\#)
                                                      do (write-char ch str-stream)))))
      (read-char stream)
      (read-char stream)  ;; Ignore the checksum
      (write-char #\+ stream) ;; Send acknowledgement
      str)
    nil)) ;; All packets start with $

;; Formats an n byte number as a little endian hexadecimal value
(defun format-n-byte-hex-le (n num stream)
  (format stream "~2,'0x" (logand #xFF num)) ;; Output least significant byte
  (if (not (= n 1))
    (format-n-byte-hex-le (1- n) (ash num -8) stream)))

;; Returns a hex string of the contents of all the registers
;; in the format expected by gdb.
(defun get-register-state (x86)
  (with-output-to-string (str-stream) 
   ;; General purpose registers
   (loop for i from 0 below 16
         do (format-n-byte-hex-le 8 (rgfi i x86) str-stream))
   ;; Instruction pointer
   (format-n-byte-hex-le 8 (rip x86) str-stream)
   ;; GDB expects eflags, so 32 bit (top 32 bits of rflags are reserved anyways)
   (format-n-byte-hex-le 4 (rflags x86) str-stream)
   ;; Segment registers
   (loop for i from 0 below 6
         do (format-n-byte-hex-le 4 (seg-visiblei i x86) str-stream))
   ;; ST0-7
   (loop for i from 0 below 8
         do (loop for j from 0 below 20
                  do (write-char #\x str-stream)))
   ;; f.*
   (loop for i from 0 below 8
         do (loop for j from 0 below 8
                  do (write-char #\x str-stream)))))

(defun parse-n-bytes-hex-le (str i n)
  (if (= n 0)
    0
    (logapp 8 (parse-integer str :start i :end (+ i 2) :radix 16)
            (ash (parse-n-bytes-hex-le str (+ i 2) (1- n)) 8))))

(defun read-bytes-from-physical-memory (start n x86 acc)
  (if (= n 0)
    acc
    (read-bytes-from-physical-memory start (- n 1) x86 (cons (memi (+ start n -1) x86) acc))))

(defun write-registers-from-string (str x86)
  (let* ((x86 (loop for i from 0 below 16
                    for x86 = (!rgfi i (parse-n-bytes-hex-le str (* i 16) 8) x86)
                    finally (return x86)))
         (x86 (!rip (parse-n-bytes-hex-le str (* 16 16) 8) x86))
         (x86 (!rflags (parse-n-bytes-hex-le str (+ (* 16 16) 16) 4) x86))
         (x86 (loop for i from 0 below 6
                    for x86 = (load-segment-reg i (parse-n-bytes-hex-le str (+ (* 16 16) 16 8 (* i 8)) 4) x86)
                    finally (return x86))))
    x86))

(defun hex-str-to-byte-list (str &optional (i 0))
  (if (not (equal (length str) i))
    (cons (parse-integer str :start i :end (+ i 2) :radix 16)
        (hex-str-to-byte-list str (+ i 2)))))

(defun write-hex-str-to-memory (addr data x86)
  (loop for b in (hex-str-to-byte-list data)
        for a from addr
        do (!memi a b x86) ;; !memi doesn't return x86
        finally (return x86)))

(defun handle-packet (packet stream x86)
  (cond ((equal packet "?") (write-packet "S00" stream) x86) ;; We don't really have a stop reason, so we'll just respond with received signal 0x00
        ((equal packet "g") (write-packet (get-register-state x86) stream) x86)
        ((equal (char packet 0) #\G) (let* ((x86 (write-registers-from-string (subseq packet 1) x86)))
                                       (write-packet "OK" stream)
                                       x86))
        ((equal (char packet 0) #\m) (let* ((comma-index (search "," packet))
                                            (addr (parse-integer packet :start 1 :end comma-index :radix 16))
                                            (l (parse-integer packet :start (1+ comma-index) :radix 16)))
                                       (write-packet (with-output-to-string (str-stream)
                                                       (loop for b in (read-bytes-from-physical-memory addr l x86 nil)
                                                             do (format str-stream "~2,'0x" b))) stream)
                                     x86))
        ((equal (char packet 0) #\M) (let* ((comma-index (search "," packet))
                                            (colon-index (search ":" packet))
                                            (addr (parse-integer packet :start 1 :end comma-index :radix 16))
                                            (data (subseq packet (1+ colon-index)))
                                            (x86 (write-hex-str-to-memory addr data x86)))
                                       (write-packet "OK" stream)
                                       x86))
        ((equal (char packet 0) #\s) (let* (x86 (x86-fetch-decode-execute (if (> (length packet) 1)
                                                                            (!rip (parse-integer packet :start 1 :radix 16) x86)
                                                                            x86)))
                                       (write-packet "S00" stream)
                                       x86))
        ((equal (char packet 0) #\c) (let* (x86 (if (> (length packet) 1)
                                                  (!rip (parse-integer packet :start 1 :radix 16) x86)
                                                  x86))
                                       (loop for x86 = (x86-fetch-decode-execute x86)
                                             finally (return x86))))
        (t (write-packet "" stream) x86)))

(defun gdb-stub (x86)
  (let* ((socket (ccl::make-socket :connect :passive ;; Listen
                                   :local-host "localhost"
                                   :local-port 11234))
         (stream (ccl::accept-connection socket)))
    (format t "Listening on localhost:11234~%")
    (loop for packet = (read-packet stream)
          until (equal packet "D")
          do (if packet
               (setf x86 (handle-packet packet stream x86))))
    (write-packet "OK" stream)
    (close socket))
  x86)

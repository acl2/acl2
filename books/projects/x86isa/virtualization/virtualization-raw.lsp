(in-package "X86ISA")

(defun get-nth-uint64 (arr n)
  (logior (aref arr (* 8 n))
          (ash (aref arr (+ (* 8 n) 1)) (* 8 1))
          (ash (aref arr (+ (* 8 n) 2)) (* 8 2))
          (ash (aref arr (+ (* 8 n) 3)) (* 8 3))
          (ash (aref arr (+ (* 8 n) 4)) (* 8 4))
          (ash (aref arr (+ (* 8 n) 5)) (* 8 5))
          (ash (aref arr (+ (* 8 n) 6)) (* 8 6))
          (ash (aref arr (+ (* 8 n) 7)) (* 8 7))))


(defun get-gprs (x86)
  (loop for i from 0 to 15
        append (let* ((val (rgfi i x86)))
                 (list (logand #xff val)
                       (logand #xff (ash val -8))
                       (logand #xff (ash val -16))
                       (logand #xff (ash val -24))
                       (logand #xff (ash val -32))
                       (logand #xff (ash val -40))
                       (logand #xff (ash val -48))
                       (logand #xff (ash val -56))))))

(defun validate-inst (x86)
  (let* ((sock (ccl::make-socket :address-family :internet
                                 :type :stream
                                 :connect :active
                                 :remote-host "localhost"
                                 :remote-port 4425))
         (response (make-array (* 18 8) :element-type '(unsigned-byte 8))))
    (read-sequence response sock)
    (close sock)
    (b* ((real-rip (get-nth-uint64 response 16))
         (real-rflags (get-nth-uint64 response 17))
         (- (format t "real-rip: ~X~&" real-rip))
         (- (format t "real-rflags: ~X~&" real-rflags))
         ((mv success? x86) (run-until-rip-or-n real-rip 30 x86))
         (- (loop for i from 0 to 15
                  do (format t "~X " (n64 (rgfi i x86)))))
         ((when (not success?)) (mv nil x86))
         (- (format t "~&"))
         (- (format t "rflags ~X~&" (rflags x86)))
         (- (format t "rip: ~X~&" (rip x86)))
         (- (format t "diffs: "))
         (- (loop for i from 0 to 15
                  do (format t "~X " (- (get-nth-uint64 response i) (n64 (rgfi i x86))))))
         (- (format t "~&")))
        (mv (and (loop for i from 0 to 15
                       always (= (get-nth-uint64 response i) (n64 (rgfi i x86))))
                 ;; Doesn't make sense to compare all bits of rflags since many
                 ;; may be undefined, but we do want to compare intf, since
                 ;; that one is always defined
                 (equal (rflagsBits->intf (rflags x86))
                        (rflagsBits->intf real-rflags)))
            x86))))

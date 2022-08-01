; RISC-V Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (acoglio on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "execution")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; 0000000 00010 00001 000 00011 0110011 : x3 <- x1 ADD x2
; 00000000 00100000 10000001 10110011
; #x00     #x20     #x81     #xb3

(defconst *init-mem*
  (append (list #xb3 #x81 #x20 #x00)
          (repeat 96 0)))

(defconst *final-mem*
  *init-mem*)

(defconst *init-xregfile*
  (append (list 0  ; x0
                10 ; x1
                20 ; x2
                0) ; x3
          (repeat 28 0)))

(defconst *final-xregfile*
  (append (list 0   ; x0
                10  ; x1
                20  ; x2
                30) ; x3
          (repeat 28 0)))

(defconst *init-pc*
  0)

(defconst *final-pc*
  4)

(defconst *init-stat*
  (make-state64i :xregfile *init-xregfile*
                 :pc *init-pc*
                 :mem *init-mem*
                 :error nil))

(defconst *final-stat*
  (make-state64i :xregfile *final-xregfile*
                 :pc *final-pc*
                 :mem *final-mem*))

(assert-event (equal (step *init-stat*)
                     *final-stat*))

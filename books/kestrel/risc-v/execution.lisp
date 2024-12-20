; RISC-V Library
;
; Copyright (C) 2024 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (www.alessandrocoglio.info)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "decoding")
(include-book "semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step ((stat state64p))
  :returns (new-stat state64p)
  (b* (((when (error64p stat)) (state64-fix stat))
       (pc (read64-pc stat))
       (enc (read64-mem-ubyte32-lendian pc stat))
       (instr? (decode enc t))
       ((unless instr?) (error64 stat)))
    (exec-instr instr? pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stepn ((n natp) (stat state64p))
  :returns (new-stat state64p)
  (cond ((zp n) (state64-fix stat))
        ((error64p stat) (state64-fix stat))
        (t (stepn (1- n) (step stat))))
  :hooks (:fix))

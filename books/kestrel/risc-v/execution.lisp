; RISC-V Library
;
; Copyright (C) 2022 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (acoglio on GitHub)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "RISCV")

(include-book "decoding")
(include-book "semantics")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define step ((stat state64ip))
  :returns (new-stat state64ip)
  (b* (((when (errorp stat)) (state64i-fix stat))
       (pc (read-pc stat))
       (enc (read-mem-ubyte32-lendian pc stat))
       (instr? (decode enc))
       ((unless instr?) (error stat)))
    (exec-instr instr? pc stat))
  :hooks (:fix))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define stepn ((n natp) (stat state64ip))
  :returns (new-stat state64ip)
  (cond ((zp n) (state64i-fix stat))
        ((errorp stat) (state64i-fix stat))
        (t (stepn (1- n) (step stat))))
  :hooks (:fix))

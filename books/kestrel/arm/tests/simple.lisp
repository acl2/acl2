; Simple tests of the AMR32 model
;
; Copyright (C) 2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ARM")

(include-book "../step")

(in-theory (disable apsr.n
                    apsr.z
                    apsr.c
                    apsr.v
                    set-apsr.n
                    set-apsr.z
                    set-apsr.c
                    set-apsr.v))

(local
 ;; for the argument to bool-to-bit
 (defthm flip-equal
   (implies (and (syntaxp (acl2::smaller-termp x y)))
            (equal (equal y x)
                   (equal x y)))))

;; Shows the result of executing a MUL instruction
(thm
 ;; MUL encoding A1
 (implies (and ;; The program counter is pointing to the MUL instruction:
           (equal (read 4 (reg *pc* arm) arm)
                  ;; cond=14 (always execute), s=1, rd=3, rm=4, rn=5
                  ;; #b1110 0000000 1 0011 0000 0100 1001 0101)
                  #b11100000000100110000010010010101)
           (not (error arm)) ; no error yet
           )
          (equal (step arm)
                 (advance-pc (set-apsr.z (bool-to-bit (equal 0 (bvmult 32 (reg 5 arm) (reg 4 arm))))
                                         (set-apsr.n (getbit 31 (bvmult 32 (reg 5 arm) (reg 4 arm)))
                                                     (set-reg 3 (bvmult 32 (reg 5 arm) (reg 4 arm))
                                                              arm))))))
 :hints (("Goal" :in-theory (enable step arm32-decode execute-inst execute-mul-alt conditionpassed))))

;; a 2 step program
(thm
 (implies (and ;; The program counter is pointing to the first MUL instruction:
           (equal (read 4 (reg *pc* arm) arm)
                  ;; cond=14 (always execute), s=1, rd=3, rm=4, rn=5
                  ;; #b1110 0000000 1 0011 0000 0100 1001 0101)
                  #b11100000000100110000010010010101)
           (equal (read 4 (bvplus 32 4 (reg *pc* arm)) arm)
                  ;; cond=14 (always execute), s=1, rd=2, rm=4, rn=3
                  ;; #b1110 0000000 1 0010 0000 0100 1001 0011)
                  #b11100000000100100000010010010011)
           (not (error arm)) ; no error yet
           )
          (equal (run 2 arm)
                 ;; state after execution:
                 (set-reg 2 ; register 2 gets (r5*r4)*r4
                          (bvmult 32 (bvmult 32 (reg 5 arm) (reg 4 arm))
                                  (reg 4 arm))
                          (set-reg 3 (bvmult 32 (reg 5 arm) (reg 4 arm))
                                   (set-reg 15 (bvplus 32 8 (reg 15 arm))
                                            (set-apsr.n (getbit 31
                                                                (bvmult 32 (bvmult 32 (reg 5 arm) (reg 4 arm))
                                                                        (reg 4 arm)))
                                                        (set-apsr.z (bool-to-bit (equal 0
                                                                                        (bvmult 32 (bvmult 32 (reg 5 arm) (reg 4 arm))
                                                                                                (reg 4 arm))))
                                                                    arm)))))))
 :hints (("Goal" :in-theory (enable run step arm32-decode execute-inst execute-mul-alt conditionpassed
                                    advance-pc
                                    add-to-address))))

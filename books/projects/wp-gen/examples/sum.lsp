;; Calculates the sum of integers from 1 to A_0101-1 (generated from an 8-bit
;; adding routine for the 6502).

(ld "pcode.lsp")

(assign sum
        '(
                                        ; LDA
          (:node
           :label L_280
           :pre (and (natp C) (natp A_0101-1) (natp A))
           :subst (
            (u_80-1 . (COPY 0))
            (A . (COPY u_80-1))
            (Z . (INT_EQUAL A 0 32))
            (S . (INT_SLESS A 0 32))
            )
           :branches ((t . L_282)
            )
           )
                                        ; CLC
          (:node
           :label L_282
           :subst (
            (C . (COPY 0))
            )
           :branches ((t . L_283)
            )
           )
                                        ; ADC
          (:node
           :label L_283
           :pre (and (natp C) (natp A_0101-1) (natp A))
           :subst (
            (u_560-1 . (COPY A_0101-1))                ; N
            (u_570-1 . (COPY C))               ; C
            (u_590-1 . (INT_ADD A u_560-1 32)) ; A + N
            (u_600-1 . (INT_CARRY A u_560-1 32)) ; (carry A + N)
            (A . (INT_ADD u_590-1 u_570-1 32))   ; A + N + C
            (u_610-1 . (INT_CARRY u_590-1 u_570-1 32))
            (C . (INT_OR u_600-1 u_610-1 32))
            (Z . (INT_EQUAL A 0 32))
            (S . (INT_SLESS A 0 32))
            (V . (COPY C))
            )
           :branches ((t . L_286)
            )
           )
                                        ; DEC
          (:node
           :label L_286
           :pre (and (natp A_0101-1) (not (equal A_0101-1 0)))
           :subst (
            (u_7c0-1 . (INT_SUB A_0101-1 1 32))
            (A_0101-1 . (COPY u_7c0-1))

            (Z . (INT_EQUAL u_7c0-1 0 32))

            (S . (INT_SLESS u_7c0-1 0 32))
            )
           :branches ((t . L_289)
            )
           )
                                        ; BNE
          (:node
           :label L_289
           :pre (natp z)
           :subst (
            (u_3b0-1 . (INT_EQUAL Z 0 32) )
            )
           :branches (((= u_3b0-1 1) . L_283)
            ((not (= u_3b0-1 1)) . L_291)
            )
           )
                                        ; JMP L_291
          (:node
           :label L_291
           :subst t
           :branches nil
           :post (= (* 2 a) (* nsave (+ 1 nsave)))

           #|
    ; RTS  ;
           (L_291
           (
           (SP . (INT_ADD SP 1))
           (u_510-2 . (LOAD RAM(SP)))
           (SP . (INT_ADD SP 1))
           )
           (t . u_510-2)
           |#
       )
      )
  )

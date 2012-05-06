(IN-PACKAGE "ACL2")

; Edited by Matt K.:
; (INCLUDE-BOOK "source_shallow" :DIR :BOOKS)
(INCLUDE-BOOK "../books/source_shallow")

; Edited by Matt K.:
; (INCLUDE-BOOK "computed-hints" :DIR :BOOKS)
(INCLUDE-BOOK "../books/computed-hints")

(DEFUND |$itr_0_typep| (X)
  (AND (TRUE-LISTP X) (NATP (NTH 0 X)) (< (NTH 0 X) 256) (NATP (NTH 1 X))
    (< (NTH 1 X) 256) (NATP (NTH 2 X)) (< (NTH 2 X) 256) (NATP (NTH 3 X))
    (< (NTH 3 X) 256) (NATP (NTH 4 X)) (< (NTH 4 X) 256) (NATP (NTH 5 X))
    (< (NTH 5 X) 256) (NATP (NTH 6 X)) (< (NTH 6 X) 256) (NATP (NTH 7 X))
    (< (NTH 7 X) 256)))

(DEFUN |$itr_1_typep| (X) (AND (NATP X) (< X 256)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_1| (|tmp_339| |tmp_338| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 8 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 8) NIL
      (CONS
        (LET ((|tmp_340| (NTH |$i| (LIST 0 1 2 3 4 5 6 7))))
          (C-WORD-PARITY 8 (C-WORD-&& (NTH |tmp_340| |tmp_338|) |tmp_339|)))
        (|$itr_comp_1| |tmp_339| |tmp_338| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_bitMmult_1| (|tmp_338| |tmp_339|)
  (IF (NOT (AND (|$itr_1_typep| |tmp_339|) (|$itr_0_typep| |tmp_338|))) 0
    (NAT-REP (REVERSE (|$itr_comp_1| |tmp_339| |tmp_338| 0)))))

(DEFUND |itr_gtimes_1| (|tmp_336| |tmp_337|)
  (IF (NOT (AND (|$itr_1_typep| |tmp_337|) (|$itr_1_typep| |tmp_336|))) 0
    (C-WORD-PMOD 15 9 (C-WORD-PMULT 8 8 |tmp_336| |tmp_337|) 283)))

(DEFUN |$itr_loop_iter_ps_3| (|tmp_334| |tmp_335| |$limit| |hist_10|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_335|))) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$itr_1_typep| |tmp_334|) (NATP |tmp_335|) (NATP |$limit|)
        (TRUE-LISTP |hist_10|))) (LIST 0)
    (IF (> |tmp_335| |$limit|) |hist_10|
      (LET
        ((|$arm-result|
           (COND ((< |tmp_335| 1) 1)
             (T (|itr_gtimes_1| |tmp_334| (NTH 0 |hist_10|))))))
        (|$itr_loop_iter_ps_3| |tmp_334| (|1+| |tmp_335|) |$limit|
          (UPDATE-NTH (LOGHEAD 0 |tmp_335|) |$arm-result| |hist_10|))))))

(DEFUND |itr_iter_ps_3| (|tmp_334| |tmp_335|)
  (IF (NOT (NATP |tmp_335|)) (LIST 0)
    (|$itr_loop_iter_ps_3| |tmp_334| 0 |tmp_335| (LIST 0))))

(DEFUND |itr_gpower_1| (|tmp_331| |tmp_332|)
  (IF (NOT (AND (|$itr_1_typep| |tmp_332|) (|$itr_1_typep| |tmp_331|))) 0
    (LET* ((|tmp_333| (|itr_iter_ps_3| |tmp_331| |tmp_332|)))
      (NTH 0 |tmp_333|))))

(DEFUND |itr_ginverse_1| (|x_3|)
  (IF (NOT (AND (|$itr_1_typep| |x_3|))) 0
    (IF (C-== |x_3| 0) 0 (C-WORD-PINV 9 8 283 |x_3|))))

(DEFUND |$itr_2_typep| (X)
  (AND (TRUE-LISTP X) (NATP (NTH 0 X)) (< (NTH 0 X) 256) (NATP (NTH 1 X))
    (< (NTH 1 X) 256) (NATP (NTH 2 X)) (< (NTH 2 X) 256) (NATP (NTH 3 X))
    (< (NTH 3 X) 256)))

(DEFUN |$itr_loop_iter_sums_3| (|xs_4| |tmp_330| |$limit| |hist_9|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_330|))) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$itr_2_typep| |xs_4|) (NATP |tmp_330|) (NATP |$limit|)
        (TRUE-LISTP |hist_9|))) (LIST 0)
    (IF (> |tmp_330| |$limit|) |hist_9|
      (LET
        ((|$arm-result|
           (COND ((< |tmp_330| 1) 0)
             (T
               (C-WORD-^^ (NTH (LOGHEAD 2 (C-WORD-- 32 |tmp_330| 1)) |xs_4|)
                 (NTH 0 |hist_9|))))))
        (|$itr_loop_iter_sums_3| |xs_4| (|1+| |tmp_330|) |$limit|
          (UPDATE-NTH (LOGHEAD 0 |tmp_330|) |$arm-result| |hist_9|))))))

(DEFUND |itr_iter_sums_3| (|xs_4| |tmp_330|)
  (IF (NOT (NATP |tmp_330|)) (LIST 0)
    (|$itr_loop_iter_sums_3| |xs_4| 0 |tmp_330| (LIST 0))))

(DEFUND |itr_byteSum_1| (|xs_3|)
  (IF (NOT (AND (|$itr_2_typep| |xs_3|))) 0
    (LET* ((|tmp_329| (|itr_iter_sums_3| |xs_3| 4))) (NTH 0 |tmp_329|))))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_2| (|tmp_326| |tmp_325| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_328| (NTH |$i| (LIST 0 1 2 3))))
          (|itr_gtimes_1| (NTH |tmp_328| |tmp_325|)
            (NTH |tmp_328| |tmp_326|)))
        (|$itr_comp_2| |tmp_326| |tmp_325| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_byteDot_1| (|tmp_325| |tmp_326|)
  (IF (NOT (AND (|$itr_2_typep| |tmp_326|) (|$itr_2_typep| |tmp_325|))) 0
    (LET* ((|tmp_327| (|$itr_comp_2| |tmp_326| |tmp_325| 0)))
      (|itr_byteSum_1| |tmp_327|))))

(DEFUND |$itr_3_typep| (X)
  (AND (TRUE-LISTP X) (TRUE-LISTP (NTH 0 X)) (NATP (NTH 0 (NTH 0 X)))
    (< (NTH 0 (NTH 0 X)) 256) (NATP (NTH 1 (NTH 0 X)))
    (< (NTH 1 (NTH 0 X)) 256) (NATP (NTH 2 (NTH 0 X)))
    (< (NTH 2 (NTH 0 X)) 256) (NATP (NTH 3 (NTH 0 X)))
    (< (NTH 3 (NTH 0 X)) 256) (TRUE-LISTP (NTH 1 X)) (NATP (NTH 0 (NTH 1 X)))
    (< (NTH 0 (NTH 1 X)) 256) (NATP (NTH 1 (NTH 1 X)))
    (< (NTH 1 (NTH 1 X)) 256) (NATP (NTH 2 (NTH 1 X)))
    (< (NTH 2 (NTH 1 X)) 256) (NATP (NTH 3 (NTH 1 X)))
    (< (NTH 3 (NTH 1 X)) 256) (TRUE-LISTP (NTH 2 X)) (NATP (NTH 0 (NTH 2 X)))
    (< (NTH 0 (NTH 2 X)) 256) (NATP (NTH 1 (NTH 2 X)))
    (< (NTH 1 (NTH 2 X)) 256) (NATP (NTH 2 (NTH 2 X)))
    (< (NTH 2 (NTH 2 X)) 256) (NATP (NTH 3 (NTH 2 X)))
    (< (NTH 3 (NTH 2 X)) 256) (TRUE-LISTP (NTH 3 X)) (NATP (NTH 0 (NTH 3 X)))
    (< (NTH 0 (NTH 3 X)) 256) (NATP (NTH 1 (NTH 3 X)))
    (< (NTH 1 (NTH 3 X)) 256) (NATP (NTH 2 (NTH 3 X)))
    (< (NTH 2 (NTH 3 X)) 256) (NATP (NTH 3 (NTH 3 X)))
    (< (NTH 3 (NTH 3 X)) 256)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_3| (|tmp_323| |tmp_322| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_324| (NTH |$i| (LIST 0 1 2 3))))
          (|itr_byteDot_1| (NTH |tmp_324| |tmp_322|) |tmp_323|))
        (|$itr_comp_3| |tmp_323| |tmp_322| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_byteMmult_1| (|tmp_322| |tmp_323|)
  (IF (NOT (AND (|$itr_2_typep| |tmp_323|) (|$itr_3_typep| |tmp_322|)))
    (LIST 0 0 0 0) (|$itr_comp_3| |tmp_323| |tmp_322| 0)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_4| (|$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 8 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 8) NIL
      (CONS
        (LET ((|i_4| (NTH |$i| (LIST 0 1 2 3 4 5 6 7))))
          (C-WORD->>> 8 248 |i_4|)) (|$itr_comp_4| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_affMat_1| NIL (|$itr_comp_4| 0))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_5| (|$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 8 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 8) NIL
      (CONS
        (LET ((|i_3| (NTH |$i| (LIST 0 1 2 3 4 5 6 7))))
          (C-WORD->>> 8 82 |i_3|)) (|$itr_comp_5| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_invAffMat_1| NIL (|$itr_comp_5| 0))

(DEFUND |itr_affine_1| (|xs_2|)
  (IF (NOT (AND (|$itr_1_typep| |xs_2|))) 0
    (C-WORD-^^ (|itr_bitMmult_1| (|itr_affMat_1|) |xs_2|) 99)))

(DEFUND |itr_invAffine_1| (|xs_1|)
  (IF (NOT (AND (|$itr_1_typep| |xs_1|))) 0
    (|itr_bitMmult_1| (|itr_invAffMat_1|) (C-WORD-^^ |xs_1| 99))))

(DEFUND |itr_tmp_321| NIL (LIST 115 114 99 101 45 115 104 97 108))

(DEFUND |itr_tmp_320| NIL (LIST 97 97 109 112 45 100 101 101 112))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_6| (|$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 256 (|-| |$i|))) :HINTS
      (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 256) NIL
      (CONS
        (LET
          ((|x_2|
             (NTH |$i|
               (LIST 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21
                 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41
                 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61
                 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81
                 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98 99 100
                 101 102 103 104 105 106 107 108 109 110 111 112 113 114 115
                 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130
                 131 132 133 134 135 136 137 138 139 140 141 142 143 144 145
                 146 147 148 149 150 151 152 153 154 155 156 157 158 159 160
                 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175
                 176 177 178 179 180 181 182 183 184 185 186 187 188 189 190
                 191 192 193 194 195 196 197 198 199 200 201 202 203 204 205
                 206 207 208 209 210 211 212 213 214 215 216 217 218 219 220
                 221 222 223 224 225 226 227 228 229 230 231 232 233 234 235
                 236 237 238 239 240 241 242 243 244 245 246 247 248 249 250
                 251 252 253 254 255))))
          (|itr_affine_1| (|itr_ginverse_1| |x_2|)))
        (|$itr_comp_6| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_sbox_1| NIL
  (IF (C-== (|itr_tmp_321|) (|itr_tmp_320|))
    (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0) (|$itr_comp_6| 0)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_7| (|$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 256 (|-| |$i|))) :HINTS
      (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 256) NIL
      (CONS
        (LET
          ((|x_1|
             (NTH |$i|
               (LIST 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21
                 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39 40 41
                 42 43 44 45 46 47 48 49 50 51 52 53 54 55 56 57 58 59 60 61
                 62 63 64 65 66 67 68 69 70 71 72 73 74 75 76 77 78 79 80 81
                 82 83 84 85 86 87 88 89 90 91 92 93 94 95 96 97 98 99 100
                 101 102 103 104 105 106 107 108 109 110 111 112 113 114 115
                 116 117 118 119 120 121 122 123 124 125 126 127 128 129 130
                 131 132 133 134 135 136 137 138 139 140 141 142 143 144 145
                 146 147 148 149 150 151 152 153 154 155 156 157 158 159 160
                 161 162 163 164 165 166 167 168 169 170 171 172 173 174 175
                 176 177 178 179 180 181 182 183 184 185 186 187 188 189 190
                 191 192 193 194 195 196 197 198 199 200 201 202 203 204 205
                 206 207 208 209 210 211 212 213 214 215 216 217 218 219 220
                 221 222 223 224 225 226 227 228 229 230 231 232 233 234 235
                 236 237 238 239 240 241 242 243 244 245 246 247 248 249 250
                 251 252 253 254 255))))
          (|itr_ginverse_1| (|itr_invAffine_1| |x_1|)))
        (|$itr_comp_7| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_invSbox_1| NIL
  (IF (C-== (|itr_tmp_321|) (|itr_tmp_320|))
    (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0
      0 0 0 0 0 0) (|$itr_comp_7| 0)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_9| (|row_2| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_319| (NTH |$i| (LIST 0 1 2 3))))
          (NTH (NTH |tmp_319| |row_2|) (|itr_sbox_1|)))
        (|$itr_comp_9| |row_2| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_8| (|state_7| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_318| (NTH |$i| (LIST 0 1 2 3))))
          (LET* ((|row_2| (NTH |tmp_318| |state_7|)))
            (|$itr_comp_9| |row_2| 0)))
        (|$itr_comp_8| |state_7| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_byteSub_1| (|state_7|)
  (IF (NOT (AND (|$itr_3_typep| |state_7|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (|$itr_comp_8| |state_7| 0)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_11| (|row_1| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_317| (NTH |$i| (LIST 0 1 2 3))))
          (NTH (NTH |tmp_317| |row_1|) (|itr_invSbox_1|)))
        (|$itr_comp_11| |row_1| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_10| (|state_6| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_316| (NTH |$i| (LIST 0 1 2 3))))
          (LET* ((|row_1| (NTH |tmp_316| |state_6|)))
            (|$itr_comp_11| |row_1| 0)))
        (|$itr_comp_10| |state_6| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_invByteSub_1| (|state_6|)
  (IF (NOT (AND (|$itr_3_typep| |state_6|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (|$itr_comp_10| |state_6| 0)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_12| (|$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS (LET ((|tmp_315| (NTH |$i| (LIST 0 1 2 3)))) |tmp_315|)
        (|$itr_comp_12| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_tmp_314| NIL (|$itr_comp_12| 0))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_13| (|state_5| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_313| (NTH |$i| (LIST 0 1 2 3))))
          (C-VEC-<<< (NTH |tmp_313| |state_5|)
            (NTH |tmp_313| (|itr_tmp_314|))))
        (|$itr_comp_13| |state_5| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_shiftRow_1| (|state_5|)
  (IF (NOT (AND (|$itr_3_typep| |state_5|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (|$itr_comp_13| |state_5| 0)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_14| (|$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS (LET ((|tmp_312| (NTH |$i| (LIST 0 1 2 3)))) |tmp_312|)
        (|$itr_comp_14| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_tmp_311| NIL (|$itr_comp_14| 0))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_15| (|state_4| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_310| (NTH |$i| (LIST 0 1 2 3))))
          (C-VEC->>> (NTH |tmp_310| |state_4|)
            (NTH |tmp_310| (|itr_tmp_311|))))
        (|$itr_comp_15| |state_4| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_invShiftRow_1| (|state_4|)
  (IF (NOT (AND (|$itr_3_typep| |state_4|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (|$itr_comp_15| |state_4| 0)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_16| (|coeff_1| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|i_2| (NTH |$i| (LIST 0 1 2 3)))) (C-VEC->>> |coeff_1| |i_2|))
        (|$itr_comp_16| |coeff_1| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_18| (|tmp_308| |tmp_307| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_309| (NTH |$i| (LIST 0 1 2 3))))
          (NTH |tmp_308| (NTH |tmp_309| |tmp_307|)))
        (|$itr_comp_18| |tmp_308| |tmp_307| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_17| (|tmp_307| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_308| (NTH |$i| (LIST 0 1 2 3))))
          (|$itr_comp_18| |tmp_308| |tmp_307| 0))
        (|$itr_comp_17| |tmp_307| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_polyMat_1| (|coeff_1|)
  (IF (NOT (AND (|$itr_2_typep| |coeff_1|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET* ((|tmp_307| (|$itr_comp_16| |coeff_1| 0)))
      (|$itr_comp_17| |tmp_307| 0))))

(DEFUND |itr_tmp_306| NIL (LIST 2 1 1 3))

(DEFUND |itr_cx_1| NIL (|itr_polyMat_1| (|itr_tmp_306|)))

(DEFUND |itr_tmp_305| NIL (LIST 14 9 13 11))

(DEFUND |itr_dx_1| NIL (|itr_polyMat_1| (|itr_tmp_305|)))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_20| (|tmp_300| |state_3| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_301| (NTH |$i| (LIST 0 1 2 3))))
          (NTH |tmp_300| (NTH |tmp_301| |state_3|)))
        (|$itr_comp_20| |tmp_300| |state_3| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_19| (|state_3| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_300| (NTH |$i| (LIST 0 1 2 3))))
          (|$itr_comp_20| |tmp_300| |state_3| 0))
        (|$itr_comp_19| |state_3| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_21| (|tmp_299| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_302| (NTH |$i| (LIST 0 1 2 3))))
          (|itr_byteMmult_1| (|itr_cx_1|) (NTH |tmp_302| |tmp_299|)))
        (|$itr_comp_21| |tmp_299| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_23| (|tmp_303| |tmp_298| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_304| (NTH |$i| (LIST 0 1 2 3))))
          (NTH |tmp_303| (NTH |tmp_304| |tmp_298|)))
        (|$itr_comp_23| |tmp_303| |tmp_298| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_22| (|tmp_298| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_303| (NTH |$i| (LIST 0 1 2 3))))
          (|$itr_comp_23| |tmp_303| |tmp_298| 0))
        (|$itr_comp_22| |tmp_298| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_mixColumn_1| (|state_3|)
  (IF (NOT (AND (|$itr_3_typep| |state_3|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|tmp_298|
         (LET* ((|tmp_299| (|$itr_comp_19| |state_3| 0)))
           (|$itr_comp_21| |tmp_299| 0)))) (|$itr_comp_22| |tmp_298| 0))))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_25| (|tmp_293| |state_2| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_294| (NTH |$i| (LIST 0 1 2 3))))
          (NTH |tmp_293| (NTH |tmp_294| |state_2|)))
        (|$itr_comp_25| |tmp_293| |state_2| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_24| (|state_2| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_293| (NTH |$i| (LIST 0 1 2 3))))
          (|$itr_comp_25| |tmp_293| |state_2| 0))
        (|$itr_comp_24| |state_2| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_26| (|tmp_292| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_295| (NTH |$i| (LIST 0 1 2 3))))
          (|itr_byteMmult_1| (|itr_dx_1|) (NTH |tmp_295| |tmp_292|)))
        (|$itr_comp_26| |tmp_292| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_28| (|tmp_296| |tmp_291| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_297| (NTH |$i| (LIST 0 1 2 3))))
          (NTH |tmp_296| (NTH |tmp_297| |tmp_291|)))
        (|$itr_comp_28| |tmp_296| |tmp_291| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_27| (|tmp_291| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_296| (NTH |$i| (LIST 0 1 2 3))))
          (|$itr_comp_28| |tmp_296| |tmp_291| 0))
        (|$itr_comp_27| |tmp_291| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_invMixColumn_1| (|state_2|)
  (IF (NOT (AND (|$itr_3_typep| |state_2|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|tmp_291|
         (LET* ((|tmp_292| (|$itr_comp_24| |state_2| 0)))
           (|$itr_comp_26| |tmp_292| 0)))) (|$itr_comp_27| |tmp_291| 0))))

(DEFUND |itr_xorS_1| (|tmp_283| |tmp_284|)
  (IF (NOT (AND (|$itr_3_typep| |tmp_284|) (|$itr_3_typep| |tmp_283|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|tmp_285|
         (LET*
           ((|tmp_286|
              (LET*
                ((|tmp_287|
                   (LET* ((|tmp_288| (C-VEC-JOIN |tmp_283|)))
                     (C-WORD-JOIN 8 |tmp_288|)))
                  (|tmp_289|
                    (LET* ((|tmp_290| (C-VEC-JOIN |tmp_284|)))
                      (C-WORD-JOIN 8 |tmp_290|))))
                (C-WORD-^^ |tmp_287| |tmp_289|))))
           (C-WORD-SPLIT 8 16 |tmp_286|)))) (C-VEC-SPLIT 4 |tmp_285|))))

(DEFUND |itr_round_1| (|tmp_278| |tmp_279|)
  (IF (NOT (AND (|$itr_3_typep| |tmp_279|) (|$itr_3_typep| |tmp_278|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|tmp_280|
         (LET*
           ((|tmp_281|
              (LET* ((|tmp_282| (|itr_byteSub_1| |tmp_278|)))
                (|itr_shiftRow_1| |tmp_282|))))
           (|itr_mixColumn_1| |tmp_281|))))
      (|itr_xorS_1| |tmp_280| |tmp_279|))))

(DEFUND |itr_finalRound_1| (|tmp_274| |tmp_275|)
  (IF (NOT (AND (|$itr_3_typep| |tmp_275|) (|$itr_3_typep| |tmp_274|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|tmp_276|
         (LET* ((|tmp_277| (|itr_byteSub_1| |tmp_274|)))
           (|itr_shiftRow_1| |tmp_277|))))
      (|itr_xorS_1| |tmp_276| |tmp_275|))))

(DEFUND |itr_invRound_1| (|tmp_269| |tmp_270|)
  (IF (NOT (AND (|$itr_3_typep| |tmp_270|) (|$itr_3_typep| |tmp_269|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|tmp_271|
         (LET*
           ((|tmp_272|
              (LET* ((|tmp_273| (|itr_invByteSub_1| |tmp_269|)))
                (|itr_invShiftRow_1| |tmp_273|))))
           (|itr_invMixColumn_1| |tmp_272|))))
      (|itr_xorS_1| |tmp_271| |tmp_270|))))

(DEFUND |itr_invFinalRound_1| (|tmp_265| |tmp_266|)
  (IF (NOT (AND (|$itr_3_typep| |tmp_266|) (|$itr_3_typep| |tmp_265|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|tmp_267|
         (LET* ((|tmp_268| (|itr_invByteSub_1| |tmp_265|)))
           (|itr_invShiftRow_1| |tmp_268|))))
      (|itr_xorS_1| |tmp_267| |tmp_266|))))

(DEFUND |$itr_4_typep| (X)
  (AND (TRUE-LISTP X) (TRUE-LISTP (NTH 0 X)) (TRUE-LISTP (NTH 0 (NTH 0 X)))
    (NATP (NTH 0 (NTH 0 (NTH 0 X)))) (< (NTH 0 (NTH 0 (NTH 0 X))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 0 X)))) (< (NTH 1 (NTH 0 (NTH 0 X))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 0 X)))) (< (NTH 2 (NTH 0 (NTH 0 X))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 0 X)))) (< (NTH 3 (NTH 0 (NTH 0 X))) 256)
    (TRUE-LISTP (NTH 1 (NTH 0 X))) (NATP (NTH 0 (NTH 1 (NTH 0 X))))
    (< (NTH 0 (NTH 1 (NTH 0 X))) 256) (NATP (NTH 1 (NTH 1 (NTH 0 X))))
    (< (NTH 1 (NTH 1 (NTH 0 X))) 256) (NATP (NTH 2 (NTH 1 (NTH 0 X))))
    (< (NTH 2 (NTH 1 (NTH 0 X))) 256) (NATP (NTH 3 (NTH 1 (NTH 0 X))))
    (< (NTH 3 (NTH 1 (NTH 0 X))) 256) (TRUE-LISTP (NTH 2 (NTH 0 X)))
    (NATP (NTH 0 (NTH 2 (NTH 0 X)))) (< (NTH 0 (NTH 2 (NTH 0 X))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 0 X)))) (< (NTH 1 (NTH 2 (NTH 0 X))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 0 X)))) (< (NTH 2 (NTH 2 (NTH 0 X))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 0 X)))) (< (NTH 3 (NTH 2 (NTH 0 X))) 256)
    (TRUE-LISTP (NTH 3 (NTH 0 X))) (NATP (NTH 0 (NTH 3 (NTH 0 X))))
    (< (NTH 0 (NTH 3 (NTH 0 X))) 256) (NATP (NTH 1 (NTH 3 (NTH 0 X))))
    (< (NTH 1 (NTH 3 (NTH 0 X))) 256) (NATP (NTH 2 (NTH 3 (NTH 0 X))))
    (< (NTH 2 (NTH 3 (NTH 0 X))) 256) (NATP (NTH 3 (NTH 3 (NTH 0 X))))
    (< (NTH 3 (NTH 3 (NTH 0 X))) 256) (TRUE-LISTP (NTH 1 X))
    (TRUE-LISTP (NTH 0 (NTH 1 X))) (NATP (NTH 0 (NTH 0 (NTH 1 X))))
    (< (NTH 0 (NTH 0 (NTH 1 X))) 256) (NATP (NTH 1 (NTH 0 (NTH 1 X))))
    (< (NTH 1 (NTH 0 (NTH 1 X))) 256) (NATP (NTH 2 (NTH 0 (NTH 1 X))))
    (< (NTH 2 (NTH 0 (NTH 1 X))) 256) (NATP (NTH 3 (NTH 0 (NTH 1 X))))
    (< (NTH 3 (NTH 0 (NTH 1 X))) 256) (TRUE-LISTP (NTH 1 (NTH 1 X)))
    (NATP (NTH 0 (NTH 1 (NTH 1 X)))) (< (NTH 0 (NTH 1 (NTH 1 X))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 1 X)))) (< (NTH 1 (NTH 1 (NTH 1 X))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 1 X)))) (< (NTH 2 (NTH 1 (NTH 1 X))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 1 X)))) (< (NTH 3 (NTH 1 (NTH 1 X))) 256)
    (TRUE-LISTP (NTH 2 (NTH 1 X))) (NATP (NTH 0 (NTH 2 (NTH 1 X))))
    (< (NTH 0 (NTH 2 (NTH 1 X))) 256) (NATP (NTH 1 (NTH 2 (NTH 1 X))))
    (< (NTH 1 (NTH 2 (NTH 1 X))) 256) (NATP (NTH 2 (NTH 2 (NTH 1 X))))
    (< (NTH 2 (NTH 2 (NTH 1 X))) 256) (NATP (NTH 3 (NTH 2 (NTH 1 X))))
    (< (NTH 3 (NTH 2 (NTH 1 X))) 256) (TRUE-LISTP (NTH 3 (NTH 1 X)))
    (NATP (NTH 0 (NTH 3 (NTH 1 X)))) (< (NTH 0 (NTH 3 (NTH 1 X))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 1 X)))) (< (NTH 1 (NTH 3 (NTH 1 X))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 1 X)))) (< (NTH 2 (NTH 3 (NTH 1 X))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 1 X)))) (< (NTH 3 (NTH 3 (NTH 1 X))) 256)
    (TRUE-LISTP (NTH 2 X)) (TRUE-LISTP (NTH 0 (NTH 2 X)))
    (NATP (NTH 0 (NTH 0 (NTH 2 X)))) (< (NTH 0 (NTH 0 (NTH 2 X))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 2 X)))) (< (NTH 1 (NTH 0 (NTH 2 X))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 2 X)))) (< (NTH 2 (NTH 0 (NTH 2 X))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 2 X)))) (< (NTH 3 (NTH 0 (NTH 2 X))) 256)
    (TRUE-LISTP (NTH 1 (NTH 2 X))) (NATP (NTH 0 (NTH 1 (NTH 2 X))))
    (< (NTH 0 (NTH 1 (NTH 2 X))) 256) (NATP (NTH 1 (NTH 1 (NTH 2 X))))
    (< (NTH 1 (NTH 1 (NTH 2 X))) 256) (NATP (NTH 2 (NTH 1 (NTH 2 X))))
    (< (NTH 2 (NTH 1 (NTH 2 X))) 256) (NATP (NTH 3 (NTH 1 (NTH 2 X))))
    (< (NTH 3 (NTH 1 (NTH 2 X))) 256) (TRUE-LISTP (NTH 2 (NTH 2 X)))
    (NATP (NTH 0 (NTH 2 (NTH 2 X)))) (< (NTH 0 (NTH 2 (NTH 2 X))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 2 X)))) (< (NTH 1 (NTH 2 (NTH 2 X))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 2 X)))) (< (NTH 2 (NTH 2 (NTH 2 X))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 2 X)))) (< (NTH 3 (NTH 2 (NTH 2 X))) 256)
    (TRUE-LISTP (NTH 3 (NTH 2 X))) (NATP (NTH 0 (NTH 3 (NTH 2 X))))
    (< (NTH 0 (NTH 3 (NTH 2 X))) 256) (NATP (NTH 1 (NTH 3 (NTH 2 X))))
    (< (NTH 1 (NTH 3 (NTH 2 X))) 256) (NATP (NTH 2 (NTH 3 (NTH 2 X))))
    (< (NTH 2 (NTH 3 (NTH 2 X))) 256) (NATP (NTH 3 (NTH 3 (NTH 2 X))))
    (< (NTH 3 (NTH 3 (NTH 2 X))) 256) (TRUE-LISTP (NTH 3 X))
    (TRUE-LISTP (NTH 0 (NTH 3 X))) (NATP (NTH 0 (NTH 0 (NTH 3 X))))
    (< (NTH 0 (NTH 0 (NTH 3 X))) 256) (NATP (NTH 1 (NTH 0 (NTH 3 X))))
    (< (NTH 1 (NTH 0 (NTH 3 X))) 256) (NATP (NTH 2 (NTH 0 (NTH 3 X))))
    (< (NTH 2 (NTH 0 (NTH 3 X))) 256) (NATP (NTH 3 (NTH 0 (NTH 3 X))))
    (< (NTH 3 (NTH 0 (NTH 3 X))) 256) (TRUE-LISTP (NTH 1 (NTH 3 X)))
    (NATP (NTH 0 (NTH 1 (NTH 3 X)))) (< (NTH 0 (NTH 1 (NTH 3 X))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 3 X)))) (< (NTH 1 (NTH 1 (NTH 3 X))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 3 X)))) (< (NTH 2 (NTH 1 (NTH 3 X))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 3 X)))) (< (NTH 3 (NTH 1 (NTH 3 X))) 256)
    (TRUE-LISTP (NTH 2 (NTH 3 X))) (NATP (NTH 0 (NTH 2 (NTH 3 X))))
    (< (NTH 0 (NTH 2 (NTH 3 X))) 256) (NATP (NTH 1 (NTH 2 (NTH 3 X))))
    (< (NTH 1 (NTH 2 (NTH 3 X))) 256) (NATP (NTH 2 (NTH 2 (NTH 3 X))))
    (< (NTH 2 (NTH 2 (NTH 3 X))) 256) (NATP (NTH 3 (NTH 2 (NTH 3 X))))
    (< (NTH 3 (NTH 2 (NTH 3 X))) 256) (TRUE-LISTP (NTH 3 (NTH 3 X)))
    (NATP (NTH 0 (NTH 3 (NTH 3 X)))) (< (NTH 0 (NTH 3 (NTH 3 X))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 3 X)))) (< (NTH 1 (NTH 3 (NTH 3 X))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 3 X)))) (< (NTH 2 (NTH 3 (NTH 3 X))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 3 X)))) (< (NTH 3 (NTH 3 (NTH 3 X))) 256)
    (TRUE-LISTP (NTH 4 X)) (TRUE-LISTP (NTH 0 (NTH 4 X)))
    (NATP (NTH 0 (NTH 0 (NTH 4 X)))) (< (NTH 0 (NTH 0 (NTH 4 X))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 4 X)))) (< (NTH 1 (NTH 0 (NTH 4 X))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 4 X)))) (< (NTH 2 (NTH 0 (NTH 4 X))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 4 X)))) (< (NTH 3 (NTH 0 (NTH 4 X))) 256)
    (TRUE-LISTP (NTH 1 (NTH 4 X))) (NATP (NTH 0 (NTH 1 (NTH 4 X))))
    (< (NTH 0 (NTH 1 (NTH 4 X))) 256) (NATP (NTH 1 (NTH 1 (NTH 4 X))))
    (< (NTH 1 (NTH 1 (NTH 4 X))) 256) (NATP (NTH 2 (NTH 1 (NTH 4 X))))
    (< (NTH 2 (NTH 1 (NTH 4 X))) 256) (NATP (NTH 3 (NTH 1 (NTH 4 X))))
    (< (NTH 3 (NTH 1 (NTH 4 X))) 256) (TRUE-LISTP (NTH 2 (NTH 4 X)))
    (NATP (NTH 0 (NTH 2 (NTH 4 X)))) (< (NTH 0 (NTH 2 (NTH 4 X))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 4 X)))) (< (NTH 1 (NTH 2 (NTH 4 X))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 4 X)))) (< (NTH 2 (NTH 2 (NTH 4 X))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 4 X)))) (< (NTH 3 (NTH 2 (NTH 4 X))) 256)
    (TRUE-LISTP (NTH 3 (NTH 4 X))) (NATP (NTH 0 (NTH 3 (NTH 4 X))))
    (< (NTH 0 (NTH 3 (NTH 4 X))) 256) (NATP (NTH 1 (NTH 3 (NTH 4 X))))
    (< (NTH 1 (NTH 3 (NTH 4 X))) 256) (NATP (NTH 2 (NTH 3 (NTH 4 X))))
    (< (NTH 2 (NTH 3 (NTH 4 X))) 256) (NATP (NTH 3 (NTH 3 (NTH 4 X))))
    (< (NTH 3 (NTH 3 (NTH 4 X))) 256) (TRUE-LISTP (NTH 5 X))
    (TRUE-LISTP (NTH 0 (NTH 5 X))) (NATP (NTH 0 (NTH 0 (NTH 5 X))))
    (< (NTH 0 (NTH 0 (NTH 5 X))) 256) (NATP (NTH 1 (NTH 0 (NTH 5 X))))
    (< (NTH 1 (NTH 0 (NTH 5 X))) 256) (NATP (NTH 2 (NTH 0 (NTH 5 X))))
    (< (NTH 2 (NTH 0 (NTH 5 X))) 256) (NATP (NTH 3 (NTH 0 (NTH 5 X))))
    (< (NTH 3 (NTH 0 (NTH 5 X))) 256) (TRUE-LISTP (NTH 1 (NTH 5 X)))
    (NATP (NTH 0 (NTH 1 (NTH 5 X)))) (< (NTH 0 (NTH 1 (NTH 5 X))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 5 X)))) (< (NTH 1 (NTH 1 (NTH 5 X))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 5 X)))) (< (NTH 2 (NTH 1 (NTH 5 X))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 5 X)))) (< (NTH 3 (NTH 1 (NTH 5 X))) 256)
    (TRUE-LISTP (NTH 2 (NTH 5 X))) (NATP (NTH 0 (NTH 2 (NTH 5 X))))
    (< (NTH 0 (NTH 2 (NTH 5 X))) 256) (NATP (NTH 1 (NTH 2 (NTH 5 X))))
    (< (NTH 1 (NTH 2 (NTH 5 X))) 256) (NATP (NTH 2 (NTH 2 (NTH 5 X))))
    (< (NTH 2 (NTH 2 (NTH 5 X))) 256) (NATP (NTH 3 (NTH 2 (NTH 5 X))))
    (< (NTH 3 (NTH 2 (NTH 5 X))) 256) (TRUE-LISTP (NTH 3 (NTH 5 X)))
    (NATP (NTH 0 (NTH 3 (NTH 5 X)))) (< (NTH 0 (NTH 3 (NTH 5 X))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 5 X)))) (< (NTH 1 (NTH 3 (NTH 5 X))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 5 X)))) (< (NTH 2 (NTH 3 (NTH 5 X))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 5 X)))) (< (NTH 3 (NTH 3 (NTH 5 X))) 256)
    (TRUE-LISTP (NTH 6 X)) (TRUE-LISTP (NTH 0 (NTH 6 X)))
    (NATP (NTH 0 (NTH 0 (NTH 6 X)))) (< (NTH 0 (NTH 0 (NTH 6 X))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 6 X)))) (< (NTH 1 (NTH 0 (NTH 6 X))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 6 X)))) (< (NTH 2 (NTH 0 (NTH 6 X))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 6 X)))) (< (NTH 3 (NTH 0 (NTH 6 X))) 256)
    (TRUE-LISTP (NTH 1 (NTH 6 X))) (NATP (NTH 0 (NTH 1 (NTH 6 X))))
    (< (NTH 0 (NTH 1 (NTH 6 X))) 256) (NATP (NTH 1 (NTH 1 (NTH 6 X))))
    (< (NTH 1 (NTH 1 (NTH 6 X))) 256) (NATP (NTH 2 (NTH 1 (NTH 6 X))))
    (< (NTH 2 (NTH 1 (NTH 6 X))) 256) (NATP (NTH 3 (NTH 1 (NTH 6 X))))
    (< (NTH 3 (NTH 1 (NTH 6 X))) 256) (TRUE-LISTP (NTH 2 (NTH 6 X)))
    (NATP (NTH 0 (NTH 2 (NTH 6 X)))) (< (NTH 0 (NTH 2 (NTH 6 X))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 6 X)))) (< (NTH 1 (NTH 2 (NTH 6 X))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 6 X)))) (< (NTH 2 (NTH 2 (NTH 6 X))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 6 X)))) (< (NTH 3 (NTH 2 (NTH 6 X))) 256)
    (TRUE-LISTP (NTH 3 (NTH 6 X))) (NATP (NTH 0 (NTH 3 (NTH 6 X))))
    (< (NTH 0 (NTH 3 (NTH 6 X))) 256) (NATP (NTH 1 (NTH 3 (NTH 6 X))))
    (< (NTH 1 (NTH 3 (NTH 6 X))) 256) (NATP (NTH 2 (NTH 3 (NTH 6 X))))
    (< (NTH 2 (NTH 3 (NTH 6 X))) 256) (NATP (NTH 3 (NTH 3 (NTH 6 X))))
    (< (NTH 3 (NTH 3 (NTH 6 X))) 256) (TRUE-LISTP (NTH 7 X))
    (TRUE-LISTP (NTH 0 (NTH 7 X))) (NATP (NTH 0 (NTH 0 (NTH 7 X))))
    (< (NTH 0 (NTH 0 (NTH 7 X))) 256) (NATP (NTH 1 (NTH 0 (NTH 7 X))))
    (< (NTH 1 (NTH 0 (NTH 7 X))) 256) (NATP (NTH 2 (NTH 0 (NTH 7 X))))
    (< (NTH 2 (NTH 0 (NTH 7 X))) 256) (NATP (NTH 3 (NTH 0 (NTH 7 X))))
    (< (NTH 3 (NTH 0 (NTH 7 X))) 256) (TRUE-LISTP (NTH 1 (NTH 7 X)))
    (NATP (NTH 0 (NTH 1 (NTH 7 X)))) (< (NTH 0 (NTH 1 (NTH 7 X))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 7 X)))) (< (NTH 1 (NTH 1 (NTH 7 X))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 7 X)))) (< (NTH 2 (NTH 1 (NTH 7 X))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 7 X)))) (< (NTH 3 (NTH 1 (NTH 7 X))) 256)
    (TRUE-LISTP (NTH 2 (NTH 7 X))) (NATP (NTH 0 (NTH 2 (NTH 7 X))))
    (< (NTH 0 (NTH 2 (NTH 7 X))) 256) (NATP (NTH 1 (NTH 2 (NTH 7 X))))
    (< (NTH 1 (NTH 2 (NTH 7 X))) 256) (NATP (NTH 2 (NTH 2 (NTH 7 X))))
    (< (NTH 2 (NTH 2 (NTH 7 X))) 256) (NATP (NTH 3 (NTH 2 (NTH 7 X))))
    (< (NTH 3 (NTH 2 (NTH 7 X))) 256) (TRUE-LISTP (NTH 3 (NTH 7 X)))
    (NATP (NTH 0 (NTH 3 (NTH 7 X)))) (< (NTH 0 (NTH 3 (NTH 7 X))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 7 X)))) (< (NTH 1 (NTH 3 (NTH 7 X))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 7 X)))) (< (NTH 2 (NTH 3 (NTH 7 X))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 7 X)))) (< (NTH 3 (NTH 3 (NTH 7 X))) 256)
    (TRUE-LISTP (NTH 8 X)) (TRUE-LISTP (NTH 0 (NTH 8 X)))
    (NATP (NTH 0 (NTH 0 (NTH 8 X)))) (< (NTH 0 (NTH 0 (NTH 8 X))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 8 X)))) (< (NTH 1 (NTH 0 (NTH 8 X))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 8 X)))) (< (NTH 2 (NTH 0 (NTH 8 X))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 8 X)))) (< (NTH 3 (NTH 0 (NTH 8 X))) 256)
    (TRUE-LISTP (NTH 1 (NTH 8 X))) (NATP (NTH 0 (NTH 1 (NTH 8 X))))
    (< (NTH 0 (NTH 1 (NTH 8 X))) 256) (NATP (NTH 1 (NTH 1 (NTH 8 X))))
    (< (NTH 1 (NTH 1 (NTH 8 X))) 256) (NATP (NTH 2 (NTH 1 (NTH 8 X))))
    (< (NTH 2 (NTH 1 (NTH 8 X))) 256) (NATP (NTH 3 (NTH 1 (NTH 8 X))))
    (< (NTH 3 (NTH 1 (NTH 8 X))) 256) (TRUE-LISTP (NTH 2 (NTH 8 X)))
    (NATP (NTH 0 (NTH 2 (NTH 8 X)))) (< (NTH 0 (NTH 2 (NTH 8 X))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 8 X)))) (< (NTH 1 (NTH 2 (NTH 8 X))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 8 X)))) (< (NTH 2 (NTH 2 (NTH 8 X))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 8 X)))) (< (NTH 3 (NTH 2 (NTH 8 X))) 256)
    (TRUE-LISTP (NTH 3 (NTH 8 X))) (NATP (NTH 0 (NTH 3 (NTH 8 X))))
    (< (NTH 0 (NTH 3 (NTH 8 X))) 256) (NATP (NTH 1 (NTH 3 (NTH 8 X))))
    (< (NTH 1 (NTH 3 (NTH 8 X))) 256) (NATP (NTH 2 (NTH 3 (NTH 8 X))))
    (< (NTH 2 (NTH 3 (NTH 8 X))) 256) (NATP (NTH 3 (NTH 3 (NTH 8 X))))
    (< (NTH 3 (NTH 3 (NTH 8 X))) 256)))

(DEFUN |$itr_loop_iter_rnds_6|
  (|tmp_262| |rndKeys_3| |initialKey_2| |tmp_263| |$limit| |hist_8|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_263|))) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$itr_3_typep| |initialKey_2|) (|$itr_4_typep| |rndKeys_3|)
        (|$itr_3_typep| |tmp_262|) (NATP |tmp_263|) (NATP |$limit|)
        (TRUE-LISTP |hist_8|)))
    (LIST (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)))
    (IF (> |tmp_263| |$limit|) |hist_8|
      (LET
        ((|$arm-result|
           (COND ((< |tmp_263| 1) (|itr_xorS_1| |tmp_262| |initialKey_2|))
             (T
               (LET* ((|tmp_264| (NTH 0 |hist_8|)))
                 (|itr_round_1| |tmp_264|
                   (NTH (LOGHEAD 4 (C-WORD-% (C-WORD-- 32 |tmp_263| 1) 9))
                     |rndKeys_3|)))))))
        (|$itr_loop_iter_rnds_6| |tmp_262| |rndKeys_3| |initialKey_2|
          (|1+| |tmp_263|) |$limit|
          (UPDATE-NTH (LOGHEAD 0 |tmp_263|) |$arm-result| |hist_8|))))))

(DEFUND |itr_iter_rnds_6| (|tmp_262| |rndKeys_3| |initialKey_2| |tmp_263|)
  (IF (NOT (NATP |tmp_263|))
    (LIST (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)))
    (|$itr_loop_iter_rnds_6| |tmp_262| |rndKeys_3| |initialKey_2| 0 |tmp_263|
      (LIST
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))))))

(DEFUND |$itr_5_typep| (X)
  (AND (TRUE-LISTP X) (TRUE-LISTP (NTH 0 X)) (TRUE-LISTP (NTH 0 (NTH 0 X)))
    (NATP (NTH 0 (NTH 0 (NTH 0 X)))) (< (NTH 0 (NTH 0 (NTH 0 X))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 0 X)))) (< (NTH 1 (NTH 0 (NTH 0 X))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 0 X)))) (< (NTH 2 (NTH 0 (NTH 0 X))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 0 X)))) (< (NTH 3 (NTH 0 (NTH 0 X))) 256)
    (TRUE-LISTP (NTH 1 (NTH 0 X))) (NATP (NTH 0 (NTH 1 (NTH 0 X))))
    (< (NTH 0 (NTH 1 (NTH 0 X))) 256) (NATP (NTH 1 (NTH 1 (NTH 0 X))))
    (< (NTH 1 (NTH 1 (NTH 0 X))) 256) (NATP (NTH 2 (NTH 1 (NTH 0 X))))
    (< (NTH 2 (NTH 1 (NTH 0 X))) 256) (NATP (NTH 3 (NTH 1 (NTH 0 X))))
    (< (NTH 3 (NTH 1 (NTH 0 X))) 256) (TRUE-LISTP (NTH 2 (NTH 0 X)))
    (NATP (NTH 0 (NTH 2 (NTH 0 X)))) (< (NTH 0 (NTH 2 (NTH 0 X))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 0 X)))) (< (NTH 1 (NTH 2 (NTH 0 X))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 0 X)))) (< (NTH 2 (NTH 2 (NTH 0 X))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 0 X)))) (< (NTH 3 (NTH 2 (NTH 0 X))) 256)
    (TRUE-LISTP (NTH 3 (NTH 0 X))) (NATP (NTH 0 (NTH 3 (NTH 0 X))))
    (< (NTH 0 (NTH 3 (NTH 0 X))) 256) (NATP (NTH 1 (NTH 3 (NTH 0 X))))
    (< (NTH 1 (NTH 3 (NTH 0 X))) 256) (NATP (NTH 2 (NTH 3 (NTH 0 X))))
    (< (NTH 2 (NTH 3 (NTH 0 X))) 256) (NATP (NTH 3 (NTH 3 (NTH 0 X))))
    (< (NTH 3 (NTH 3 (NTH 0 X))) 256) (TRUE-LISTP (NTH 1 X))
    (TRUE-LISTP (NTH 0 (NTH 1 X))) (TRUE-LISTP (NTH 0 (NTH 0 (NTH 1 X))))
    (NATP (NTH 0 (NTH 0 (NTH 0 (NTH 1 X)))))
    (< (NTH 0 (NTH 0 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 0 (NTH 1 X)))))
    (< (NTH 1 (NTH 0 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 0 (NTH 1 X)))))
    (< (NTH 2 (NTH 0 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 0 (NTH 1 X)))))
    (< (NTH 3 (NTH 0 (NTH 0 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 1 (NTH 0 (NTH 1 X))))
    (NATP (NTH 0 (NTH 1 (NTH 0 (NTH 1 X)))))
    (< (NTH 0 (NTH 1 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 0 (NTH 1 X)))))
    (< (NTH 1 (NTH 1 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 0 (NTH 1 X)))))
    (< (NTH 2 (NTH 1 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 0 (NTH 1 X)))))
    (< (NTH 3 (NTH 1 (NTH 0 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 2 (NTH 0 (NTH 1 X))))
    (NATP (NTH 0 (NTH 2 (NTH 0 (NTH 1 X)))))
    (< (NTH 0 (NTH 2 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 0 (NTH 1 X)))))
    (< (NTH 1 (NTH 2 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 0 (NTH 1 X)))))
    (< (NTH 2 (NTH 2 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 0 (NTH 1 X)))))
    (< (NTH 3 (NTH 2 (NTH 0 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 3 (NTH 0 (NTH 1 X))))
    (NATP (NTH 0 (NTH 3 (NTH 0 (NTH 1 X)))))
    (< (NTH 0 (NTH 3 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 0 (NTH 1 X)))))
    (< (NTH 1 (NTH 3 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 0 (NTH 1 X)))))
    (< (NTH 2 (NTH 3 (NTH 0 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 0 (NTH 1 X)))))
    (< (NTH 3 (NTH 3 (NTH 0 (NTH 1 X)))) 256) (TRUE-LISTP (NTH 1 (NTH 1 X)))
    (TRUE-LISTP (NTH 0 (NTH 1 (NTH 1 X))))
    (NATP (NTH 0 (NTH 0 (NTH 1 (NTH 1 X)))))
    (< (NTH 0 (NTH 0 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 1 (NTH 1 X)))))
    (< (NTH 1 (NTH 0 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 1 (NTH 1 X)))))
    (< (NTH 2 (NTH 0 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 1 (NTH 1 X)))))
    (< (NTH 3 (NTH 0 (NTH 1 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 1 (NTH 1 (NTH 1 X))))
    (NATP (NTH 0 (NTH 1 (NTH 1 (NTH 1 X)))))
    (< (NTH 0 (NTH 1 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 1 (NTH 1 X)))))
    (< (NTH 1 (NTH 1 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 1 (NTH 1 X)))))
    (< (NTH 2 (NTH 1 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 1 (NTH 1 X)))))
    (< (NTH 3 (NTH 1 (NTH 1 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 2 (NTH 1 (NTH 1 X))))
    (NATP (NTH 0 (NTH 2 (NTH 1 (NTH 1 X)))))
    (< (NTH 0 (NTH 2 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 1 (NTH 1 X)))))
    (< (NTH 1 (NTH 2 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 1 (NTH 1 X)))))
    (< (NTH 2 (NTH 2 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 1 (NTH 1 X)))))
    (< (NTH 3 (NTH 2 (NTH 1 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 3 (NTH 1 (NTH 1 X))))
    (NATP (NTH 0 (NTH 3 (NTH 1 (NTH 1 X)))))
    (< (NTH 0 (NTH 3 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 1 (NTH 1 X)))))
    (< (NTH 1 (NTH 3 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 1 (NTH 1 X)))))
    (< (NTH 2 (NTH 3 (NTH 1 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 1 (NTH 1 X)))))
    (< (NTH 3 (NTH 3 (NTH 1 (NTH 1 X)))) 256) (TRUE-LISTP (NTH 2 (NTH 1 X)))
    (TRUE-LISTP (NTH 0 (NTH 2 (NTH 1 X))))
    (NATP (NTH 0 (NTH 0 (NTH 2 (NTH 1 X)))))
    (< (NTH 0 (NTH 0 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 2 (NTH 1 X)))))
    (< (NTH 1 (NTH 0 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 2 (NTH 1 X)))))
    (< (NTH 2 (NTH 0 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 2 (NTH 1 X)))))
    (< (NTH 3 (NTH 0 (NTH 2 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 1 (NTH 2 (NTH 1 X))))
    (NATP (NTH 0 (NTH 1 (NTH 2 (NTH 1 X)))))
    (< (NTH 0 (NTH 1 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 2 (NTH 1 X)))))
    (< (NTH 1 (NTH 1 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 2 (NTH 1 X)))))
    (< (NTH 2 (NTH 1 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 2 (NTH 1 X)))))
    (< (NTH 3 (NTH 1 (NTH 2 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 2 (NTH 2 (NTH 1 X))))
    (NATP (NTH 0 (NTH 2 (NTH 2 (NTH 1 X)))))
    (< (NTH 0 (NTH 2 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 2 (NTH 1 X)))))
    (< (NTH 1 (NTH 2 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 2 (NTH 1 X)))))
    (< (NTH 2 (NTH 2 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 2 (NTH 1 X)))))
    (< (NTH 3 (NTH 2 (NTH 2 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 3 (NTH 2 (NTH 1 X))))
    (NATP (NTH 0 (NTH 3 (NTH 2 (NTH 1 X)))))
    (< (NTH 0 (NTH 3 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 2 (NTH 1 X)))))
    (< (NTH 1 (NTH 3 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 2 (NTH 1 X)))))
    (< (NTH 2 (NTH 3 (NTH 2 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 2 (NTH 1 X)))))
    (< (NTH 3 (NTH 3 (NTH 2 (NTH 1 X)))) 256) (TRUE-LISTP (NTH 3 (NTH 1 X)))
    (TRUE-LISTP (NTH 0 (NTH 3 (NTH 1 X))))
    (NATP (NTH 0 (NTH 0 (NTH 3 (NTH 1 X)))))
    (< (NTH 0 (NTH 0 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 3 (NTH 1 X)))))
    (< (NTH 1 (NTH 0 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 3 (NTH 1 X)))))
    (< (NTH 2 (NTH 0 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 3 (NTH 1 X)))))
    (< (NTH 3 (NTH 0 (NTH 3 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 1 (NTH 3 (NTH 1 X))))
    (NATP (NTH 0 (NTH 1 (NTH 3 (NTH 1 X)))))
    (< (NTH 0 (NTH 1 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 3 (NTH 1 X)))))
    (< (NTH 1 (NTH 1 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 3 (NTH 1 X)))))
    (< (NTH 2 (NTH 1 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 3 (NTH 1 X)))))
    (< (NTH 3 (NTH 1 (NTH 3 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 2 (NTH 3 (NTH 1 X))))
    (NATP (NTH 0 (NTH 2 (NTH 3 (NTH 1 X)))))
    (< (NTH 0 (NTH 2 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 3 (NTH 1 X)))))
    (< (NTH 1 (NTH 2 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 3 (NTH 1 X)))))
    (< (NTH 2 (NTH 2 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 3 (NTH 1 X)))))
    (< (NTH 3 (NTH 2 (NTH 3 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 3 (NTH 3 (NTH 1 X))))
    (NATP (NTH 0 (NTH 3 (NTH 3 (NTH 1 X)))))
    (< (NTH 0 (NTH 3 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 3 (NTH 1 X)))))
    (< (NTH 1 (NTH 3 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 3 (NTH 1 X)))))
    (< (NTH 2 (NTH 3 (NTH 3 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 3 (NTH 1 X)))))
    (< (NTH 3 (NTH 3 (NTH 3 (NTH 1 X)))) 256) (TRUE-LISTP (NTH 4 (NTH 1 X)))
    (TRUE-LISTP (NTH 0 (NTH 4 (NTH 1 X))))
    (NATP (NTH 0 (NTH 0 (NTH 4 (NTH 1 X)))))
    (< (NTH 0 (NTH 0 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 4 (NTH 1 X)))))
    (< (NTH 1 (NTH 0 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 4 (NTH 1 X)))))
    (< (NTH 2 (NTH 0 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 4 (NTH 1 X)))))
    (< (NTH 3 (NTH 0 (NTH 4 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 1 (NTH 4 (NTH 1 X))))
    (NATP (NTH 0 (NTH 1 (NTH 4 (NTH 1 X)))))
    (< (NTH 0 (NTH 1 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 4 (NTH 1 X)))))
    (< (NTH 1 (NTH 1 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 4 (NTH 1 X)))))
    (< (NTH 2 (NTH 1 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 4 (NTH 1 X)))))
    (< (NTH 3 (NTH 1 (NTH 4 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 2 (NTH 4 (NTH 1 X))))
    (NATP (NTH 0 (NTH 2 (NTH 4 (NTH 1 X)))))
    (< (NTH 0 (NTH 2 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 4 (NTH 1 X)))))
    (< (NTH 1 (NTH 2 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 4 (NTH 1 X)))))
    (< (NTH 2 (NTH 2 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 4 (NTH 1 X)))))
    (< (NTH 3 (NTH 2 (NTH 4 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 3 (NTH 4 (NTH 1 X))))
    (NATP (NTH 0 (NTH 3 (NTH 4 (NTH 1 X)))))
    (< (NTH 0 (NTH 3 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 4 (NTH 1 X)))))
    (< (NTH 1 (NTH 3 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 4 (NTH 1 X)))))
    (< (NTH 2 (NTH 3 (NTH 4 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 4 (NTH 1 X)))))
    (< (NTH 3 (NTH 3 (NTH 4 (NTH 1 X)))) 256) (TRUE-LISTP (NTH 5 (NTH 1 X)))
    (TRUE-LISTP (NTH 0 (NTH 5 (NTH 1 X))))
    (NATP (NTH 0 (NTH 0 (NTH 5 (NTH 1 X)))))
    (< (NTH 0 (NTH 0 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 5 (NTH 1 X)))))
    (< (NTH 1 (NTH 0 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 5 (NTH 1 X)))))
    (< (NTH 2 (NTH 0 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 5 (NTH 1 X)))))
    (< (NTH 3 (NTH 0 (NTH 5 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 1 (NTH 5 (NTH 1 X))))
    (NATP (NTH 0 (NTH 1 (NTH 5 (NTH 1 X)))))
    (< (NTH 0 (NTH 1 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 5 (NTH 1 X)))))
    (< (NTH 1 (NTH 1 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 5 (NTH 1 X)))))
    (< (NTH 2 (NTH 1 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 5 (NTH 1 X)))))
    (< (NTH 3 (NTH 1 (NTH 5 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 2 (NTH 5 (NTH 1 X))))
    (NATP (NTH 0 (NTH 2 (NTH 5 (NTH 1 X)))))
    (< (NTH 0 (NTH 2 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 5 (NTH 1 X)))))
    (< (NTH 1 (NTH 2 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 5 (NTH 1 X)))))
    (< (NTH 2 (NTH 2 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 5 (NTH 1 X)))))
    (< (NTH 3 (NTH 2 (NTH 5 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 3 (NTH 5 (NTH 1 X))))
    (NATP (NTH 0 (NTH 3 (NTH 5 (NTH 1 X)))))
    (< (NTH 0 (NTH 3 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 5 (NTH 1 X)))))
    (< (NTH 1 (NTH 3 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 5 (NTH 1 X)))))
    (< (NTH 2 (NTH 3 (NTH 5 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 5 (NTH 1 X)))))
    (< (NTH 3 (NTH 3 (NTH 5 (NTH 1 X)))) 256) (TRUE-LISTP (NTH 6 (NTH 1 X)))
    (TRUE-LISTP (NTH 0 (NTH 6 (NTH 1 X))))
    (NATP (NTH 0 (NTH 0 (NTH 6 (NTH 1 X)))))
    (< (NTH 0 (NTH 0 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 6 (NTH 1 X)))))
    (< (NTH 1 (NTH 0 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 6 (NTH 1 X)))))
    (< (NTH 2 (NTH 0 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 6 (NTH 1 X)))))
    (< (NTH 3 (NTH 0 (NTH 6 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 1 (NTH 6 (NTH 1 X))))
    (NATP (NTH 0 (NTH 1 (NTH 6 (NTH 1 X)))))
    (< (NTH 0 (NTH 1 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 6 (NTH 1 X)))))
    (< (NTH 1 (NTH 1 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 6 (NTH 1 X)))))
    (< (NTH 2 (NTH 1 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 6 (NTH 1 X)))))
    (< (NTH 3 (NTH 1 (NTH 6 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 2 (NTH 6 (NTH 1 X))))
    (NATP (NTH 0 (NTH 2 (NTH 6 (NTH 1 X)))))
    (< (NTH 0 (NTH 2 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 6 (NTH 1 X)))))
    (< (NTH 1 (NTH 2 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 6 (NTH 1 X)))))
    (< (NTH 2 (NTH 2 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 6 (NTH 1 X)))))
    (< (NTH 3 (NTH 2 (NTH 6 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 3 (NTH 6 (NTH 1 X))))
    (NATP (NTH 0 (NTH 3 (NTH 6 (NTH 1 X)))))
    (< (NTH 0 (NTH 3 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 6 (NTH 1 X)))))
    (< (NTH 1 (NTH 3 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 6 (NTH 1 X)))))
    (< (NTH 2 (NTH 3 (NTH 6 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 6 (NTH 1 X)))))
    (< (NTH 3 (NTH 3 (NTH 6 (NTH 1 X)))) 256) (TRUE-LISTP (NTH 7 (NTH 1 X)))
    (TRUE-LISTP (NTH 0 (NTH 7 (NTH 1 X))))
    (NATP (NTH 0 (NTH 0 (NTH 7 (NTH 1 X)))))
    (< (NTH 0 (NTH 0 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 7 (NTH 1 X)))))
    (< (NTH 1 (NTH 0 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 7 (NTH 1 X)))))
    (< (NTH 2 (NTH 0 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 7 (NTH 1 X)))))
    (< (NTH 3 (NTH 0 (NTH 7 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 1 (NTH 7 (NTH 1 X))))
    (NATP (NTH 0 (NTH 1 (NTH 7 (NTH 1 X)))))
    (< (NTH 0 (NTH 1 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 7 (NTH 1 X)))))
    (< (NTH 1 (NTH 1 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 7 (NTH 1 X)))))
    (< (NTH 2 (NTH 1 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 7 (NTH 1 X)))))
    (< (NTH 3 (NTH 1 (NTH 7 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 2 (NTH 7 (NTH 1 X))))
    (NATP (NTH 0 (NTH 2 (NTH 7 (NTH 1 X)))))
    (< (NTH 0 (NTH 2 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 7 (NTH 1 X)))))
    (< (NTH 1 (NTH 2 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 7 (NTH 1 X)))))
    (< (NTH 2 (NTH 2 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 7 (NTH 1 X)))))
    (< (NTH 3 (NTH 2 (NTH 7 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 3 (NTH 7 (NTH 1 X))))
    (NATP (NTH 0 (NTH 3 (NTH 7 (NTH 1 X)))))
    (< (NTH 0 (NTH 3 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 7 (NTH 1 X)))))
    (< (NTH 1 (NTH 3 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 7 (NTH 1 X)))))
    (< (NTH 2 (NTH 3 (NTH 7 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 7 (NTH 1 X)))))
    (< (NTH 3 (NTH 3 (NTH 7 (NTH 1 X)))) 256) (TRUE-LISTP (NTH 8 (NTH 1 X)))
    (TRUE-LISTP (NTH 0 (NTH 8 (NTH 1 X))))
    (NATP (NTH 0 (NTH 0 (NTH 8 (NTH 1 X)))))
    (< (NTH 0 (NTH 0 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 0 (NTH 8 (NTH 1 X)))))
    (< (NTH 1 (NTH 0 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 0 (NTH 8 (NTH 1 X)))))
    (< (NTH 2 (NTH 0 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 0 (NTH 8 (NTH 1 X)))))
    (< (NTH 3 (NTH 0 (NTH 8 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 1 (NTH 8 (NTH 1 X))))
    (NATP (NTH 0 (NTH 1 (NTH 8 (NTH 1 X)))))
    (< (NTH 0 (NTH 1 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 8 (NTH 1 X)))))
    (< (NTH 1 (NTH 1 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 8 (NTH 1 X)))))
    (< (NTH 2 (NTH 1 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 8 (NTH 1 X)))))
    (< (NTH 3 (NTH 1 (NTH 8 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 2 (NTH 8 (NTH 1 X))))
    (NATP (NTH 0 (NTH 2 (NTH 8 (NTH 1 X)))))
    (< (NTH 0 (NTH 2 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 2 (NTH 8 (NTH 1 X)))))
    (< (NTH 1 (NTH 2 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 2 (NTH 8 (NTH 1 X)))))
    (< (NTH 2 (NTH 2 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 2 (NTH 8 (NTH 1 X)))))
    (< (NTH 3 (NTH 2 (NTH 8 (NTH 1 X)))) 256)
    (TRUE-LISTP (NTH 3 (NTH 8 (NTH 1 X))))
    (NATP (NTH 0 (NTH 3 (NTH 8 (NTH 1 X)))))
    (< (NTH 0 (NTH 3 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 8 (NTH 1 X)))))
    (< (NTH 1 (NTH 3 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 8 (NTH 1 X)))))
    (< (NTH 2 (NTH 3 (NTH 8 (NTH 1 X)))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 8 (NTH 1 X)))))
    (< (NTH 3 (NTH 3 (NTH 8 (NTH 1 X)))) 256) (TRUE-LISTP (NTH 2 X))
    (TRUE-LISTP (NTH 0 (NTH 2 X))) (NATP (NTH 0 (NTH 0 (NTH 2 X))))
    (< (NTH 0 (NTH 0 (NTH 2 X))) 256) (NATP (NTH 1 (NTH 0 (NTH 2 X))))
    (< (NTH 1 (NTH 0 (NTH 2 X))) 256) (NATP (NTH 2 (NTH 0 (NTH 2 X))))
    (< (NTH 2 (NTH 0 (NTH 2 X))) 256) (NATP (NTH 3 (NTH 0 (NTH 2 X))))
    (< (NTH 3 (NTH 0 (NTH 2 X))) 256) (TRUE-LISTP (NTH 1 (NTH 2 X)))
    (NATP (NTH 0 (NTH 1 (NTH 2 X)))) (< (NTH 0 (NTH 1 (NTH 2 X))) 256)
    (NATP (NTH 1 (NTH 1 (NTH 2 X)))) (< (NTH 1 (NTH 1 (NTH 2 X))) 256)
    (NATP (NTH 2 (NTH 1 (NTH 2 X)))) (< (NTH 2 (NTH 1 (NTH 2 X))) 256)
    (NATP (NTH 3 (NTH 1 (NTH 2 X)))) (< (NTH 3 (NTH 1 (NTH 2 X))) 256)
    (TRUE-LISTP (NTH 2 (NTH 2 X))) (NATP (NTH 0 (NTH 2 (NTH 2 X))))
    (< (NTH 0 (NTH 2 (NTH 2 X))) 256) (NATP (NTH 1 (NTH 2 (NTH 2 X))))
    (< (NTH 1 (NTH 2 (NTH 2 X))) 256) (NATP (NTH 2 (NTH 2 (NTH 2 X))))
    (< (NTH 2 (NTH 2 (NTH 2 X))) 256) (NATP (NTH 3 (NTH 2 (NTH 2 X))))
    (< (NTH 3 (NTH 2 (NTH 2 X))) 256) (TRUE-LISTP (NTH 3 (NTH 2 X)))
    (NATP (NTH 0 (NTH 3 (NTH 2 X)))) (< (NTH 0 (NTH 3 (NTH 2 X))) 256)
    (NATP (NTH 1 (NTH 3 (NTH 2 X)))) (< (NTH 1 (NTH 3 (NTH 2 X))) 256)
    (NATP (NTH 2 (NTH 3 (NTH 2 X)))) (< (NTH 2 (NTH 3 (NTH 2 X))) 256)
    (NATP (NTH 3 (NTH 3 (NTH 2 X)))) (< (NTH 3 (NTH 3 (NTH 2 X))) 256)))

(DEFUND |itr_rounds_1| (|tmp_258| |tmp_259|)
  (IF (NOT (AND (|$itr_5_typep| |tmp_259|) (|$itr_3_typep| |tmp_258|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|initialKey_1| (NTH 0 |tmp_259|)) (|rndKeys_2| (NTH 1 |tmp_259|))
        (|tmp_260|
          (LET*
            ((|tmp_261|
               (|itr_iter_rnds_6| |tmp_258| |rndKeys_2| |initialKey_1|
                 (C-WORD-- 32 10 1)))) (NTH 0 |tmp_261|))))
      (|itr_finalRound_1| |tmp_260| (NTH 2 |tmp_259|)))))

(DEFUN |$itr_loop_iter_rnds_5|
  (|tmp_255| |invRndKeys_2| |finalKey_2| |tmp_256| |$limit| |hist_7|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_256|))) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$itr_3_typep| |finalKey_2|) (|$itr_4_typep| |invRndKeys_2|)
        (|$itr_3_typep| |tmp_255|) (NATP |tmp_256|) (NATP |$limit|)
        (TRUE-LISTP |hist_7|)))
    (LIST (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)))
    (IF (> |tmp_256| |$limit|) |hist_7|
      (LET
        ((|$arm-result|
           (COND ((< |tmp_256| 1) (|itr_xorS_1| |tmp_255| |finalKey_2|))
             (T
               (LET* ((|tmp_257| (NTH 0 |hist_7|)))
                 (|itr_invRound_1| |tmp_257|
                   (NTH (LOGHEAD 4 (C-WORD-% (C-WORD-- 32 |tmp_256| 1) 9))
                     |invRndKeys_2|)))))))
        (|$itr_loop_iter_rnds_5| |tmp_255| |invRndKeys_2| |finalKey_2|
          (|1+| |tmp_256|) |$limit|
          (UPDATE-NTH (LOGHEAD 0 |tmp_256|) |$arm-result| |hist_7|))))))

(DEFUND |itr_iter_rnds_5| (|tmp_255| |invRndKeys_2| |finalKey_2| |tmp_256|)
  (IF (NOT (NATP |tmp_256|))
    (LIST (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)))
    (|$itr_loop_iter_rnds_5| |tmp_255| |invRndKeys_2| |finalKey_2| 0
      |tmp_256|
      (LIST
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))))))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_29| (|rndKeys_1| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 9 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 9) NIL
      (CONS
        (LET ((|tmp_251| (NTH |$i| (LIST 0 1 2 3 4 5 6 7 8))))
          (NTH (|-| (|1-| 9) |tmp_251|) |rndKeys_1|))
        (|$itr_comp_29| |rndKeys_1| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_30| (|tmp_250| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 9 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 9) NIL
      (CONS
        (LET ((|tmp_252| (NTH |$i| (LIST 0 1 2 3 4 5 6 7 8))))
          (|itr_invMixColumn_1| (NTH |tmp_252| |tmp_250|)))
        (|$itr_comp_30| |tmp_250| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_invRounds_1| (|tmp_248| |tmp_249|)
  (IF (NOT (AND (|$itr_5_typep| |tmp_249|) (|$itr_3_typep| |tmp_248|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|rndKeys_1| (NTH 1 |tmp_249|)) (|finalKey_1| (NTH 2 |tmp_249|))
        (|invRndKeys_1|
          (LET* ((|tmp_250| (|$itr_comp_29| |rndKeys_1| 0)))
            (|$itr_comp_30| |tmp_250| 0)))
        (|tmp_253|
          (LET*
            ((|tmp_254|
               (|itr_iter_rnds_5| |tmp_248| |invRndKeys_1| |finalKey_1|
                 (C-WORD-- 32 10 1)))) (NTH 0 |tmp_254|))))
      (|itr_invFinalRound_1| |tmp_253| (NTH 0 |tmp_249|)))))

(DEFUND |itr_xorB4_1| (|tmp_246| |tmp_247|)
  (IF (NOT (AND (|$itr_2_typep| |tmp_247|) (|$itr_2_typep| |tmp_246|)))
    (LIST 0 0 0 0)
    (C-WORD-SPLIT 8 4
      (C-WORD-^^ (C-WORD-JOIN 8 |tmp_246|) (C-WORD-JOIN 8 |tmp_247|)))))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_31| (|p_1| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_245| (NTH |$i| (LIST 0 1 2 3))))
          (NTH (NTH |tmp_245| |p_1|) (|itr_sbox_1|)))
        (|$itr_comp_31| |p_1| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_subByte_1| (|p_1|)
  (IF (NOT (AND (|$itr_2_typep| |p_1|))) (LIST 0 0 0 0)
    (|$itr_comp_31| |p_1| 0)))

(DEFUND |itr_rcon_1| (|i_1|)
  (IF (NOT (AND (|$itr_1_typep| |i_1|))) (LIST 0 0 0 0)
    (LIST (|itr_gpower_1| 2 (C-WORD-- 8 |i_1| 1)) 0 0 0)))

(DEFUND |itr_nextWord_1| (|tmp_238| |tmp_239| |tmp_240|)
  (IF
    (NOT
      (AND (|$itr_2_typep| |tmp_240|) (|$itr_2_typep| |tmp_239|)
        (|$itr_1_typep| |tmp_238|))) (LIST 0 0 0 0)
    (LET*
      ((|tmp_241|
         (IF (C-== (C-WORD-% |tmp_238| 4) 0)
           (LET*
             ((|tmp_242|
                (LET* ((|tmp_243| (C-VEC-<<< |tmp_240| 1)))
                  (|itr_subByte_1| |tmp_243|)))
               (|tmp_244| (|itr_rcon_1| (C-WORD-/ |tmp_238| 4))))
             (|itr_xorB4_1| |tmp_242| |tmp_244|)) |tmp_240|)))
      (|itr_xorB4_1| |tmp_239| |tmp_241|))))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_32| (|$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 40 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 40) NIL
      (CONS
        (LET
          ((|tmp_237|
             (NTH |$i|
               (LIST 0 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 21
                 22 23 24 25 26 27 28 29 30 31 32 33 34 35 36 37 38 39))))
          (C-WORD-+ 8 4 |tmp_237|)) (|$itr_comp_32| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_tmp_236| NIL (|$itr_comp_32| 0))

(DEFUN |$itr_loop_iter_w_3| (|keyCols_2| |tmp_235| |$limit| |hist_6|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 |$limit| (|-| |tmp_235|))) :HINTS
      (MEASURE-HINT)))
  (IF
    (NOT
      (AND (|$itr_3_typep| |keyCols_2|) (NATP |tmp_235|) (NATP |$limit|)
        (TRUE-LISTP |hist_6|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (IF (> |tmp_235| |$limit|) |hist_6|
      (LET
        ((|$arm-result|
           (COND ((< |tmp_235| 4) (NTH (LOGHEAD 2 |tmp_235|) |keyCols_2|))
             (T
               (|itr_nextWord_1|
                 (NTH (LOGHEAD 6 (C-WORD-% (C-WORD-- 32 |tmp_235| 4) 40))
                   (|itr_tmp_236|))
                 (NTH (LOGHEAD 6 (C-WORD-- 32 |tmp_235| 4)) |hist_6|)
                 (NTH (LOGHEAD 6 (C-WORD-- 32 |tmp_235| 1)) |hist_6|))))))
        (|$itr_loop_iter_w_3| |keyCols_2| (|1+| |tmp_235|) |$limit|
          (UPDATE-NTH (LOGHEAD 6 |tmp_235|) |$arm-result| |hist_6|))))))

(DEFUND |itr_iter_w_3| (|keyCols_2| |tmp_235|)
  (IF (NOT (NATP |tmp_235|))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (|$itr_loop_iter_w_3| |keyCols_2| 0 |tmp_235|
      (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
        (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)))))

(DEFUND |$itr_6_typep| (X)
  (AND (TRUE-LISTP X) (NATP (NTH 0 X)) (< (NTH 0 X) 256) (NATP (NTH 1 X))
    (< (NTH 1 X) 256) (NATP (NTH 2 X)) (< (NTH 2 X) 256) (NATP (NTH 3 X))
    (< (NTH 3 X) 256) (NATP (NTH 4 X)) (< (NTH 4 X) 256) (NATP (NTH 5 X))
    (< (NTH 5 X) 256) (NATP (NTH 6 X)) (< (NTH 6 X) 256) (NATP (NTH 7 X))
    (< (NTH 7 X) 256) (NATP (NTH 8 X)) (< (NTH 8 X) 256) (NATP (NTH 9 X))
    (< (NTH 9 X) 256) (NATP (NTH 10 X)) (< (NTH 10 X) 256) (NATP (NTH 11 X))
    (< (NTH 11 X) 256) (NATP (NTH 12 X)) (< (NTH 12 X) 256) (NATP (NTH 13 X))
    (< (NTH 13 X) 256) (NATP (NTH 14 X)) (< (NTH 14 X) 256) (NATP (NTH 15 X))
    (< (NTH 15 X) 256)))

(DEFUND |itr_keyExpansion_1| (|key_2|)
  (IF (NOT (AND (|$itr_6_typep| |key_2|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)
      (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET*
      ((|keyCols_1| (C-VEC-SPLIT 4 |key_2|))
        (|tmp_234| (|itr_iter_w_3| |keyCols_1| 43))) (FIRSTN 44 |tmp_234|))))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_35| (|tmp_232| |ws_1| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_233| (NTH |$i| (LIST 0 1 2 3))))
          (NTH |tmp_232| (NTH |tmp_233| |ws_1|)))
        (|$itr_comp_35| |tmp_232| |ws_1| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_34| (|ws_1| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_232| (NTH |$i| (LIST 0 1 2 3))))
          (|$itr_comp_35| |tmp_232| |ws_1| 0))
        (|$itr_comp_34| |ws_1| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_33| (|tmp_229| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 11 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 11) NIL
      (CONS
        (LET ((|tmp_231| (NTH |$i| (LIST 0 1 2 3 4 5 6 7 8 9 10))))
          (LET* ((|ws_1| (NTH |tmp_231| |tmp_229|)))
            (|$itr_comp_34| |ws_1| 0)))
        (|$itr_comp_33| |tmp_229| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_keySchedule_1| (|key_1|)
  (IF (NOT (AND (|$itr_6_typep| |key_1|)))
    (LIST (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
      (LIST
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
        (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)))
      (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0)))
    (LET*
      ((|rKeys_1|
         (LET*
           ((|tmp_229|
              (LET* ((|tmp_230| (|itr_keyExpansion_1| |key_1|)))
                (C-VEC-SPLIT 4 |tmp_230|)))) (|$itr_comp_33| |tmp_229| 0))))
      (LIST (NTH 0 |rKeys_1|) (C-VEC-SEGMENT 9 |rKeys_1| 1)
        (NTH 10 |rKeys_1|)))))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_37| (|tmp_227| |tmp_226| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_228| (NTH |$i| (LIST 0 1 2 3))))
          (NTH |tmp_227| (NTH |tmp_228| |tmp_226|)))
        (|$itr_comp_37| |tmp_227| |tmp_226| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_36| (|tmp_226| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_227| (NTH |$i| (LIST 0 1 2 3))))
          (|$itr_comp_37| |tmp_227| |tmp_226| 0))
        (|$itr_comp_36| |tmp_226| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_stripe_1| (|block_1|)
  (IF (NOT (AND (|$itr_6_typep| |block_1|)))
    (LIST (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0) (LIST 0 0 0 0))
    (LET* ((|tmp_226| (C-VEC-SPLIT 4 |block_1|)))
      (|$itr_comp_36| |tmp_226| 0))))

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_39| (|tmp_224| |state_1| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_225| (NTH |$i| (LIST 0 1 2 3))))
          (NTH |tmp_224| (NTH |tmp_225| |state_1|)))
        (|$itr_comp_39| |tmp_224| |state_1| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(SET-IGNORE-OK T)

(DEFUN |$itr_comp_38| (|state_1| |$i|)
  (DECLARE
    (XARGS :MEASURE (ACL2-COUNT (|+| 1 4 (|-| |$i|))) :HINTS (MEASURE-HINT)))
  (IF (NOT (NATP |$i|)) NIL
    (IF (>= |$i| 4) NIL
      (CONS
        (LET ((|tmp_224| (NTH |$i| (LIST 0 1 2 3))))
          (|$itr_comp_39| |tmp_224| |state_1| 0))
        (|$itr_comp_38| |state_1| (|1+| |$i|))))))

(SET-IGNORE-OK NIL)

(DEFUND |itr_unstripe_1| (|state_1|)
  (IF (NOT (AND (|$itr_3_typep| |state_1|)))
    (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    (C-VEC-JOIN (|$itr_comp_38| |state_1| 0))))

(DEFUND |itr_encrypt_1| (|tmp_220| |tmp_221|)
  (IF (NOT (AND (|$itr_5_typep| |tmp_221|) (|$itr_6_typep| |tmp_220|)))
    (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    (LET*
      ((|tmp_222|
         (LET* ((|tmp_223| (|itr_stripe_1| |tmp_220|)))
           (|itr_rounds_1| |tmp_223| |tmp_221|))))
      (|itr_unstripe_1| |tmp_222|))))

(DEFUND |itr_decrypt_1| (|tmp_216| |tmp_217|)
  (IF (NOT (AND (|$itr_5_typep| |tmp_217|) (|$itr_6_typep| |tmp_216|)))
    (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    (LET*
      ((|tmp_218|
         (LET* ((|tmp_219| (|itr_stripe_1| |tmp_216|)))
           (|itr_invRounds_1| |tmp_219| |tmp_217|))))
      (|itr_unstripe_1| |tmp_218|))))

(DEFUND |itr_aes| (|tmp_128| |tmp_129|)
  (IF (NOT (AND (|$itr_6_typep| |tmp_129|) (|$itr_6_typep| |tmp_128|)))
    (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    (LET* ((|tmp_205| (|itr_keySchedule_1| |tmp_129|)))
      (|itr_encrypt_1| |tmp_128| |tmp_205|))))

(DEFUND |itr_sea| (|tmp_126| |tmp_127|)
  (IF (NOT (AND (|$itr_6_typep| |tmp_127|) (|$itr_6_typep| |tmp_126|)))
    (LIST 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)
    (LET* ((|tmp_206| (|itr_keySchedule_1| |tmp_127|)))
      (|itr_decrypt_1| |tmp_126| |tmp_206|))))

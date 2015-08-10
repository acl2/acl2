
(in-package "ACL2")

;; This file contains the examples from
;; our paper and their proofs using the BDD system.

;; For a description of the example and how this relates to
;; our SAT system see our workshop paper, "A SAT-Based
;; Procedure for Verifying Finite State Machines in ACL2."

(defun n-bleq (n x y)
  (if (zp n)
      t
    (and (iff (car x) (car y))
         (n-bleq (1- n) (cdr x) (cdr y)))))

(defun xor3 (x y z)
  (xor x (xor y z)))

(defun maj3 (x y z)
  (if x (or y z)
    (and y z)))

;; Returns a n+1 length sum of the first
;; n bits of a and b (plus the carray).
(defun v-adder (n c a b)
  (if (zp n)
      (list c)
    (cons (xor3 c (car a) (car b))
          (v-adder (1- n)
                   (maj3 c (car a) (car b))
                   (cdr a) (cdr b)))))

(defthm v-adder-rewrite
  (equal
   (v-adder n c a b)
   (if (zp n)
       (list c)
     (cons (xor3 c (car a) (car b))
           (v-adder (1- n)
                    (maj3 c (car a) (car b))
                    (cdr a) (cdr b))))))

(defthm n-bleq-rewrite
  (equal
   (n-bleq n x y)
   (if (zp n)
       t
     (and (iff (car x) (car y))
          (n-bleq (1- n) (cdr x) (cdr y))))))

;;(i-am-here)

;; 4 Bit Adder Associativity
(defthm 4-adder-assoc
  (let ((a (list a0 a1 a2 a3))
        (b (list b0 b1 b2 b3))
        (c (list c0 c1 c2 c3)))
 (implies
  (and (boolean-listp a)
       (boolean-listp b)
       (boolean-listp c))
  (n-bleq 4 (v-adder 4 nil (v-adder 4 nil a b) c)
          (v-adder 4 nil a (v-adder 4 nil b c)))))
  :hints (("Goal" :bdd (:vars (a0 b0 c0 a1 b1 c1 a2 b2 c2 a3 b3 c3)))))

;; 32 bit adder associativity
(defthm 32-adder-assoc
  (let ((a (list a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21
                 a22 a23 a24 a25 a26 a27 a28 a29 a30 a31))
        (b (list b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21
                 b22 b23 b24 b25 b26 b27 b28 b29 b30 b31))
        (c (list c0 c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 c13 c14 c15 c16 c17 c18 c19 c20 c21
                 c22 c23 c24 c25 c26 c27 c28 c29 c30 c31)))
    (implies
     (and (boolean-listp a)
          (boolean-listp b)
          (boolean-listp c))
     (n-bleq 32 (v-adder 32 nil (v-adder 32 nil a b) c)
             (v-adder 32 nil a (v-adder 32 nil b c)))))
  :hints (("Goal" :bdd (:vars (a0 b0 c0 a1 b1 c1 a2 b2 c2 a3 b3 c3 a4 b4 c4
                                  a5 b5 c5 a6 b6 c6 a7 b7 c7 a8 b8 c8 a9 b9 c9
                                  a10 b10 c10 a11 b11 c11 a12 b12 c12 a13 b13 c13 a14 b14 c14
                                  a15 b15 c15 a16 b16 c16 a17 b17 c17 a18 b18 c18 a19 b19 c19
                                  a20 b20 c20 a21 b21 c21 a22 b22 c22 a23 b23 c23 a24 b24 c24
                                  a25 b25 c25 a26 b26 c26 a27 b27 c27 a28 b28 c28 a29 b29 c29
                                  a30 b30 c30 a31 b31 c31)))))

#| I'm not proving the larger examples inside the book, just to save time

;; 200 Bit adder associativity
(defthm 200-adder-assoc
  (let ((a (list
A_0 A_1 A_2 A_3 A_4 A_5 A_6 A_7 A_8
     A_9 A_10 A_11 A_12 A_13 A_14 A_15 A_16
     A_17 A_18 A_19 A_20 A_21 A_22 A_23 A_24
     A_25 A_26 A_27 A_28 A_29 A_30 A_31 A_32
     A_33 A_34 A_35 A_36 A_37 A_38 A_39 A_40
     A_41 A_42 A_43 A_44 A_45 A_46 A_47 A_48
     A_49 A_50 A_51 A_52 A_53 A_54 A_55 A_56
     A_57 A_58 A_59 A_60 A_61 A_62 A_63 A_64
     A_65 A_66 A_67 A_68 A_69 A_70 A_71 A_72
     A_73 A_74 A_75 A_76 A_77 A_78 A_79 A_80
     A_81 A_82 A_83 A_84 A_85 A_86 A_87 A_88
     A_89 A_90 A_91 A_92 A_93 A_94 A_95 A_96
     A_97 A_98 A_99 A_100 A_101 A_102 A_103
     A_104 A_105 A_106 A_107 A_108 A_109
     A_110 A_111 A_112 A_113 A_114 A_115
     A_116 A_117 A_118 A_119 A_120 A_121
     A_122 A_123 A_124 A_125 A_126 A_127
     A_128 A_129 A_130 A_131 A_132 A_133
     A_134 A_135 A_136 A_137 A_138 A_139
     A_140 A_141 A_142 A_143 A_144 A_145
     A_146 A_147 A_148 A_149 A_150 A_151
     A_152 A_153 A_154 A_155 A_156 A_157
     A_158 A_159 A_160 A_161 A_162 A_163
     A_164 A_165 A_166 A_167 A_168 A_169
     A_170 A_171 A_172 A_173 A_174 A_175
     A_176 A_177 A_178 A_179 A_180 A_181
     A_182 A_183 A_184 A_185 A_186 A_187
     A_188 A_189 A_190 A_191 A_192 A_193
     A_194 A_195 A_196 A_197 A_198 A_199))

        (b (list
B_0 B_1 B_2 B_3 B_4 B_5 B_6 B_7 B_8
     B_9 B_10 B_11 B_12 B_13 B_14 B_15 B_16
     B_17 B_18 B_19 B_20 B_21 B_22 B_23 B_24
     B_25 B_26 B_27 B_28 B_29 B_30 B_31 B_32
     B_33 B_34 B_35 B_36 B_37 B_38 B_39 B_40
     B_41 B_42 B_43 B_44 B_45 B_46 B_47 B_48
     B_49 B_50 B_51 B_52 B_53 B_54 B_55 B_56
     B_57 B_58 B_59 B_60 B_61 B_62 B_63 B_64
     B_65 B_66 B_67 B_68 B_69 B_70 B_71 B_72
     B_73 B_74 B_75 B_76 B_77 B_78 B_79 B_80
     B_81 B_82 B_83 B_84 B_85 B_86 B_87 B_88
     B_89 B_90 B_91 B_92 B_93 B_94 B_95 B_96
     B_97 B_98 B_99 B_100 B_101 B_102 B_103
     B_104 B_105 B_106 B_107 B_108 B_109
     B_110 B_111 B_112 B_113 B_114 B_115
     B_116 B_117 B_118 B_119 B_120 B_121
     B_122 B_123 B_124 B_125 B_126 B_127
     B_128 B_129 B_130 B_131 B_132 B_133
     B_134 B_135 B_136 B_137 B_138 B_139
     B_140 B_141 B_142 B_143 B_144 B_145
     B_146 B_147 B_148 B_149 B_150 B_151
     B_152 B_153 B_154 B_155 B_156 B_157
     B_158 B_159 B_160 B_161 B_162 B_163
     B_164 B_165 B_166 B_167 B_168 B_169
     B_170 B_171 B_172 B_173 B_174 B_175
     B_176 B_177 B_178 B_179 B_180 B_181
     B_182 B_183 B_184 B_185 B_186 B_187
     B_188 B_189 B_190 B_191 B_192 B_193
     B_194 B_195 B_196 B_197 B_198 B_199))

        (c (list
C_0 C_1 C_2 C_3 C_4 C_5 C_6 C_7 C_8
     C_9 C_10 C_11 C_12 C_13 C_14 C_15 C_16
     C_17 C_18 C_19 C_20 C_21 C_22 C_23 C_24
     C_25 C_26 C_27 C_28 C_29 C_30 C_31 C_32
     C_33 C_34 C_35 C_36 C_37 C_38 C_39 C_40
     C_41 C_42 C_43 C_44 C_45 C_46 C_47 C_48
     C_49 C_50 C_51 C_52 C_53 C_54 C_55 C_56
     C_57 C_58 C_59 C_60 C_61 C_62 C_63 C_64
     C_65 C_66 C_67 C_68 C_69 C_70 C_71 C_72
     C_73 C_74 C_75 C_76 C_77 C_78 C_79 C_80
     C_81 C_82 C_83 C_84 C_85 C_86 C_87 C_88
     C_89 C_90 C_91 C_92 C_93 C_94 C_95 C_96
     C_97 C_98 C_99 C_100 C_101 C_102 C_103
     C_104 C_105 C_106 C_107 C_108 C_109
     C_110 C_111 C_112 C_113 C_114 C_115
     C_116 C_117 C_118 C_119 C_120 C_121
     C_122 C_123 C_124 C_125 C_126 C_127
     C_128 C_129 C_130 C_131 C_132 C_133
     C_134 C_135 C_136 C_137 C_138 C_139
     C_140 C_141 C_142 C_143 C_144 C_145
     C_146 C_147 C_148 C_149 C_150 C_151
     C_152 C_153 C_154 C_155 C_156 C_157
     C_158 C_159 C_160 C_161 C_162 C_163
     C_164 C_165 C_166 C_167 C_168 C_169
     C_170 C_171 C_172 C_173 C_174 C_175
     C_176 C_177 C_178 C_179 C_180 C_181
     C_182 C_183 C_184 C_185 C_186 C_187
     C_188 C_189 C_190 C_191 C_192 C_193
     C_194 C_195 C_196 C_197 C_198 C_199)))

    (implies
     (and (boolean-listp a)
          (boolean-listp b)
          (boolean-listp c))
     (n-bleq 200 (v-adder 200 nil (v-adder 200 nil a b) c)
             (v-adder 200 nil a (v-adder 200 nil b c)))))
;;  :hints (("Goal" :bdd (:vars nil))))

  :hints (("Goal" :bdd (:vars (A_0 B_0 C_0 A_1 B_1 C_1
     A_2 B_2 C_2 A_3 B_3 C_3 A_4 B_4 C_4 A_5
     B_5 C_5 A_6 B_6 C_6 A_7 B_7 C_7 A_8 B_8
     C_8 A_9 B_9 C_9 A_10 B_10 C_10 A_11 B_11
     C_11 A_12 B_12 C_12 A_13 B_13 C_13 A_14
     B_14 C_14 A_15 B_15 C_15 A_16 B_16 C_16
     A_17 B_17 C_17 A_18 B_18 C_18 A_19 B_19
     C_19 A_20 B_20 C_20 A_21 B_21 C_21 A_22
     B_22 C_22 A_23 B_23 C_23 A_24 B_24 C_24
     A_25 B_25 C_25 A_26 B_26 C_26 A_27 B_27
     C_27 A_28 B_28 C_28 A_29 B_29 C_29 A_30
     B_30 C_30 A_31 B_31 C_31 A_32 B_32 C_32
     A_33 B_33 C_33 A_34 B_34 C_34 A_35 B_35
     C_35 A_36 B_36 C_36 A_37 B_37 C_37 A_38
     B_38 C_38 A_39 B_39 C_39 A_40 B_40 C_40
     A_41 B_41 C_41 A_42 B_42 C_42 A_43 B_43
     C_43 A_44 B_44 C_44 A_45 B_45 C_45 A_46
     B_46 C_46 A_47 B_47 C_47 A_48 B_48 C_48
     A_49 B_49 C_49 A_50 B_50 C_50 A_51 B_51
     C_51 A_52 B_52 C_52 A_53 B_53 C_53 A_54
     B_54 C_54 A_55 B_55 C_55 A_56 B_56 C_56
     A_57 B_57 C_57 A_58 B_58 C_58 A_59 B_59
     C_59 A_60 B_60 C_60 A_61 B_61 C_61 A_62
     B_62 C_62 A_63 B_63 C_63 A_64 B_64 C_64
     A_65 B_65 C_65 A_66 B_66 C_66 A_67 B_67
     C_67 A_68 B_68 C_68 A_69 B_69 C_69 A_70
     B_70 C_70 A_71 B_71 C_71 A_72 B_72 C_72
     A_73 B_73 C_73 A_74 B_74 C_74 A_75 B_75
     C_75 A_76 B_76 C_76 A_77 B_77 C_77 A_78
     B_78 C_78 A_79 B_79 C_79 A_80 B_80 C_80
     A_81 B_81 C_81 A_82 B_82 C_82 A_83 B_83
     C_83 A_84 B_84 C_84 A_85 B_85 C_85 A_86
     B_86 C_86 A_87 B_87 C_87 A_88 B_88 C_88
     A_89 B_89 C_89 A_90 B_90 C_90 A_91 B_91
     C_91 A_92 B_92 C_92 A_93 B_93 C_93 A_94
     B_94 C_94 A_95 B_95 C_95 A_96 B_96 C_96
     A_97 B_97 C_97 A_98 B_98 C_98 A_99 B_99
     C_99 A_100 B_100 C_100 A_101 B_101 C_101
     A_102 B_102 C_102 A_103 B_103 C_103
     A_104 B_104 C_104 A_105 B_105 C_105
     A_106 B_106 C_106 A_107 B_107 C_107
     A_108 B_108 C_108 A_109 B_109 C_109
     A_110 B_110 C_110 A_111 B_111 C_111
     A_112 B_112 C_112 A_113 B_113 C_113
     A_114 B_114 C_114 A_115 B_115 C_115
     A_116 B_116 C_116 A_117 B_117 C_117
     A_118 B_118 C_118 A_119 B_119 C_119
     A_120 B_120 C_120 A_121 B_121 C_121
     A_122 B_122 C_122 A_123 B_123 C_123
     A_124 B_124 C_124 A_125 B_125 C_125
     A_126 B_126 C_126 A_127 B_127 C_127
     A_128 B_128 C_128 A_129 B_129 C_129
     A_130 B_130 C_130 A_131 B_131 C_131
     A_132 B_132 C_132 A_133 B_133 C_133
     A_134 B_134 C_134 A_135 B_135 C_135
     A_136 B_136 C_136 A_137 B_137 C_137
     A_138 B_138 C_138 A_139 B_139 C_139
     A_140 B_140 C_140 A_141 B_141 C_141
     A_142 B_142 C_142 A_143 B_143 C_143
     A_144 B_144 C_144 A_145 B_145 C_145
     A_146 B_146 C_146 A_147 B_147 C_147
     A_148 B_148 C_148 A_149 B_149 C_149
     A_150 B_150 C_150 A_151 B_151 C_151
     A_152 B_152 C_152 A_153 B_153 C_153
     A_154 B_154 C_154 A_155 B_155 C_155
     A_156 B_156 C_156 A_157 B_157 C_157
     A_158 B_158 C_158 A_159 B_159 C_159
     A_160 B_160 C_160 A_161 B_161 C_161
     A_162 B_162 C_162 A_163 B_163 C_163
     A_164 B_164 C_164 A_165 B_165 C_165
     A_166 B_166 C_166 A_167 B_167 C_167
     A_168 B_168 C_168 A_169 B_169 C_169
     A_170 B_170 C_170 A_171 B_171 C_171
     A_172 B_172 C_172 A_173 B_173 C_173
     A_174 B_174 C_174 A_175 B_175 C_175
     A_176 B_176 C_176 A_177 B_177 C_177
     A_178 B_178 C_178 A_179 B_179 C_179
     A_180 B_180 C_180 A_181 B_181 C_181
     A_182 B_182 C_182 A_183 B_183 C_183
     A_184 B_184 C_184 A_185 B_185 C_185
     A_186 B_186 C_186 A_187 B_187 C_187
     A_188 B_188 C_188 A_189 B_189 C_189
     A_190 B_190 C_190 A_191 B_191 C_191
     A_192 B_192 C_192 A_193 B_193 C_193
     A_194 B_194 C_194 A_195 B_195 C_195
     A_196 B_196 C_196 A_197 B_197 C_197
     A_198 B_198 C_198 A_199 B_199 C_199)))))
|#


(defun nth-cdr (n x)
  (if (zp n)
      x
    (nth-cdr (1- n) (cdr x))))

(defun nth-sublist (n lst)
  (if (zp n)
      nil
    (cons (car lst) (nth-sublist (1- n) (cdr lst)))))

(defun append-n (n x y)
  (if (zp n)
      y
    (cons (car x) (append-n (1- n) (cdr x) y))))

(defun n-nills (n)
  (if (zp n)
      nil
    (cons nil (n-nills (1- n)))))

(defun rev-n (n x ans)
  (if (zp n)
      ans
    (rev-n (1- n) (cdr x) (cons (car x) ans))))

(defun mux-n-help (n in rsel)
  (if (zp n)
      (car in)
    (if (car rsel)
        (mux-n-help (1- n) (nth-cdr (expt 2 (1- n)) in) (cdr rsel))
      (mux-n-help (1- n) in (cdr rsel)))))

(defun mux-n (n in sel)
  (mux-n-help n in (rev-n n sel nil)))

(defun mux-n-w-help (n w in)
  (if (zp n)
      nil
    (cons (car in) (mux-n-w-help (1- n) w (nth-cdr w in)))))

(defun mux-n-w1 (nw sn w in sel)
  (if (zp nw)
      nil
    (cons (mux-n sn (mux-n-w-help (expt 2 sn) w in) sel)
          (mux-n-w1 (1- nw) sn w (cdr in) sel))))

(defun mux-n-w (n w in sel)
  (mux-n-w1 w n w in sel))

(defun shift-mux-help (n w reg)
  (if (zp n)
      nil
    (append-n w reg (shift-mux-help (1- n) w (cons nil reg)))))

(defun shifter (sn rn rshift reg)
  (if (zp sn)
      reg
    (mux-n-w sn rn (shift-mux-help (expt 2 sn) rn reg) rshift)))

(defthm append-n-rewrite
  (equal
   (append-n n x y)
   (if (zp n)
       y
     (cons (car x) (append-n (1- n) (cdr x) y)))))

(defthm nth-cdr-rewrite
  (equal
   (nth-cdr n x)
   (if (zp n)
       x
     (nth-cdr (1- n) (cdr x)))))

(defthm nth-sublist-rewrite
  (equal
   (nth-sublist n lst)
   (if (zp n)
       nil
     (cons (car lst) (nth-sublist (1- n) (cdr lst))))))

(defthm n-nills-rewrite
  (equal
   (n-nills n)
   (if (zp n)
       nil
     (cons nil (n-nills (1- n))))))

(defthm rev-n-rewrite
  (equal
   (rev-n n x ans)
   (if (zp n)
       ans
     (rev-n (1- n) (cdr x) (cons (car x) ans)))))

(defthm mux-n-help-rewrite
  (equal
   (mux-n-help n in rsel)
   (if (zp n)
       (car in)
     (if (car rsel)
         (mux-n-help (1- n) (nth-cdr (expt 2 (1- n)) in) (cdr rsel))
       (mux-n-help (1- n) in (cdr rsel)))))
  :hints (("Goal" :in-theory (disable nth-cdr-rewrite))))

(defthm mux-n-w-help-rewrite
  (equal
   (mux-n-w-help n w in)
   (if (zp n)
       nil
     (cons (car in) (mux-n-w-help (1- n) w (nth-cdr w in)))))
  :hints (("Goal" :in-theory (disable nth-cdr-rewrite))))

(defthm mux-n-w1-rewrite
  (equal
   (mux-n-w1 nw sn w in sel)
   (if (zp nw)
       nil
     (cons (mux-n sn (mux-n-w-help (expt 2 sn) w in) sel)
           (mux-n-w1 (1- nw) sn w (cdr in) sel))))
    :hints (("Goal" :in-theory (disable mux-n-w-help-rewrite mux-n-w-help mux-n mux-n-help-rewrite))))

(defthm shift-mux-help-rewrite
  (equal
   (shift-mux-help n w reg)
   (if (zp n)
       nil
     (append-n w reg (shift-mux-help (1- n) w (cons nil reg)))))
  :hints (("Goal" :in-theory (disable append-n-rewrite))))

;;(i-am-here)

;; 32x6 Shift-0
(defthm 32x6-shift-0
 (let ((shift0 (list S_0 S_1 S_2 S_3 S_4 t))
       (reg (list R_0 R_1 R_2 R_3 R_4 R_5 R_6 R_7
     R_8 R_9 R_10 R_11 R_12 R_13 R_14 R_15
     R_16 R_17 R_18 R_19 R_20 R_21 R_22 R_23
     R_24 R_25 R_26 R_27 R_28 R_29 R_30 R_31)))
   (implies
    (and (boolean-listp shift0)
         (boolean-listp reg))
    (equal (shifter 6 32 shift0 reg)
           (n-nills 32))))
 :hints (("Goal" :bdd (:vars nil))))

#| I'm not proving the larger examples inside the book, just to save time

;; 64x7 Shift-0
(defthm 64x7-shift-0
 (let ((shift0 (list S_0 S_1 S_2 S_3 S_4 S_5 t))
       (reg (list R_0 R_1 R_2 R_3 R_4 R_5 R_6 R_7
                  R_8 R_9 R_10 R_11 R_12 R_13 R_14 R_15
                  R_16 R_17 R_18 R_19 R_20 R_21 R_22 R_23
                  R_24 R_25 R_26 R_27 R_28 R_29 R_30 R_31
                  R_32 R_33 R_34 R_35 R_36 R_37 R_38 R_39
                  R_40 R_41 R_42 R_43 R_44 R_45 R_46 R_47
                  R_48 R_49 R_50 R_51 R_52 R_53 R_54 R_55
                  R_56 R_57 R_58 R_59 R_60 R_61 R_62 R_63)))
   (implies
    (and (boolean-listp shift0)
         (boolean-listp reg))
    (equal (shifter 7 64 shift0 reg)
           (n-nills 64))))
 :hints (("Goal" :bdd (:vars nil))))
|#

;; 32x4 Add-shift
(defthm 32x4-add-shift
 (let ((shift0 (list S_0 S_1 S_2 S_3))
       (shift1 (list SS_0 SS_1 SS_2 SS_3))
       (reg (list REG_0 REG_1
       REG_2 REG_3 REG_4 REG_5 REG_6 REG_7
       REG_8 REG_9 REG_10 REG_11 REG_12 REG_13
       REG_14 REG_15 REG_16 REG_17 REG_18
       REG_19 REG_20 REG_21 REG_22 REG_23
       REG_24 REG_25 REG_26 REG_27 REG_28
       REG_29 REG_30 REG_31)))
   (implies (and (boolean-listp shift0)
                 (boolean-listp shift1)
                 (boolean-listp reg))
            (equal (shifter 4 32 shift0 (shifter 4 32 shift1 reg))
                   (shifter 5 32 (v-adder 4 nil shift0 shift1) reg))))
       :hints (("Goal" :bdd (:vars nil))))

#| I'm not proving the larger examples inside the book, just to save time

;; 64x6 Add-shift
(defthm 64x6-add-shift
 (let ((shift0 (list S_0 S_1 S_2 S_3 S_4 S_5))
       (shift1 (list SS_0 SS_1 SS_2 SS_3 SS_4 SS_5))
       (reg (list REG_0 REG_1
       REG_2 REG_3 REG_4 REG_5 REG_6 REG_7
       REG_8 REG_9 REG_10 REG_11 REG_12 REG_13
       REG_14 REG_15 REG_16 REG_17 REG_18
       REG_19 REG_20 REG_21 REG_22 REG_23
       REG_24 REG_25 REG_26 REG_27 REG_28
       REG_29 REG_30 REG_31 REG_32 REG_33
       REG_34 REG_35 REG_36 REG_37 REG_38
       REG_39 REG_40 REG_41 REG_42 REG_43
       REG_44 REG_45 REG_46 REG_47 REG_48
       REG_49 REG_50 REG_51 REG_52 REG_53
       REG_54 REG_55 REG_56 REG_57 REG_58
       REG_59 REG_60 REG_61 REG_62 REG_63)))
   (implies (and (boolean-listp shift0)
                 (boolean-listp shift1)
                 (boolean-listp reg))
            (equal (shifter 6 64 shift0 (shifter 6 64 shift1 reg))
                   (shifter 7 64 (v-adder 6 nil shift0 shift1) reg))))
       :hints (("Goal" :bdd (:vars nil))))
|#

(defun eif (x y z)
  (if x y z))

(defthm eif-rewrite
  (equal (eif x (cons a y) (cons b z))
         (cons (if x a b) (eif x y z)))
  :hints (("Goal" :in-theory (enable eif))))

(defthm eif-rewrite-nil
  (equal (eif x nil nil)
         nil)
  :hints (("Goal" :in-theory (enable eif))))

(in-theory (disable eif))

(defun increment (n x)
  (if (zp n)
      nil
    (if (car x)
        (cons nil (increment (1- n) (cdr x)))
      (cons t (cdr x)))))

(defthm increment-rewrite
  (equal (increment n x)
         (if (zp n)
             nil
           (eif (car x)
               (cons nil (increment (1- n) (cdr x)))
             (cons t (cdr x)))))
  :hints (("Goal" :in-theory (enable eif))))

(defun next_digit_counter_state (x)
  (if (n-bleq 4 x '(t nil nil t))
      (list '(nil nil nil nil) t)
    (list (increment 4 x) nil)))

(defun enif (x y z)
  (if x y z))

(defthm enif-rewrite
  (equal (enif x (cons y0 y) (cons z0 z))
         (cons (eif x y0 z0) (eif x y z)))
  :hints (("Goal" :in-theory (enable eif enif))))

(defthm enif-nil
  (equal (enif x nil nil)
         nil)
  :hints (("Goal" :in-theory (enable enif))))

(in-theory (disable enif))

(defthm next_digit_counter_state_open
  (equal (next_digit_counter_state x)
         (enif (n-bleq 4 x '(t nil nil t))
              (list '(nil nil nil nil) t)
              (list (increment 4 x) nil)))
  :hints (("Goal" :in-theory (enable enif eif))))

(in-theory (disable next_digit_counter_state))

(defun next_counter_state (n x)
  (let* ((curr_d_out (next_digit_counter_state (car x)))
         (curr_d_val (car curr_d_out))
         (curr_d_reset (cadr curr_d_out)))
    (if (zp n)
        nil
      (if curr_d_reset
          (cons curr_d_val (next_counter_state (1- n) (cdr x)))
        (cons curr_d_val (cdr x))))))

(defun eeif (x y z) (if x y z))

(defthm eeif-open
  (equal
   (eeif x (cons y0 y) (cons z0 z))
   (cons (eif x y0 z0) (eeif x y z)))
  :hints (("Goal" :in-theory (enable eeif eif))))

(defthm eeif-nil
  (equal
   (eeif x nil nil)
   nil))

(in-theory (disable eeif))

(defthm next_counter_state-rewrite
  (equal
   (next_counter_state n x)
   (let* ((curr_d_out (next_digit_counter_state (car x)))
          (curr_d_val (car curr_d_out))
          (curr_d_reset (cadr curr_d_out)))
     (if (zp n)
         nil
       (eeif curr_d_reset
          (cons curr_d_val (next_counter_state (1- n) (cdr x)))
        (cons curr_d_val (cdr x))))))
  :hints (("Goal" :in-theory (e/d (eeif eif) (next_digit_counter_state_open)))))

(in-theory (disable eif))

(defun valid_digit (a)
  (let ((a1 (cadr a))
        (a2 (caddr a))
        (a3 (cadddr a)))
    (not (and a3 (or a2 a1)))))

(defun valid_digits (n x)
  (if (zp n)
      (not (consp x))
    (and (valid_digit (car x))
         (valid_digits (1- n) (cdr x)))))


(defthm valid_digits-rewrite
  (equal
   (valid_digits n x)
   (if (zp n)
       (not (consp x))
     (and (valid_digit (car x))
          (valid_digits (1- n) (cdr x)))))
  :hints (("Goal" :in-theory (enable eif))))

;; (i-am-here)

;; 100 Digit Counter Invariant
(defthm 100-dig-inv
  (let ((X_99 (LIST X_99_0 X_99_1 X_99_2 X_99_3))
        (X_98 (LIST X_98_0 X_98_1 X_98_2 X_98_3))
        (X_97 (LIST X_97_0 X_97_1 X_97_2 X_97_3))
        (X_96 (LIST X_96_0 X_96_1 X_96_2 X_96_3))
        (X_95 (LIST X_95_0 X_95_1 X_95_2 X_95_3))
        (X_94 (LIST X_94_0 X_94_1 X_94_2 X_94_3))
        (X_93 (LIST X_93_0 X_93_1 X_93_2 X_93_3))
        (X_92 (LIST X_92_0 X_92_1 X_92_2 X_92_3))
        (X_91 (LIST X_91_0 X_91_1 X_91_2 X_91_3))
        (X_90 (LIST X_90_0 X_90_1 X_90_2 X_90_3))
        (X_89 (LIST X_89_0 X_89_1 X_89_2 X_89_3))
        (X_88 (LIST X_88_0 X_88_1 X_88_2 X_88_3))
        (X_87 (LIST X_87_0 X_87_1 X_87_2 X_87_3))
        (X_86 (LIST X_86_0 X_86_1 X_86_2 X_86_3))
        (X_85 (LIST X_85_0 X_85_1 X_85_2 X_85_3))
        (X_84 (LIST X_84_0 X_84_1 X_84_2 X_84_3))
        (X_83 (LIST X_83_0 X_83_1 X_83_2 X_83_3))
        (X_82 (LIST X_82_0 X_82_1 X_82_2 X_82_3))
        (X_81 (LIST X_81_0 X_81_1 X_81_2 X_81_3))
        (X_80 (LIST X_80_0 X_80_1 X_80_2 X_80_3))
        (X_79 (LIST X_79_0 X_79_1 X_79_2 X_79_3))
        (X_78 (LIST X_78_0 X_78_1 X_78_2 X_78_3))
        (X_77 (LIST X_77_0 X_77_1 X_77_2 X_77_3))
        (X_76 (LIST X_76_0 X_76_1 X_76_2 X_76_3))
        (X_75 (LIST X_75_0 X_75_1 X_75_2 X_75_3))
        (X_74 (LIST X_74_0 X_74_1 X_74_2 X_74_3))
        (X_73 (LIST X_73_0 X_73_1 X_73_2 X_73_3))
        (X_72 (LIST X_72_0 X_72_1 X_72_2 X_72_3))
        (X_71 (LIST X_71_0 X_71_1 X_71_2 X_71_3))
        (X_70 (LIST X_70_0 X_70_1 X_70_2 X_70_3))
        (X_69 (LIST X_69_0 X_69_1 X_69_2 X_69_3))
        (X_68 (LIST X_68_0 X_68_1 X_68_2 X_68_3))
        (X_67 (LIST X_67_0 X_67_1 X_67_2 X_67_3))
        (X_66 (LIST X_66_0 X_66_1 X_66_2 X_66_3))
        (X_65 (LIST X_65_0 X_65_1 X_65_2 X_65_3))
        (X_64 (LIST X_64_0 X_64_1 X_64_2 X_64_3))
        (X_63 (LIST X_63_0 X_63_1 X_63_2 X_63_3))
        (X_62 (LIST X_62_0 X_62_1 X_62_2 X_62_3))
        (X_61 (LIST X_61_0 X_61_1 X_61_2 X_61_3))
        (X_60 (LIST X_60_0 X_60_1 X_60_2 X_60_3))
        (X_59 (LIST X_59_0 X_59_1 X_59_2 X_59_3))
        (X_58 (LIST X_58_0 X_58_1 X_58_2 X_58_3))
        (X_57 (LIST X_57_0 X_57_1 X_57_2 X_57_3))
        (X_56 (LIST X_56_0 X_56_1 X_56_2 X_56_3))
        (X_55 (LIST X_55_0 X_55_1 X_55_2 X_55_3))
        (X_54 (LIST X_54_0 X_54_1 X_54_2 X_54_3))
        (X_53 (LIST X_53_0 X_53_1 X_53_2 X_53_3))
        (X_52 (LIST X_52_0 X_52_1 X_52_2 X_52_3))
        (X_51 (LIST X_51_0 X_51_1 X_51_2 X_51_3))
        (X_50 (LIST X_50_0 X_50_1 X_50_2 X_50_3))
        (X_49 (LIST X_49_0 X_49_1 X_49_2 X_49_3))
        (X_48 (LIST X_48_0 X_48_1 X_48_2 X_48_3))
        (X_47 (LIST X_47_0 X_47_1 X_47_2 X_47_3))
        (X_46 (LIST X_46_0 X_46_1 X_46_2 X_46_3))
        (X_45 (LIST X_45_0 X_45_1 X_45_2 X_45_3))
        (X_44 (LIST X_44_0 X_44_1 X_44_2 X_44_3))
        (X_43 (LIST X_43_0 X_43_1 X_43_2 X_43_3))
        (X_42 (LIST X_42_0 X_42_1 X_42_2 X_42_3))
        (X_41 (LIST X_41_0 X_41_1 X_41_2 X_41_3))
        (X_40 (LIST X_40_0 X_40_1 X_40_2 X_40_3))
        (X_39 (LIST X_39_0 X_39_1 X_39_2 X_39_3))
        (X_38 (LIST X_38_0 X_38_1 X_38_2 X_38_3))
        (X_37 (LIST X_37_0 X_37_1 X_37_2 X_37_3))
        (X_36 (LIST X_36_0 X_36_1 X_36_2 X_36_3))
        (X_35 (LIST X_35_0 X_35_1 X_35_2 X_35_3))
        (X_34 (LIST X_34_0 X_34_1 X_34_2 X_34_3))
        (X_33 (LIST X_33_0 X_33_1 X_33_2 X_33_3))
        (X_32 (LIST X_32_0 X_32_1 X_32_2 X_32_3))
        (X_31 (LIST X_31_0 X_31_1 X_31_2 X_31_3))
        (X_30 (LIST X_30_0 X_30_1 X_30_2 X_30_3))
        (X_29 (LIST X_29_0 X_29_1 X_29_2 X_29_3))
        (X_28 (LIST X_28_0 X_28_1 X_28_2 X_28_3))
        (X_27 (LIST X_27_0 X_27_1 X_27_2 X_27_3))
        (X_26 (LIST X_26_0 X_26_1 X_26_2 X_26_3))
        (X_25 (LIST X_25_0 X_25_1 X_25_2 X_25_3))
        (X_24 (LIST X_24_0 X_24_1 X_24_2 X_24_3))
        (X_23 (LIST X_23_0 X_23_1 X_23_2 X_23_3))
        (X_22 (LIST X_22_0 X_22_1 X_22_2 X_22_3))
        (X_21 (LIST X_21_0 X_21_1 X_21_2 X_21_3))
        (X_20 (LIST X_20_0 X_20_1 X_20_2 X_20_3))
        (X_19 (LIST X_19_0 X_19_1 X_19_2 X_19_3))
        (X_18 (LIST X_18_0 X_18_1 X_18_2 X_18_3))
        (X_17 (LIST X_17_0 X_17_1 X_17_2 X_17_3))
        (X_16 (LIST X_16_0 X_16_1 X_16_2 X_16_3))
        (X_15 (LIST X_15_0 X_15_1 X_15_2 X_15_3))
        (X_14 (LIST X_14_0 X_14_1 X_14_2 X_14_3))
        (X_13 (LIST X_13_0 X_13_1 X_13_2 X_13_3))
        (X_12 (LIST X_12_0 X_12_1 X_12_2 X_12_3))
        (X_11 (LIST X_11_0 X_11_1 X_11_2 X_11_3))
        (X_10 (LIST X_10_0 X_10_1 X_10_2 X_10_3))
        (X_9 (LIST X_9_0 X_9_1 X_9_2 X_9_3))
        (X_8 (LIST X_8_0 X_8_1 X_8_2 X_8_3))
        (X_7 (LIST X_7_0 X_7_1 X_7_2 X_7_3))
        (X_6 (LIST X_6_0 X_6_1 X_6_2 X_6_3))
        (X_5 (LIST X_5_0 X_5_1 X_5_2 X_5_3))
        (X_4 (LIST X_4_0 X_4_1 X_4_2 X_4_3))
        (X_3 (LIST X_3_0 X_3_1 X_3_2 X_3_3))
        (X_2 (LIST X_2_0 X_2_1 X_2_2 X_2_3))
        (X_1 (LIST X_1_0 X_1_1 X_1_2 X_1_3))
        (X_0 (LIST X_0_0 X_0_1 X_0_2 X_0_3)))
    (let ((x (list
              X_0 X_1 X_2
              X_3 X_4 X_5 X_6 X_7 X_8 X_9 X_10 X_11
              X_12 X_13 X_14 X_15 X_16 X_17 X_18 X_19
              X_20 X_21 X_22 X_23 X_24 X_25 X_26 X_27
              X_28 X_29 X_30 X_31 X_32 X_33 X_34 X_35
              X_36 X_37 X_38 X_39 X_40 X_41 X_42 X_43
              X_44 X_45 X_46 X_47 X_48 X_49 X_50 X_51
              X_52 X_53 X_54 X_55 X_56 X_57 X_58 X_59
              X_60 X_61 X_62 X_63 X_64 X_65 X_66 X_67
              X_68 X_69 X_70 X_71 X_72 X_73 X_74 X_75
              X_76 X_77 X_78 X_79 X_80 X_81 X_82 X_83
              X_84 X_85 X_86 X_87 X_88 X_89 X_90 X_91
              X_92 X_93 X_94 X_95 X_96 X_97 X_98 X_99)))
      (implies (and
                (BOOLEAN-LISTP X_99)
                (BOOLEAN-LISTP X_98)
                (BOOLEAN-LISTP X_97)
                (BOOLEAN-LISTP X_96)
                (BOOLEAN-LISTP X_95)
                (BOOLEAN-LISTP X_94)
                (BOOLEAN-LISTP X_93)
                (BOOLEAN-LISTP X_92)
                (BOOLEAN-LISTP X_91)
                (BOOLEAN-LISTP X_90)
                (BOOLEAN-LISTP X_89)
                (BOOLEAN-LISTP X_88)
                (BOOLEAN-LISTP X_87)
                (BOOLEAN-LISTP X_86)
                (BOOLEAN-LISTP X_85)
                (BOOLEAN-LISTP X_84)
                (BOOLEAN-LISTP X_83)
                (BOOLEAN-LISTP X_82)
                (BOOLEAN-LISTP X_81)
                (BOOLEAN-LISTP X_80)
                (BOOLEAN-LISTP X_79)
                (BOOLEAN-LISTP X_78)
                (BOOLEAN-LISTP X_77)
                (BOOLEAN-LISTP X_76)
                (BOOLEAN-LISTP X_75)
                (BOOLEAN-LISTP X_74)
                (BOOLEAN-LISTP X_73)
                (BOOLEAN-LISTP X_72)
                (BOOLEAN-LISTP X_71)
                (BOOLEAN-LISTP X_70)
                (BOOLEAN-LISTP X_69)
                (BOOLEAN-LISTP X_68)
                (BOOLEAN-LISTP X_67)
                (BOOLEAN-LISTP X_66)
                (BOOLEAN-LISTP X_65)
                (BOOLEAN-LISTP X_64)
                (BOOLEAN-LISTP X_63)
                (BOOLEAN-LISTP X_62)
                (BOOLEAN-LISTP X_61)
                (BOOLEAN-LISTP X_60)
                (BOOLEAN-LISTP X_59)
                (BOOLEAN-LISTP X_58)
                (BOOLEAN-LISTP X_57)
                (BOOLEAN-LISTP X_56)
                (BOOLEAN-LISTP X_55)
                (BOOLEAN-LISTP X_54)
                (BOOLEAN-LISTP X_53)
                (BOOLEAN-LISTP X_52)
                (BOOLEAN-LISTP X_51)
                (BOOLEAN-LISTP X_50)
                (BOOLEAN-LISTP X_49)
                (BOOLEAN-LISTP X_48)
                (BOOLEAN-LISTP X_47)
                (BOOLEAN-LISTP X_46)
                (BOOLEAN-LISTP X_45)
                (BOOLEAN-LISTP X_44)
                (BOOLEAN-LISTP X_43)
                (BOOLEAN-LISTP X_42)
                (BOOLEAN-LISTP X_41)
                (BOOLEAN-LISTP X_40)
                (BOOLEAN-LISTP X_39)
                (BOOLEAN-LISTP X_38)
                (BOOLEAN-LISTP X_37)
                (BOOLEAN-LISTP X_36)
                (BOOLEAN-LISTP X_35)
                (BOOLEAN-LISTP X_34)
                (BOOLEAN-LISTP X_33)
                (BOOLEAN-LISTP X_32)
                (BOOLEAN-LISTP X_31)
                (BOOLEAN-LISTP X_30)
                (BOOLEAN-LISTP X_29)
                (BOOLEAN-LISTP X_28)
                (BOOLEAN-LISTP X_27)
                (BOOLEAN-LISTP X_26)
                (BOOLEAN-LISTP X_25)
                (BOOLEAN-LISTP X_24)
                (BOOLEAN-LISTP X_23)
                (BOOLEAN-LISTP X_22)
                (BOOLEAN-LISTP X_21)
                (BOOLEAN-LISTP X_20)
                (BOOLEAN-LISTP X_19)
                (BOOLEAN-LISTP X_18)
                (BOOLEAN-LISTP X_17)
                (BOOLEAN-LISTP X_16)
                (BOOLEAN-LISTP X_15)
                (BOOLEAN-LISTP X_14)
                (BOOLEAN-LISTP X_13)
                (BOOLEAN-LISTP X_12)
                (BOOLEAN-LISTP X_11)
                (BOOLEAN-LISTP X_10)
                (BOOLEAN-LISTP X_9)
                (BOOLEAN-LISTP X_8)
                (BOOLEAN-LISTP X_7)
                (BOOLEAN-LISTP X_6)
                (BOOLEAN-LISTP X_5)
                (BOOLEAN-LISTP X_4)
                (BOOLEAN-LISTP X_3)
                (BOOLEAN-LISTP X_2)
                (BOOLEAN-LISTP X_1)
                (BOOLEAN-LISTP X_0)
                (valid_digits 100 x))
             (valid_digits 100 (next_counter_state 100 x)))))
  :hints (("Goal" :bdd (:vars nil))))



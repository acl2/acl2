; JVM instructions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "floats")
(include-book "fields") ;for field-idp
(include-book "method-descriptors")

(local (in-theory (disable member-equal jvm::typep))) ;for speed

;; The name of a method is just a string
(defun method-namep (obj) (declare (xargs :guard t)) (stringp obj))

;; Disabled by default
;; Needed if we call string functions on method-names
(defthmd stringp-when-method-namep
  (implies (stringp name)
           (method-namep name)))

;takes the decimal number version of the opcode and gives back the symbolic name
;fixme could use an array for this, for speed.
;fixme generalize this to map from the number to the format of the opcode?
(defconst acl2::*opcode-to-name-table*
  '((0 . :nop)
    (1 . :aconst_null)
    (2 . :iconst_m1)
    (3 . :iconst_0)
    (4 . :iconst_1)
    (5 . :iconst_2)
    (6 . :iconst_3)
    (7 . :iconst_4)
    (8 . :iconst_5)
    (9 . :lconst_0)
    (10 . :lconst_1)
    (11 . :fconst_0)
    (12 . :fconst_1)
    (13 . :fconst_2)
    (14 . :dconst_0)
    (15 . :dconst_1)
    (16 . :bipush)
    (17 . :sipush)
    (18 . :ldc)
    (19 . :ldc_w)
    (20 . :ldc2_w)
    (21 . :iload)
    (22 . :lload)
    (23 . :fload)
    (24 . :dload)
    (25 . :aload)
    (26 . :iload_0)
    (27 . :iload_1)
    (28 . :iload_2)
    (29 . :iload_3)
    (30 . :lload_0)
    (31 . :lload_1)
    (32 . :lload_2)
    (33 . :lload_3)
    (34 . :fload_0)
    (35 . :fload_1)
    (36 . :fload_2)
    (37 . :fload_3)
    (38 . :dload_0)
    (39 . :dload_1)
    (40 . :dload_2)
    (41 . :dload_3)
    (42 . :aload_0)
    (43 . :aload_1)
    (44 . :aload_2)
    (45 . :aload_3)
    (46 . :iaload)
    (47 . :laload)
    (48 . :faload)
    (49 . :daload)
    (50 . :aaload)
    (51 . :baload)
    (52 . :caload)
    (53 . :saload)
    (54 . :istore)
    (55 . :lstore)
    (56 . :fstore)
    (57 . :dstore)
    (58 . :astore)
    (59 . :istore_0)
    (60 . :istore_1)
    (61 . :istore_2)
    (62 . :istore_3)
    (63 . :lstore_0)
    (64 . :lstore_1)
    (65 . :lstore_2)
    (66 . :lstore_3)
    (67 . :fstore_0)
    (68 . :fstore_1)
    (69 . :fstore_2)
    (70 . :fstore_3)
    (71 . :dstore_0)
    (72 . :dstore_1)
    (73 . :dstore_2)
    (74 . :dstore_3)
    (75 . :astore_0)
    (76 . :astore_1)
    (77 . :astore_2)
    (78 . :astore_3)
    (79 . :iastore)
    (80 . :lastore)
    (81 . :fastore)
    (82 . :dastore)
    (83 . :aastore)
    (84 . :bastore)
    (85 . :castore)
    (86 . :sastore)
    (87 . :pop)
    (88 . :pop2)
    (89 . :dup)
    (90 . :dup_x1)
    (91 . :dup_x2)
    (92 . :dup2)
    (93 . :dup2_x1)
    (94 . :dup2_x2)
    (95 . :swap)
    (96 . :iadd)
    (97 . :ladd)
    (98 . :fadd)
    (99 . :dadd)
    (100 . :isub)
    (101 . :lsub)
    (102 . :fsub)
    (103 . :dsub)
    (104 . :imul)
    (105 . :lmul)
    (106 . :fmul)
    (107 . :dmul)
    (108 . :idiv)
    (109 . :ldiv)
    (110 . :fdiv)
    (111 . :ddiv)
    (112 . :irem)
    (113 . :lrem)
    (114 . :frem)
    (115 . :drem)
    (116 . :ineg)
    (117 . :lneg)
    (118 . :fneg)
    (119 . :dneg)
    (120 . :ishl)
    (121 . :lshl)
    (122 . :ishr)
    (123 . :lshr)
    (124 . :iushr)
    (125 . :lushr)
    (126 . :iand)
    (127 . :land)
    (128 . :ior)
    (129 . :lor)
    (130 . :ixor)
    (131 . :lxor)
    (132 . :iinc)
    (133 . :i2l)
    (134 . :i2f)
    (135 . :i2d)
    (136 . :l2i)
    (137 . :l2f)
    (138 . :l2d)
    (139 . :f2i)
    (140 . :f2l)
    (141 . :f2d)
    (142 . :d2i)
    (143 . :d2l)
    (144 . :d2f)
    (145 . :i2b)
    (146 . :i2c)
    (147 . :i2s)
    (148 . :lcmp)
    (149 . :fcmpl)
    (150 . :fcmpg)
    (151 . :dcmpl)
    (152 . :dcmpg)
    (153 . :ifeq)
    (154 . :ifne)
    (155 . :iflt)
    (156 . :ifge)
    (157 . :ifgt)
    (158 . :ifle)
    (159 . :if_icmpeq)
    (160 . :if_icmpne)
    (161 . :if_icmplt)
    (162 . :if_icmpge)
    (163 . :if_icmpgt)
    (164 . :if_icmple)
    (165 . :if_acmpeq)
    (166 . :if_acmpne)
    (167 . :goto)
    (168 . :jsr)
    (169 . :ret)
    (170 . :tableswitch)
    (171 . :lookupswitch)
    (172 . :ireturn)
    (173 . :lreturn)
    (174 . :freturn)
    (175 . :dreturn)
    (176 . :areturn)
    (177 . :return)
    (178 . :getstatic)
    (179 . :putstatic)
    (180 . :getfield)
    (181 . :putfield)
    (182 . :invokevirtual)
    (183 . :invokespecial)
    (184 . :invokestatic)
    (185 . :invokeinterface)
    (186 . :invokedynamic)
    (187 . :new)
    (188 . :newarray)
    (189 . :anewarray)
    (190 . :arraylength)
    (191 . :athrow)
    (192 . :checkcast)
    (193 . :instanceof)
    (194 . :monitorenter)
    (195 . :monitorexit)
    (196 . :wide) ;special handling for this
    (197 . :multianewarray)
    (198 . :ifnull)
    (199 . :ifnonnull)
    (200 . :goto_w)
    (201 . :jsr_w)))

;todo package
(defconst acl2::*opcodes* (strip-cdrs acl2::*opcode-to-name-table*))

;fixme add into the below.  or deprecate?
(defun invokevirtual-instructionp (x)
  (declare (xargs :guard t))
  (and (consp x)
       (eq :invokevirtual (first x))
       (let ((args (acl2::fargs x)))
         (and (= 4 (len args))
              (reference-typep (first args))
              (method-namep (second args))
              (method-descriptorp (third args))
              (all-typep (fourth args))))))

;fixme guard should restrict this to an instruction
(defun instruction-args (x)
  (declare (xargs :guard (true-listp x)))
  (acl2::fargs x))

(defun inst-lengthp (len)
  (declare (xargs :guard t))
  (natp len))

(defund jvm-instructionp (inst)
  (declare (xargs :guard t))
  (and (consp inst)
       (member-eq (car inst) acl2::*opcodes*)
       (true-listp (cdr inst))))

(defthm jvm-instructionp-forward-to-consp
  (implies (jvm-instructionp inst)
           (consp inst))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable jvm-instructionp))))


;todo: invokedynamic
(defund len-of-invoke-instruction (opcode)
  (declare (xargs :guard t))
  (case opcode
        (:INVOKEVIRTUAL 3)
        (:INVOKESTATIC 3)
        (:INVOKESPECIAL 3)
        (:invokeinterface 5)
        (:ldc 2) ; LDC now counts as an invoke instruction because it can run a dummy method to build a class object
        (:ldc_w 3)
        (otherwise (prog2$ (er hard? 'len-of-invoke-instruction "Unknown invoke instruction: ~x0" opcode)
                           3 ;needed to show that the new frame is ok
                           ))))

(defthm len-of-invoke-instruction-constant-opener
  (implies (syntaxp (quotep opcode))
           (equal (len-of-invoke-instruction opcode)
                  (case opcode
                    (:INVOKEVIRTUAL 3)
                    (:INVOKESTATIC 3)
                    (:INVOKESPECIAL 3)
                    (:invokeinterface 5)
                    (:ldc 2) ; LDC now counts as an invoke instruction because it can run a dummy method to build a class object
                    (:ldc_w 3)
                    (otherwise (prog2$ (er hard? 'len-of-invoke-instruction "Unknown invoke instruction: ~x0" opcode)
                                       3 ;needed to show that the new frame is ok
                                       )))))
  :hints (("Goal" :in-theory (enable LEN-OF-INVOKE-INSTRUCTION))))

;These are the ops that have only one byte (the opcode itself) in the
;instruction stream.  The order here shouldn't matter (could sort by
;frequency).
(defconst *one-byte-ops*
  '(:NOP
    :ACONST_NULL
    :ICONST_M1
    :ICONST_0
    :ICONST_1
    :ICONST_2
    :ICONST_3
    :ICONST_4
    :ICONST_5
    :LCONST_0
    :LCONST_1
    :FCONST_0
    :FCONST_1
    :FCONST_2
    :DCONST_0
    :DCONST_1
    :ILOAD_0
    :ILOAD_1
    :ILOAD_2
    :ILOAD_3
    :LLOAD_0
    :LLOAD_1
    :LLOAD_2
    :LLOAD_3
    :FLOAD_0
    :FLOAD_1
    :FLOAD_2
    :FLOAD_3
    :DLOAD_0
    :DLOAD_1
    :DLOAD_2
    :DLOAD_3
    :ALOAD_0
    :ALOAD_1
    :ALOAD_2
    :ALOAD_3
    :ISTORE_0
    :ISTORE_1
    :ISTORE_2
    :ISTORE_3
    :LSTORE_0
    :LSTORE_1
    :LSTORE_2
    :LSTORE_3
    :FSTORE_0
    :FSTORE_1
    :FSTORE_2
    :FSTORE_3
    :DSTORE_0
    :DSTORE_1
    :DSTORE_2
    :DSTORE_3
    :ASTORE_0
    :ASTORE_1
    :ASTORE_2
    :ASTORE_3
    :POP
    :POP2
    :DUP
    :DUP_X1
    :DUP_X2
    :DUP2
    :DUP2_X1
    :DUP2_X2
    :SWAP
    :IADD
    :LADD
    :FADD
    :DADD
    :ISUB
    :LSUB
    :FSUB
    :DSUB
    :IMUL
    :LMUL
    :FMUL
    :DMUL
    :IDIV
    :LDIV
    :FDIV
    :DDIV
    :IREM
    :LREM
    :FREM
    :DREM
    :INEG
    :LNEG
    :FNEG
    :DNEG
    :ISHL
    :LSHL
    :ISHR
    :LSHR
    :IUSHR
    :LUSHR
    :IAND
    :LAND
    :IOR
    :LOR
    :IXOR
    :LXOR
    :I2L
    :I2F
    :I2D
    :L2I
    :L2F
    :L2D
    :F2I
    :F2L
    :F2D
    :D2I
    :D2L
    :D2F
    :I2B
    :I2C
    :I2S
    :LCMP
    :FCMPL
    :FCMPG
    :DCMPL
    :DCMPG
    :IRETURN
    :LRETURN
    :FRETURN
    :DRETURN
    :ARETURN
    :RETURN
    :ARRAYLENGTH
    :ATHROW
    :MONITORENTER
    :MONITOREXIT
    :IALOAD
    :LALOAD
    :FALOAD
    :DALOAD
    :AALOAD
    :BALOAD
    :CALOAD
    :SALOAD
    :IASTORE
    :LASTORE
    :FASTORE
    :DASTORE
    :AASTORE
    :BASTORE
    :CASTORE
    :SASTORE))


;; Recognize a program counter.
(defund pcp (val)
  (declare (xargs :guard t))
  (natp val))

;; Recognize a list of program counters.
(defund acl2::all-pcp (pcs)
  (declare (xargs :guard t))
  (if (atom pcs)
      t
    (and (jvm::pcp (first pcs))
         (acl2::all-pcp (rest pcs)))))

(defthm pcp-of-car
  (implies (acl2::all-pcp pcs)
           (equal (pcp (car pcs))
                  (consp pcs)))
  :hints (("Goal" :in-theory (enable acl2::all-pcp))))

(defthm all-pcp-of-cdr
  (implies (acl2::all-pcp pcs)
           (acl2::all-pcp (cdr pcs)))
  :hints (("Goal" :in-theory (enable acl2::all-pcp))))

(defund valid-pcp (pc valid-pcs)
  (declare (xargs :guard (and; (pcp pc)
                              (true-listp valid-pcs)
                              (acl2::all-pcp valid-pcs))
                 :guard-hints (("Goal" :in-theory (enable pcp)))))
  (and (pcp pc) ;drop?
       (member pc valid-pcs)))

;recognize an offset to a program counter
(defund pc-offsetp (val)
  (declare (xargs :guard t))
  (integerp val)) ;fixme constrain to not make the whole pc negative...

(defthm pcp-of-len-of-invoke-instruction
  (pcp (len-of-invoke-instruction opcode))
  :hints (("Goal" :in-theory (enable len-of-invoke-instruction))))

;fixme move or copy some of these checks (the ones not involving PC) into jvm-instructionp
;fixme improve to check the args of the instructions (e.g., that the inst-len stored is an integer for those instructions that can be preceded by WIDE)
;we need the pc here to make sure that relative jumps are okay
(defund jvm-instruction-okayp (inst pc valid-pcs)
  (declare (xargs :guard (and (pcp pc)
                              (true-listp valid-pcs)
                              (acl2::all-pcp valid-pcs))
                  :guard-hints (("Goal" :in-theory (e/d (jvm-instructionp len-of-invoke-instruction)
                                                        ( ;memberp-of-cons
                                                         ))))))
  (and (jvm-instructionp inst) ;fixme eventually drop this (or at least the member-eq)
       ;; (not (cw "Checking ~x0~%" inst))
       (or (member-eq (car inst) *one-byte-ops*)
           (case (car inst)
             ;;fixme add the rest of the cases!
             (:new (and (= 1 (len (instruction-args inst)))
                        (class-namep (farg1 inst))
                        (valid-pcp (+ 3 pc) valid-pcs)))
             (:putfield (and (= 3 (len (instruction-args inst)))
                             (class-namep (farg1 inst))
                             (field-idp (farg2 inst))
                             (valid-pcp (+ 3 pc) valid-pcs)))
             ((:invokevirtual :invokeinterface)
              (and (= 4 (len (instruction-args inst)))
                   (reference-typep (farg1 inst)) ;todo: think about array types
                   (method-namep (farg2 inst))
                   (method-descriptorp (farg3 inst))
                   (true-listp (farg4 inst))
                   (all-typep (farg4 inst))
                   (valid-pcp (+ (len-of-invoke-instruction (car inst)) pc) valid-pcs)))
             ((:invokestatic :invokespecial)
              (and (= 5 (len (instruction-args inst)))
                   (reference-typep (farg1 inst)) ;todo: think about array types
                   (method-namep (farg2 inst))
                   (method-descriptorp (farg3 inst))
                   (true-listp (farg4 inst))
                   (all-typep (farg4 inst))
                   (booleanp (farg5 inst))
                   (valid-pcp (+ (len-of-invoke-instruction (car inst)) pc) valid-pcs)))
             ((:if_acmpeq :if_acmpne :if_icmpeq :if_icmpne
                          :if_icmplt :if_icmpge :if_icmpgt :if_icmple
                          :ifeq :ifne :iflt :ifge :ifgt :ifle
                          :ifnull :ifnonnull)
              (and (= 1 (len (instruction-args inst)))
                   (pc-offsetp (farg1 inst))
                   (valid-pcp (+ 3 pc) valid-pcs)
                   (valid-pcp (+ (farg1 inst) pc) valid-pcs)))
             ((:goto :jsr)
              (and (= 1 (len (instruction-args inst)))
                   (pc-offsetp (farg1 inst))
                   (valid-pcp (+ (farg1 inst) pc) valid-pcs) ;no need to check the instr following this unconditional jump
                   ))
             ((:getfield :putfield :getstatic :putstatic)
              (and (= 3 (len (instruction-args inst)))
                   (class-namep (farg1 inst))
                   (field-idp (farg2 inst))
                   (booleanp (farg3 inst))))
             ((:iload :lload :fload
                      :dload :aload :istore
                      :lstore
                      :fstore :dstore
                      :astore :ret)
              (and (= 2 (len (instruction-args inst)))
                   (unsigned-byte-p 16 (farg2 inst))
                   (inst-lengthp (farg2 inst)) ;total length of the instruction (stored because of wide)
                   ))
             (:iinc (and (= 3 (len (instruction-args inst)))
                         (unsigned-byte-p 16 (farg1 inst))
                         (signed-byte-p 16 (farg2 inst))
                         (or (eql 3 (farg3 inst))
                             (eql 6 (farg3 inst)))))
             ((:checkcast :anewarray :instanceof)
              (and (= 1 (len (instruction-args inst)))
                   (typep (farg1 inst))))
             (:newarray (and (= 1 (len (instruction-args inst)))
                             (member-eq (farg1 inst) *primitive-types*)))
             (:bipush (and (= 1 (len (instruction-args inst)))
                           (signed-byte-p 8 (farg1 inst))))
             (:sipush (and (= 1 (len (instruction-args inst)))
                           (signed-byte-p 16 (farg1 inst))))
             ((:ldc :ldc_w)
              (and (= 1 (len (instruction-args inst)))
                   (or (unsigned-byte-p 32 (farg1 inst))
                       (java-floatp (farg1 inst))
                       (stringp (farg1 inst))
                       (and (true-listp (farg1 inst))
                            (= 2 (len (farg1 inst)))
                            (eq :class (first (farg1 inst)))
                            (class-namep (second (farg1 inst)))))))
             (:ldc2_w
              (and (= 1 (len (instruction-args inst)))
                   (or (unsigned-byte-p 64 (farg1 inst))
                       (java-doublep (farg1 inst)))))
             ((:goto_w :jsr_w)
              (and (= 1 (len (instruction-args inst)))
                   (signed-byte-p 32 (farg1 inst))))
             (:invokedynamic ;may change
              (and (= 1 (len (instruction-args inst)))
                   (unsigned-byte-p 16 (farg1 inst))))
             (:multianewarray
              (and (= 2 (len (instruction-args inst)))
                   (typep (farg1 inst))
                   (unsigned-byte-p 8 (farg2 inst))))
             (:tableswitch
              (and (= 4 (len (instruction-args inst)))
                   (signed-byte-p 32 (farg1 inst))
                   (signed-byte-p 32 (farg2 inst))
                   (signed-byte-p 32 (farg3 inst))
                   (and (true-listp (farg4 inst))
                        ;(all-signed-byte-p 32 (farg4 inst))
                        )))
             (:lookupswitch
              (and (= 2 (len (instruction-args inst)))
                   (and (alistp (farg1 inst))
                        ;(all-signed-byte-p 32 (strip-cars (farg1 inst)))
                        ;(all-signed-byte-p 32 (strip-cdrs (farg1 inst)))
                        )
                   (signed-byte-p 32 (farg2 inst))))
             ;; :wide is handled specially
             (otherwise (er hard? 'jvm-instruction-okayp "Unknown opcode: ~x0" (car inst)))))))

(defthm jvm-instructionp-when-jvm-instruction-okayp
  (implies (jvm-instruction-okayp inst pc valid-pcs)
           (jvm-instructionp inst))
  :hints (("Goal" :in-theory (enable jvm-instruction-okayp))))

;extract the op-code from an instruction
;make a macro? (why?)
(defund op-code (inst)
  (declare (xargs :guard (jvm-instructionp inst)
                  :guard-hints (("Goal" :in-theory (enable jvm-instructionp)))))
  (car inst))

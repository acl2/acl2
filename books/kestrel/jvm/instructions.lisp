; JVM instructions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "floats") ; for java-floatp
(include-book "fields") ;for field-idp
(include-book "method-descriptors")
(include-book "method-names")
(include-book "kestrel/bv-lists/signed-byte-listp-def" :dir :system)
(include-book "kestrel/utilities/def-constant-opener" :dir :system)

(local (in-theory (disable member-equal jvm::typep))) ;for speed

;takes the decimal number version of the opcode and gives back the symbolic name
;fixme could use an array for this, for speed.
;fixme generalize this to map from the number to the format of the opcode?
(defconst *opcode-to-name-table*
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

;These are the ops that have only one byte (the opcode itself) in the
;instruction stream.  The order here shouldn't matter (could sort by
;frequency).
(defconst *one-byte-ops*
  '(:AALOAD
    :AASTORE
    :ACONST_NULL
    :ALOAD_0
    :ALOAD_1
    :ALOAD_2
    :ALOAD_3
    :ARETURN
    :ARRAYLENGTH
    :ASTORE_0
    :ASTORE_1
    :ASTORE_2
    :ASTORE_3
    :ATHROW
    :BALOAD
    :BASTORE
    :CALOAD
    :CASTORE
    :D2F
    :D2I
    :D2L
    :DADD
    :DALOAD
    :DASTORE
    :DCMPG
    :DCMPL
    :DCONST_0
    :DCONST_1
    :DDIV
    :DLOAD_0
    :DLOAD_1
    :DLOAD_2
    :DLOAD_3
    :DMUL
    :DNEG
    :DREM
    :DRETURN
    :DSTORE_0
    :DSTORE_1
    :DSTORE_2
    :DSTORE_3
    :DSUB
    :DUP
    :DUP_X1
    :DUP_X2
    :DUP2
    :DUP2_X1
    :DUP2_X2
    :F2D
    :F2I
    :F2L
    :FADD
    :FALOAD
    :FASTORE
    :FCMPG
    :FCMPL
    :FCONST_0
    :FCONST_1
    :FCONST_2
    :FDIV
    :FLOAD_0
    :FLOAD_1
    :FLOAD_2
    :FLOAD_3
    :FMUL
    :FNEG
    :FREM
    :FRETURN
    :FSTORE_0
    :FSTORE_1
    :FSTORE_2
    :FSTORE_3
    :FSUB
    :I2B
    :I2C
    :I2D
    :I2F
    :I2L
    :I2S
    :IADD
    :IALOAD
    :IAND
    :IASTORE
    :ICONST_M1
    :ICONST_0
    :ICONST_1
    :ICONST_2
    :ICONST_3
    :ICONST_4
    :ICONST_5
    :IDIV
    :ILOAD_0
    :ILOAD_1
    :ILOAD_2
    :ILOAD_3
    :IMUL
    :INEG
    :IOR
    :IREM
    :IRETURN
    :ISHL
    :ISHR
    :ISTORE_0
    :ISTORE_1
    :ISTORE_2
    :ISTORE_3
    :ISUB
    :IUSHR
    :IXOR
    :L2D
    :L2F
    :L2I
    :LADD
    :LALOAD
    :LAND
    :LASTORE
    :LCMP
    :LCONST_0
    :LCONST_1
    :LDIV
    :LLOAD_0
    :LLOAD_1
    :LLOAD_2
    :LLOAD_3
    :LMUL
    :LNEG
    :LOR
    :LREM
    :LRETURN
    :LSHL
    :LSHR
    :LSTORE_0
    :LSTORE_1
    :LSTORE_2
    :LSTORE_3
    :LSUB
    :LUSHR
    :LXOR
    :MONITORENTER
    :MONITOREXIT
    :NOP
    :POP
    :POP2
    :RETURN
    :SALOAD
    :SASTORE
    :SWAP))

(defconst *opcodes* (remove-eq :wide (strip-cdrs *opcode-to-name-table*)))

(defun opcodep (opcode)
  (declare (xargs :guard t))
  (if (member-eq opcode *opcodes*) t nil))

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

(defun inst-lengthp (len)
  (declare (xargs :guard t))
  (posp len))

;; Recognizes a list of well-formed arguments for the given OPCODE.
;; This does not check jump targets, as that requires knowing the set of valid PCs, but see jvm-instruction-okayp.
(defund instruction-argsp (opcode args)
  (declare (xargs :guard (and (opcodep opcode)
                              (true-listp args))))
  (if (member-eq opcode *one-byte-ops*)
      (null args)
    (case opcode
      ((:aload :astore :dload :dstore :fload :fstore :iload :istore :lload :lstore :ret)
       (and (= 2 (len args))
            (unsigned-byte-p 16 (first args)) ; 1 or 2 bytes depending on :wide
            (inst-lengthp (second args)) ;total length of the instruction (stored because of :wide)
            (or (= 2 (second args))      ; depending on :wide
                (= 4 (second args)))))
      ((:anewarray :checkcast :instanceof)
       (and (= 1 (len args))
            (typep (first args))))
      (:bipush
       (and (= 1 (len args))
            (signed-byte-p 8 (first args))))
      ((:getfield :getstatic :putfield :putstatic)
       (and (= 3 (len args))
            (class-namep (first args))
            (field-idp (second args))
            (booleanp (third args))))
      ((:goto :jsr) ; combine with a case below?
       (and (= 1 (len args))
            (signed-byte-p 16 (first args))))
      ((:goto_w :jsr_w)
       (and (= 1 (len args))
            (signed-byte-p 32 (first args))))
      ((:if_acmpeq :if_acmpne
                   :if_icmpeq :if_icmpne :if_icmplt :if_icmpge :if_icmpgt :if_icmple
                   :ifeq :ifne :iflt :ifge :ifgt :ifle
                   :ifnull :ifnonnull)
       (and (= 1 (len args))
            (signed-byte-p 16 (first args))))
      (:iinc
       (and (= 3 (len args))
            (unsigned-byte-p 16 (first args)) ; 1 or 2 bytes depending on :wide
            (signed-byte-p 16 (second args))  ; 1 or 2 bytes depending on :wide
            (inst-lengthp (third args))
            (or (eql 3 (third args))
                (eql 6 (third args)))))
      (:invokedynamic ; todo: check once implemented
       (and (= 1 (len args))
            (unsigned-byte-p 16 (first args))))
      ((:invokeinterface :invokevirtual)
       (and (= 4 (len args))
            (reference-typep (first args)) ;todo: think about array types
            (method-namep (second args))
            (method-descriptorp (third args))
            (true-listp (fourth args))
            (all-typep (fourth args))))
      ((:invokespecial :invokestatic)
       (and (= 5 (len args))
            (reference-typep (first args)) ;todo: think about array types
            (method-namep (second args))
            (method-descriptorp (third args))
            (true-listp (fourth args))
            (all-typep (fourth args))
            (booleanp (fifth args))))
      ((:ldc :ldc_w)
       (and (= 1 (len args))
            (let ((tagged-value (first args)))
              (and (consp tagged-value)
                   (let* ((tag (car tagged-value))
                          (value (cdr tagged-value)))
                     (or (and (eq :int tag)
                              (unsigned-byte-p 32 value))
                         (and (eq :float tag)
                              (java-floatp value))
                         (and (eq :string tag)
                              (stringp value))
                         (and (eq :class tag)
                              (class-namep value))))))))
      (:ldc2_w
       (and (= 1 (len args))
            (let ((tagged-value (first args)))
              (and (consp tagged-value)
                   (let* ((tag (car tagged-value))
                          (value (cdr tagged-value)))
                     (or (and (eq :long tag)
                              (unsigned-byte-p 64 value))
                         (and (eq :double tag)
                              (java-doublep value))))))))
      (:lookupswitch
       (and (= 3 (len args))
            (signed-byte-p 32 (first args)) ; default
            (and (alistp (second args))     ; match-offset pairs
                 ;; todo: avoid consing here (also avoid walking down the alist twice):
                 (acl2::signed-byte-listp 32 (strip-cars (second args)))
                 (acl2::signed-byte-listp 32 (strip-cdrs (second args))))
            (inst-lengthp (third args)) ; inst-len ; todo: add lower bound
            ))
      (:multianewarray
       (and (= 2 (len args))
            (typep (first args))
            (unsigned-byte-p 8 (second args))))
      (:new
       (and (= 1 (len args))
            (class-namep (first args))))
      (:newarray
       (and (= 1 (len args))
            (member-eq (first args) *primitive-types*)))
      (:sipush (and (= 1 (len args))
                    (signed-byte-p 16 (first args)) ; todo: check this
                    ))
      (:tableswitch
       (and (= 5 (len args))
            (signed-byte-p 32 (first args))
            (signed-byte-p 32 (second args))
            (signed-byte-p 32 (third args))
            (and (true-listp (fourth args))
                 (acl2::signed-byte-listp 32 (fourth args))
                 )
            (inst-lengthp (fifth args)) ; inst-len ; todo: add lower bound
            ))
      ;; :wide is handled specially (not a valid instruction)
      (otherwise (er hard? 'instruction-argsp "Unknown opcode: ~x0" opcode)))))

(defund instructionp (inst)
  (declare (xargs :guard t))
  (and (consp inst)
       (let ((opcode (car inst))
             (args (cdr inst)))
         (and (member-eq opcode *opcodes*)
              ;; (not (eq (car inst) :wide)) ; gets handled in the parser
              (true-listp args)
              (instruction-argsp opcode args)))))

(defthm instructionp-forward-to-consp
  (implies (instructionp inst)
           (consp inst))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable instructionp))))

;;extracts the op-code from an instruction
(defund instruction-opcode (inst)
  (declare (xargs :guard (instructionp inst)))
  (car inst))

;;extracts the arguments from an instruction
(defund instruction-args (inst)
  (declare (xargs :guard (instructionp inst)))
  (cdr inst))

(defthmd instructionp-redef
  (equal (instructionp inst)
         (and (consp inst)
              (let ((opcode (instruction-opcode inst))
                    (args (instruction-args inst)))
                (and (member-eq opcode *opcodes*)
                     (true-listp args)
                     (instruction-argsp opcode args)))))
  :hints (("Goal" :in-theory (enable instructionp
                                     instruction-args
                                     instruction-opcode))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;todo: invokedynamic
;todo: what about NEW and other things that can invoke a staticinitializer?
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

(acl2::def-constant-opener len-of-invoke-instruction)

;; Returns the length of the instruction INST.  Instructions that can be
;; preceded by :wide have their lengths stored in the instruction, as do
;; :lookupswitch and :tableswitch.
(defund inst-len (inst)
  (declare (xargs :guard (instructionp inst)
                  :guard-hints (("Goal" :in-theory (enable instructionp member-equal instruction-opcode)))))
  (let ((opcode (instruction-opcode inst)))
    (if (member-eq opcode *one-byte-ops*)
        1
      (case opcode
        ;; Two-byte opcodes:
        ((:bipush :ldc :newarray) 2)
        ;; Three-byte opcodes:
        ((:anewarray
          :checkcast
          :getfield :getstatic
          :goto
          :if_acmpeq :if_acmpne
          :if_icmpeq :if_icmpne :if_icmplt :if_icmpge :if_icmpgt :if_icmple
          :ifeq :ifne :iflt :ifge :ifgt :ifle
          :ifnonnull :ifnull
          :instanceof
          :invokespecial
          :invokestatic
          :invokevirtual
          :jsr
          :ldc_w
          :ldc2_w
          :new
          :putfield :putstatic
          :sipush)
         3)
        ;; Four-byte opcodes:
        (:multianewarray 4)
        ;; Five-byte opcodes:
        ((:goto_w :invokedynamic :invokeinterface :jsr_w) 5)
        ;; These can be preceded by :wide, so they store the length in arg2:
        ((:aload :astore
          :dload :dstore
          :fload :fstore
          :iload :istore
          :lload :lstore
          :ret)
         (nfix (farg2 inst))  ; todo: remove the nfix
         )
        ;; This can be preceded by :wide, so it stores the length in arg3:
        (:iinc (nfix (farg3 inst))) ; todo: drop the nfix
        ;; These have variable lengths, so they store the length as the last arg:
        (:lookupswitch (nfix (farg3 inst)))    ; todo: drop the nfix
        (:tableswitch (nfix (farg5 inst)))    ; todo: drop the nfix
        ;; No case for :wide here because that gets handled when we parse the
        ;; class file, depending on the next opcode.
        (otherwise (er hard 'inst-len "Unhandled opcode."))))))

(defthm natp-of-inst-len
  (implies (instructionp inst)
           (natp (inst-len inst)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable inst-len instructionp member-equal instruction-opcode))))

(defthm posp-of-inst-len
  (implies (instructionp inst)
           (posp (inst-len inst)))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :in-theory (enable inst-len instructionp member-equal instruction-opcode instruction-argsp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recognize a program counter.
(defund pcp (val)
  (declare (xargs :guard t))
  (natp val))

;; Recognize a list of program counters.
(defund all-pcp (pcs)
  (declare (xargs :guard t))
  (if (atom pcs)
      t
    (and (jvm::pcp (first pcs))
         (all-pcp (rest pcs)))))

(defthm all-pcp-of-revappend
  (implies (and (all-pcp x)
                (all-pcp y))
           (all-pcp (revappend x y)))
  :hints (("Goal" :induct t
           :in-theory (enable all-pcp revappend))))

(defthm all-pcp-of-reverse
  (implies (and (all-pcp x)
                (true-listp x))
           (all-pcp (acl2::reverse x)))
  :hints (("Goal" ; :induct t
           :in-theory (enable acl2::reverse))))

(defthm pcp-of-car
  (implies (all-pcp pcs)
           (equal (pcp (car pcs))
                  (consp pcs)))
  :hints (("Goal" :in-theory (enable all-pcp))))

(defthm all-pcp-of-cdr
  (implies (all-pcp pcs)
           (all-pcp (cdr pcs)))
  :hints (("Goal" :in-theory (enable all-pcp))))

(defund valid-pcp (pc valid-pcs)
  (declare (xargs :guard (and; (pcp pc)
                              (true-listp valid-pcs)
                              (all-pcp valid-pcs))
                 :guard-hints (("Goal" :in-theory (enable pcp)))))
  (and (pcp pc) ;drop?
       (member pc valid-pcs)))

(defthm valid-pcp-forward-to-pcp
  (implies (valid-pcp pc valid-pcs)
           (pcp pc))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable valid-pcp))))

;recognize an offset to a program counter
(defund pc-offsetp (val)
  (declare (xargs :guard t))
  (integerp val)) ;fixme constrain to not make the whole pc negative...

(defthm pcp-of-len-of-invoke-instruction
  (pcp (len-of-invoke-instruction opcode))
  :hints (("Goal" :in-theory (enable len-of-invoke-instruction))))

;we need the pc here to make sure that relative jumps are okay
(defund jvm-instruction-okayp (inst pc valid-pcs)
  (declare (xargs :guard (and (instructionp inst) ; includes basic checks on args
                              (pcp pc)
                              (true-listp valid-pcs)
                              (all-pcp valid-pcs))
                  :guard-hints (("Goal" :in-theory (e/d (instructionp
                                                         len-of-invoke-instruction
                                                         instruction-argsp
                                                         instruction-opcode
                                                         member-equal)
                                                        (;memberp-of-cons
                                                         ))))))
  (case (instruction-opcode inst)
    ((:aload :astore :dload :dstore :fload :fstore :iload :istore :lload :lstore :ret)
     (valid-pcp (+ (farg2 inst) pc) valid-pcs))
    (:iinc
     (valid-pcp (+ (farg3 inst) pc) valid-pcs))
    ((:goto :jsr)
     (valid-pcp (+ (farg1 inst) pc) valid-pcs))
    ((:goto_w :jsr_w) ; combine with the above?
     (valid-pcp (+ (farg1 inst) pc) valid-pcs))
    ((:if_acmpeq :if_acmpne
                 :if_icmpeq :if_icmpne :if_icmplt :if_icmpge :if_icmpgt :if_icmple
                 :ifeq :ifne :iflt :ifge :ifgt :ifle
                 :ifnull :ifnonnull)
     (valid-pcp (+ (farg1 inst) pc) valid-pcs))
    ;; todo: add checks for these instructions?:
    ;; (:tableswitch
    ;;  (and (= 5 (len (instruction-args inst)))
    ;;       (signed-byte-p 32 (farg1 inst))
    ;;       (signed-byte-p 32 (farg2 inst))
    ;;       (signed-byte-p 32 (farg3 inst))
    ;;       (and (true-listp (farg4 inst))
    ;;            (acl2::signed-byte-listp 32 (farg4 inst))
    ;;            )
    ;;       (inst-lengthp (farg5 inst)) ; inst-len ; todo: add lower bound
    ;;       ))
    ;;     (:lookupswitch
    ;;  (and (= 3 (len (instruction-args inst)))
    ;;       (signed-byte-p 32 (farg1 inst)) ; default
    ;;       (and (alistp (farg2 inst))      ; match-offset pairs
    ;;            ;; todo: avoid consing here (also avoid walking down the alist twice):
    ;;            (acl2::signed-byte-listp 32 (strip-cars (farg2 inst)))
    ;;            (acl2::signed-byte-listp 32 (strip-cdrs (farg2 inst))))
    ;;       (inst-lengthp (farg3 inst)) ; inst-len ; todo: add lower bound
    ;;       ))
    ;; :wide is handled specially (not a valid instruction)
    (otherwise t)))

;; (defthm instructionp-when-jvm-instruction-okayp
;;   (implies (jvm-instruction-okayp inst pc valid-pcs)
;;            (instructionp inst))
;;   :hints (("Goal" :in-theory (enable jvm-instruction-okayp))))

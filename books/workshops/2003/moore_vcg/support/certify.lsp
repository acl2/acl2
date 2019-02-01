;(certify-book "defpun")
;(u)

; The following comment line tells the build system that if *acl2-exports*
; changes, then every book that uses this file should be recertified:
; (depends-on "build/acl2-exports.certdep" :dir :system)

(defpkg "LABEL" '(nil t))
(defpkg "JVM" '(nil t))
(defpkg "M5"
  (set-difference-equal
   (union-eq
    '(JVM::SCHEDULED
      JVM::UNSCHEDULED
      JVM::REF
      JVM::LOCKED
      JVM::S_LOCKED
      JVM::UNLOCKED
      JVM::AALOAD
      JVM::AASTORE
      JVM::ACONST_NULL
      JVM::ALOAD
      JVM::ALOAD_0
      JVM::ALOAD_1
      JVM::ALOAD_2
      JVM::ALOAD_3
      JVM::ANEWARRAY
      JVM::ARETURN
      JVM::ARRAYLENGTH
      JVM::ASTORE
      JVM::ASTORE_0
      JVM::ASTORE_1
      JVM::ASTORE_2
      JVM::ASTORE_3
      JVM::BALOAD
      JVM::BASTORE
      JVM::BIPUSH
      JVM::CALOAD
      JVM::CASTORE
      JVM::DUP
      JVM::DUP_X1
      JVM::DUP_X2
      JVM::DUP2
      JVM::DUP2_X1
      JVM::DUP2_X2
      JVM::GETFIELD
      JVM::GETSTATIC
      JVM::GOTO
      JVM::GOTO_W
      JVM::I2B
      JVM::I2C
      JVM::I2L
      JVM::I2S
      JVM::IADD
      JVM::IALOAD
      JVM::IAND
      JVM::IASTORE
      JVM::ICONST_M1
      JVM::ICONST_0
      JVM::ICONST_1
      JVM::ICONST_2
      JVM::ICONST_3
      JVM::ICONST_4
      JVM::ICONST_5
      JVM::IDIV
      JVM::IF_ACMPEQ
      JVM::IF_ACMPNE
      JVM::IF_ICMPEQ
      JVM::IF_ICMPGE
      JVM::IF_ICMPGT
      JVM::IF_ICMPLE
      JVM::IF_ICMPLT
      JVM::IF_ICMPNE
      JVM::IFEQ
      JVM::IFGE
      JVM::IFGT
      JVM::IFLE
      JVM::IFLT
      JVM::IFNE
      JVM::IFNONNULL
      JVM::IFNULL
      JVM::IINC
      JVM::ILOAD
      JVM::ILOAD_0
      JVM::ILOAD_1
      JVM::ILOAD_2
      JVM::ILOAD_3
      JVM::IMUL
      JVM::INEG
      JVM::INSTANCEOF
      JVM::INVOKESPECIAL
      JVM::INVOKESTATIC
      JVM::INVOKEVIRTUAL
      JVM::IOR
      JVM::IREM
      JVM::IRETURN
      JVM::ISHL
      JVM::ISHR
      JVM::ISTORE
      JVM::ISTORE_0
      JVM::ISTORE_1
      JVM::ISTORE_2
      JVM::ISTORE_3
      JVM::ISUB
      JVM::IUSHR
      JVM::IXOR
      JVM::JSR
      JVM::JSR_W
      JVM::L2I
      JVM::LADD
      JVM::LALOAD
      JVM::LAND
      JVM::LASTORE
      JVM::LCMP
      JVM::LCONST_0
      JVM::LCONST_1
      JVM::LDC
      JVM::LDC_W
      JVM::LDC2_W
      JVM::LDIV
      JVM::LLOAD
      JVM::LLOAD_0
      JVM::LLOAD_1
      JVM::LLOAD_2
      JVM::LLOAD_3
      JVM::LMUL
      JVM::LNEG
      JVM::LOR
      JVM::LREM
      JVM::LRETURN
      JVM::LSHL
      JVM::LSHR
      JVM::LSTORE
      JVM::LSTORE_0
      JVM::LSTORE_1
      JVM::LSTORE_2
      JVM::LSTORE_3
      JVM::LSUB
      JVM::LUSHR
      JVM::LXOR
      JVM::MONITORENTER
      JVM::MONITOREXIT
      JVM::MULTIANEWARRAY
      JVM::NEW
      JVM::NEWARRAY
      JVM::NOP
      JVM::POP
      JVM::POP2
      JVM::PUTFIELD
      JVM::PUTSTATIC
      JVM::RET
      JVM::RETURN
      JVM::SALOAD
      JVM::SASTORE
      JVM::SIPUSH
      JVM::SWAP
      ASSOC-EQUAL LEN NTH ZP SYNTAXP
      QUOTEP FIX NFIX E0-ORDINALP E0-ORD-<)
    (union-eq *acl2-exports*
              *common-lisp-symbols-from-main-lisp-package*))
   '(PC PROGRAM PUSH POP RETURN REVERSE STEP ++)))
(certify-book "m5" 3)
(u) (u) (u) (u)

(include-book "m5")
(certify-book "utilities" 1)
(u) (u)

(include-book "utilities")
(certify-book "demo" 1)
(u) (u)

(include-book "utilities")
(certify-book "vcg-examples" 1)
(u) (u)

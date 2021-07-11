; Rules about instructions
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2021 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "JVM")

(include-book "jvm")

;; TODO: How does using rules to open DO-INST compare to allowing it to open
;; (perhaps only when the INST is a constant, to avoid huge case splits)?

;; TODO: Consider ordering these to put the most common instructions last (so
;; they'll be tried first by ACL2).

;; This variant passes inst to the execute- function
(defmacro def-do-inst-theorem-with-inst (opcode)
  `(defthm ,(acl2::pack-in-package-of-symbol 'do-inst 'do-inst-of- opcode)
     (equal (do-inst ',(intern (string-upcase (symbol-name opcode)) "KEYWORD") inst th s)
            (,(intern-in-package-of-symbol (symbol-name (acl2::pack-in-package-of-symbol 'do-inst 'execute- opcode)) 'do-inst) inst th s))
     :hints (("Goal" :in-theory (enable do-inst)))))

;TODO: Use this more
;; This is for the simple case where only TH, and S (not INST) are passed to the execute- function.
(defmacro def-do-inst-theorem (opcode)
  `(defthm ,(acl2::pack-in-package-of-symbol 'do-inst 'do-inst-of- opcode)
     (equal (do-inst ',(intern (string-upcase (symbol-name opcode)) "KEYWORD") inst th s)
            (,(intern-in-package-of-symbol (symbol-name (acl2::pack-in-package-of-symbol 'do-inst 'execute- opcode)) 'do-inst) th s))
     :hints (("Goal" :in-theory (enable do-inst)))))

(def-do-inst-theorem aaload)
(def-do-inst-theorem aastore)

(def-do-inst-theorem aconst_null)

(def-do-inst-theorem-with-inst aload)

(defthm do-inst-of-aload_0
  (equal (do-inst ':aload_0 inst th s)
         (execute-aload_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-aload_1
  (equal (do-inst ':aload_1 inst th s)
         (execute-aload_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-aload_2
  (equal (do-inst ':aload_2 inst th s)
         (execute-aload_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-aload_3
  (equal (do-inst ':aload_3 inst th s)
         (execute-aload_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem-with-inst anewarray)

(def-do-inst-theorem areturn)

(def-do-inst-theorem arraylength)

(def-do-inst-theorem-with-inst astore)

(defthm do-inst-of-astore_0
  (equal (do-inst ':astore_0 inst th s)
         (execute-astore_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-astore_1
  (equal (do-inst ':astore_1 inst th s)
         (execute-astore_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-astore_2
  (equal (do-inst ':astore_2 inst th s)
         (execute-astore_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-astore_3
  (equal (do-inst ':astore_3 inst th s)
         (execute-astore_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem baload)
(def-do-inst-theorem bastore)

(def-do-inst-theorem-with-inst bipush)

(def-do-inst-theorem caload)
(def-do-inst-theorem castore)

(defthm do-inst-of-dconst_0
  (equal (do-inst ':dconst_0 inst th s)
         (execute-dconst_x 0 th s))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-dconst_1
  (equal (do-inst ':dconst_1 inst th s)
         (execute-dconst_x 1 th s))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem dup)
(def-do-inst-theorem dup_x1)
(def-do-inst-theorem dup_x2)
(def-do-inst-theorem dup2)
(def-do-inst-theorem dup2_x1)
(def-do-inst-theorem dup2_x2)

(defthm do-inst-of-fconst_0
  (equal (do-inst ':fconst_0 inst th s)
         (execute-fconst_x 0 th s))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-fconst_1
  (equal (do-inst ':fconst_1 inst th s)
         (execute-fconst_x 1 th s))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-fconst_2
  (equal (do-inst ':fconst_2 inst th s)
         (execute-fconst_x 2 th s))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem-with-inst getfield)
(def-do-inst-theorem-with-inst getstatic)

(def-do-inst-theorem-with-inst goto)
(def-do-inst-theorem-with-inst goto_w)

(def-do-inst-theorem i2b)
(def-do-inst-theorem i2c)
(def-do-inst-theorem i2l)
(def-do-inst-theorem i2s)

(def-do-inst-theorem iadd)

(def-do-inst-theorem iand)

(def-do-inst-theorem iaload)

(def-do-inst-theorem iastore)

(defthm do-inst-of-iconst_m1
  (equal (do-inst ':iconst_m1 inst th s)
         (execute-iconst_x th s -1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-iconst_0
  (equal (do-inst ':iconst_0 inst th s)
         (execute-iconst_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-iconst_1
  (equal (do-inst ':iconst_1 inst th s)
         (execute-iconst_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-iconst_2
  (equal (do-inst ':iconst_2 inst th s)
         (execute-iconst_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-iconst_3
  (equal (do-inst ':iconst_3 inst th s)
         (execute-iconst_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-iconst_4
  (equal (do-inst ':iconst_4 inst th s)
         (execute-iconst_x th s 4))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-iconst_5
  (equal (do-inst ':iconst_5 inst th s)
         (execute-iconst_x th s 5))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem idiv)

(def-do-inst-theorem-with-inst if_acmpeq)
(def-do-inst-theorem-with-inst if_acmpne)

(def-do-inst-theorem-with-inst if_icmpeq)
(def-do-inst-theorem-with-inst if_icmpge)
(def-do-inst-theorem-with-inst if_icmpgt)
(def-do-inst-theorem-with-inst if_icmple)
(def-do-inst-theorem-with-inst if_icmplt)
(def-do-inst-theorem-with-inst if_icmpne)

(def-do-inst-theorem-with-inst ifeq)
(def-do-inst-theorem-with-inst ifge)
(def-do-inst-theorem-with-inst ifgt)
(def-do-inst-theorem-with-inst ifle)
(def-do-inst-theorem-with-inst iflt)
(def-do-inst-theorem-with-inst ifne)
(def-do-inst-theorem-with-inst ifnonnull)
(def-do-inst-theorem-with-inst ifnull)

(def-do-inst-theorem-with-inst iinc)

(def-do-inst-theorem-with-inst iload)

(defthm do-inst-of-iload_0
  (equal (do-inst ':iload_0 inst th s)
         (execute-iload_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-iload_1
  (equal (do-inst ':iload_1 inst th s)
         (execute-iload_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-iload_2
  (equal (do-inst ':iload_2 inst th s)
         (execute-iload_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-iload_3
  (equal (do-inst ':iload_3 inst th s)
         (execute-iload_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem imul)
(def-do-inst-theorem ineg)

(def-do-inst-theorem-with-inst instanceof)
(def-do-inst-theorem-with-inst checkcast)

(def-do-inst-theorem-with-inst invokeinterface)
(def-do-inst-theorem-with-inst invokespecial)
(def-do-inst-theorem-with-inst invokestatic)
(def-do-inst-theorem-with-inst invokevirtual)

(def-do-inst-theorem ior)
(def-do-inst-theorem irem)

(def-do-inst-theorem ireturn)

(def-do-inst-theorem ishl)
(def-do-inst-theorem ishr)

(def-do-inst-theorem-with-inst istore)

(defthm do-inst-of-istore_0
  (equal (do-inst ':istore_0 inst th s)
         (execute-istore_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-istore_1
  (equal (do-inst ':istore_1 inst th s)
         (execute-istore_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-istore_2
  (equal (do-inst ':istore_2 inst th s)
         (execute-istore_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-istore_3
  (equal (do-inst ':istore_3 inst th s)
         (execute-istore_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem isub)
(def-do-inst-theorem iushr)
(def-do-inst-theorem ixor)

(def-do-inst-theorem-with-inst lookupswitch)

(def-do-inst-theorem-with-inst jsr)
(def-do-inst-theorem-with-inst jsr_w)

(def-do-inst-theorem l2i)

(def-do-inst-theorem ladd)

(def-do-inst-theorem laload)

(def-do-inst-theorem land)

(def-do-inst-theorem lastore)

(def-do-inst-theorem lcmp)

(defthm do-inst-of-lconst_0
  (equal (do-inst ':lconst_0 inst th s)
         (execute-lconst_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-lconst_1
  (equal (do-inst ':lconst_1 inst th s)
         (execute-lconst_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-ldc
  (equal (do-inst ':ldc inst th s)
         (execute-ldc inst th s nil))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-ldc_w
  (equal (do-inst ':ldc_w inst th s)
         (execute-ldc inst th s t))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem-with-inst ldc2_w)

(def-do-inst-theorem ldiv)

(defthm do-inst-of-lload
  (equal (do-inst ':lload inst th s)
         (execute-lload inst th s))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-lload_0
  (equal (do-inst ':lload_0 inst th s)
         (execute-lload_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-lload_1
  (equal (do-inst ':lload_1 inst th s)
         (execute-lload_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-lload_2
  (equal (do-inst ':lload_2 inst th s)
         (execute-lload_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-lload_3
  (equal (do-inst ':lload_3 inst th s)
         (execute-lload_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem lmul)
(def-do-inst-theorem lneg)
(def-do-inst-theorem lor)
(def-do-inst-theorem lrem)

(def-do-inst-theorem lreturn)

(def-do-inst-theorem lshl)
(def-do-inst-theorem lshr)

(def-do-inst-theorem-with-inst lstore)

(defthm do-inst-of-lstore_0
  (equal (do-inst ':lstore_0 inst th s)
         (execute-lstore_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-lstore_1
  (equal (do-inst ':lstore_1 inst th s)
         (execute-lstore_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-lstore_2
  (equal (do-inst ':lstore_2 inst th s)
         (execute-lstore_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-lstore_3
  (equal (do-inst ':lstore_3 inst th s)
         (execute-lstore_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))

(def-do-inst-theorem lsub)
(def-do-inst-theorem lushr)
(def-do-inst-theorem lxor)

(def-do-inst-theorem monitorenter)
(def-do-inst-theorem monitorexit)

(def-do-inst-theorem-with-inst multianewarray)

(def-do-inst-theorem-with-inst new)
(def-do-inst-theorem-with-inst newarray)

(def-do-inst-theorem nop)
(def-do-inst-theorem pop)
(def-do-inst-theorem pop2)

(def-do-inst-theorem-with-inst ret)

(def-do-inst-theorem-with-inst putfield)
(def-do-inst-theorem-with-inst putstatic)

(def-do-inst-theorem return)

(def-do-inst-theorem-with-inst sipush)

(def-do-inst-theorem sastore)
(def-do-inst-theorem saload)

(def-do-inst-theorem swap)

(def-do-inst-theorem-with-inst tableswitch)

(def-do-inst-theorem d2f)
(def-do-inst-theorem d2i)
(def-do-inst-theorem d2l)

(def-do-inst-theorem fadd)
(def-do-inst-theorem fdiv)
(def-do-inst-theorem fmul)
(def-do-inst-theorem fneg)
(def-do-inst-theorem frem)
(def-do-inst-theorem fsub)

(def-do-inst-theorem dadd)
(def-do-inst-theorem ddiv)
(def-do-inst-theorem dmul)
(def-do-inst-theorem dneg)
(def-do-inst-theorem drem)
(def-do-inst-theorem dsub)

(def-do-inst-theorem faload)

(def-do-inst-theorem daload)

(def-do-inst-theorem fastore)

(def-do-inst-theorem dastore)

(def-do-inst-theorem f2i)
(def-do-inst-theorem f2d)
(def-do-inst-theorem f2l)
(def-do-inst-theorem i2f)
(def-do-inst-theorem i2d)
(def-do-inst-theorem l2d)
(def-do-inst-theorem l2f)

(def-do-inst-theorem fcmpg)
(def-do-inst-theorem fcmpl)

(def-do-inst-theorem dcmpg)
(def-do-inst-theorem dcmpl)

(def-do-inst-theorem dreturn)
(def-do-inst-theorem freturn)

(def-do-inst-theorem-with-inst fload)
(def-do-inst-theorem-with-inst dload)
(def-do-inst-theorem-with-inst fstore)
(def-do-inst-theorem-with-inst dstore)

(defthm do-inst-of-fload_0
  (equal (do-inst ':fload_0 inst th s)
         (execute-fload_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-fload_1
  (equal (do-inst ':fload_1 inst th s)
         (execute-fload_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-fload_2
  (equal (do-inst ':fload_2 inst th s)
         (execute-fload_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-fload_3
  (equal (do-inst ':fload_3 inst th s)
         (execute-fload_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))


(defthm do-inst-of-dload_0
  (equal (do-inst ':dload_0 inst th s)
         (execute-dload_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-dload_1
  (equal (do-inst ':dload_1 inst th s)
         (execute-dload_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-dload_2
  (equal (do-inst ':dload_2 inst th s)
         (execute-dload_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-dload_3
  (equal (do-inst ':dload_3 inst th s)
         (execute-dload_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))


(defthm do-inst-of-fstore_0
  (equal (do-inst ':fstore_0 inst th s)
         (execute-fstore_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-fstore_1
  (equal (do-inst ':fstore_1 inst th s)
         (execute-fstore_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-fstore_2
  (equal (do-inst ':fstore_2 inst th s)
         (execute-fstore_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-fstore_3
  (equal (do-inst ':fstore_3 inst th s)
         (execute-fstore_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))


(defthm do-inst-of-dstore_0
  (equal (do-inst ':dstore_0 inst th s)
         (execute-dstore_x th s 0))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-dstore_1
  (equal (do-inst ':dstore_1 inst th s)
         (execute-dstore_x th s 1))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-dstore_2
  (equal (do-inst ':dstore_2 inst th s)
         (execute-dstore_x th s 2))
  :hints (("Goal" :in-theory (enable do-inst))))

(defthm do-inst-of-dstore_3
  (equal (do-inst ':dstore_3 inst th s)
         (execute-dstore_x th s 3))
  :hints (("Goal" :in-theory (enable do-inst))))

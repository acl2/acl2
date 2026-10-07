; Determining which classes a given class mentions
;
; Copyright (C) 2020-2026 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Do we need to support non-ascii pathnames?

(include-book "kestrel/jvm/classes" :dir :system)
(include-book "std/util/bstar" :dir :system)

(local (in-theory (disable jvm::typep)))

(local
 (defthm true-listp-when-class-name-listp
   (implies (jvm::class-name-listp names)
            (true-listp names))
   :hints (("Goal" :in-theory (enable jvm::class-name-listp)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;move
(defun jvm::instruction-listp (l)
  (declare (xargs :guard t))
  (if (not (consp l))
      (null l)
    (and (jvm::instructionp (first l))
         (jvm::instruction-listp (rest l)))))

(defthm instruction-listp-of-strip-cdrs-when-method-programp-aux
  (implies (jvm::method-programp-aux p next-pc valid-pcs)
           (jvm::instruction-listp (strip-cdrs p)))
  :hints (("Goal" :in-theory (enable jvm::method-programp-aux))))

(defthm instruction-listp-of-strip-cdrs-when-method-program
 (implies (jvm::method-programp p)
          (jvm::instruction-listp (strip-cdrs p)))
 :hints (("Goal" :in-theory (enable jvm::method-programp))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund add-mentioned-classes-from-type (type acc)
  (declare (xargs :guard (and (jvm::typep type)
                              (jvm::class-name-listp acc))))
  (if (jvm::class-or-interface-namep type)
      (add-to-set-equal type acc)
    acc))

(defthm class-name-listp-of-add-mentioned-classes-from-type
  (implies (jvm::class-name-listp acc)
           (jvm::class-name-listp (add-mentioned-classes-from-type type acc)))
  :hints (("Goal" :in-theory (enable add-mentioned-classes-from-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund add-mentioned-classes-from-types (types acc)
  (declare (xargs :guard (and (jvm::all-typep types)
                              (true-listp types)
                              (jvm::class-name-listp acc))))
  (if (endp types)
      acc
    (let* ((type (first types))
           (acc (add-mentioned-classes-from-type type acc)))
      (add-mentioned-classes-from-types (rest types) acc))))

(defthm class-name-listp-of-add-mentioned-classes-from-types
  (implies (jvm::class-name-listp acc)
           (jvm::class-name-listp (add-mentioned-classes-from-types types acc)))
  :hints (("Goal" :in-theory (enable add-mentioned-classes-from-types))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund add-mentioned-classes-from-instruction (instruction acc)
  (declare (xargs :guard (and (jvm::instructionp instruction) ;see also JVM::JVM-INSTRUCTION-OKAYP (make a version that doesn't refer to PCs?)
                              (jvm::class-name-listp acc))
                  :guard-hints (("Goal" :in-theory (enable jvm::instructionp)))))
  (let ((opcode (first instruction)))
    (case opcode
      ((:invokevirtual :invokestatic :invokespecial
                       :new
                       :checkcast :anewarray :instanceof
                       :getfield :putfield :getstatic :putstatic ;maybe look into the field-id for these?
                       :invokeinterface
                       :multianewarray)
       (let ((type (farg1 instruction)))
         (if (not (jvm::typep type)) ; todo: prove this can't happen
             (prog2$ (er hard? 'add-mentioned-classes-from-instruction "Bad instruction: ~x0." instruction)
                     acc)
           (add-mentioned-classes-from-type type acc))))
      (t acc))))

(defthm class-name-listp-of-add-mentioned-classes-from-instruction
  (implies (jvm::class-name-listp acc)
           (jvm::class-name-listp (add-mentioned-classes-from-instruction instruction acc)))
  :hints (("Goal" :in-theory (enable add-mentioned-classes-from-instruction))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund add-mentioned-classes-from-instructions (instructions acc)
  (declare (xargs :guard (and (jvm::instruction-listp instructions)
                              (jvm::class-name-listp acc))))
  (if (endp instructions)
      acc
    (let* ((instruction (first instructions))
           (acc (add-mentioned-classes-from-instruction instruction acc)))
      (add-mentioned-classes-from-instructions (rest instructions) acc))))

(defthm class-name-listp-of-add-mentioned-classes-from-instructions
  (implies (jvm::class-name-listp acc)
           (jvm::class-name-listp (add-mentioned-classes-from-instructions instructions acc)))
  :hints (("Goal" :in-theory (enable add-mentioned-classes-from-instructions))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;extends ACC
;this just looks at the types of the fields
(defund add-mentioned-classes-from-fields (field-info-alist acc)
  (declare (xargs :guard (and (jvm::field-info-alistp field-info-alist)
                              (jvm::class-name-listp acc))
                  :guard-hints (("Goal" :in-theory (enable jvm::field-info-alistp jvm::field-id-listp jvm::field-idp)))))
  (if (endp field-info-alist)
      acc
    (let* ((entry (first field-info-alist))
           (field-id (car entry))
           (field-type (cdr field-id))
           (acc (add-mentioned-classes-from-type field-type acc)))
      (add-mentioned-classes-from-fields (rest field-info-alist) acc))))

(defthm class-name-listp-of-add-mentioned-classes-from-fields
  (implies (jvm::class-name-listp acc)
           (jvm::class-name-listp (add-mentioned-classes-from-fields field-info-alist acc)))
  :hints (("Goal" :in-theory (enable add-mentioned-classes-from-fields))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defund add-mentioned-classes-from-methods (method-info-alist acc)
  (declare (xargs :guard (and (jvm::method-info-alistp method-info-alist)
                              (jvm::class-name-listp acc))
                  :guard-hints (("Goal" :in-theory (enable jvm::method-info-alistp jvm::method-id-listp strip-cars
                                                           )))))
  (if (endp method-info-alist)
      acc
    (b* ((entry (first method-info-alist))
         ;; (method-id (car entry))
         (method-info (cdr entry))
         ;; Add any classes mentioned in parameter types:
         (acc (add-mentioned-classes-from-types (lookup-eq :parameter-types method-info) acc)) ; todo: named accessor for parameter-types
         ;; Add any classes mentioned in the program:
         (acc (if (or (jvm::method-abstractp method-info)
                      (jvm::method-nativep method-info))
                  acc ;; no program, so skip this method: ; todo: just check the program against :no-program
                (b* ((program (jvm::method-program method-info))
                     (instructions (if nil ; (eq :no-program program)
                                       nil
                                     (strip-cdrs program))))
                  (add-mentioned-classes-from-instructions instructions acc)))))
      ;; Continue with the next method:
      (add-mentioned-classes-from-methods (rest method-info-alist) acc))))

(defthm class-name-listp-of-add-mentioned-classes-from-methods
  (implies (jvm::class-name-listp acc)
           (jvm::class-name-listp (add-mentioned-classes-from-methods method-info-alist acc)))
  :hints (("Goal" :in-theory (enable add-mentioned-classes-from-methods))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of class-names.
(defund mentioned-classes-from-class-info (class-info)
  (declare (xargs :guard (jvm::class-infop0 class-info)))
  (b* ((superclass (jvm::class-decl-superclass class-info)) ;may be none
       (interfaces (jvm::class-decl-interfaces class-info))
       (acc (if (eq :none superclass) nil (list superclass))) ;start with the super class
       (acc (union-equal acc interfaces))
       (acc (add-mentioned-classes-from-fields (jvm::class-decl-non-static-fields class-info) acc))
       (acc (add-mentioned-classes-from-fields (jvm::class-decl-static-fields class-info) acc))
       (acc (add-mentioned-classes-from-methods (jvm::class-decl-methods class-info) acc)))
    acc))

(defthm class-name-listp-of-mentioned-classes-from-class-info
  (implies (jvm::class-infop0 class-info)
           (jvm::class-name-listp (mentioned-classes-from-class-info class-info)))
  :hints (("Goal" :in-theory (enable mentioned-classes-from-class-info))))

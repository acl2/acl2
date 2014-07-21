;; x86-state.lisp

;; x86-state has all the abstract stobj fields' RoW/WoW rules.

(in-package "ACL2")

(include-book "x86-state-defabsstobj")

; ======================================================================

;; We now generate the theorems we want about the accessors/updaters of the
;; abstract x86-32 state.  Note that from now onwards, all the reasoning that
;; we do about the processor state will use the abstract stobj.

(defun read-over-write-thms-array (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        ((equal (mk-name (subseq (symbol-name (car (car x86-32-model)))
                                 0
                                 (search "$C" (symbol-name
                                               (car (car x86-32-model))))))
                this-name)
         (read-over-write-thms-array this-name (cdr x86-32-model)))
        (t
         (let* ((x86-32-model-field (car x86-32-model))
                (that-name (car x86-32-model-field))
                (end (search "$C" (symbol-name that-name)))
                (that-name (subseq (symbol-name that-name) 0 end))
                (that-type (caddr x86-32-model-field)))
           (cond ((and (consp that-type)
                       (equal (car that-type) 'array))
                  (let ((this-getter (mk-name this-name "I"))
                        (that-setter (mk-name "!" that-name "I")))
                    (cons `(DEFTHM ,(mk-name this-getter "-" that-setter)
                             (EQUAL (,this-getter I2 (,that-setter I1 VAL x86-32))
                                    (,this-getter I2 x86-32)))
                          (read-over-write-thms-array this-name (cdr x86-32-model)))))
                 (t
                  (let ((this-getter (mk-name this-name "I"))
                        (that-setter (mk-name "!" that-name)))
                    (cons `(DEFTHM ,(mk-name this-getter "-" that-setter)
                             (EQUAL (,this-getter I (,that-setter VAL x86-32))
                                    (,this-getter I x86-32)))
                          (read-over-write-thms-array this-name (cdr x86-32-model))))))))))

(defun write-over-write-thms-array-1 (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         (let* ((x86-32-model-field (car x86-32-model))
                (that-name (car x86-32-model-field))
                (end (search "$C" (symbol-name that-name)))
                (that-name (subseq (symbol-name that-name) 0 end))
                (that-type (caddr x86-32-model-field)))
           (cond ((and (consp that-type)
                       (equal (car that-type) 'array))
                  (let ((this-setter (mk-name "!" this-name "I"))
                        (that-setter (mk-name "!" that-name "I")))
                    (cons `(DEFTHM ,(mk-name this-setter "-" that-setter)
                             (EQUAL (,this-setter I2 VAL2 (,that-setter I1 VAL1 x86-32))
                                    (,that-setter I1 VAL1 (,this-setter I2 VAL2 x86-32))))
                          (write-over-write-thms-array-1 this-name (cdr x86-32-model)))))
                 (t
                  (let ((this-setter (mk-name "!" this-name "I"))
                        (that-setter (mk-name "!" that-name)))
                    (cons `(DEFTHM ,(mk-name this-setter "-" that-setter)
                             (EQUAL (,this-setter I VAL2 (,that-setter VAL1 x86-32))
                                    (,that-setter VAL1 (,this-setter I VAL2 x86-32))))
                          (write-over-write-thms-array-1 this-name (cdr x86-32-model))))))))))

(defun write-over-write-thms-array (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        ((equal (car (car x86-32-model))
                this-name)
         ;; We wish to nest field updates in the same order (inside to
         ;; outside) as they are given in the x86-32 model.  So we
         ;; generate the write over write commutativity lemmatta only
         ;; for fields that come after this one in the model.
         (write-over-write-thms-array-1 this-name (cdr x86-32-model)))
        (t
         (write-over-write-thms-array this-name (cdr x86-32-model)))))

(defun read-over-write-thms-simple (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        ((equal (mk-name (subseq (symbol-name (car (car x86-32-model)))
                                 0
                                 (search "$C" (symbol-name
                                               (car (car x86-32-model))))))
                this-name)
         (read-over-write-thms-simple this-name (cdr x86-32-model)))
        (t
         (let* ((x86-32-model-field (car x86-32-model))
                (that-name (car x86-32-model-field))
                (end (search "$C" (symbol-name that-name)))
                (that-name (subseq (symbol-name that-name) 0 end))
                (that-type (caddr x86-32-model-field)))
           (cond ((and (consp that-type)
                       (equal (car that-type) 'array))
                  (let ((this-getter (mk-name this-name))
                        (that-setter (mk-name "!" that-name "I")))
                    (cons `(DEFTHM ,(mk-name this-getter "-" that-setter)
                             (EQUAL (,this-getter (,that-setter I VAL x86-32))
                                    (,this-getter x86-32)))
                          (read-over-write-thms-simple this-name (cdr x86-32-model)))))
                 (t
                  (let ((this-getter (mk-name this-name))
                        (that-setter (mk-name "!" that-name)))
                    (cons `(DEFTHM ,(mk-name this-getter "-" that-setter)
                             (EQUAL (,this-getter (,that-setter VAL x86-32))
                                    (,this-getter x86-32)))
                          (read-over-write-thms-simple this-name (cdr x86-32-model))))))))))

(defun write-over-write-thms-simple-1 (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         (let* ((x86-32-model-field (car x86-32-model))
                (that-name (car x86-32-model-field))
                (end (search "$C" (symbol-name that-name)))
                (that-name (subseq (symbol-name that-name) 0 end))
                (that-type (caddr x86-32-model-field)))
           (cond ((and (consp that-type)
                       (equal (car that-type) 'array))
                  (let ((this-setter (mk-name "!" this-name))
                        (that-setter (mk-name "!" that-name "I")))
                    (cons `(DEFTHM ,(mk-name this-setter "-" that-setter)
                             (EQUAL (,this-setter VAL2 (,that-setter I VAL1 x86-32))
                                    (,that-setter I VAL1 (,this-setter VAL2 x86-32))))
                          (write-over-write-thms-simple-1 this-name (cdr x86-32-model)))))
                 (t
                  (let ((this-setter (mk-name "!" this-name))
                        (that-setter (mk-name "!" that-name)))
                    (cons `(DEFTHM ,(mk-name this-setter "-" that-setter)
                             (EQUAL (,this-setter VAL2 (,that-setter VAL1 x86-32))
                                    (,that-setter VAL1 (,this-setter VAL2 x86-32))))
                          (write-over-write-thms-simple-1 this-name
                                                          (cdr x86-32-model))))))))))

(defun write-over-write-thms-simple (this-name x86-32-model)
  (cond ((endp x86-32-model)
         '())
        ((equal (car (car x86-32-model))
                this-name)
         ;; We wish to nest field updates in the same order (inside to
         ;; outside) as they are given in the x86-32 model.  So we
         ;; generate the write over write commutativity lemmatta only
         ;; for fields that come after this one in the model.  (These
         ;; rules commute "this" inside "that")
         (write-over-write-thms-simple-1 this-name (cdr x86-32-model)))
        (t
         (write-over-write-thms-simple this-name (cdr x86-32-model)))))

(defun x86-32-stobj-field-thms-fn-1 (x86-32-model-field x86-32-model)
  ;; this function is rather brittle, in that it assumes that the
  ;; elements of the x86-32-model are defined in a rigid manner.
  (let* ((name (car x86-32-model-field))
         (end (search "$C" (symbol-name name)))
         (name (mk-name (subseq (symbol-name name) 0 end)))
         (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array)
                (consp (cadr type))
                (equal (car (cadr type)) 'unsigned-byte))
           (let* ((predicate (mk-name name "P"))
                  (namei     (mk-name name "I"))
                  (getter    namei)
                  (setter    (mk-name "!" namei))
                  (size      (cadr (cadr  type)))
                  (length    (if (equal (car (cddr (cddr (cddr x86-32-model-field))))
                                        'T)
                                 ;; resizable array
                                 `(,(mk-name name "-LENGTH") x86-32)
                               (car  (caddr type)))))
             `( ;; readers
               (DEFTHM ,(mk-name predicate "-FORWARD")
                 (IMPLIES (,predicate X)
                          (NAT-LISTP X))
                 :RULE-CLASSES :FORWARD-CHAINING)
               (DEFTHM ,(mk-name "NATP-" getter)
                 (IMPLIES (FORCED-AND (x86-32P x86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length))
                          (AND (INTEGERP (,getter I x86-32))
                               (<= 0 (,getter I x86-32))))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (ENCAPSULATE
                ()
                ;; I used to have this local, but some of the proofs
                ;; about functions such as memi needed them.
                (DEFTHM ,(mk-name "NTH-OF-" getter "-LESS-THAN-EXPT-2-" size)
                  (IMPLIES (AND (,predicate X)
                                (INTEGERP I)
                                (<= 0 I)
                                (< I (LEN X)))
                           (< (NTH I X) ,(expt 2 size)))
                  :HINTS (("Goal" :IN-THEORY (E/D (NTH ,predicate) ())))
                  :RULE-CLASSES :LINEAR)
                (DEFTHM ,(mk-name getter "-LESS-THAN-EXPT-2-" size)
                  (IMPLIES (FORCED-AND (x86-32P x86-32)
                                       (INTEGERP I)
                                       (<= 0 I)
                                       (< I ,length))
                           (< (,getter I x86-32) ,(expt 2 size)))
                  :RULE-CLASSES :LINEAR)
                )
               ;; writers
               (DEFTHM ,(mk-name predicate "-UPDATE-NTH")
                 (IMPLIES (FORCED-AND (,predicate X)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I (LEN X))
                                      (INTEGERP V)
                                      (<= 0 V)
                                      (< V ,(expt 2 size)))
                          (,predicate (UPDATE-NTH I V X)))
                 :HINTS (("Goal" :IN-THEORY (E/D (UPDATE-NTH) ()))))
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter "1")
                 (IMPLIES (FORCED-AND ;; (x86-32P x86-32)
                           (INTEGERP I1)
                           (<= 0 I1)
                           ;;(< I1 ,length)
                           (INTEGERP I2)
                           (<= 0 I2)
                           ;;(< I2 ,length)
                           )
                          (EQUAL (,getter I2 (,setter I1 V x86-32))
                                 (IF (EQUAL I1 I2)
                                     V
                                     (,getter I2 x86-32)))))
               (DEFTHM ,(mk-name setter "-" setter "-SAME")
                 (IMPLIES (FORCED-AND ;; (x86-32P x86-32)
                           ;;(INTEGERP I)
                           ;;(<= 0 I)
                           ;;(< I ,length)
                           )
                          (EQUAL (,setter I V2 (,setter I V1 x86-32))
                                 (,setter I V2 x86-32))))
               (DEFTHM ,(mk-name setter "-" setter "-DIFFERENT")
                 ;; do we wnat to specify the loop-stopper?
                 (IMPLIES (AND (NOT (EQUAL I1 I2))
                               (FORCED-AND ;; (x86-32P x86-32)
                                (INTEGERP I1)
                                (<= 0 I1)
                                ;;(< I1 ,length)
                                (INTEGERP I2)
                                (<= 0 I2)
                                ;;(< I2 ,length)
                                ))
                          (EQUAL (,setter I2 V2 (,setter I1 V1 x86-32))
                                 (,setter I1 V1 (,setter I2 V2 x86-32)))))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCED-AND (x86-32P x86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length))
                          (EQUAL (,setter I (,getter I x86-32) x86-32)
                                 x86-32)))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-array name x86-32-model)
               ,@(write-over-write-thms-array name x86-32-model)
               )))
          ((and (consp type)
                (equal (car type) 'array)
                (consp (cadr type))
                (equal (car (cadr type)) 'signed-byte))
           (let* ((predicate (mk-name name "P"))
                  (namei     (mk-name name "I"))
                  (getter    namei)
                  (setter    (mk-name "!" namei))

                  (size      (1- (cadr (cadr  type))))
                  (length    (if (equal (car (cddr (cddr (cddr x86-32-model-field))))
                                        'T)
                                 ;; resizable array
                                 `(,(mk-name name "-LENGTH") x86-32)
                               (car  (caddr type)))))
             `( ;; readers
               (DEFTHM ,(mk-name predicate "-FORWARD")
                 (IMPLIES (,predicate X)
                          (INTEGER-LISTP X))
                 :RULE-CLASSES :FORWARD-CHAINING)
               (DEFTHM ,(mk-name "INTEGERP-" getter)
                 (IMPLIES (FORCED-AND (x86-32P x86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length))
                          (INTEGERP (,getter I x86-32)))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (ENCAPSULATE
                ()
                ;; I used to have this local, but some of the proofs
                ;; about functions such as memi needed them.
                (DEFTHM ,(mk-name "NTH-OF-" getter "-LESS-THAN-EXPT-2-" size)
                  (IMPLIES (AND (,predicate X)
                                (INTEGERP I)
                                (<= 0 I)
                                (< I (LEN X)))
                           (< (NTH I X) ,(expt 2 size)))
                  :HINTS (("Goal" :IN-THEORY (E/D (NTH ,predicate) ())))
                  :RULE-CLASSES :LINEAR)
                (DEFTHM ,(mk-name "NTH-OF-" getter "-GE-NEG-EXPT-2-" size)
                  (IMPLIES (AND (,predicate X)
                                (INTEGERP I)
                                (<= 0 I)
                                (< I (LEN X)))
                           (<= ,(- (expt 2 size)) (NTH I X)))
                  :HINTS (("Goal" :IN-THEORY (E/D (NTH ,predicate) ())))
                  :RULE-CLASSES :LINEAR)
                (DEFTHM ,(mk-name getter "-LESS-THAN-EXPT-2-" size)
                  (IMPLIES (FORCED-AND (x86-32P x86-32)
                                       (INTEGERP I)
                                       (<= 0 I)
                                       (< I ,length))
                           (< (,getter I x86-32) ,(expt 2 size)))
                  :RULE-CLASSES :LINEAR)
                (DEFTHM ,(mk-name getter "-GE-NEG-EXPT-2-" size)
                  (IMPLIES (FORCED-AND (x86-32P x86-32)
                                       (INTEGERP I)
                                       (<= 0 I)
                                       (< I ,length))
                           (<= ,(- (expt 2 size)) (,getter I x86-32)))
                  :RULE-CLASSES :LINEAR)
                )
               ;; writers
               (DEFTHM ,(mk-name predicate "-UPDATE-NTH")
                 (IMPLIES (FORCED-AND (,predicate X)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I (LEN X))
                                      (INTEGERP V)
                                      (<= ,(- (expt 2 size)) V)
                                      (< V ,(expt 2 size)))
                          (,predicate (UPDATE-NTH I V X)))
                 :HINTS (("Goal" :IN-THEORY (E/D (UPDATE-NTH) ()))))
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter "1")
                 (IMPLIES (FORCED-AND ;; (x86-32P x86-32)
                           (INTEGERP I1)
                           (<= 0 I1)
                           ;;(< I1 ,length)
                           (INTEGERP I2)
                           (<= 0 I2)
                           ;;(< I2 ,length)
                           )
                          (EQUAL (,getter I2 (,setter I1 V x86-32))
                                 (IF (EQUAL I1 I2)
                                     V
                                     (,getter I2 x86-32)))))
               (DEFTHM ,(mk-name setter "-" setter "-SAME")
                 (IMPLIES (FORCED-AND ;; (x86-32P x86-32)
                           ;;(INTEGERP I)
                           ;;(<= 0 I)
                           ;;(< I ,length)
                           )
                          (EQUAL (,setter I V2 (,setter I V1 x86-32))
                                 (,setter I V2 x86-32))))
               (DEFTHM ,(mk-name setter "-" setter "-DIFFERENT")
                 ;; do we want to specify the loop-stopper?
                 (IMPLIES (AND (NOT (EQUAL I1 I2))
                               (FORCED-AND ;; (x86-32P x86-32)
                                (INTEGERP I1)
                                (<= 0 I1)
                                ;;(< I1 ,length)
                                (INTEGERP I2)
                                (<= 0 I2)
                                ;;(< I2 ,length)
                                ))
                          (EQUAL (,setter I2 V2 (,setter I1 V1 x86-32))
                                 (,setter I1 V1 (,setter I2 V2 x86-32)))))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCED-AND (x86-32P x86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length))
                          (EQUAL (,setter I (,getter I x86-32) x86-32)
                                 x86-32)))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-array name x86-32-model)
               ,@(write-over-write-thms-array name x86-32-model)
               )))
          ((and (consp type)
                (equal (car type) 'unsigned-byte))
           (let* ((predicate (mk-name name "P"))
                  (getter  (mk-name name))
                  (setter  (mk-name "!" name))
                  (size    (cadr type)))
             `( ;; readers
               (DEFTHM ,(mk-name "NATP-" name)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (AND (INTEGERP (,getter x86-32))
                               (<= 0 (,getter x86-32))))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (DEFTHM ,(mk-name name "-LESS-THAN-EXPT-2-" size)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (< (,getter x86-32) ,(expt 2 size)))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
                 :RULE-CLASSES :LINEAR)
               ;; writers
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (EQUAL (,getter (,setter V x86-32))
                        V))
               (DEFTHM ,(mk-name setter "-" setter)
                 (EQUAL (,setter V2 (,setter V1 x86-32))
                        (,setter V2 x86-32)))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (EQUAL (,setter (,getter x86-32) x86-32)
                                 x86-32)))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-simple name x86-32-model)
               ,@(write-over-write-thms-simple name x86-32-model)
               )))
          ((and (consp type)
                (equal (car type) 'signed-byte))
           (let* ((predicate (mk-name name "P"))
                  (getter  (mk-name name))
                  (setter  (mk-name "!" name))
                  (size    (1- (cadr type))))
             `( ;; readers
               (DEFTHM ,(mk-name "INTEGERP-" name)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (INTEGERP (,getter x86-32)))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (DEFTHM ,(mk-name name "-LESS-THAN-EXPT-2-" size)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (< (,getter x86-32) ,(expt 2 size)))
                 :RULE-CLASSES :LINEAR)
               (DEFTHM ,(mk-name name "-GE-NEGATIVE-EXPT-2-" size)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (<= ,(- (expt 2 size)) (,getter x86-32)))
                 :RULE-CLASSES :LINEAR)
               ;; writers
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (EQUAL (,getter (,setter V x86-32))
                        V))
               (DEFTHM ,(mk-name setter "-" setter)
                 (EQUAL (,setter V2 (,setter V1 x86-32))
                        (,setter V2 x86-32)))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (EQUAL (,setter (,getter x86-32) x86-32)
                                 x86-32)))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-simple name x86-32-model)
               ,@(write-over-write-thms-simple name x86-32-model)
               )))
          ((and (consp type)
                (equal (car type) 'integer))
           (let* ((predicate (mk-name name "P"))
                  (getter  (mk-name name))
                  (setter  (mk-name "!" name))
                  (size    (caddr type)))
             `( ;; readers
               (DEFTHM ,(mk-name "NATP-" name)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (AND (INTEGERP (,getter x86-32))
                               (<= 0 (,getter x86-32))))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
                 :RULE-CLASSES :TYPE-PRESCRIPTION)
               (DEFTHM ,(mk-name name "-LESS-THAN-" size)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (<= (,getter x86-32) ,size))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
                 :RULE-CLASSES :LINEAR)
               ;; writers
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (EQUAL (,getter (,setter V x86-32))
                        V))
               (DEFTHM ,(mk-name setter "-" setter)
                 (EQUAL (,setter V2 (,setter V1 x86-32))
                        (,setter V2 x86-32)))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (EQUAL (,setter (,getter x86-32) x86-32)
                                 x86-32)))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-simple name x86-32-model)
               ,@(write-over-write-thms-simple name x86-32-model)
               )))
          (t
           ;; type is presumably 'T
           (let* ((getter name)
                  (setter (mk-name "!" name)))
             `( ;; readers
               ;; none
               ;; writers
               ;; read over write and such --- this field
               (DEFTHM ,(mk-name getter "-" setter)
                 (EQUAL (,getter (,setter V x86-32))
                        V))
               (DEFTHM ,(mk-name setter "-" setter)
                 (EQUAL (,setter V2 (,setter V1 x86-32))
                        (,setter V2 x86-32)))
               (DEFTHM ,(mk-name setter "-" getter)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (EQUAL (,setter (,getter x86-32) x86-32)
                                 x86-32)))
               ;; read over write and such --- other field
               ,@(read-over-write-thms-simple name x86-32-model)
               ,@(write-over-write-thms-simple name x86-32-model)
               ))))))

(defun x86-32-stobj-x86-32p-setter-thms-fn-1 (x86-32-model-field)
  ;; this function is rather brittle, in that it assumes that the
  ;; elements of the x86-32-model are defined in a rigid manner.
  (let* ((name (car x86-32-model-field))
         (type (caddr x86-32-model-field))
         (end  (search "$C" (symbol-name name)))
         (name (mk-name (subseq (symbol-name name) 0 end)))
         (predicate (mk-name name "P")))
    (cond ((and (consp type)
                (equal (car type) 'array)
                (consp (cadr type))
                (equal (car (cadr type)) 'unsigned-byte))
           (let* ((namei     (mk-name name "I"))
                  (setter    (mk-name "!" namei))
                  (size      (cadr (cadr  type)))
                  (length    (if (equal (car (cddr (cddr (cddr x86-32-model-field))))
                                        'T)
                                 ;; resizable array
                                 `(,(mk-name name "-LENGTH") x86-32)
                               (car  (caddr type)))))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (x86-32P x86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length)
                                      (INTEGERP V)
                                      (<= 0 V)
                                      (< V ,(expt 2 size)))
                          ,(if (or (equal name 'mem-table)
                                   (equal name 'mem-array))
                               ;; Because of the good-memp predicate,
                               ;; we must handle these two
                               ;; seperately.  In fact, these fields
                               ;; will only be modified by !memi, and
                               ;; it is that which we will prove
                               ;; maintains the x86-32p predicate.
                               `(x86-32P-PRE (,setter I V x86-32))
                             `(x86-32P (,setter I V x86-32))))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
               )))
          ((and (consp type)
                (equal (car type) 'array)
                (consp (cadr type))
                (equal (car (cadr type)) 'signed-byte))
           (let* ((namei     (mk-name name "I"))
                  (setter    (mk-name "!" namei))
                  (size      (1- (cadr (cadr  type))))
                  (length    (if (equal (car (cddr (cddr (cddr x86-32-model-field))))
                                        'T)
                                 ;; resizable array
                                 `(,(mk-name name "-LENGTH") x86-32)
                               (car  (caddr type)))))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (x86-32P x86-32)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length)
                                      (INTEGERP V)
                                      (<= ,(- (expt 2 size)) V)
                                      (< V ,(expt 2 size)))
                          ,(if (or (equal name 'mem-table)
                                   (equal name 'mem-array))
                               ;; Because of the good-memp predicate,
                               ;; we must handle these two
                               ;; seperately.  In fact, these fields
                               ;; will only be modified by !memi, and
                               ;; it is that which we will prove
                               ;; maintains the x86-32p predicate.
                               `(x86-32P-PRE (,setter I V x86-32))
                             `(x86-32P (,setter I V x86-32))))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
               )))
          ((and (consp type)
                (equal (car type) 'unsigned-byte))
           (let* ((setter  (mk-name "!" name))
                  (size    (cadr type)))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (x86-32P x86-32)
                                      ;; can we replace these with
                                      ;; nXYp?  do we want to?
                                      (INTEGERP V)
                                      (<= 0 V)
                                      (< V ,(expt 2 size)))
                          ,(if (equal name 'mem-array-next-addr)
                               ;; Because of the good-memp predicate,
                               ;; we must handle this one seperately.
                               ;; In fact, this field will only be
                               ;; modified by !memi, and it is that
                               ;; which we will prove maintains the
                               ;; x86-32p predicate.
                               `(x86-32P-PRE (,setter V x86-32))
                             `(x86-32P (,setter V x86-32))))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))))
             ))
          ((and (consp type)
                (equal (car type) 'signed-byte))
           (let* ((setter  (mk-name "!" name))
                  (size    (1- (cadr type))))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (x86-32P x86-32)
                                      ;; can we replace these with
                                      ;; iXYp?  do we want to?
                                      (INTEGERP V)
                                      (<= ,(- (expt 2 size)) V)
                                      (< V ,(expt 2 size)))
                          ,(if (equal name 'mem-array-next-addr)
                               ;; Because of the good-memp predicate,
                               ;; we must handle this one seperately.
                               ;; In fact, this field will only be
                               ;; modified by !memi, and it is that
                               ;; which we will prove maintains the
                               ;; x86-32p predicate.
                               `(x86-32P-PRE (,setter V x86-32))
                             `(x86-32P (,setter V x86-32))))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
               )))
          ((and (consp type)
                (equal (car type) 'integer))
           (let* ((setter  (mk-name "!" name))
                  (size    (caddr type)))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCED-AND (x86-32P x86-32)
                                      ;; can we replace these with
                                      ;; nXYp?  do we want to?
                                      (INTEGERP V)
                                      (<= 0 V)
                                      (<= V ,size))
                          ,(if (equal name 'mem-array-next-addr)
                               ;; Because of the good-memp predicate,
                               ;; we must handle this one seperately.
                               ;; In fact, this field will only be
                               ;; modified by !memi, and it is that
                               ;; which we will prove maintains the
                               ;; x86-32p predicate.
                               `(x86-32P-PRE (,setter V x86-32))
                             `(x86-32P (,setter V x86-32))))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
               )))
          (t
           ;; type is presumably 'T
           (let* ((setter (mk-name "!" name)))
             `((DEFTHM ,(mk-name "X86-32P-" setter)
                 (IMPLIES (FORCE (x86-32P x86-32))
                          (x86-32P (,setter V x86-32)))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))))

             )))))

(defun x86-32-stobj-x86-32p-setter-thms-fn (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         `(,@(x86-32-stobj-x86-32p-setter-thms-fn-1 (car x86-32-model))
           ,@(x86-32-stobj-x86-32p-setter-thms-fn (cdr x86-32-model))))))

(defun x86-32-stobj-field-thms-fn (x86-32-model full-x86-32-model)
  ;; we use two copies of the x86-32-model, one to step through here, and
  ;; one to step through in x86-32-stobj-field-thms-fn-1 so that we can
  ;; generate the read-over-write lematta for different fields.
 (cond ((endp x86-32-model)
         '())
        (t
         `(,@(x86-32-stobj-field-thms-fn-1 (car x86-32-model)
                                           full-x86-32-model)
           ,@(x86-32-stobj-field-thms-fn (cdr x86-32-model)
                                         full-x86-32-model)))))

; Lemmas to help with proofs about STOBJs that hold x86-32 state.  Our
; goal is to prove a nice set of forward-chaining lemmas, as our
; predicates seem nicely set up for that.

(defmacro x86-32-stobj-field-thms (x86-32-model)
  `(ENCAPSULATE
    ()

    (LOCAL
     (DEFTHM NAT-LISTP-THM
       (IMPLIES (AND (NAT-LISTP X)
                     (INTEGERP I)
                     (<= 0 I)
                     (< I (LEN X)))
                (AND (INTEGERP (NTH I X))
                     (<= 0 (NTH I X))))))

    (LOCAL
     (DEFTHM UPDATE-NTH-THM-1
       (EQUAL (UPDATE-NTH I V2 (UPDATE-NTH I V1 X))
              (UPDATE-NTH I V2 X))))

    (LOCAL
     (DEFTHM UPDATE-NTH-THM-2
       (IMPLIES (AND (INTEGERP I1)
                     (<= 0 I1)
                     (INTEGERP I2)
                     (<= 0 I2)
                     (NOT (EQUAL I1 I2)))
                (EQUAL (UPDATE-NTH I2 V2 (UPDATE-NTH I1 V1 X))
                       (UPDATE-NTH I1 V1 (UPDATE-NTH I2 V2 X))))))

    (LOCAL
     (DEFTHM UPDATE-NTH-THM-3
       (IMPLIES (AND (INTEGERP N)
                     (<= 0 N)
                     (< N (LEN x86-32))
                     (INTEGERP I)
                     (<= 0 I)
                     (< I (LEN (NTH N x86-32))))
                (EQUAL (UPDATE-NTH N
                                   (UPDATE-NTH I (NTH I (NTH N x86-32))
                                               (NTH N x86-32))
                                   x86-32)
                       x86-32))))

    (LOCAL
     (DEFTHM UPDATE-NTH-THM-4
       (IMPLIES (AND (INTEGERP I)
                     (<= 0 I)
                     (< I (LEN x86-32)))
                (EQUAL (UPDATE-NTH I (NTH I x86-32) x86-32)
                       x86-32))))

    (LOCAL
     (IN-THEORY (E/D ()
                     (NTH UPDATE-NTH))))

    ,@(x86-32-stobj-field-thms-fn x86-32-model x86-32-model)
    ,@(x86-32-stobj-x86-32p-setter-thms-fn x86-32-model)))

;; TO-DO@Shilpi: Where was length disabled?  Should it have been
;; disabled locally
(in-theory (enable length))

(make-event
 ;; To get the events generated by this make-event: put
 ;; `(x86-32-stobj-field-thms ,*x86-32-model*) through ACL2, and trans1 the
 ;; output.
 `(x86-32-stobj-field-thms ,*pruned-x86-32-model*))

;; Some rules about the memory in the abstract stobj:

(defthm memi-is-an-unsigned-byte
  (implies (x86-32p x86-32) ; With abstract stobj, can omit (n45p addr)!
           (n08p (memi addr x86-32)))
  :hints (("Goal" :in-theory (enable memi x86-32p)
           :use ((:instance memp-aux-necc
                            (i addr)
                            (x (nth *memi* x86-32))))))
  :rule-classes
  ((:type-prescription
    :corollary
    (implies (forced-and (x86-32p x86-32))
             (integerp (memi addr x86-32))))
   (:linear
    :corollary
    (implies (forced-and (x86-32p x86-32))
             (<= 0 (memi addr x86-32))))
   (:linear
    :corollary
    (implies (forced-and (x86-32p x86-32))
             (< (memi addr x86-32)
                256)))))

;; Do I need the following rule?
;; (defthm memi-forward
;;   (implies (memp x)
;;            (nat-listp x))
;;   :rule-classes :forward-chaining)

(defthm x86-32p-!memi
  (implies (and (x86-32p x86-32)
                (n32p i)
                (n08p v))
           (x86-32p (!memi i v x86-32))))

(defthm memi-!memi
  (equal (memi i (!memi j v x86-32))
         (if (equal i j)
             (or v 0)
           (memi i x86-32))))

(LOCAL
;; Taken from x86-32-stobj-field-thms.
 (DEFTHM UPDATE-NTH-THM-1
   (EQUAL (UPDATE-NTH I V2 (UPDATE-NTH I V1 X))
          (UPDATE-NTH I V2 X))))

(defthm !memi-!memi-same
  (equal (!memi i v1 (!memi i v2 x))
         (!memi i v1 x))
  :hints (("Goal" :in-theory (enable !memi))))

(defthm !memi-!memi-different
  (implies (and (not (equal i1 i2))
                (forced-and (integerp i1)
                            (<= 0 i1)
                            (integerp i2)
                            (<= 0 i2)))
           (equal (!memi i2 v2 (!memi i1 v1 x86-32))
                  (!memi i1 v1 (!memi i2 v2 x86-32)))))

;; ======================================================================

;; Disabling abstract stobj functions:

(defun disable-abs-stobj-fns-fn-1 (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         (let* ((name (car (car x86-32-model)))
                (name (mk-name (subseq (symbol-name name) 0
                                       (search "$C" (symbol-name name)))))
                (type (caddr (car x86-32-model))))
           (cond ((and (consp type)
                       (equal (car type) 'array))
                  (let* ((namei     (mk-name name "I"))
                         (getter    namei)
                         (setter    (mk-name "!" namei))
                         (recognizer (mk-name name "P")))
                    (append `(,getter
                              ,setter
                              ,recognizer
                              )
                            (disable-abs-stobj-fns-fn-1 (cdr x86-32-model)))))
                 (t
                  (let* ((getter  name)
                         (setter  (mk-name "!" name))
                         (recognizer (mk-name name "P")))
                    (append `(,getter ,setter ,recognizer)
                            (disable-abs-stobj-fns-fn-1
                             (cdr x86-32-model))))))))))

(defmacro disable-abs-stobj-fns-fn (x86-32-model)
  `(IN-THEORY
    (DISABLE ,@(disable-abs-stobj-fns-fn-1 x86-32-model))))

(make-event
 `(disable-abs-stobj-fns-fn ,*pruned-x86-32-model*))

(in-theory (disable memi !memi
                    x86-32p))

;; ======================================================================

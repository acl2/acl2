;; AUTHOR:
;; Shilpi Goel <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "x86-abstract-state")

;; ======================================================================

(defsection x86-state-field-theorems

  :parents (machine)

  :short "Theorems about the fields of @('x86')"

  :long "<p>For the @('x86') abstract stobj, we prove all the fields'
  <i>field type</i>, <i>writing the read</i>, and intra-field
  <i>RoW</i> (read-over-write) and <i>WoW</i> (write-over-write)
  rules. E.g., for the field RGF, these rules are as follows:</p>

<p>Field type:</p>
<ul>
  <li><tt>RGFI-IS-I64P</tt></li>
  <li><tt>X86P-!RGFI</tt></li>
</ul>

  <p>Writing the Read:</p>
<ul>
  <li><tt>!RGFI-RGFI</tt></li>
</ul>

  <p>RoW (intra-field):</p>
<ul>
  <li><tt>RGFI-!RGFI</tt></li>
</ul>

  <p>WoW (intra-field):</p>
<ul>
  <li><tt>!RGFI-!RGFI-SAME</tt></li>
  <li><tt>!RGFI-!RGFI-DIFFERENT-UNEQUAL-INDICES</tt></li>
  <li><tt>!RGFI-!RGFI-DIFFERENT-CONCRETE-INDICES</tt></li>
</ul>

  <p>Inter-field RoW and WoW theorems like <tt>RGFI-!FLGI</tt>, can be
  found in @(see x86-RoW-WoW-thms)</p>"

  (defun x86-stobj-field-thms-fn-1 (x86-model-field)
    ;; E.g., (x86-stobj-field-thms-fn-1 (car *pruned-x86-model*))

    ;; This function assumes that x86-model-field is defined using the
    ;; same syntax as that for a field in a defstobj definition.

    (let* ((name (car x86-model-field))
           (end (search "$C" (symbol-name name)))
           (name (mk-name (subseq (symbol-name name) 0 end)))
           (type (caddr x86-model-field)))
      (cond

       ((and (consp type)
             (equal (car type) 'array)
             (consp (cadr type)))
        (let* ((predicate (mk-name name "P"))
               (namei     (mk-name name "I"))
               (constant (mk-name "*" name "I*"))
               (getter    namei)
               (setter    (mk-name "!" namei))
               (size      (cadr (cadr  type))))
          `(
            ;; Field type theorem:
            ,(if (equal (car (cadr type)) 'unsigned-byte)
                 `(DEFTHM-USB ,(mk-name getter (if (< size 10) "-IS-N0" "-IS-N") size "P")
                    :hyp (FORCE (X86P X86))
                    :bound ,size
                    :concl (,getter I X86)
                    :HINTS (("GOAL" :IN-THEORY (E/D (,getter X86P) ())
                             :USE ((:INSTANCE ,(mk-name predicate "-AUX-NECC")
                                              (I I)
                                              (X (NTH ,constant
                                                      X86))))))
                    :gen-linear t
                    :gen-type t)

               `(DEFTHM-SB ,(mk-name getter "-IS-I" size "P")
                  :hyp (X86P X86)
                  :bound ,size
                  :concl (,getter I X86)
                  :HINTS (("GOAL" :IN-THEORY (E/D (,getter X86P) ())
                           :USE ((:INSTANCE ,(mk-name predicate "-AUX-NECC")
                                            (I I)
                                            (X (NTH ,constant
                                                    X86))))))
                  :gen-type t
                  :gen-linear t))

            ;; RoW Theorem:
            (DEFTHM ,(mk-name getter "-" setter)
              (EQUAL (,getter I2 (,setter I1 V x86))
                     (IF (EQUAL I1 I2)
                         V
                         (,getter I2 x86))))

            ;; WoW Theorems:
            (DEFTHM ,(mk-name setter "-" setter "-SAME")
              (EQUAL (,setter I V2 (,setter I V1 x86))
                     (,setter I V2 x86)))

            (DEFTHM ,(mk-name setter "-" setter "-DIFFERENT-CONCRETE-INDICES")
              (IMPLIES (AND (SYNTAXP (QUOTEP I1))
                            (SYNTAXP (QUOTEP I2)))
                       (EQUAL (,setter I2 V2 (,setter I1 V1 x86))
                              (IF (< I1 I2)
                                  (,setter I1 V1 (,setter I2 V2 x86))
                                  (,setter I2 V2 (,setter I1 V1 x86)))))
              :RULE-CLASSES ((:REWRITE :LOOP-STOPPER ((I2 I1)))))

            (DEFTHM ,(mk-name setter "-" setter "-DIFFERENT-UNEQUAL-INDICES")
              (IMPLIES (NOT (EQUAL I1 I2))
                       (EQUAL (,setter I2 V2 (,setter I1 V1 x86))
                              (,setter I1 V1 (,setter I2 V2 x86))))
              :RULE-CLASSES ((:REWRITE :LOOP-STOPPER ((I2 I1)))))

            ;; Writing the Read Theorem:
            (DEFTHMD ,(mk-name setter "-" getter)
              ;; We need the hypothesis (x86P x86) because
              ;; (equal (update-nth n (nth n x) x) x) is true only
              ;; if n < (len x). So, really, (true-listp x86) and (equal (len x86)
              ;; (1+ *memi*)) would have sufficed.
              (IMPLIES (AND (EQUAL X (,getter I x86))
                            (x86P x86))
                       (EQUAL (,setter I X x86)
                              x86)))

            )))

       ((and (consp type)
             (equal (car type) 'unsigned-byte))
        (let* ((getter  (mk-name name))
               (setter  (mk-name "!" name))
               (size    (cadr type)))
          `( ;; Field Type Theorem:
            (DEFTHM-USB ,(mk-name getter "-IS-N" size "P")
              :hyp (FORCE (X86P X86))
              :bound ,size
              :concl (,getter X86)
              :HINTS (("GOAL" :IN-THEORY (E/D (,getter X86P) ())))
              :gen-type t
              :gen-linear t)

            ;; RoW Theorem:
            (DEFTHM ,(mk-name getter "-" setter)
              (EQUAL (,getter (,setter V x86))
                     V))

            ;; WoW Theorems:
            (DEFTHM ,(mk-name setter "-" setter)
              (EQUAL (,setter V2 (,setter V1 x86))
                     (,setter V2 x86)))

            (DEFTHMD ,(mk-name setter "-" getter)
              (IMPLIES (AND (EQUAL X (,getter x86))
                            (x86P x86))
                       (EQUAL (,setter X x86)
                              x86)))
            )))

       ((and (consp type)
             (equal (car type) 'signed-byte))
        (let* ((getter  (mk-name name))
               (setter  (mk-name "!" name))
               (size    (cadr type)))
          `( ;; Field Type Theorems:
            (DEFTHM-SB ,(mk-name getter "-IS-I" size "P")
              :hyp (X86P X86)
              :bound ,size
              :concl (,getter X86)
              :HINTS (("GOAL" :IN-THEORY (E/D (,getter X86P) ())))
              :gen-linear t
              :gen-type t)

            ;; RoW Theorem:
            (DEFTHM ,(mk-name getter "-" setter)
              (EQUAL (,getter (,setter V x86))
                     V))

            ;; WoW Theorems:
            (DEFTHM ,(mk-name setter "-" setter)
              (EQUAL (,setter V2 (,setter V1 x86))
                     (,setter V2 x86)))

            (DEFTHMD ,(mk-name setter "-" getter)
              (IMPLIES (AND (EQUAL X (,getter x86))
                            (x86P x86))
                       (EQUAL (,setter X x86)
                              x86)))
            )))

       ((and (consp type)
             (equal (car type) 'integer))
        (let* ((predicate (mk-name name "P"))
               (getter  (mk-name name))
               (setter  (mk-name "!" name))
               (size    (caddr type)))
          `( ;; Field Type Theorem:

            (DEFTHM-NATP ,(mk-name "NATP-" name)
              :hyp (FORCE (X86P X86))
              :concl (,getter X86)
              :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))

            (DEFTHM ,(mk-name name "-LESS-THAN-" size)
              (IMPLIES (FORCE (X86P X86))
                       (<= (,getter X86) ,size))
              :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
              :RULE-CLASSES :LINEAR)

            ;; RoW Theorem:
            (DEFTHM ,(mk-name getter "-" setter)
              (EQUAL (,getter (,setter V x86))
                     V))

            ;; WoW Theorems:
            (DEFTHM ,(mk-name setter "-" setter)
              (EQUAL (,setter V2 (,setter V1 x86))
                     (,setter V2 x86)))

            (DEFTHMD ,(mk-name setter "-" getter)
              (IMPLIES (AND (EQUAL X (,getter X86))
                            (x86P x86))
                       (EQUAL (,setter X x86)
                              x86)))
            )))

       ((and (consp type)
             (equal (car type) 'satisfies))
        ;; Env field is dealt with in this case.
        (let* ((getter name)
               (setter (mk-name "!" name))
               (predicate (cadr type)))
          `( ;; Field Type Theorem:
            (DEFTHM ,(mk-name predicate "-" name)
              (IMPLIES (X86P X86)
                       (,predicate (,name X86))))

            ;; RoW Theorem:
            (DEFTHM ,(mk-name getter "-" setter)
              (EQUAL (,getter (,setter V x86))
                     V))

            ;; WoW Theorem:
            (DEFTHM ,(mk-name setter "-" setter)
              (EQUAL (,setter V2 (,setter V1 x86))
                     (,setter V2 x86)))

            ;; Writing the Read Theorem:
            (DEFTHMD ,(mk-name setter "-" getter)
              (IMPLIES (AND (EQUAL X (,getter X86))
                            (X86P X86))
                       (EQUAL (,setter X x86)
                              x86))
              :hints (("Goal" :in-theory (e/d (UPDATE-NTH) ()))))
            )))

       (t
        ;; type is presumably 'T (like MS and FAULT fields)
        (let* ((getter name)
               (setter (mk-name "!" name)))
          `(
            ;; No Field Type Theorem

            ;; RoW Theorem:
            (DEFTHM ,(mk-name getter "-" setter)
              (EQUAL (,getter (,setter V x86))
                     V))

            ;; WoW Theorem:
            (DEFTHM ,(mk-name setter "-" setter)
              (EQUAL (,setter V2 (,setter V1 x86))
                     (,setter V2 x86)))

            ;; Writing the Read Theorem:
            (DEFTHMD ,(mk-name setter "-" getter)
              (IMPLIES (AND (EQUAL X (,getter X86))
                            (x86P x86))
                       (EQUAL (,setter X x86)
                              x86)))
            )))
       )))

  (defun x86-stobj-x86p-setter-thms-fn-1 (x86-model-field)
    ;; E.g., (x86-stobj-x86p-setter-thms-fn-1 (car *pruned-x86-model*))

    ;; This function assumes that x86-model-field is defined using the
    ;; same syntax as that for a field in a defstobj definition.

    (let* ((name (car x86-model-field))
           (type (caddr x86-model-field))
           (end  (search "$C" (symbol-name name)))
           (name (mk-name (subseq (symbol-name name) 0 end)))
           (predicate (mk-name name "P")))
      (cond ((and (consp type)
                  (equal (car type) 'array)
                  (consp (cadr type))
                  (equal (car (cadr type)) 'unsigned-byte))
             (let* ((namei     (mk-name name "I"))
                    (setter    (mk-name "!" namei))
                    (size      (cadr (cadr  type))))
               `((DEFTHM ,(mk-name "X86P-" setter)
                   (IMPLIES (FORCED-AND (x86P x86)
                                        ;; i should not be an
                                        ;; ill-formed-key.
                                        (INTEGERP I)
                                        (UNSIGNED-BYTE-P ,size V))
                            ,(if (or (equal name 'mem-table)
                                     (equal name 'mem-array))
                                 ;; Because of the good-memp predicate,
                                 ;; we must handle these two
                                 ;; seperately.  In fact, these fields
                                 ;; will only be modified by !memi.
                                 `(x86P-PRE (,setter I V x86))
                               `(x86P (,setter I V x86))))
                   :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
                 )))
            ((and (consp type)
                  (equal (car type) 'array)
                  (consp (cadr type))
                  (equal (car (cadr type)) 'signed-byte))
             (let* ((namei     (mk-name name "I"))
                    (setter    (mk-name "!" namei))
                    (size      (cadr (cadr  type))))
               `((DEFTHM ,(mk-name "X86P-" setter)
                   (IMPLIES (FORCED-AND (x86P x86)
                                        (INTEGERP I)
                                        ;; i should not be
                                        ;; an ill-formed-key.
                                        (SIGNED-BYTE-P ,size V))
                            ,(if (or (equal name 'mem-table)
                                     (equal name 'mem-array))
                                 ;; Because of the good-memp predicate,
                                 ;; we must handle these two
                                 ;; seperately.  In fact, these fields
                                 ;; will only be modified by !memi.
                                 `(x86P-PRE (,setter I V x86))
                               `(x86P (,setter I V x86))))
                   :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
                 )))            

            ((and (consp type)
                  (equal (car type) 'unsigned-byte))
             (let* ((setter  (mk-name "!" name))
                    (size    (cadr type)))
               `((DEFTHM ,(mk-name "X86P-" setter)
                   (IMPLIES (FORCED-AND (x86P x86)
                                        (UNSIGNED-BYTE-P ,size V))
                            ,(if (equal name 'mem-array-next-addr)
                                 ;; Because of the good-memp predicate,
                                 ;; we must handle this one seperately.
                                 ;; In fact, this field will only be
                                 ;; modified by !memi, and it is that
                                 ;; which we will prove maintains the
                                 ;; x86p predicate.
                                 `(x86P-PRE (,setter V x86))
                               `(x86P (,setter V x86))))
                   :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))))
               ))
            ((and (consp type)
                  (equal (car type) 'signed-byte))
             (let* ((setter  (mk-name "!" name))
                    (size    (cadr type)))
               `((DEFTHM ,(mk-name "X86P-" setter)
                   (IMPLIES (FORCED-AND (x86P x86)
                                        (SIGNED-BYTE-P ,size V))
                            ,(if (equal name 'mem-array-next-addr)
                                 ;; Because of the good-memp predicate,
                                 ;; we must handle this one seperately.
                                 ;; In fact, this field will only be
                                 ;; modified by !memi, and it is that
                                 ;; which we will prove maintains the
                                 ;; x86p predicate.
                                 `(x86P-PRE (,setter V x86))
                               `(x86P (,setter V x86))))
                   :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
                 )))
            ((and (consp type)
                  (equal (car type) 'integer))
             (let* ((setter  (mk-name "!" name))
                    (size    (caddr type)))
               `((DEFTHM ,(mk-name "X86P-" setter)
                   (IMPLIES (FORCED-AND (x86P x86)
                                        (INTEGERP V)
                                        (<= 0 V)
                                        (<= V ,size))
                            ,(if (equal name 'mem-array-next-addr)
                                 ;; Because of the good-memp predicate,
                                 ;; we must handle this one seperately.
                                 ;; In fact, this field will only be
                                 ;; modified by !memi, and it is that
                                 ;; which we will prove maintains the
                                 ;; x86p predicate.
                                 `(x86P-PRE (,setter V x86))
                               `(x86P (,setter V x86))))
                   :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
                 )))

            ((and (consp type)
                  (equal (car type) 'satisfies))
             ;; Env field is dealt with in this case.
             (let* ((setter (mk-name "!" name))
                    (predicate (cadr type)))
               `((DEFTHM ,(mk-name "X86P-" setter)
                   (IMPLIES (FORCED-AND (X86P X86)
                                        (,predicate V))
                            (x86P (,setter V x86)))
                   :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))))

               ))
            (t
             ;; type is presumably 'T
             (let* ((setter (mk-name "!" name)))
               `((DEFTHM ,(mk-name "X86P-" setter)
                   (IMPLIES (FORCE (x86P x86))
                            (x86P (,setter V x86)))
                   :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))))

               )))))

  (defun x86-stobj-x86p-setter-thms-fn (x86-model)
    ;; Generates x86p-* theorems for all fields in "x86-model".
    (cond ((endp x86-model)
           '())
          (t
           `(,@(x86-stobj-x86p-setter-thms-fn-1 (car x86-model))
             ,@(x86-stobj-x86p-setter-thms-fn (cdr x86-model))))))

  (defun x86-stobj-field-thms-fn (x86-model)
    (cond ((endp x86-model)
           '())
          (t
           `(,@(x86-stobj-field-thms-fn-1 (car x86-model))
             ,@(x86-stobj-field-thms-fn (cdr x86-model))))))

  (defmacro x86-stobj-field-thms (x86-model)
    `(ENCAPSULATE
      ()

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
                       (< N (LEN x86))
                       (INTEGERP I)
                       (<= 0 I)
                       (< I (LEN (NTH N x86))))
                  (EQUAL (UPDATE-NTH N
                                     (UPDATE-NTH I (NTH I (NTH N x86))
                                                 (NTH N x86))
                                     x86)
                         x86))))

      (LOCAL
       (DEFTHM UPDATE-NTH-THM-4
         (IMPLIES (AND (INTEGERP I)
                       (<= 0 I)
                       (< I (LEN x86)))
                  (EQUAL (UPDATE-NTH I (NTH I x86) x86)
                         x86))))

      (LOCAL
       (DEFTHM UPDATE-NTH-THM-5
         (IMPLIES (AND (EQUAL (NTH N X) E)
                       (NATP N)
                       (< N (LEN X)))
                  (EQUAL (UPDATE-NTH N E X) X))))

      (LOCAL
       (IN-THEORY (E/D ()
                       (NTH UPDATE-NTH))))

      ,@(x86-stobj-field-thms-fn x86-model)
      ,@(x86-stobj-x86p-setter-thms-fn x86-model)))

  (make-event
   ;; To get the events generated by this make-event: put
   ;; `(x86-stobj-field-thms ,*pruned-x86-model-modified-mem*)
   ;; through ACL2, and trans1 the output.
   `(x86-stobj-field-thms ,*pruned-x86-model-modified-mem*))

  )


;; ======================================================================

;; Globally disabling abstract stobj functions so that these rules can
;; fire when needed:

(globally-disable '(abstract-stobj-fns-ruleset memi !memi x86p))

;; ======================================================================

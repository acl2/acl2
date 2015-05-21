;; ORIGINAL AUTHOR:
;; Soumava Ghosh       <soumava@cs.utexas.edu>

(in-package "X86ISA")

(include-book "elf-constants"
              :ttags (:syscall-exec :include-raw :other-non-det :undef-flg))

(local (include-book "std/lists/nthcdr" :dir :system))

(local (include-book "std/lists/take" :dir :system))

;; ========================================================

;; A stobj to store some useful info during the parsing process

(defconst *elf-body*
  `(
    (elf-file-size                  :type (satisfies natp)   :initially 0)
    (sections-num                   :type (unsigned-byte 64) :initially 0)
    (elf-header-size                :type (unsigned-byte 64) :initially 0)

    ;; note-ABI-tag section
    (note-ABI-tag-addr              :type (unsigned-byte 64)     :initially 0)
    (note-ABI-tag-size              :type (unsigned-byte 64)     :initially 0)
    (note-ABI-tag-offset            :type (unsigned-byte 64)     :initially 0)
    (note-ABI-tag-bytes             :type (satisfies byte-listp) :initially nil)

    ;; note-gnu-build-id section
    (note-gnu-buildid-addr          :type (unsigned-byte 64)     :initially 0)
    (note-gnu-buildid-size          :type (unsigned-byte 64)     :initially 0)
    (note-gnu-buildid-offset        :type (unsigned-byte 64)     :initially 0)
    (note-gnu-buildid-bytes         :type (satisfies byte-listp) :initially nil)

    ;; rela-plt section
    (rela-plt-addr                  :type (unsigned-byte 64)     :initially 0)
    (rela-plt-size                  :type (unsigned-byte 64)     :initially 0)
    (rela-plt-offset                :type (unsigned-byte 64)     :initially 0)
    (rela-plt-bytes                 :type (satisfies byte-listp) :initially nil)

    ;; init section
    (init-addr                      :type (unsigned-byte 64)     :initially 0)
    (init-size                      :type (unsigned-byte 64)     :initially 0)
    (init-offset                    :type (unsigned-byte 64)     :initially 0)
    (init-bytes                     :type (satisfies byte-listp) :initially nil)

    ;; plt section
    (plt-addr                       :type (unsigned-byte 64)     :initially 0)
    (plt-size                       :type (unsigned-byte 64)     :initially 0)
    (plt-offset                     :type (unsigned-byte 64)     :initially 0)
    (plt-bytes                      :type (satisfies byte-listp) :initially nil)

    ;; text section
    (text-addr                      :type (unsigned-byte 64)     :initially 0)
    (text-size                      :type (unsigned-byte 64)     :initially 0)
    (text-offset                    :type (unsigned-byte 64)     :initially 0)
    (text-bytes                     :type (satisfies byte-listp) :initially nil)

    ;; fini section
    (fini-addr                      :type (unsigned-byte 64)     :initially 0)
    (fini-size                      :type (unsigned-byte 64)     :initially 0)
    (fini-offset                    :type (unsigned-byte 64)     :initially 0)
    (fini-bytes                     :type (satisfies byte-listp) :initially nil)

    ;; rodata section
    (rodata-addr                    :type (unsigned-byte 64)     :initially 0)
    (rodata-size                    :type (unsigned-byte 64)     :initially 0)
    (rodata-offset                  :type (unsigned-byte 64)     :initially 0)
    (rodata-bytes                   :type (satisfies byte-listp) :initially nil)

    ;; eh-frame section
    (eh-frame-addr                  :type (unsigned-byte 64)     :initially 0)
    (eh-frame-size                  :type (unsigned-byte 64)     :initially 0)
    (eh-frame-offset                :type (unsigned-byte 64)     :initially 0)
    (eh-frame-bytes                 :type (satisfies byte-listp) :initially nil)

    ;; gcc-except-table section
    (gcc-except-table-addr          :type (unsigned-byte 64)     :initially 0)
    (gcc-except-table-size          :type (unsigned-byte 64)     :initially 0)
    (gcc-except-table-offset        :type (unsigned-byte 64)     :initially 0)
    (gcc-except-table-bytes         :type (satisfies byte-listp) :initially nil)

    ;; init-array section
    (init-array-addr                :type (unsigned-byte 64)     :initially 0)
    (init-array-size                :type (unsigned-byte 64)     :initially 0)
    (init-array-offset              :type (unsigned-byte 64)     :initially 0)
    (init-array-bytes               :type (satisfies byte-listp) :initially nil)

    ;; fini-array section
    (fini-array-addr                :type (unsigned-byte 64)     :initially 0)
    (fini-array-size                :type (unsigned-byte 64)     :initially 0)
    (fini-array-offset              :type (unsigned-byte 64)     :initially 0)
    (fini-array-bytes               :type (satisfies byte-listp) :initially nil)

    ;; ctors section
    (ctors-addr                     :type (unsigned-byte 64)     :initially 0)
    (ctors-size                     :type (unsigned-byte 64)     :initially 0)
    (ctors-offset                   :type (unsigned-byte 64)     :initially 0)
    (ctors-bytes                    :type (satisfies byte-listp) :initially nil)

    ;; dtors section
    (dtors-addr                     :type (unsigned-byte 64)     :initially 0)
    (dtors-size                     :type (unsigned-byte 64)     :initially 0)
    (dtors-offset                   :type (unsigned-byte 64)     :initially 0)
    (dtors-bytes                    :type (satisfies byte-listp) :initially nil)

    ;; jcr section
    (jcr-addr                       :type (unsigned-byte 64)     :initially 0)
    (jcr-size                       :type (unsigned-byte 64)     :initially 0)
    (jcr-offset                     :type (unsigned-byte 64)     :initially 0)
    (jcr-bytes                      :type (satisfies byte-listp) :initially nil)

    ;; data-rel-ro section
    (data-rel-ro-addr               :type (unsigned-byte 64)     :initially 0)
    (data-rel-ro-size               :type (unsigned-byte 64)     :initially 0)
    (data-rel-ro-offset             :type (unsigned-byte 64)     :initially 0)
    (data-rel-ro-bytes              :type (satisfies byte-listp) :initially nil)

    ;; got section
    (got-addr                       :type (unsigned-byte 64)     :initially 0)
    (got-size                       :type (unsigned-byte 64)     :initially 0)
    (got-offset                     :type (unsigned-byte 64)     :initially 0)
    (got-bytes                      :type (satisfies byte-listp) :initially nil)

    ;; got-plt section
    (got-plt-addr                   :type (unsigned-byte 64)     :initially 0)
    (got-plt-size                   :type (unsigned-byte 64)     :initially 0)
    (got-plt-offset                 :type (unsigned-byte 64)     :initially 0)
    (got-plt-bytes                  :type (satisfies byte-listp) :initially nil)

    ;; data section
    (data-addr                      :type (unsigned-byte 64)     :initially 0)
    (data-size                      :type (unsigned-byte 64)     :initially 0)
    (data-offset                    :type (unsigned-byte 64)     :initially 0)
    (data-bytes                     :type (satisfies byte-listp) :initially nil)

    ;; tdata section
    (tdata-addr                     :type (unsigned-byte 64)     :initially 0)
    (tdata-size                     :type (unsigned-byte 64)     :initially 0)
    (tdata-offset                   :type (unsigned-byte 64)     :initially 0)
    (tdata-bytes                    :type (satisfies byte-listp) :initially nil)

    ;; bss section
    (bss-addr                       :type (unsigned-byte 64)     :initially 0)
    (bss-size                       :type (unsigned-byte 64)     :initially 0)
    (bss-offset                     :type (unsigned-byte 64)     :initially 0)
    (bss-bytes                      :type (satisfies byte-listp) :initially nil)

    ;; tbss section
    (tbss-addr                      :type (unsigned-byte 64)     :initially 0)
    (tbss-size                      :type (unsigned-byte 64)     :initially 0)
    (tbss-offset                    :type (unsigned-byte 64)     :initially 0)
    (tbss-bytes                     :type (satisfies byte-listp) :initially nil)

    ))

(defun create-elf-stobj-1 (elf)
  `(DEFSTOBJ ELF
     ,@elf
     :INLINE t
     :RENAMING (,@(create-stobj-renaming-fn elf))))

(defmacro create-elf-stobj ()
  (create-elf-stobj-1 *elf-body*))

(create-elf-stobj)

;; Some "type" theorems about the fields of elf

(encapsulate ()

(local
 (defthm update-nth-thm-1
   (equal (update-nth i v2 (update-nth i v1 x))
          (update-nth i v2 x))))

(local
 (defthm update-nth-thm-2
   (implies (and (integerp i1)
                 (<= 0 i1)
                 (integerp i2)
                 (<= 0 i2)
                 (not (equal i1 i2)))
            (equal (update-nth i2 v2 (update-nth i1 v1 x))
                   (update-nth i1 v1 (update-nth i2 v2 x))))))

(local
 (defthm update-nth-thm-3
   (implies (and (integerp n)
                 (<= 0 n)
                 (< n (len x86))
                 (integerp i)
                 (<= 0 i)
                 (< i (len (nth n x86))))
            (equal (update-nth n
                               (update-nth i (nth i (nth n x86))
                                           (nth n x86))
                               x86)
                   x86))))

(local
 (defthm update-nth-thm-4
   (implies (and (integerp i)
                 (<= 0 i)
                 (< i (len x86)))
            (equal (update-nth i (nth i x86) x86)
                   x86))))

(local
 (defthm update-nth-thm-5
   (implies (and (equal (nth n x) e)
                 (natp n)
                 (< n (len x)))
            (equal (update-nth n e x) x))))

(local
 (in-theory (e/d (length) (nth update-nth))))

(defun elf-stobj-field-thms-fn-1 (elffield)
  ;; E.g., (elf-stobj-field-thms-fn-1 (car *elf-body*))

  (let* ((name (car elffield))
         (type (caddr elffield)))
    (cond

     ((and (consp type)
           (equal (car type) 'array)
           (consp (cadr type)))
      (let* ((predicate (mk-name name "P"))
             (namei     (mk-name name "I"))
             (getter    namei)
             (setter    (mk-name "!" namei))
             (size      (cadr (cadr  type)))
             (expt-size (expt 2 size))
             (neg-expt-size-1 (- (expt 2 (1- size))))
             (expt-size-1 (expt 2 (1- size)))
             (length    (if (equal (car (cddr (cddr (cddr elffield))))
                                   'T)
                            ;; resizable array
                            `(,(mk-name name "-LENGTH") elf)
                          (car  (caddr type))))
             )
        `( ;; reader
          ,(if (equal (car (cadr type)) 'unsigned-byte)
               `((DEFTHM ,(mk-name getter (if (< size 10) "-IS-N0" "-IS-N") size "P")
                   (IMPLIES (AND (ELFP ELF)
                                 (NATP I)
                                 (< I ,length)
                                 )
                            (,(mk-name "N" (if (< size 10) "0" "") size "P")
                             (,getter I ELF)))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,predicate ELFP) ())))
                   :RULE-CLASSES
                   ((:TYPE-PRESCRIPTION
                     :COROLLARY
                     (IMPLIES (FORCED-AND (ELFP ELF)
                                          (NATP I)
                                          (< I ,length)
                                          )
                              (AND (INTEGERP (,getter I ELF))
                                   (<= 0 (,getter I ELF))))
                     :HINTS (("GOAL" :IN-THEORY (E/D () (ELFP)))))
                    (:LINEAR
                     :COROLLARY
                     (IMPLIES (FORCED-AND (ELFP ELF)
                                          (NATP I)
                                          (< I ,length)
                                          )
                              (< (,getter I ELF) ,expt-size))
                     :HINTS (("GOAL" :IN-THEORY (E/D () (ELFP)))))))
                 (DEFTHM ,(mk-name "ELFP-" setter)
                   (IMPLIES (FORCED-AND (elfP elf)
                                        (INTEGERP I)
                                        (<= 0 I)
                                        (< I ,length)
                                        (INTEGERP V)
                                        (<= 0 V)
                                        (< V ,(expt 2 size)))
                            (elfP (,setter I V elf)))
                   :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))))
             `((DEFTHM ,(mk-name getter "-IS-I" size "P")
                 (IMPLIES (AND (ELFP ELF)
                               (NATP I)
                               (< I ,length)
                               )
                          (,(mk-name "I" size "P") (,getter I ELF)))
                 :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,predicate ELFP) ())))
                 :RULE-CLASSES
                 ((:TYPE-PRESCRIPTION
                   :COROLLARY
                   (IMPLIES (FORCED-AND (ELFP ELF)
                                        (NATP I)
                                        (< I ,length)
                                        )
                            (AND (INTEGERP (,getter I ELF))
                                 (<= ,neg-expt-size-1 (,getter I ELF))))
                   :HINTS (("GOAL" :IN-THEORY (E/D () (ELFP)))))
                  (:LINEAR
                   :COROLLARY
                   (IMPLIES (FORCED-AND (ELFP ELF)
                                        (NATP I)
                                        (< I ,length)
                                        )
                            (< (,getter I ELF) ,expt-size-1))
                   :HINTS (("GOAL" :IN-THEORY (E/D () (ELFP)))))))
               (DEFTHM ,(mk-name "ELFP-" setter)
                 (IMPLIES (FORCED-AND (elfP elf)
                                      (INTEGERP I)
                                      (<= 0 I)
                                      (< I ,length)
                                      (INTEGERP V)
                                      (<= ,(- (expt 2 size)) V)
                                      (< V ,(expt 2 size)))
                          (elfP (,setter I V elf)))
                 :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))))

             ))))

     ((and (consp type)
           (equal (car type) 'unsigned-byte))
      (let* ((predicate (mk-name name "P"))
             (getter  (mk-name name))
             (setter  (mk-name "!" name))
             (size    (cadr type))
             (expt-size (expt 2 size)))
        `( ;; readers
          (DEFTHM ,(mk-name getter "-IS-N" size "P")
            (IMPLIES (ELFP ELF)
                     (,(mk-name "N" size "P") (,getter ELF)))
            :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,predicate ELFP) ())))
            :RULE-CLASSES
            ((:TYPE-PRESCRIPTION
              :COROLLARY
              (IMPLIES (FORCED-AND (ELFP ELF))
                       (AND (INTEGERP (,getter ELF))
                            (<= 0 (,getter ELF))))
              :HINTS (("GOAL" :IN-THEORY (E/D () (ELFP)))))
             (:LINEAR
              :COROLLARY
              (IMPLIES (FORCED-AND (ELFP ELF))
                       (< (,getter ELF) ,expt-size))
              :HINTS (("GOAL" :IN-THEORY (E/D () (ELFP)))))))
          ;; writer
          (DEFTHM ,(mk-name "ELFP-" setter)
            (IMPLIES (FORCED-AND (elfP elf)
                                 (INTEGERP V)
                                 (<= 0 V)
                                 (< V ,(expt 2 size)))
                     (elfP (,setter V elf)))
            :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
          )))

     ((and (consp type)
           (equal (car type) 'signed-byte))
      (let* ((predicate (mk-name name "P"))
             (getter  (mk-name name))
             (setter (mk-name "!" name))
             (size    (cadr type))
             (neg-expt-size-1 (- (expt 2 (1- size))))
             (expt-size-1 (expt 2 (1- size))))
        `( ;; readers
          (DEFTHM ,(mk-name getter "-IS-I" size "P")
            (IMPLIES (ELFP ELF)
                     (,(mk-name "I" size "P") (,getter ELF)))
            :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,predicate ELFP) ())))
            :RULE-CLASSES
            ((:TYPE-PRESCRIPTION
              :COROLLARY
              (IMPLIES (FORCED-AND (ELFP ELF))
                       (AND (INTEGERP (,getter ELF))
                            (<= ,neg-expt-size-1 (,getter ELF))))
              :HINTS (("GOAL" :IN-THEORY (E/D () (ELFP)))))
             (:LINEAR
              :COROLLARY
              (IMPLIES (FORCED-AND (ELFP ELF))
                       (< (,getter ELF) ,expt-size-1))
              :HINTS (("GOAL" :IN-THEORY (E/D () (ELFP)))))))

          ;; writers
          (DEFTHM ,(mk-name "ELFP-" setter)
            (IMPLIES (FORCED-AND (elfP elf)
                                 ;; can we replace these with
                                 ;; iXYp?  do we want to?
                                 (INTEGERP V)
                                 (<= ,(- (expt 2 size)) V)
                                 (< V ,(expt 2 size)))
                     (elfP (,setter V elf)))
            :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))

          )))

     ((and (consp type)
           (equal (car type) 'integer))
      (let* ((predicate (mk-name name "P"))
             (getter  (mk-name name))
             (setter  (mk-name "!" name))
             (size    (caddr type)))
        `( ;; readers

          (DEFTHM ,(mk-name "NATP-" name)
            (IMPLIES (FORCE (ELFP ELF))
                     (AND (INTEGERP (,getter ELF))
                          (<= 0 (,getter ELF))))
            :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
            :RULE-CLASSES :TYPE-PRESCRIPTION)

          (DEFTHM ,(mk-name name "-LESS-THAN-" size)
            (IMPLIES (FORCE (ELFP ELF))
                     (<= (,getter ELF) ,size))
            :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
            :RULE-CLASSES :LINEAR)

          ;; writers
          (DEFTHM ,(mk-name "ELFP-" setter)
            (IMPLIES (FORCED-AND (elfP elf)
                                 (INTEGERP V)
                                 (<= 0 V)
                                 (<= V ,size))
                     (elfP (,setter V elf)))
            :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
          )))

     ((and (consp type)
           (equal (car type) 'satisfies))

      (let* ((predicate (cadr type))
             (setter (mk-name "!" name)))
        `( ;; readers
          (DEFTHM ,(mk-name predicate "-" name)
            (IMPLIES (ELFP ELF)
                     (,predicate (,name ELF)))
            :HINTS (("GOAL" :IN-THEORY (E/D (,name ,predicate ELFP) ()))))

          ;; writers
          (DEFTHM ,(mk-name "ELFP-" setter)
            (IMPLIES (FORCED-AND (ELFP ELF)
                                 (,predicate V))
                     (elfP (,setter V elf)))
            :HINTS (("GOAL" :IN-THEORY (ENABLE ,setter ,predicate elfp))))
          )))
     (t ;; Type is presumably t
      `((DEFTHM ,(mk-name "ELFP-!" name)
          (IMPLIES (FORCE (ELFP ELF)
                          (elfP (,(mk-name "!" name) V elf)))
                   :HINTS (("GOAL" :IN-THEORY (ENABLE elfp)))))))
     )))

(defun elf-stobj-field-thms-fn (elf)
  (cond ((endp elf)
         '())
        (t
         `(,@(elf-stobj-field-thms-fn-1 (car elf))
           ,@(elf-stobj-field-thms-fn (cdr elf))))))

(defmacro elf-field-theorems ()
  `(PROGN
    ,@(elf-stobj-field-thms-fn *elf-body*)))

(elf-field-theorems)

) ;; End of encapsulate

(defun disable-elf-stobj-fns-fn-1 (elf-model)
  (cond ((endp elf-model)
         '())
        (t
         (let* ((name (car (car elf-model)))
                (type (caddr (car elf-model))))
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
                            (disable-elf-stobj-fns-fn-1 (cdr elf-model)))))
                 (t
                  (let* ((getter  name)
                         (setter  (mk-name "!" name))
                         (recognizer (mk-name name "P")))
                    (append `(,getter ,setter ,recognizer)
                            (disable-elf-stobj-fns-fn-1
                             (cdr elf-model))))))))))

(defmacro disable-elf-stobj-fns-fn (elf-model)
  `(IN-THEORY
    (DISABLE ,@(disable-elf-stobj-fns-fn-1 elf-model))))

(make-event
 `(disable-elf-stobj-fns-fn ,*elf-body*))

(in-theory (disable elfp))

;; ===================================================================

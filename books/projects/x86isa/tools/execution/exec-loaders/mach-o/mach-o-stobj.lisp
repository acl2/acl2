; X86ISA Library

; Note: The license below is based on the template at:
; http://opensource.org/licenses/BSD-3-Clause

; Copyright (C) 2015, Regents of the University of Texas
; All rights reserved.

; Redistribution and use in source and binary forms, with or without
; modification, are permitted provided that the following conditions are
; met:

; o Redistributions of source code must retain the above copyright
;   notice, this list of conditions and the following disclaimer.

; o Redistributions in binary form must reproduce the above copyright
;   notice, this list of conditions and the following disclaimer in the
;   documentation and/or other materials provided with the distribution.

; o Neither the name of the copyright holders nor the names of its
;   contributors may be used to endorse or promote products derived
;   from this software without specific prior written permission.

; THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
; "AS IS" AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
; LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR
; A PARTICULAR PURPOSE ARE DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT
; HOLDER OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT, INCIDENTAL,
; SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT NOT
; LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
; DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
; THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
; (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
; OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.

; Original Author(s):
; Shilpi Goel         <shigoel@cs.utexas.edu>

(in-package "X86ISA")

(include-book "mach-o-constants"
              :ttags (:include-raw :syscall-exec :other-non-det :undef-flg))

;; ======================================================================

;; A stobj to store some useful info during the parsing process.

(defconst *mach-o-body*
  `(
    (mach-o-file-size             :type (satisfies natp)
                                  :initially   0)
    (load-cmds-size               :type (unsigned-byte 64)
                                  :initially   0)
    (mach-o-header-size           :type (unsigned-byte 64)
                                  :initially   0)
    ;; TEXT Segment

    ;; text section:
    (TEXT-text-section-addr       :type (unsigned-byte 64)
                                  :initially   0)
    (TEXT-text-section-size       :type (unsigned-byte 64)
                                  :initially   0)
    (TEXT-text-section-offset     :type (unsigned-byte 64)
                                  :initially   0)
    (TEXT-text-section-bytes      :type (satisfies byte-listp)
                                  :initially nil)

    ;; cstring section:
    (TEXT-cstring-section-addr    :type (unsigned-byte 64)
                                  :initially   0)
    (TEXT-cstring-section-size    :type (unsigned-byte 64)
                                  :initially   0)
    (TEXT-cstring-section-offset  :type (unsigned-byte 64)
                                  :initially   0)
    (TEXT-cstring-section-bytes   :type (satisfies byte-listp)
                                  :initially nil)

    ;; const section:
    (TEXT-const-section-addr      :type (unsigned-byte 64)
                                  :initially   0)
    (TEXT-const-section-size      :type (unsigned-byte 64)
                                  :initially   0)
    (TEXT-const-section-offset    :type (unsigned-byte 64)
                                  :initially   0)
    (TEXT-const-section-bytes     :type (satisfies byte-listp)
                                  :initially nil)
    ;; DATA Segment

    ;; data section:
    (DATA-data-section-addr      :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-data-section-size      :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-data-section-offset    :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-data-section-bytes     :type (satisfies byte-listp)
                                 :initially nil)

    ;; dyld section:
    (DATA-dyld-section-addr      :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-dyld-section-size      :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-dyld-section-offset    :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-dyld-section-bytes     :type (satisfies byte-listp)
                                 :initially nil)

    ;; const section:
    (DATA-const-section-addr     :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-const-section-size     :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-const-section-offset   :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-const-section-bytes    :type (satisfies byte-listp)
                                 :initially nil)

    ;; bss section:
    (DATA-bss-section-addr       :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-bss-section-size       :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-bss-section-offset     :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-bss-section-bytes      :type (satisfies byte-listp)
                                 :initially nil)

    ;; common section:
    (DATA-common-section-addr    :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-common-section-size    :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-common-section-offset  :type (unsigned-byte 64)
                                 :initially   0)
    (DATA-common-section-bytes   :type (satisfies byte-listp)
                                 :initially nil)
    ))

(defun create-mach-o-stobj-1 (mach-o)
  `(DEFSTOBJ MACH-O
     ,@mach-o
     :INLINE t
     :RENAMING (,@(create-stobj-renaming-fn MACH-O))))

(defmacro create-mach-o-stobj ()
  (create-mach-o-stobj-1 *mach-o-body*))

(create-mach-o-stobj)

;; Some "type" theorems about the fields of mach-o:

(encapsulate
 ()

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
                  (< n (len x))
                  (integerp i)
                  (<= 0 i)
                  (< i (len (nth n x))))
             (equal (update-nth n
                                (update-nth i (nth i (nth n x))
                                            (nth n x))
                                x)
                    x))))

 (local
  (defthm update-nth-thm-4
    (implies (and (integerp i)
                  (<= 0 i)
                  (< i (len x)))
             (equal (update-nth i (nth i x) x)
                    x))))

 (local
  (defthm update-nth-thm-5
    (implies (and (equal (nth n x) e)
                  (natp n)
                  (< n (len x)))
             (equal (update-nth n e x) x))))

 (local
  (in-theory (e/d (length) (nth update-nth))))

 (defun mach-o-stobj-field-thms-fn-1 (mach-ofield)
   ;; E.g., (mach-o-stobj-field-thms-fn-1 (car *mach-o-body*))

   (let* ((name (car mach-ofield))
          (type (caddr mach-ofield)))
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
              (length    (if (equal (car (cddr (cddr (cddr mach-ofield))))
                                    'T)
                             ;; resizable array
                             `(,(mk-name name "-LENGTH") mach-o)
                           (car  (caddr type))))
              )
         `( ;; reader
           ,(if (equal (car (cadr type)) 'unsigned-byte)
                `((DEFTHM ,(mk-name getter (if (< size 10) "-IS-N0" "-IS-N") size "P")
                    (IMPLIES (AND (MACH-OP MACH-O)
                                  (NATP I)
                                  (< I ,length)
                                  )
                             (,(mk-name "N" (if (< size 10) "0" "") size "P")
                              (,getter I MACH-O)))
                    :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,predicate MACH-OP) ())))
                    :RULE-CLASSES
                    ((:TYPE-PRESCRIPTION
                      :COROLLARY
                      (IMPLIES (FORCED-AND (MACH-OP MACH-O)
                                           (NATP I)
                                           (< I ,length)
                                           )
                               (AND (INTEGERP (,getter I MACH-O))
                                    (<= 0 (,getter I MACH-O))))
                      :HINTS (("GOAL" :IN-THEORY (E/D () (MACH-OP)))))
                     (:LINEAR
                      :COROLLARY
                      (IMPLIES (FORCED-AND (MACH-OP MACH-O)
                                           (NATP I)
                                           (< I ,length)
                                           )
                               (< (,getter I MACH-O) ,expt-size))
                      :HINTS (("GOAL" :IN-THEORY (E/D () (MACH-OP)))))))
                  (DEFTHM ,(mk-name "MACH-OP-" setter)
                    (IMPLIES (FORCED-AND (mach-oP mach-o)
                                         (INTEGERP I)
                                         (<= 0 I)
                                         (< I ,length)
                                         (INTEGERP V)
                                         (<= 0 V)
                                         (< V ,(expt 2 size)))
                             (mach-oP (,setter I V mach-o)))
                    :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))))
              `((DEFTHM ,(mk-name getter "-IS-I" size "P")
                  (IMPLIES (AND (MACH-OP MACH-O)
                                (NATP I)
                                (< I ,length)
                                )
                           (,(mk-name "I" size "P") (,getter I MACH-O)))
                  :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,predicate MACH-OP) ())))
                  :RULE-CLASSES
                  ((:TYPE-PRESCRIPTION
                    :COROLLARY
                    (IMPLIES (FORCED-AND (MACH-OP MACH-O)
                                         (NATP I)
                                         (< I ,length)
                                         )
                             (AND (INTEGERP (,getter I MACH-O))
                                  (<= ,neg-expt-size-1 (,getter I MACH-O))))
                    :HINTS (("GOAL" :IN-THEORY (E/D () (MACH-OP)))))
                   (:LINEAR
                    :COROLLARY
                    (IMPLIES (FORCED-AND (MACH-OP MACH-O)
                                         (NATP I)
                                         (< I ,length)
                                         )
                             (< (,getter I MACH-O) ,expt-size-1))
                    :HINTS (("GOAL" :IN-THEORY (E/D () (MACH-OP)))))))
                (DEFTHM ,(mk-name "MACH-OP-" setter)
                  (IMPLIES (FORCED-AND (mach-oP mach-o)
                                       (INTEGERP I)
                                       (<= 0 I)
                                       (< I ,length)
                                       (INTEGERP V)
                                       (<= ,(- (expt 2 size)) V)
                                       (< V ,(expt 2 size)))
                           (mach-oP (,setter I V mach-o)))
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
             (IMPLIES (MACH-OP MACH-O)
                      (,(mk-name "N" size "P") (,getter MACH-O)))
             :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,predicate MACH-OP) ())))
             :RULE-CLASSES
             ((:TYPE-PRESCRIPTION
               :COROLLARY
               (IMPLIES (FORCED-AND (MACH-OP MACH-O))
                        (AND (INTEGERP (,getter MACH-O))
                             (<= 0 (,getter MACH-O))))
               :HINTS (("GOAL" :IN-THEORY (E/D () (MACH-OP)))))
              (:LINEAR
               :COROLLARY
               (IMPLIES (FORCED-AND (MACH-OP MACH-O))
                        (< (,getter MACH-O) ,expt-size))
               :HINTS (("GOAL" :IN-THEORY (E/D () (MACH-OP)))))))
           ;; writer
           (DEFTHM ,(mk-name "MACH-OP-" setter)
             (IMPLIES (FORCED-AND (mach-oP mach-o)
                                  (INTEGERP V)
                                  (<= 0 V)
                                  (< V ,(expt 2 size)))
                      (mach-oP (,setter V mach-o)))
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
             (IMPLIES (MACH-OP MACH-O)
                      (,(mk-name "I" size "P") (,getter MACH-O)))
             :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,predicate MACH-OP) ())))
             :RULE-CLASSES
             ((:TYPE-PRESCRIPTION
               :COROLLARY
               (IMPLIES (FORCED-AND (MACH-OP MACH-O))
                        (AND (INTEGERP (,getter MACH-O))
                             (<= ,neg-expt-size-1 (,getter MACH-O))))
               :HINTS (("GOAL" :IN-THEORY (E/D () (MACH-OP)))))
              (:LINEAR
               :COROLLARY
               (IMPLIES (FORCED-AND (MACH-OP MACH-O))
                        (< (,getter MACH-O) ,expt-size-1))
               :HINTS (("GOAL" :IN-THEORY (E/D () (MACH-OP)))))))

           ;; writers
           (DEFTHM ,(mk-name "MACH-OP-" setter)
             (IMPLIES (FORCED-AND (mach-oP mach-o)
                                  ;; can we replace these with
                                  ;; iXYp?  do we want to?
                                  (INTEGERP V)
                                  (<= ,(- (expt 2 size)) V)
                                  (< V ,(expt 2 size)))
                      (mach-oP (,setter V mach-o)))
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
             (IMPLIES (FORCE (MACH-OP MACH-O))
                      (AND (INTEGERP (,getter MACH-O))
                           (<= 0 (,getter MACH-O))))
             :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
             :RULE-CLASSES :TYPE-PRESCRIPTION)

           (DEFTHM ,(mk-name name "-LESS-THAN-" size)
             (IMPLIES (FORCE (MACH-OP MACH-O))
                      (<= (,getter MACH-O) ,size))
             :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate)))
             :RULE-CLASSES :LINEAR)

           ;; writers
           (DEFTHM ,(mk-name "MACH-OP-" setter)
             (IMPLIES (FORCED-AND (mach-oP mach-o)
                                  (INTEGERP V)
                                  (<= 0 V)
                                  (<= V ,size))
                      (mach-oP (,setter V mach-o)))
             :HINTS (("GOAL" :IN-THEORY (ENABLE ,predicate))))
           )))

      ((and (consp type)
            (equal (car type) 'satisfies))

       (let* ((predicate (cadr type))
              (setter (mk-name "!" name)))
         `( ;; readers
           (DEFTHM ,(mk-name predicate "-" name)
             (IMPLIES (MACH-OP MACH-O)
                      (,predicate (,name MACH-O)))
             :HINTS (("GOAL" :IN-THEORY (E/D (,name ,predicate MACH-OP) ()))))

           ;; writers
           (DEFTHM ,(mk-name "MACH-OP-" setter)
             (IMPLIES (FORCED-AND (MACH-OP MACH-O)
                                  (,predicate V))
                      (mach-oP (,setter V mach-o)))
             :HINTS (("GOAL" :IN-THEORY (ENABLE ,setter ,predicate mach-op))))
           )))
      (t ;; Type is presumably t
       `((DEFTHM ,(mk-name "MACH-OP-!" name)
           (IMPLIES (FORCE (MACH-OP MACH-O)
                           (mach-oP (,(mk-name "!" name) V mach-o)))
                    :HINTS (("GOAL" :IN-THEORY (ENABLE mach-op)))))))
      )))

 (defun mach-o-stobj-field-thms-fn (mach-o)
   (cond ((endp mach-o)
          '())
         (t
          `(,@(mach-o-stobj-field-thms-fn-1 (car mach-o))
            ,@(mach-o-stobj-field-thms-fn (cdr mach-o))))))

 (defmacro mach-o-field-theorems ()
   `(PROGN
     ,@(mach-o-stobj-field-thms-fn *mach-o-body*)))

 (mach-o-field-theorems)

 ) ;; End of encapsulate

(defun disable-mach-o-stobj-fns-fn-1 (mach-o-model)
  (cond ((endp mach-o-model)
         '())
        (t
         (let* ((name (car (car mach-o-model)))
                (type (caddr (car mach-o-model))))
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
                            (disable-mach-o-stobj-fns-fn-1 (cdr mach-o-model)))))
                 (t
                  (let* ((getter  name)
                         (setter  (mk-name "!" name))
                         (recognizer (mk-name name "P")))
                    (append `(,getter ,setter ,recognizer)
                            (disable-mach-o-stobj-fns-fn-1
                             (cdr mach-o-model))))))))))

(defmacro disable-mach-o-stobj-fns-fn (mach-o-model)
  `(IN-THEORY
    (DISABLE ,@(disable-mach-o-stobj-fns-fn-1 mach-o-model))))

(make-event
 `(disable-mach-o-stobj-fns-fn ,*mach-o-body*))

(in-theory (disable mach-op))

;; ==================================================================-

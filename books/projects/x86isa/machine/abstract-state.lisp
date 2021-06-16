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
; Matt Kaufmann       <kaufmann@cs.utexas.edu>

(in-package "X86ISA")

(include-book "concrete-memory")
(include-book "records-0" :dir :utils)

;; ======================================================================

(defsection abstract-state
  :parents (machine)
  :short "Definition of an abstract stobj @('x86') corresponding to
@('x86$c')."

  :long "<p>From now on in our books, we will work with @('x86')
  instead of @('x86$c').</p>"

  )

(local (xdoc::set-default-parents abstract-state))

;; ======================================================================

;; Constants and function renaming stuff:

(defun prune-x86-model-1 (field x86-model)
  (cond ((endp x86-model) nil)
        ((equal field (caar x86-model))
         (cdr x86-model))
        (t (cons (car x86-model)
                 (prune-x86-model-1 field (cdr x86-model))))))

(defun prune-x86-model (fields x86-model)
  (cond ((endp fields) x86-model)
        (t (prune-x86-model (cdr fields)
                            (prune-x86-model-1 (car fields) x86-model)))))

(defconst *pruned-x86-model*
  (prune-x86-model
   '(MEM-TABLE MEM-ARRAY MEM-ARRAY-NEXT-ADDR)
   *x86$c-model*))

(defconst *pruned-x86-model-modified-mem*
  (append *pruned-x86-model*
          '((MEM$C :TYPE (ARRAY (UNSIGNED-BYTE 8)
                                (#.*MEM-SIZE-IN-BYTES*))
                   :INITIALLY 0
                   :RESIZABLE NIL))))

(defun get-x86-field-names (x86-model)
  (if (endp x86-model)
      (mv nil nil)
    (b* ((field (car x86-model))
         (concrete-name (car field))
         (type-decl (caddr field))
         (type (and (consp type-decl)
                    (equal (car type-decl) 'array)))
         (stripped-string
          (subseq (symbol-name concrete-name) 0
                  (search "$C" (symbol-name
                                concrete-name))))
         (stripped-name (mk-name stripped-string))
         (abstract-name (if type
                            (mk-name stripped-name "I")
                          stripped-name))
         (abstract-constant (mk-name "*" abstract-name "*"))
         (field-keyword (intern stripped-string "KEYWORD"))
         ((mv abstract-constants field-keywords)
          (get-x86-field-names (cdr x86-model))))
        (mv (cons abstract-constant abstract-constants)
            (cons field-keyword field-keywords)))))

(defun define-abstract-stobj-indices ()
  (b* (((mv abstract-const-names &)
        (get-x86-field-names *pruned-x86-model-modified-mem*))
       (len-const-names (len abstract-const-names)))
    `(progn
       (defconsts
         ,abstract-const-names
         ,(b* ((lst (increasing-list 0 1 len-const-names)))
            (cons 'mv lst)))
       (defconst *x86-abs-stobj-len*
         ,len-const-names))))

(make-event
 ;; Defines *rgfi*, *rip*, *memi*, etc.
 (define-abstract-stobj-indices))

(defconst *x86-field-names-as-keywords*
  ;; List of (:rgf :rip ...), etc.
  (b* (((mv & field-keywords)
        (get-x86-field-names *pruned-x86-model-modified-mem*)))
    field-keywords))

;; =====================================================================
;; Abstract stobj field recognizers
;; ======================================================================

(defsection field-recognizers

  :parents (abstract-state)

  :short "Definition of the <tt>:logic</tt> recognizers of the
  abstract stobj fields"

  :long "<p>We define the recognizers of the array fields using
  @('defun-sk').  The simple fields are defined using
  @('unsigned-byte-p'), @('signed-byte-p'), or other appropriate
  functions like @('env-alistp').</p>"

  (defun x86$a-recognizers-1 (x86-model-field)
    ;; This function assumes that x86-model-field is defined using the
    ;; same syntax as that for a field in a defstobj definition.
    (let ((name (car x86-model-field))
          (type (caddr x86-model-field)))

      (cond ((and (consp type)
                  (equal (car type) 'array)
                  (consp (cadr type)))
             (let* ((name      (mk-name (subseq (symbol-name name) 0
                                                (search "$C" (symbol-name
                                                              name)))))
                    (recognizer (mk-name name "P"))
                    (recognizer-aux (mk-name name "P-AUX"))
                    (size-num      (cadr (cadr type)))
                    (size (symbol-name (if (< size-num 10)
                                           (acl2::packn (list 0 size-num))
                                         (acl2::packn (list size-num)))))
                    ;; Assuming that there are no resizable arrays...
                    (length (caaddr (caddr x86-model-field)))
                    (unsigned? (equal (car (cadr type)) 'unsigned-byte))
                    (byte-p (if unsigned? 'UNSIGNED-BYTE-P 'SIGNED-BYTE-P))
                    (logfn (if unsigned? 'LOGHEAD 'LOGEXT)))

               `((DEFUN-SK ,recognizer-aux (X)
                   (FORALL I
                           (implies (and (natp i)
                                         (< i ,length))
                                    (,(if unsigned?
                                          (mk-name "N" size "P")
                                        (mk-name "I" size "P"))
                                     (GZ I X)))))
                 (DEFN ,recognizer (X)
                   (EC-CALL (,recognizer-aux X)))

                 (DEFTHM ,(mk-name "INTEGERP-OF-GZ-OF-" recognizer-aux)
                   (implies (and (,recognizer-aux x)
                                 (natp i)
                                 (< i ,length))
                            (integerp (gz i x)))
                   :hints (("Goal"
                            :in-theory (disable
                                        unsigned-byte-p
                                        signed-byte-p
                                        ,(mk-name recognizer-aux "-NECC"))
                            :use ((:instance ,(mk-name recognizer-aux "-NECC"))))))

                 (LOCAL
                  (DEFTHM ,(mk-name recognizer-aux "-OF-SZ-HELPER")
                    (IMPLIES (AND (NATP J)
                                  (< J ,length)
                                  (,recognizer-aux X))
                             (,byte-p ,size-num (GZ J (SZ I (,logfn ,size-num V) X))))
                    :HINTS (("GOAL"
                             :CASES ((EQUAL I J))
                             :IN-THEORY (E/D ()
                                             (,(mk-name recognizer-aux "-NECC")
                                              UNSIGNED-BYTE-P
                                              SIGNED-BYTE-P))
                             :USE ((:INSTANCE ,(mk-name recognizer-aux "-NECC")
                                              (I J)))))))

                 (DEFTHM ,(mk-name recognizer-aux "-OF-SZ")
                   (IMPLIES (,recognizer-aux X)
                            (,recognizer-aux (SZ I (,logfn ,size-num V) X)))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,recognizer-aux)
                                                   (,(mk-name recognizer-aux "-NECC")
                                                    UNSIGNED-BYTE-P
                                                    SIGNED-BYTE-P))))))))

            ((and (consp type)
                  (or (equal (car type) 'unsigned-byte)
                      (equal (car type) 'signed-byte)))
             (let* ((name      (mk-name (subseq (symbol-name name) 0
                                                (search "$C" (symbol-name
                                                              name)))))
                    (recognizer (mk-name name "P"))
                    (car-type (mk-name (car type) "-P"))
                    (size      (cadr type)))

               `((DEFN ,recognizer (X)
                   (,car-type ,size X)))))

            ((and (consp type)
                  (equal (car type) 'integer))
             (let* ((name      (mk-name (subseq (symbol-name name) 0
                                                (search "$C" (symbol-name
                                                              name)))))
                    (recognizer (mk-name name "P"))
                    (min      (cadr type))
                    (max      (caddr type)))
               `((DEFN ,recognizer (X)
                   (AND (INTEGERP X)
                        (<= ,min X)
                        (<= X ,max))))))

            ((and (consp type)
                  (equal (car type) 'satisfies))
             (let* ((name      (mk-name (subseq (symbol-name name) 0
                                                (search "$C" (symbol-name
                                                              name)))))
                    (recognizer (mk-name name "P"))
                    (predicate (cadr type)))
               `((DEFN ,recognizer (X)
                   (,predicate X)))))

            (t
             ;; type is presumably 'T
             (let* ((name      (mk-name (subseq (symbol-name name) 0
                                                (search "$C" (symbol-name
                                                              name)))))
                    (recognizer (mk-name name "P")))
               `((DEFN ,recognizer (X)
                   (DECLARE (IGNORABLE X))
                   T)))))))

  (defun x86$a-recognizers-2 (pruned-x86-model)
    (cond ((endp pruned-x86-model)
           '())
          (t
           `(,@(x86$a-recognizers-1 (car pruned-x86-model))
             ,@(x86$a-recognizers-2
                (cdr pruned-x86-model))))))

  (defmacro x86$a-recognizers ()
    (cons 'progn
          (x86$a-recognizers-2 *pruned-x86-model-modified-mem*)))

  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))

  (x86$a-recognizers)

  ;; Since we never want to execute these predicates, we disable their
  ;; executable counterparts.

  (globally-disable '((:executable-counterpart rgfp)
                      (:executable-counterpart rflagsp)
                      (:executable-counterpart seg-visiblep)
                      (:executable-counterpart seg-hidden-basep)
                      (:executable-counterpart seg-hidden-limitp)
                      (:executable-counterpart seg-hidden-attrp)
                      (:executable-counterpart strp)
                      (:executable-counterpart ssr-visiblep)
                      (:executable-counterpart ssr-hidden-basep)
                      (:executable-counterpart ssr-hidden-limitp)
                      (:executable-counterpart ssr-hidden-attrp)
                      (:executable-counterpart ctrp)
                      (:executable-counterpart msrp)
                      (:executable-counterpart dbgp)
                      (:executable-counterpart fp-datap)
                      (:executable-counterpart zmmp)
                      (:executable-counterpart memp))))

;; ======================================================================
;; Abstract stobj recognizer x86$ap
;; ======================================================================

(defsection abstract-stobj-recognizer

  :parents (abstract-state)

  :short "Definition of @('x86$ap')"

  (defun create-x86-abs-stobj-recognizer-1 (x86-model-field)
    (let ((name (car x86-model-field))
          (type (caddr x86-model-field)))
      (cond ((and (consp type)
                  (equal (car type) 'array))
             (let* ((stripped-name (mk-name
                                    (subseq (symbol-name name) 0
                                            (search "$C" (symbol-name name)))))
                    (constant (mk-name "*" stripped-name "I*"))
                    (predicate (mk-name stripped-name "P")))
               `((,predicate (NTH ,constant X)))))
            (t
             (let* ((stripped-name (mk-name
                                    (subseq (symbol-name name) 0
                                            (search "$C" (symbol-name name)))))
                    (constant (mk-name "*" stripped-name "*"))
                    (predicate (mk-name stripped-name "P")))
               `((,predicate (NTH ,constant X))))))))

  (defun create-x86-abs-stobj-recognizer-2 (x86-model)
    (cond ((endp x86-model)
           '())
          (t
           `(,(create-x86-abs-stobj-recognizer-1
               (car x86-model))
             ,@(create-x86-abs-stobj-recognizer-2
                (cdr x86-model))))))

  (defun append-elements (x acc)
    (cond ((endp x)
           acc)
          (t
           (append-elements (cdr x) (append acc (car x))))))

  ;; (append-elements (create-x86-abs-stobj-recognizer-2 *pruned-x86-model-modified-mem*) nil)

  (defun create-x86-abstract-stobj-recognizer-1
    (pruned-x86-model-list)

    `(DEFUN x86$AP (X)
       (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T))
       ;; From :pe x86$cp-pre
       (AND (TRUE-LISTP X)
            (= (LENGTH X) *x86-abs-stobj-len*)
            ,@pruned-x86-model-list
            T)))

  (defmacro create-x86-abstract-stobj-recognizer ()
    (create-x86-abstract-stobj-recognizer-1
     (append-elements (create-x86-abs-stobj-recognizer-2
                       *pruned-x86-model-modified-mem*)
                      nil)))

  ;; x86$ap:
  (create-x86-abstract-stobj-recognizer))

;; ======================================================================
;; Abstract stobj creator create-x86$a
;; ======================================================================

(defsection abstract-stobj-creator

  :parents (abstract-state)

  :short "Definition of @('create-x86$a')"

  (make-event (define-abstract-stobj-indices))

  ;; (defun abstract-stobj-field-defaults (x86-model)
  ;;   (if (endp x86-model)
  ;;       nil
  ;;     (b* ((x86-model-field (car x86-model))
  ;;          (initial (second (member :initially x86-model-field))))
  ;;       (cons initial
  ;;             (abstract-stobj-field-defaults (cdr x86-model))))))

  ;; When adding a "field" to the abstract stobj, remember the order;
  ;; see the function define-abstract-stobj-indices for this order.
  ;; Also, the values here match the :initially values in the defstobj
  ;; definition.  So I could get them programmatically if I wanted to.

  (defn create-x86$a ()
    (list '0      ;; rgfi
          '0      ;; rip
          '2      ;; rflags
          '0      ;; seg-visiblei
          '0      ;; seg-hidden-basei
          '0      ;; seg-hidden-limiti
          '0      ;; seg-hidden-attri
          '0      ;; stri
          '0      ;; ssr-visiblei
          '0      ;; ssr-hidden-basei
          '0      ;; ssr-hidden-limiti
          '0      ;; ssr-hidden-attri
          '0      ;; ctri
          '0      ;; dbgi
          '0      ;; fp-datai
          '0      ;; fp-ctrl
          '0      ;; fp-status
          '0      ;; fp-tag
          '0      ;; fp-last-inst
          '0      ;; fp-last-data
          '0      ;; fp-opcode
          '0      ;; zmmi
          '8064   ;; mxcsr
          '0      ;; msri
          'nil    ;; ms
          'nil    ;; fault
          'nil    ;; env
          '0      ;; undef
          't      ;; app-view
          't      ;; marking-view
          ':linux ;; os-info
          '0      ;; memi
          )))

;; ======================================================================
;; Abstract stobj field accessors and updaters
;; ======================================================================

(defsection field-accessors-and-updaters

  :parents (abstract-state)

  :short "Definitions of the <tt>:logic</tt> functions for abstract
  stobj field accessors and updaters"

  (defun x86$a-accessors-and-updaters-1 (x86-model-field)
    ;; This function assumes that x86-model-field is defined using the
    ;; same syntax as that for a field in a defstobj definition.
    (let ((name (car x86-model-field))
          (type (caddr x86-model-field)))

      (cond

       ((and (consp type)
             (equal (car type) 'array)
             (consp (cadr type))
             (equal (car (cadr type)) 'unsigned-byte))
        ;; We assume that there is no resizable array.  The memory was a
        ;; resizable array in the concrete stobj, but we handle memory
        ;; differently in the abstract stobj.
        (let* ((name      (mk-name (subseq (symbol-name name) 0
                                           (search "$C" (symbol-name
                                                         name)))))
               (constant  (mk-name "*" name "I*"))
               (getter    (mk-name name "$AI"))
               (setter    (mk-name "!" name "$AI"))
               (size      (cadr (cadr type)))
               (length    (caaddr (caddr x86-model-field))))
          `((DEFUN ,(mk-name getter) (I x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (NATP I)
                                          (< I ,length))))
              (LOGHEAD ,size
                       (GZ I (NTH ,constant x86))))
            (DEFUN ,(mk-name setter) (I V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (NATP I)
                                          (< I ,length)
                                          (UNSIGNED-BYTE-P ,size V))))
              (UPDATE-NTH ,constant
                          (SZ I
                              (LOGHEAD ,size V)
                              (NTH ,constant x86)) x86)))))

       ((and (consp type)
             (equal (car type) 'array)
             (consp (cadr type))
             (equal (car (cadr type)) 'signed-byte))
        (let* ((name      (mk-name (subseq (symbol-name name) 0
                                           (search "$C" (symbol-name
                                                         name)))))
               (constant  (mk-name "*" name "I*"))
               (getter    (mk-name name "$AI"))
               (setter    (mk-name "!" name "$AI"))
               (size      (cadr (cadr type)))
               (length    (caaddr (caddr x86-model-field))))
          `((DEFUN ,(mk-name getter) (I x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (NATP I)
                                          (< I ,length))))
              (LOGEXT ,size
                      (GZ I (NTH ,constant x86))))
            (DEFUN ,(mk-name setter) (I V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (NATP I)
                                          (< I ,length)
                                          (SIGNED-BYTE-P ,size V))))
              (UPDATE-NTH ,constant
                          (SZ I
                              (LOGEXT ,size V)
                              (NTH ,constant x86)) x86)))))

       ((and (consp type)
             (equal (car type) 'unsigned-byte))
        (let* ((name      (mk-name (subseq (symbol-name name) 0
                                           (search "$C" (symbol-name
                                                         name)))))
               (constant  (mk-name "*" name "*"))
               (getter    (mk-name name "$A"))
               (setter    (mk-name "!" name "$A"))
               (size      (cadr type)))
          `((DEFUN ,getter (x86)
              (DECLARE (XARGS :GUARD (x86$AP x86)))
              (LOGHEAD ,size (NTH ,constant x86)))
            (DEFUN ,setter (V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (UNSIGNED-BYTE-P ,size V))))
              (UPDATE-NTH ,constant (LOGHEAD ,size V) x86)))))

       ((and (consp type)
             (equal (car type) 'signed-byte))
        (let* ((name      (mk-name (subseq (symbol-name name) 0
                                           (search "$C" (symbol-name
                                                         name)))))
               (constant  (mk-name "*" name "*"))
               (getter    (mk-name name "$A"))
               (setter    (mk-name "!" name "$A"))
               (size      (cadr type)))
          `((DEFUN ,getter (x86)
              (DECLARE (XARGS :GUARD (x86$AP x86)))
              (LOGEXT ,size (NTH ,constant x86)))
            (DEFUN ,setter (V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (SIGNED-BYTE-P ,size V))))
              (UPDATE-NTH ,constant (LOGEXT ,size V) x86)))))

       ((and (consp type)
             (equal (car type) 'integer))
        (let* ((name      (mk-name (subseq (symbol-name name) 0
                                           (search "$C" (symbol-name
                                                         name)))))
               (constant    (mk-name "*" name "*"))
               (getter      (mk-name name "$A"))
               (setter      (mk-name "!" name "$A"))
               (default-val (second (member :initially x86-model-field)))
               (min         (cadr type))
               (max         (caddr type)))
          `((DEFUN ,getter (x86)
              (DECLARE (XARGS :GUARD (x86$AP x86)))
              (let ((RAW-VAL (NTH ,constant x86)))
                (if (AND (INTEGERP RAW-VAL)
                         (<= ,min RAW-VAL)
                         (<= RAW-VAL ,max))
                    RAW-VAL
                  ,default-val)))
            (DEFUN ,setter (V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (INTEGERP V)
                                          (<= ,min V)
                                          (<= V ,max))))
              (UPDATE-NTH ,constant
                          (if (AND (INTEGERP V)
                                   (<= ,min V)
                                   (<= V ,max))
                              V
                            ,default-val)
                          x86)))))

       ((and (consp type)
             (equal (car type) 'satisfies))
        ;; env field
        (let* ((name        (mk-name (subseq (symbol-name name) 0
                                             (search "$C" (symbol-name
                                                           name)))))
               (predicate   (cadr type))
               (constant    (mk-name "*" name "*"))
               (getter      (mk-name name "$A"))
               (setter      (mk-name "!" name "$A"))
               (default-val (second (member :initially x86-model-field))))
          `((DEFUN ,getter (x86)
              (DECLARE (XARGS :GUARD (X86$AP X86)))
              (let ((RAW-VAL (NTH ,constant X86)))
                (if (,predicate RAW-VAL)
                    RAW-VAL
                  ,default-val)))
            (DEFUN ,setter (V X86)
              (DECLARE (XARGS :GUARD (AND (X86$AP X86)
                                          (,predicate V))))
              (UPDATE-NTH ,constant
                          (if (,predicate V)
                              V
                            ,default-val)
                          X86)))))

       (t
        ;; type is T
        (let* ((name      (mk-name (subseq (symbol-name name) 0
                                           (search "$C" (symbol-name
                                                         name)))))
               (constant  (mk-name "*" name "*"))
               (getter    (mk-name name "$A"))
               (setter    (mk-name "!" name "$A")))
          `((DEFUN ,getter (x86)
              (DECLARE (XARGS :GUARD (x86$AP x86)))
              (NTH ,constant x86))
            (DEFUN ,setter (V x86)
              (DECLARE (XARGS :GUARD (x86$AP x86)))
              (UPDATE-NTH ,constant V x86))))))))

  (defun x86$a-accessors-and-updaters-2 (pruned-x86-model)
    (cond ((endp pruned-x86-model)
           '())
          (t
           `(,@(x86$a-accessors-and-updaters-1 (car pruned-x86-model))
             ,@(x86$a-accessors-and-updaters-2
                (cdr pruned-x86-model))))))

  (defmacro x86$a-accessors-and-updaters ()
    (cons 'progn
          (x86$a-accessors-and-updaters-2 *pruned-x86-model-modified-mem*)))

  (x86$a-accessors-and-updaters))


;; ======================================================================
;; Correspondence predicate
;; ======================================================================

(defsection correspondence-predicate

  :parents (abstract-state)

  :short "Definition of the correspondence predicate @('corr')"

  :long "<p>When do the abstract and concrete stobjs correspond?</p>

 <p>Note that accessing an out of bounds index of an array field in
  the concrete stobj will (logically) return a @('nil').  In the
  abstract stobj, because of our use of @('records-0'), the same index
  will return a @('0').  So, the abstract and concrete stobjs
  correspond only when the indices are within bounds.</p>

  <p>One interesting aspect of these correspondence functions is that
  they have guards.  ACL2 doesn't require us to have guarded
  correspondence functions --- in fact, they need not even be
  executable.  But we have guards in these correspondence functions
  because we actually execute them in a @('with-local-stobj')! So
  guards are nice here because they give us execution efficiency.
  Without guards, proving @('corr-flg-init') takes around 120s; with
  guards, it takes around 8s. See functions like @('hack-rgf') for
  details.</p>"

  (defun create-x86-correspondence-function-1 (x86-model-field)
    ;; This function assumes that x86-model-field is defined using the
    ;; same syntax as that for a field in a defstobj definition.
    (let ((name (car x86-model-field))
          (type (caddr x86-model-field)))
      (cond

       ((and (consp type)
             (equal (car type) 'array)
             (consp (cadr type)))
        ;; We assume that there is no resizable array.  The memory was a
        ;; resizable array in the concrete stobj, but we handle memory
        ;; differently in the abstract stobj.
        (let* ((name      (mk-name (subseq (symbol-name name) 0
                                           (search "$C" (symbol-name
                                                         name)))))
               (getter    (mk-name name "$CI"))
               (length    (caaddr (caddr x86-model-field))))
          `((DEFUN ,(mk-name "CORR-" name "-AUX") (I X86$C FIELD)
              (DECLARE (XARGS :STOBJS (X86$C)
                              :GUARD (AND (X86$CP X86$C)
                                          (NATP I)
                                          (< I ,length)
                                          (GOOD-ALISTP FIELD))))
              (IF (ZP I)
                  (EQUAL (,getter I X86$c) (GZ  I FIELD))
                  (AND (EQUAL (,getter I X86$c) (GZ  I FIELD))
                       (,(mk-name "CORR-" name "-AUX")
                        (1- I) X86$c FIELD))))
            (DEFUN ,(mk-name "CORR-" name) (X86$C FIELD)
              (DECLARE (XARGS :STOBJS (X86$C)
                              :VERIFY-GUARDS NIL
                              :GUARD (AND (X86$CP X86$C)
                                          (GOOD-ALISTP FIELD))))
              (,(mk-name "CORR-" name "-AUX") (1- ,length) X86$C FIELD)))))

       (t
        nil))))

  (defun create-x86-correspondence-function-2 (x86-model)
    (cond ((endp x86-model)
           '())
          ((let* ((field (car x86-model))
                  (type (caddr field)))
             (and (consp type)
                  (equal (car type) 'array)))
           (append (create-x86-correspondence-function-1 (car x86-model))
                   (create-x86-correspondence-function-2 (cdr x86-model))))
          (t
           (create-x86-correspondence-function-2 (cdr x86-model)))))

  (defmacro create-x86-correspondence-function (x86-model)
    `(create-x86-correspondence-function-2 ,x86-model))

  (defmacro create-x86-correspondence-functions ()
    (cons 'progn
          (create-x86-correspondence-function *pruned-x86-model*)))

  (create-x86-correspondence-functions)

  ;; Memory field:

  (defun-sk corr-mem (x86$c field)
    ;; corr-mem is our memory correspondence predicate --- it says that
    ;; looking up the memory in the concrete stobj returns the same value
    ;; as looking it up in the abstract stobj.
    (forall i
            (implies (and (natp i)
                          (< i *mem-size-in-bytes*))
                     (equal (mem$ci i x86$c)
                            (gz i field)))))

  (defun create-x86-correspondence-predicate-1 (x86-model-field)
    (let ((name1 (car x86-model-field))
          (type (caddr x86-model-field)))
      (cond ((and (consp type)
                  (equal (car type) 'array))
             (let* ((name      (mk-name (subseq (symbol-name name1) 0
                                                (search "$C" (symbol-name
                                                              name1)))))
                    (constant (mk-name "*" name "I*"))
                    (corr-name (mk-name "CORR-" name)))
               `(,corr-name C (NTH ,constant A))))
            (t
             (let* ((name      (mk-name (subseq (symbol-name name1) 0
                                                (search "$C" (symbol-name
                                                              name1)))))
                    (constant (mk-name "*" name "*"))
                    (concrete-const (mk-name "*" name1 "*")))
               `(EQUAL (NTH ,concrete-const C)
                       (NTH ,constant A)))))))

  (defun create-x86-correspondence-predicate-2 (x86-model)
    (cond ((endp x86-model)
           '())
          (t
           `(,(create-x86-correspondence-predicate-1 (car x86-model))
             ,@(create-x86-correspondence-predicate-2 (cdr x86-model))))))

  (defun create-x86-correspondence-predicate-fn (pruned-x86-model)

    ;; This is our correspondence predicate, used in the defabsstobj
    ;; event that is below.  It says that C and A satisfy their
    ;; respective (strong) invariants, and that the fields correspond.

    `(DEFUN-NX CORR (C A)
       (AND (x86$CP C)
            (x86$AP A)
            ,@pruned-x86-model
            (CORR-MEM C (NTH *MEMI* A)))))

  (defmacro create-x86-correspondence-predicate ()
    (create-x86-correspondence-predicate-fn
     (create-x86-correspondence-predicate-2 *pruned-x86-model*)))

  (create-x86-correspondence-predicate)

  (in-theory (disable corr-rgf
                      corr-seg-visible
                      corr-seg-hidden-base
                      corr-seg-hidden-limit
                      corr-seg-hidden-attr
                      corr-str
                      corr-ssr-visible
                      corr-ssr-hidden-base
                      corr-ssr-hidden-limit
                      corr-ssr-hidden-attr
                      corr-ctr
                      corr-dbg
                      corr-fp-data
                      corr-zmm
                      corr-msr
                      corr-mem)))

;; ======================================================================
;; Admitting the defabsstobj (x86) and proof obligations
;; ======================================================================

(defsection creating-x86-abstract-stobj

  :parents (abstract-state)

  :short "Creation of the abstract stobj @('x86')."

  (defun create-x86-abstract-stobj-exports-1 (x86-model-field)
    (let* ((name (car x86-model-field))
           (type (caddr x86-model-field)))
      (cond

       ((and (consp type)
             (equal (car type) 'array))
        (b* ((name (mk-name (subseq (symbol-name name) 0
                                    (search "$C" (symbol-name
                                                  name)))))
             (getter (mk-name name "I*"))
             (setter (mk-name "!" name "I*"))
             (abs-getter (mk-name name "$AI"))
             (con-getter (mk-name name "$CI"))
             (abs-setter (mk-name "!" name "$AI"))
             (con-setter (mk-name "!" name "$CI")))
          `((,getter :LOGIC ,abs-getter
                     :EXEC ,con-getter)
            (,setter :LOGIC ,abs-setter
                     :EXEC ,con-setter
                     ;; The memory field is a "compound" field, derived
                     ;; from three fields in the concrete stobj.
                     :PROTECT ,(equal name 'MEM)))))
       (t
        (b* ((name (mk-name (subseq (symbol-name name) 0
                                    (search "$C" (symbol-name
                                                  name)))))
             (getter (mk-name name "*"))
             (setter (mk-name "!" name "*"))
             (abs-getter (mk-name name "$A"))
             (con-getter (mk-name name "$C"))
             (abs-setter (mk-name "!" name "$A"))
             (con-setter (mk-name "!" name "$C")))
          `((,getter :LOGIC ,abs-getter
                     :EXEC ,con-getter)
            (,setter :LOGIC ,abs-setter
                     :EXEC ,con-setter)))))))

  (defun create-x86-abstract-stobj-exports-2 (x86-model)
    (cond ((endp x86-model)
           '())
          (t
           `(,(create-x86-abstract-stobj-exports-1
               (car x86-model))
             ,@(create-x86-abstract-stobj-exports-2
                (cdr x86-model))))))

  (defun create-x86-abstract-stobj-fn (pruned-x86-model-list)
    `(DEFABSSTOBJ X86
       :FOUNDATION X86$C
       :RECOGNIZER (X86P
                    :LOGIC X86$AP
                    :EXEC X86$CP-PRE)
       :CREATOR (CREATE-X86
                 :LOGIC CREATE-X86$A
                 :EXEC CREATE-X86$C)
       :CORR-FN CORR
       :EXPORTS ,pruned-x86-model-list))

  (defmacro create-x86-abstract-stobj ()
    (create-x86-abstract-stobj-fn
     (append-elements (create-x86-abstract-stobj-exports-2
                       *pruned-x86-model-modified-mem*)
                      nil)))

  ;; At this point during development, we evaluated the defabsstobj
  ;; event (obtained by (create-x86-abstract-stobj)) at the end of this
  ;; file) in order to print to the terminal all of its proof obligation
  ;; events.  We pasted those in below -- the parts in caps are the
  ;; parts that were automatically generated (with obvious exceptions,
  ;; for example, when suffixes such as "-1" are added after "}") -- and
  ;; then put ourselves to the task of admitting them all.

  ;; Start proof of CREATE-x86@{CORRESPONDENCE}.

  ;; Here comes a trick for avoiding executing make-list-ac on large
  ;; lists (especially mem-table and mem-array in our model).  This will
  ;; be useful when proving subgoals about field recognizers for the
  ;; concrete stobj.

  (defun make-list-ac$ (n val ac)
    (declare (xargs :guard (and (integerp n) (>= n 0))))
    (make-list-ac n val ac))

  (defthm make-list-ac-is-make-list-ac$
    (implies (syntaxp (and (quotep n)
                           (quotep val)
                           (quotep ac)
                           (natp (cadr n))
                           (< (cadr n) 20)))
             (equal (make-list-ac n val ac)
                    (make-list-ac$ n val ac))))

  (defthm len-make-list-ac
    (equal (len (make-list-ac n val ac))
           (+ (nfix n) (len ac)))
    :hints (("Goal" :in-theory (enable make-list-ac))))

  (defthm mem-tablep-make-list-ac
    (implies (and (unsigned-byte-p 26 val)
                  (mem-tablep ac))
             (mem-tablep (make-list-ac n val ac)))
    :hints (("Goal" :in-theory (enable make-list-ac mem-tablep))))

  (defthm mem-arrayp-make-list-ac
    (implies (and (unsigned-byte-p 8 val)
                  (mem-arrayp ac))
             (mem-arrayp (make-list-ac n val ac)))
    :hints (("Goal" :in-theory (enable make-list-ac mem-arrayp))))

  (local (in-theory (disable make-list-ac
                             (make-list-ac)
                             (create-x86$c)
                             (create-x86$a))))

  (defun corr-array-fields-init-1 (x86-model-field)
    ;; This function assumes that x86-model-field is defined using the
    ;; same syntax as that for a field in a defstobj definition.
    (let ((name (car x86-model-field))
          (type (caddr x86-model-field)))

      (cond ((and (consp type)
                  (equal (car type) 'array)
                  (consp (cadr type)))
             (let* ((name      (mk-name (subseq (symbol-name name) 0
                                                (search "$C" (symbol-name
                                                              name)))))
                    (hack-name (mk-name "HACK-" name))
                    (corr-name (mk-name "CORR-" name)))

               `((LOCAL
                  (DEFUN ,hack-name ()
                    (WITH-LOCAL-STOBJ
                      X86$C
                      (MV-LET (RESULT X86$C)
                        (MV (,corr-name X86$C 0) X86$C)
                        RESULT))))
                 (DEFTHM ,(mk-name corr-name "-INIT")
                   (,corr-name (CREATE-X86$C) 0)
                   :HINTS (("GOAL" :USE (,hack-name)
                            :IN-THEORY
                            (UNION-THEORIES '((,hack-name))
                                            (THEORY 'MINIMAL-THEORY))))
                   :RULE-CLASSES NIL))))

            (t nil))))

  (defun corr-array-fields-init-2 (pruned-x86-model)
    (cond ((endp pruned-x86-model)
           '())
          (t
           `(,@(corr-array-fields-init-1 (car pruned-x86-model))
             ,@(corr-array-fields-init-2
                (cdr pruned-x86-model))))))

  ;; (corr-array-fields-init-2 *pruned-x86-model*)

  (defmacro corr-array-fields-init ()
    (cons 'progn
          (corr-array-fields-init-2 *pruned-x86-model*)))

  (encapsulate
    ()

    (local
     (defun hack ()
       (with-local-stobj
         x86$c
         (mv-let (result x86$c)
           (mv (x86$cp x86$c) x86$c)
           result))))

    ;; The :use hint below creates this goal

    ;; (implies (equal (hack) (with-local-stobj ...))
    ;;          (x86$cp (create-x86$c)))

    ;; which in turn reduces to the following.

    ;; (implies (equal t (x86$cp (create-x86$c)))
    ;;          (x86$cp (create-x86$c)))

    (defthm x86$cp-create-x86$c
      (x86$cp (create-x86$c))
      :hints (("Goal" :use (hack)
               :in-theory (union-theories
                           '((hack))
                           (theory 'minimal-theory))))
      :rule-classes nil)

    ;; Similar stuff for the array and flags fields...
    (corr-array-fields-init)

    ) ;; End of encapsulate

  ;; Start proof of corr-mem-init (which takes too long using the above
  ;; with-local-stobj approach).

  (defun onesp-mem-table (k lst)
    ;; Omit guard; this is only used for helping with the proofs.  Note
    ;; that lst refers to the mem-table.  See the definition of mem$ci
    ;; to see where (ash k (- *2^x-byte-pseudo-page*)) comes from.
    (cond ((zp k) t)
          (t (let ((k (1- k)))
               (and (eql (nth (logtail *2^x-byte-pseudo-page* k) lst) 1)
                    (onesp-mem-table k lst))))))

  (encapsulate
    ()

    (local (include-book "centaur/bitops/ihs-extensions" :dir :system))
    (local (include-book "arithmetic/top" :dir :system))

    (defrulel onesp-mem-table-implies-mem$ci-is-0-lemma
      (implies (and (onesp-mem-table k mem-table)
                    (integerp i)
                    (<= 0 i)
                    (integerp k)
                    (< i k))
               (equal (nth (logtail *2^x-byte-pseudo-page* i) mem-table)
                      1)))

    (defrulel onesp-mem-table-implies-mem$ci-is-0
      (implies (and (onesp-mem-table k (nth *mem-tablei* x86$c))
                    (integerp i)
                    (<= 0 i)
                    (natp k)
                    (< i k))
               (equal (mem$ci i x86$c) 0))
      :hints (("Goal" :in-theory (enable mem$ci mem-tablei))))

    (defthm corr-mem-for-all-ones-in-mem-table
      (implies (onesp-mem-table *mem-size-in-bytes*
                                (nth *mem-tablei* x86$c))
               (corr-mem x86$c 0))
      :hints (("Goal" :in-theory (enable corr-mem))))

    ) ;; End of encapsulate

  (encapsulate
    ()

    (local (include-book "arithmetic-5/top" :dir :system))

    (defthm nth-make-list-ac-1
      (implies (and (natp k)
                    (natp n))
               (equal (nth k (make-list-ac n val ac))
                      (cond ((< k n) val)
                            (t (nth (- k n) ac)))))
      :hints (("Goal" :in-theory (enable nth make-list-ac))))

    (defrulel ash-monotone-2-lemma
      (implies (<= x y)
               (<= (* x (expt 2 z)) (* y (expt 2 z))))
      :rule-classes :linear)

    (defthm ash-monotone-2
      (implies (and (natp y)
                    (<= x y))
               (<= (ash x z) (ash y z)))
      :rule-classes :linear)

    (defthm onesp-mem-table-make-list-ac
      (implies (and (posp k1)
                    (natp k2)
                    (< (logtail *2^x-byte-pseudo-page* (1- k1))
                       k2))
               (onesp-mem-table k1 ; *mem-size-in-bytes*
                                (make-list-ac k2 1 nil)))
      :hints (("Goal" :induct t)))

    ) ;; End of encapsulate

  (defthm corr-mem-init
    (corr-mem (create-x86$c) 0)
    :rule-classes nil)

  (DEFRULEL CREATE-X86{CORRESPONDENCE}
    (CORR (CREATE-X86$C)
          (CREATE-X86$A))
    :hints (("Goal"
             :use (x86$cp-create-x86$c
                   corr-rgf-init
                   corr-seg-visible-init
                   corr-seg-hidden-base-init
                   corr-seg-hidden-limit-init
                   corr-seg-hidden-attr-init
                   corr-str-init
                   corr-ssr-visible-init
                   corr-ssr-hidden-base-init
                   corr-ssr-hidden-limit-init
                   corr-ssr-hidden-attr-init
                   corr-ctr-init
                   corr-dbg-init
                   corr-msr-init
                   corr-mem-init
                   corr-fp-data-init
                   corr-zmm-init)))
    :RULE-CLASSES NIL)

  (DEFRULEL CREATE-X86{PRESERVED}
    (X86$AP (CREATE-X86$A))
    ;; Note that we disable the executable counterpart of x86$ap.
    :hints (("Goal" :in-theory (disable (x86$ap))))
    :RULE-CLASSES NIL)

  (in-theory (disable rgfp-aux
                      seg-visiblep-aux
                      seg-hidden-basep-aux
                      seg-hidden-limitp-aux
                      seg-hidden-attrp-aux
                      strp-aux
                      ssr-visiblep-aux
                      ssr-hidden-basep-aux
                      ssr-hidden-limitp-aux
                      ssr-hidden-attrp-aux
                      ctrp-aux     dbgp-aux
                      msrp-aux     fp-datap-aux
                      zmmp-aux     memp-aux))

  ;; Lemmas needed for the accessor correspondence theorems:

  (defun create-accessor-$a-corr-lemmas-1 (x86-model-field)
    (let* ((name (car x86-model-field))
           (type (caddr x86-model-field)))
      (cond ((and (consp type)
                  (equal (car type) 'array))
             (let* ((length (caaddr (caddr x86-model-field)))
                    (stripped-name (mk-name
                                    (subseq (symbol-name name) 0
                                            (search "$C"
                                                    (symbol-name name)))))
                    (constant (mk-name "*" stripped-name "I*"))
                    (getter (mk-name stripped-name "$CI"))
                    (corr-name (mk-name "CORR-" stripped-name))
                    (corr-name-aux (mk-name corr-name "-AUX"))
                    (field-corr (mk-name stripped-name "I{CORRESPONDENCE}")))

               `((DEFTHMD ,(mk-name field-corr "-HELPER-1")
                   (IMPLIES (AND (X86$AP X86)
                                 (INTEGERP J)
                                 (<= 0 J)
                                 (<= 0 (1- J))
                                 (< J ,length)
                                 (X86$CP X86$C))
                            (EQUAL (,corr-name-aux J X86$C (NTH ,constant X86))
                                   (AND (EQUAL (,getter J X86$C)
                                               (GZ  J (NTH ,constant X86)))
                                        (,corr-name-aux (1- J) X86$C
                                                        (NTH ,constant X86))))))

                 (DEFTHMD ,(mk-name field-corr "-HELPER-2")
                   (IMPLIES (AND (X86$AP X86)
                                 (,corr-name-aux J X86$C (NTH ,constant X86))
                                 (INTEGERP J)
                                 (<= 0 J)
                                 (< J ,length)
                                 (INTEGERP I)
                                 (<= 0 I)
                                 (<= I J)
                                 (X86$CP X86$C))
                            (EQUAL (,getter I X86$C)
                                   (GZ  I (NTH ,constant X86))))
                   :HINTS (("GOAL" :INDUCT (,corr-name-aux J X86$C
                                                           (NTH ,constant X86)))
                           ("SUBGOAL *1/2" :IN-THEORY (E/D () (X86$AP))
                            :USE ((:INSTANCE ,(mk-name field-corr
                                                       "-HELPER-1"))))))
                 )))
            (t
             nil))))

  (defun create-accessor-$a-corr-lemmas-2 (pruned-x86-model)
    (cond ((endp pruned-x86-model)
           '())
          (t
           `(,@(create-accessor-$a-corr-lemmas-1 (car pruned-x86-model))
             ,@(create-accessor-$a-corr-lemmas-2
                (cdr pruned-x86-model))))))

  ;; (create-accessor-$a-corr-lemmas-2 *pruned-x86-model*)

  (defmacro create-accessor-$a-corr-lemmas ()
    (cons 'progn
          (create-accessor-$a-corr-lemmas-2 *pruned-x86-model*)))

  (create-accessor-$a-corr-lemmas)

  ;; Lemmas needed for the updater correspondence theorems:

  (defthm mem-tablei-update-nth
    (implies (not (equal n *mem-tablei*))
             (equal (mem-tablei i (update-nth n x x86))
                    (mem-tablei i x86)))
    :hints (("Goal" :in-theory (enable mem-tablei))))

  (defthm mem-arrayi-update-nth
    (implies (not (equal n *mem-arrayi*))
             (equal (mem-arrayi i (update-nth n x x86))
                    (mem-arrayi i x86)))
    :hints (("Goal" :in-theory (enable mem-arrayi))))

  (defthm mem-array-next-addr-update-nth
    (implies (not (equal n *mem-array-next-addr*))
             (equal (mem-array-next-addr (update-nth n x x86))
                    (mem-array-next-addr x86)))
    :hints (("Goal" :in-theory (enable mem-array-next-addr))))

  (defthm mem$ci-update-nth
    (implies (and (not (equal n *mem-tablei*))
                  (not (equal n *mem-arrayi*))
                  (not (equal n *mem-array-next-addr*)))
             (equal (mem$ci i (update-nth n x x86))
                    (mem$ci i x86)))
    :hints (("Goal" :in-theory (e/d (mem$ci) (force (force))))))

  (defthm corr-mem-update-nth
    (implies (and (not (equal n *mem-tablei*))
                  (not (equal n *mem-arrayi*))
                  (not (equal n *mem-array-next-addr*)))
             (iff (corr-mem (update-nth n x x86) field)
                  (corr-mem x86 field)))
    :hints (("Goal"
             :in-theory (disable corr-mem mem$ci !mem$ci gz)
             :use ((:instance corr-mem
                              (x86$c (update-nth n x x86)))
                   (:instance corr-mem-necc
                              (x86$c x86)
                              (i (corr-mem-witness (update-nth n x x86)
                                                   field)))
                   (:instance corr-mem
                              (x86$c x86))
                   (:instance corr-mem-necc
                              (x86$c (update-nth n x x86))
                              (i (corr-mem-witness x86 field)))))))

  (defun create-updater-correspondence-lemmas-1 (x86-model-field)
    (let* ((name (car x86-model-field))
           (type (caddr x86-model-field)))
      (cond ((and (consp type)
                  (equal (car type) 'array))
             (let* ((length (caaddr (caddr x86-model-field)))
                    (stripped-name (mk-name
                                    (subseq (symbol-name name) 0
                                            (search "$C"
                                                    (symbol-name
                                                     name)))))
                    ;; (concrete-const (mk-name "*" name "I*"))
                    ;; (constant (mk-name "*" stripped-name "I*"))
                    (constant (mk-name "*" name "I*"))
                    (getter (mk-name stripped-name "$CI"))
                    (corr-name (mk-name "CORR-" stripped-name))
                    (corr-name-aux (mk-name corr-name "-AUX")))

               `((DEFTHM ,(mk-name getter "-UPDATE-NTH")
                   (IMPLIES (AND (NOT (EQUAL N ,constant))
                                 (NATP N))
                            (EQUAL (,getter I (UPDATE-NTH N X X86))
                                   (,getter I X86)))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,getter) ()))))

                 (LOCAL
                  (DEFTHMD ,(mk-name corr-name "-UPDATE-NTH-HELPER-1")
                    (IMPLIES (AND (NATP J)
                                  (< J ,length)
                                  (NATP N)
                                  (NOT (EQUAL N ,constant))
                                  (,corr-name-aux J (UPDATE-NTH N X X86) FIELD))
                             (,corr-name-aux J X86 FIELD))))

                 (LOCAL
                  (DEFTHMD ,(mk-name corr-name "-UPDATE-NTH-1")
                    (IMPLIES (AND (NATP N)
                                  (NOT (EQUAL N ,constant))
                                  (,corr-name (UPDATE-NTH N X X86) FIELD))
                             (,corr-name X86 FIELD))
                    :HINTS (("GOAL" :IN-THEORY (E/D (,corr-name) ())
                             :USE ((:INSTANCE
                                    ,(mk-name corr-name "-UPDATE-NTH-HELPER-1")
                                    (J (1- ,length))))))))

                 (LOCAL
                  (DEFTHMD ,(mk-name corr-name "-UPDATE-NTH-HELPER-2")
                    (IMPLIES (AND (NATP J)
                                  (< J ,length)
                                  (NATP N)
                                  (NOT (EQUAL N ,constant))
                                  (,corr-name-aux J X86 FIELD))
                             (,corr-name-aux J (UPDATE-NTH N X X86) FIELD))))

                 (LOCAL
                  (DEFTHMD ,(mk-name corr-name "-UPDATE-NTH-2")
                    (IMPLIES (AND (NATP N)
                                  (NOT (EQUAL N ,constant))
                                  (,corr-name X86 FIELD))
                             (,corr-name (UPDATE-NTH N X X86) FIELD))
                    :HINTS (("GOAL" :IN-THEORY (E/D (,corr-name) ())
                             :USE ((:INSTANCE ,(mk-name corr-name "-UPDATE-NTH-HELPER-2")
                                              (J (1- ,length))))))))

                 (DEFTHMD ,(mk-name corr-name "-UPDATE-NTH")
                   (IMPLIES (AND (NATP N)
                                 (NOT (EQUAL N ,constant)))
                            (IFF (,corr-name X86 FIELD)
                                 (,corr-name (UPDATE-NTH N X X86) FIELD)))
                   :HINTS (("GOAL" :USE ((:INSTANCE ,(mk-name corr-name "-UPDATE-NTH-1"))
                                         (:INSTANCE ,(mk-name corr-name "-UPDATE-NTH-2"))))))

                 )))
            (t
             nil))))

  (defun create-updater-correspondence-lemmas-2 (pruned-x86-model)
    (cond ((endp pruned-x86-model)
           '())
          (t
           `(,@(create-updater-correspondence-lemmas-1 (car pruned-x86-model))
             ,@(create-updater-correspondence-lemmas-2
                (cdr pruned-x86-model))))))

  ;; (create-updater-correspondence-lemmas-2 *pruned-x86-model*)

  (defmacro create-updater-correspondence-lemmas ()
    (cons 'progn
          (create-updater-correspondence-lemmas-2 *pruned-x86-model*)))

  (local (include-book "centaur/bitops/ihsext-basics" :dir :system))

  (create-updater-correspondence-lemmas)

  (local (in-theory (disable update-nth)))

  (defun create-updater-$a-corr-lemmas-1 (x86-model-field)
    ;; SSR and STR are handled in a different case.  Something to do with the
    ;; length of these fields (2), and proofs proceeding differently...
    (let* ((name (car x86-model-field))
           (type (caddr x86-model-field)))
      (cond ((and (not (equal name 'STR$C))
                  (not (equal name 'SSR-VISIBLE$C))
                  (not (equal name 'SSR-HIDDEN-BASE$C))
                  (not (equal name 'SSR-HIDDEN-LIMIT$C))
                  (not (equal name 'SSR-HIDDEN-ATTR$C))
                  (consp type)
                  (equal (car type) 'array))
             (let* ((length (caaddr (caddr x86-model-field)))
                    (size-num (cadr (cadr  type)))
                    (size (symbol-name (if (< size-num 10)
                                           (acl2::packn (list 0 size-num))
                                         (acl2::packn (list size-num)))))
                    (stripped-name (mk-name
                                    (subseq (symbol-name name) 0
                                            (search "$C"
                                                    (symbol-name
                                                     name)))))
                    (new-constant (mk-name "*" stripped-name "I*"))
                    (constant (mk-name "*" name "I*"))
                    (getter (mk-name stripped-name "$CI"))
                    (setter (mk-name "!" stripped-name "$CI"))
                    (a-getter (mk-name stripped-name "$AI"))
                    (a-setter (mk-name "!" stripped-name "$AI"))
                    (corr-name (mk-name "CORR-" stripped-name))
                    (corr-name-aux (mk-name corr-name "-AUX"))
                    (up-nth (mk-name stripped-name "$CP-UPDATE-NTH"))
                    (recognizer-aux (mk-name stripped-name "P-AUX"))
                    (recognizer (mk-name stripped-name "P"))
                    (recognizer-aux-necc (mk-name stripped-name "P-AUX-NECC"))
                    (recognizer-aux-witness (mk-name stripped-name "P-AUX-WITNESS")))

               `((DEFTHM ,(mk-name "X86$CP-" setter)
                   (IMPLIES (AND (X86$CP X86$C)
                                 (NATP I)
                                 (< I ,length)
                                 (,(if (equal (car (cadr type)) 'signed-byte)
                                       (mk-name "I" size "P")
                                     (mk-name "N" size "P")) V))
                            (X86$CP (,setter I V X86$C)))
                   :HINTS (("GOAL" :IN-THEORY (E/D (X86$CP X86$CP-PRE GOOD-MEMP ,setter)
                                                   (,up-nth))
                            :USE ((:INSTANCE ,up-nth
                                             (X (NTH ,constant X86$C)))))))

                 (DEFTHM ,(mk-name stripped-name "P-S")
                   (IMPLIES (AND (,recognizer ,stripped-name)
                                 (INTEGERP I) ;; index should not be an ill-formed-key.
                                 (,(if (equal (car (cadr type)) 'signed-byte)
                                       (mk-name "I" size "P")
                                     (mk-name "N" size "P")) V))
                            (,recognizer (SZ I V ,stripped-name)))
                   :HINTS (("GOAL"
                            :IN-THEORY (E/D (GZ-OF-SZ-REDUX)
                                            (,recognizer-aux))
                            :USE ((:INSTANCE ,recognizer-aux-necc
                                             (I (,recognizer-aux-witness
                                                 (SZ I V ,stripped-name)))
                                             (X ,stripped-name)))
                            :EXPAND ((,recognizer-aux (SZ I V ,stripped-name))))))

                 (DEFTHM ,(mk-name getter "-" setter)
                   (IMPLIES (AND (NATP I)
                                 (NATP J))
                            (EQUAL (,getter I (,setter J V X86$C))
                                   (IF (EQUAL I J)
                                       V
                                       (,getter I X86$C))))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,setter) ()))))

                 (DEFTHM ,(mk-name a-getter "-" a-setter)
                   (EQUAL (,a-getter I (,a-setter J V X86))
                          (IF (EQUAL I J)
                              ,(if (equal (car (cadr type)) 'unsigned-byte)
                                   `(loghead ,size-num V)
                                 `(logext ,size-num V))
                              (,a-getter I X86)))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,a-getter ,a-setter) ()))))

                 (DEFRULEDL ,(mk-name corr-name "-UPDATE-" stripped-name "-1")
                   (IMPLIES (AND (,corr-name-aux J X86$C (NTH ,new-constant X86))
                                 (NATP J)
                                 (NATP I))
                            (,corr-name-aux J (,setter I V X86$C)
                                            (SZ I V (NTH ,new-constant X86))))
                   :HINTS (("GOAL"
                            :INDUCT (,corr-name-aux J X86$C (NTH ,new-constant X86))
                            :IN-THEORY (e/d () (X86$AP)))))

                 (DEFRULEDL ,(mk-name corr-name "-UPDATE-" stripped-name "-2")
                   (IMPLIES (AND (,corr-name-aux J X86$C (NTH ,new-constant X86))
                                 (NATP J)
                                 (NATP I))
                            (,corr-name-aux J
                                            (UPDATE-NTH ,constant
                                                        (UPDATE-NTH
                                                         I V
                                                         (NTH ,constant X86$C))
                                                        X86$C)
                                            (SZ I V (NTH ,new-constant X86))))
                   :HINTS (("GOAL"
                            :IN-THEORY (e/d (,(mk-name corr-name "-UPDATE-"
                                                       stripped-name "-1")
                                             ,setter)
                                            (X86$AP))
                            :USE ((:INSTANCE ,(mk-name corr-name "-UPDATE-"
                                                       stripped-name "-1"))
                                  ))))

                 (DEFRULEL ,(mk-name corr-name "-UPDATE-" stripped-name)
                   (IMPLIES (AND (,corr-name X86$C (NTH ,new-constant X86))
                                 (NATP I))
                            (,corr-name
                             (UPDATE-NTH ,constant
                                         (UPDATE-NTH
                                          I V
                                          (NTH ,constant X86$C))
                                         X86$C)
                             (SZ I V (NTH ,new-constant X86))))
                   :HINTS (("GOAL"
                            :IN-THEORY (e/d (,setter
                                             ,corr-name)
                                            (X86$AP))
                            :USE ((:INSTANCE ,(mk-name corr-name "-UPDATE-"
                                                       stripped-name "-2")
                                             (j (1- ,length))))))))))
            ((and (or (equal name 'STR$C)
                      (equal name 'SSR-VISIBLE$C)
                      (equal name 'SSR-HIDDEN-BASE$C)
                      (equal name 'SSR-HIDDEN-LIMIT$C)
                      (equal name 'SSR-HIDDEN-ATTR$C))
                  (consp type)
                  (equal (car type) 'array))
             (let* ((length (caaddr (caddr x86-model-field)))
                    (size-num (cadr (cadr  type)))
                    (size (symbol-name (if (< size-num 10)
                                           (acl2::packn (list 0 size-num))
                                         (acl2::packn (list size-num)))))
                    (stripped-name (mk-name
                                    (subseq (symbol-name name) 0
                                            (search "$C"
                                                    (symbol-name name)))))
                    (new-constant (mk-name "*" stripped-name "I*"))
                    (constant (mk-name "*" name "I*"))
                    (getter (mk-name stripped-name "$CI"))
                    (setter (mk-name "!" stripped-name "$CI"))
                    (a-getter (mk-name stripped-name "$AI"))
                    (a-setter (mk-name "!" stripped-name "$AI"))
                    (corr-name (mk-name "CORR-" stripped-name))
                    (up-nth (mk-name stripped-name "$CP-UPDATE-NTH"))
                    (recognizer-aux (mk-name stripped-name "P-AUX"))
                    (recognizer (mk-name stripped-name "P"))
                    (recognizer-aux-necc (mk-name stripped-name "P-AUX-NECC"))
                    (recognizer-aux-witness (mk-name stripped-name "P-AUX-WITNESS")))

               `((DEFTHM ,(mk-name "X86$CP-" getter)
                   (IMPLIES (AND (X86$CP X86$C)
                                 (NATP I)
                                 (< I ,length)
                                 (,(if (equal (car (cadr type)) 'signed-byte)
                                       (mk-name "I" size "P")
                                     (mk-name "N" size "P")) V))
                            (X86$CP (,setter I V X86$C)))
                   :HINTS (("GOAL" :IN-THEORY (E/D (X86$CP X86$CP-PRE GOOD-MEMP ,setter)
                                                   (,up-nth))
                            :USE ((:INSTANCE ,up-nth
                                             (X (NTH ,constant X86$C)))))))

                 (DEFTHM ,(mk-name stripped-name "P-S")
                   (IMPLIES (AND (,recognizer ,stripped-name)
                                 ;; index should not be an
                                 ;; ill-formed-key.
                                 (INTEGERP I)
                                 (,(if (equal (car (cadr type)) 'signed-byte)
                                       (mk-name "I" size "P")
                                     (mk-name "N" size "P")) V))
                            (,recognizer (SZ I V ,stripped-name)))
                   :HINTS (("GOAL"
                            :IN-THEORY (E/D (GZ-OF-SZ-REDUX)
                                            (,recognizer-aux))
                            :USE ((:INSTANCE ,recognizer-aux-necc
                                             (I (,recognizer-aux-witness
                                                 (SZ I V ,stripped-name)))
                                             (X ,stripped-name)))
                            :EXPAND ((,recognizer-aux (SZ I V ,stripped-name))))))

                 (DEFTHM ,(mk-name getter "-" setter)
                   (IMPLIES (AND (NATP I)
                                 (NATP J))
                            (EQUAL (,getter I (,setter J V X86$C))
                                   (IF (EQUAL I J)
                                       V
                                       (,getter I X86$C))))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,getter ,setter) ()))))

                 (DEFTHM ,(mk-name a-getter "-" a-setter)
                   (EQUAL (,a-getter I (,a-setter J V X86))
                          (IF (EQUAL I J)
                              ,(if (equal (car (cadr type)) 'unsigned-byte)
                                   `(loghead ,size-num V)
                                 `(logext ,size-num V))
                              (,a-getter I X86)))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,a-getter ,a-setter) ()))))

                 (DEFRULEL ,(mk-name corr-name "-UPDATE-" stripped-name)
                   (IMPLIES (AND (,corr-name X86$C (NTH ,new-constant X86))
                                 (NATP I)
                                 (,(if (equal (car (cadr type)) 'signed-byte)
                                       (mk-name "I" size "P")
                                     (mk-name "N" size "P")) V))
                            (,corr-name
                             (UPDATE-NTH ,constant
                                         (UPDATE-NTH
                                          I V
                                          (NTH ,constant X86$C))
                                         X86$C)
                             (SZ I V (NTH ,new-constant X86))))
                   :HINTS (("GOAL"
                            :IN-THEORY (e/d (,setter
                                             ,getter
                                             ,corr-name)
                                            (X86$AP))))))))
            (t
             nil))))

  (defun create-updater-$a-corr-lemmas-2 (pruned-x86-model)
    (cond ((endp pruned-x86-model)
           '())
          (t
           `(,@(create-updater-$a-corr-lemmas-1 (car pruned-x86-model))
             ,@(create-updater-$a-corr-lemmas-2
                (cdr pruned-x86-model))))))

  ;; (create-updater-$a-corr-lemmas-2 *pruned-x86-model*)

  (defmacro create-updater-$a-corr-lemmas ()
    (cons 'progn
          (create-updater-$a-corr-lemmas-2 *pruned-x86-model*)))

  (create-updater-$a-corr-lemmas)

  (define hints-for-updater-correspondence-lemmas
    ((field-name symbolp)
     (field-type (or (eql field-type 'array)
                     (eql field-type 'simple))))
    :verify-guards nil

    (b* ((corr-update-thm-name
          (mk-name "CORR-" field-name "-UPDATE-" field-name))
         (constant-name$c
          (mk-name "*" field-name (if (eq field-type 'array) "$CI*" "$C*")))
         (accessor$c
          (mk-name field-name "$C" (if (eq field-type 'array) "I" "")))
         (updater$c
          (mk-name "!" field-name "$C" (if (eq field-type 'array) "I" "")))
         (recognizer$c
          (mk-name field-name "$CP"))
         (x-instance
          (if (eq field-type 'array)
              `(UPDATE-NTH I V (NTH ,constant-name$c X86$C))
            `V)))

      `(("Goal"
         :in-theory
         (e/d (,accessor$c
               ,updater$c ,recognizer$c
               X86$CP X86$CP-PRE GOOD-MEMP)
              (,@(and (equal field-type 'array)
                      `(,corr-update-thm-name))))
         :use (,@(and (equal field-type 'array)
                      `((:instance ,corr-update-thm-name)))
               ,@(and (not (eq field-name 'RGF))
                      `((:instance corr-rgf-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *rgfi* x86)))))
               ,@(and (not (eq field-name 'SEG-VISIBLE))
                      `((:instance corr-seg-visible-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *seg-visiblei* x86)))))
               ,@(and (not (eq field-name 'SEG-HIDDEN-BASE))
                      `((:instance corr-seg-hidden-base-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *seg-hidden-basei* x86)))))
               ,@(and (not (eq field-name 'SEG-HIDDEN-LIMIT))
                      `((:instance corr-seg-hidden-limit-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *seg-hidden-limiti* x86)))))
               ,@(and (not (eq field-name 'SEG-HIDDEN-ATTR))
                      `((:instance corr-seg-hidden-attr-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *seg-hidden-attri* x86)))))
               ,@(and (not (eq field-name 'STR))
                      `((:instance corr-str-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *stri* x86)))))
               ,@(and (not (eq field-name 'SSR-VISIBLE))
                      `((:instance corr-ssr-visible-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *ssr-visiblei* x86)))))
               ,@(and (not (eq field-name 'SSR-HIDDEN-BASE))
                      `((:instance corr-ssr-hidden-base-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *ssr-hidden-basei* x86)))))
               ,@(and (not (eq field-name 'SSR-HIDDEN-LIMIT))
                      `((:instance corr-ssr-hidden-limit-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *ssr-hidden-limiti* x86)))))
               ,@(and (not (eq field-name 'SSR-HIDDEN-ATTR))
                      `((:instance corr-ssr-hidden-attr-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *ssr-hidden-attri* x86)))))
               ,@(and (not (eq field-name 'CTR))
                      `((:instance corr-ctr-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *ctri* x86)))))
               ,@(and (not (eq field-name 'DBG))
                      `((:instance corr-dbg-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *dbgi* x86)))))
               ,@(and (not (eq field-name 'MSR))
                      `((:instance corr-msr-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *msri* x86)))))
               ,@(and (not (eq field-name 'FP-DATA))
                      `((:instance corr-fp-data-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *fp-datai* x86)))))
               ,@(and (not (eq field-name 'ZMM))
                      `((:instance corr-zmm-update-nth
                                   (n ,constant-name$c)
                                   (x ,x-instance)
                                   (x86 X86$C)
                                   (field (nth *zmmi* x86))))))))))

  (DEFRULEL RGFI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *64-bit-general-purpose-registers-len*))
             (EQUAL (RGF$CI I X86$C) (RGF$AI I X86)))
    :hints (("Goal" :use
             ((:instance
               RGFI{CORRESPONDENCE}-helper-2
               (j (1- *64-bit-general-purpose-registers-len*))))
             :in-theory (e/d (corr-rgf) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFRULEL RGFI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *64-bit-general-purpose-registers-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (RGF$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !RGFI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *64-bit-general-purpose-registers-len*)
                    (SIGNED-BYTE-P 64 V))
               (CORR (!RGF$CI I V X86$C)
                     (!RGF$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'RGF 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-rgf-update-rgf))))

  (DEFRULEL !RGFI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *64-bit-general-purpose-registers-len*)
                  (SIGNED-BYTE-P 64 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (RGF$C-LENGTH X86$C))
                  (SIGNED-BYTE-P 64 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !RGFI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *64-bit-general-purpose-registers-len*)
                  (SIGNED-BYTE-P 64 V))
             (X86$AP (!RGF$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL RIP*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (RIP$C X86$C) (RIP$A X86)))
    :hints (("Goal" :in-theory (e/d (rip$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !RIP*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (SIGNED-BYTE-P 48 V))
               (CORR (!RIP$C V X86$C) (!RIP$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'RIP 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !RIP*{PRESERVED}
    (IMPLIES (AND (X86$AP X86) (SIGNED-BYTE-P 48 V))
             (X86$AP (!RIP$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHM RFLAGS*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (RFLAGS$C X86$C) (RFLAGS$A X86)))
    :hints (("Goal" :in-theory (e/d (rflags$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFTHM !RFLAGS*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (UNSIGNED-BYTE-P 32 V))
               (CORR (!RFLAGS$C V X86$C)
                     (!RFLAGS$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'RFLAGS 'simple)
      :RULE-CLASSES NIL))

  (DEFTHM !RFLAGS*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 32 V))
             (X86$AP (!RFLAGS$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL SEG-VISIBLEI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (EQUAL (SEG-VISIBLE$CI I X86$C) (SEG-VISIBLE$AI I X86)))
    :HINTS (("Goal"
             :use ((:instance seg-visiblei{correspondence}-helper-2
                              (j (1- *segment-register-names-len*))))
             :in-theory (e/d (x86$ap corr-seg-visible) ())))
    :RULE-CLASSES NIL)

  (DEFRULEL SEG-VISIBLEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-VISIBLE$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !SEG-VISIBLEI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *segment-register-names-len*)
                    (UNSIGNED-BYTE-P 16 V))
               (CORR (!SEG-VISIBLE$CI I V X86$C)
                     (!SEG-VISIBLE$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'SEG-VISIBLE 'array)
      :rule-classes nil))

  (local (in-theory (e/d () (corr-seg-visible-update-seg-visible))))

  (DEFRULEL !SEG-VISIBLEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-VISIBLE$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 16 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !SEG-VISIBLEI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!SEG-VISIBLE$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL SEG-HIDDEN-BASEI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (EQUAL (SEG-HIDDEN-BASE$CI I X86$C) (SEG-HIDDEN-BASE$AI I X86)))
    :HINTS (("Goal"
             :use ((:instance seg-hidden-basei{correspondence}-helper-2
                              (j (1- *segment-register-names-len*))))
             :in-theory (e/d (x86$ap corr-seg-hidden-base) ())))
    :RULE-CLASSES NIL)

  (DEFRULEL SEG-HIDDEN-BASEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-HIDDEN-BASE$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !SEG-HIDDEN-BASEI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *segment-register-names-len*)
                    (UNSIGNED-BYTE-P 64 V))
               (CORR (!SEG-HIDDEN-BASE$CI I V X86$C)
                     (!SEG-HIDDEN-BASE$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'SEG-HIDDEN-BASE 'array)
      :rule-classes nil))

  (local (in-theory (e/d () (corr-seg-hidden-base-update-seg-hidden-base))))

  (DEFRULEL !SEG-HIDDEN-BASEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-HIDDEN-BASE$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 64 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !SEG-HIDDEN-BASEI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (X86$AP (!SEG-HIDDEN-BASE$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL SEG-HIDDEN-LIMITI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (EQUAL (SEG-HIDDEN-LIMIT$CI I X86$C) (SEG-HIDDEN-LIMIT$AI I X86)))
    :HINTS (("Goal"
             :use ((:instance seg-hidden-limiti{correspondence}-helper-2
                              (j (1- *segment-register-names-len*))))
             :in-theory (e/d (x86$ap corr-seg-hidden-limit) ())))
    :RULE-CLASSES NIL)

  (DEFRULEL SEG-HIDDEN-LIMITI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-HIDDEN-LIMIT$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !SEG-HIDDEN-LIMITI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *segment-register-names-len*)
                    (UNSIGNED-BYTE-P 32 V))
               (CORR (!SEG-HIDDEN-LIMIT$CI I V X86$C)
                     (!SEG-HIDDEN-LIMIT$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'SEG-HIDDEN-LIMIT 'array)
      :rule-classes nil))

  (local (in-theory (e/d () (corr-seg-hidden-limit-update-seg-hidden-limit))))

  (DEFRULEL !SEG-HIDDEN-LIMITI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 32 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-HIDDEN-LIMIT$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 32 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !SEG-HIDDEN-LIMITI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 32 V))
             (X86$AP (!SEG-HIDDEN-LIMIT$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL SEG-HIDDEN-ATTRI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (EQUAL (SEG-HIDDEN-ATTR$CI I X86$C) (SEG-HIDDEN-ATTR$AI I X86)))
    :HINTS (("Goal"
             :use ((:instance seg-hidden-attri{correspondence}-helper-2
                              (j (1- *segment-register-names-len*))))
             :in-theory (e/d (x86$ap corr-seg-hidden-attr) ())))
    :RULE-CLASSES NIL)

  (DEFRULEL SEG-HIDDEN-ATTRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-HIDDEN-ATTR$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !SEG-HIDDEN-ATTRI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *segment-register-names-len*)
                    (UNSIGNED-BYTE-P 16 V))
               (CORR (!SEG-HIDDEN-ATTR$CI I V X86$C)
                     (!SEG-HIDDEN-ATTR$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'SEG-HIDDEN-ATTR 'array)
      :rule-classes nil))

  (local (in-theory (e/d () (corr-seg-hidden-attr-update-seg-hidden-attr))))

  (DEFRULEL !SEG-HIDDEN-ATTRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-HIDDEN-ATTR$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 16 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !SEG-HIDDEN-ATTRI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!SEG-HIDDEN-ATTR$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL STRI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR x86$C x86)
                  (x86$AP x86)
                  (NATP I)
                  (< I *gdtr-idtr-names-len*))
             (EQUAL (STR$CI I x86$C)
                    (STR$AI I x86)))
    :hints (("Goal"
             :use ((:instance stri{correspondence}-helper-2
                              (j (1- *gdtr-idtr-names-len*))))
             :in-theory (e/d (corr-str) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFRULEL STRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *gdtr-idtr-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (STR$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !STRI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *gdtr-idtr-names-len*)
                    (UNSIGNED-BYTE-P 80 V))
               (CORR (!STR$CI I V X86$C)
                     (!STR$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'STR 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-str-update-str))))

  (DEFRULEL !STRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *gdtr-idtr-names-len*)
                  (UNSIGNED-BYTE-P 80 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (STR$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 80 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !STRI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *gdtr-idtr-names-len*)
                  (UNSIGNED-BYTE-P 80 V))
             (X86$AP (!STR$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL SSR-VISIBLEI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (EQUAL (SSR-VISIBLE$CI I X86$C) (SSR-VISIBLE$AI I X86)))
    :HINTS
    (("Goal"
      :use ((:instance ssr-VISIBLEi{correspondence}-helper-2
                       (j (1- *ldtr-tr-names-len*))))
      :in-theory (e/d (corr-ssr-VISIBLE) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFRULEL SSR-VISIBLEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-VISIBLE$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !SSR-VISIBLEI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *ldtr-tr-names-len*)
                    (UNSIGNED-BYTE-P 16 V))
               (CORR (!SSR-VISIBLE$CI I V X86$C)
                     (!SSR-VISIBLE$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'SSR-VISIBLE 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-ssr-visible-update-ssr-visible))))

  (DEFRULEL !SSR-VISIBLEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-VISIBLE$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 16 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !SSR-VISIBLEI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!SSR-VISIBLE$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL SSR-HIDDEN-BASEI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (EQUAL (SSR-HIDDEN-BASE$CI I X86$C) (SSR-HIDDEN-BASE$AI I X86)))
    :HINTS
    (("Goal"
      :use ((:instance ssr-HIDDEN-BASEi{correspondence}-helper-2
                       (j (1- *ldtr-tr-names-len*))))
      :in-theory (e/d (corr-ssr-HIDDEN-BASE) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFRULEL SSR-HIDDEN-BASEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-HIDDEN-BASE$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !SSR-HIDDEN-BASEI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *ldtr-tr-names-len*)
                    (UNSIGNED-BYTE-P 64 V))
               (CORR (!SSR-HIDDEN-BASE$CI I V X86$C)
                     (!SSR-HIDDEN-BASE$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'SSR-HIDDEN-BASE 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-ssr-hidden-base-update-ssr-hidden-base))))

  (DEFRULEL !SSR-HIDDEN-BASEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-HIDDEN-BASE$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 64 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !SSR-HIDDEN-BASEI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (X86$AP (!SSR-HIDDEN-BASE$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL SSR-HIDDEN-LIMITI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (EQUAL (SSR-HIDDEN-LIMIT$CI I X86$C) (SSR-HIDDEN-LIMIT$AI I X86)))
    :HINTS
    (("Goal"
      :use ((:instance ssr-HIDDEN-LIMITi{correspondence}-helper-2
                       (j (1- *ldtr-tr-names-len*))))
      :in-theory (e/d (corr-ssr-HIDDEN-LIMIT) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFRULEL SSR-HIDDEN-LIMITI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-HIDDEN-LIMIT$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !SSR-HIDDEN-LIMITI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *ldtr-tr-names-len*)
                    (UNSIGNED-BYTE-P 32 V))
               (CORR (!SSR-HIDDEN-LIMIT$CI I V X86$C)
                     (!SSR-HIDDEN-LIMIT$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'SSR-HIDDEN-LIMIT 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-ssr-hidden-limit-update-ssr-hidden-limit))))

  (DEFRULEL !SSR-HIDDEN-LIMITI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 32 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-HIDDEN-LIMIT$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 32 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !SSR-HIDDEN-LIMITI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 32 V))
             (X86$AP (!SSR-HIDDEN-LIMIT$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL SSR-HIDDEN-ATTRI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (EQUAL (SSR-HIDDEN-ATTR$CI I X86$C) (SSR-HIDDEN-ATTR$AI I X86)))
    :HINTS
    (("Goal"
      :use ((:instance ssr-HIDDEN-ATTRi{correspondence}-helper-2
                       (j (1- *ldtr-tr-names-len*))))
      :in-theory (e/d (corr-ssr-HIDDEN-ATTR) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFRULEL SSR-HIDDEN-ATTRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-HIDDEN-ATTR$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !SSR-HIDDEN-ATTRI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *ldtr-tr-names-len*)
                    (UNSIGNED-BYTE-P 16 V))
               (CORR (!SSR-HIDDEN-ATTR$CI I V X86$C)
                     (!SSR-HIDDEN-ATTR$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'SSR-HIDDEN-ATTR 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-ssr-hidden-attr-update-ssr-hidden-attr))))

  (DEFRULEL !SSR-HIDDEN-ATTRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-HIDDEN-ATTR$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 16 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !SSR-HIDDEN-ATTRI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!SSR-HIDDEN-ATTR$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL CTRI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *control-register-names-len*))
             (EQUAL (CTR$CI I X86$C) (CTR$AI I X86)))
    :hints
    (("Goal"
      :use ((:instance ctri{correspondence}-helper-2
                       (j (1- *control-register-names-len*))))
      :in-theory (e/d (corr-ctr) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFRULEL CTRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *control-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (CTR$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !CTRI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *control-register-names-len*)
                    (UNSIGNED-BYTE-P 64 V))
               (CORR (!CTR$CI I V X86$C)
                     (!CTR$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'CTR 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-ctr-update-ctr))))

  (DEFRULEL !CTRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *control-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (CTR$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 64 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !CTRI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *control-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (X86$AP (!CTR$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL DBGI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *debug-register-names-len*))
             (EQUAL (DBG$CI I X86$C) (DBG$AI I X86)))
    :hints
    (("Goal"
      :use ((:instance dbgi{correspondence}-helper-2
                       (j (1- *debug-register-names-len*))))
      :in-theory (e/d (corr-dbg) (x86$ap corr-dbg-aux))))
    :RULE-CLASSES NIL)

  (DEFRULEL DBGI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *debug-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (DBG$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !DBGI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *debug-register-names-len*)
                    (UNSIGNED-BYTE-P 64 V))
               (CORR (!DBG$CI I V X86$C)
                     (!DBG$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'DBG 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-dbg-update-dbg))))

  (DEFRULEL !DBGI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *debug-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (DBG$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 64 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !DBGI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *debug-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (X86$AP (!DBG$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL FP-DATAI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *fp-data-register-names-len*))
             (EQUAL (FP-DATA$CI I X86$C)
                    (FP-DATA$AI I X86)))
    :hints (("Goal" :use
             ((:instance
               FP-DATAI{CORRESPONDENCE}-helper-2
               (j (1- *fp-data-register-names-len*))))
             :in-theory (e/d (corr-fp-data) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFRULEL FP-DATAI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 8))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (FP-DATA$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)


  (make-event
   `(DEFRULEL !FP-DATAI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I 8)
                    (UNSIGNED-BYTE-P 80 V))
               (CORR (!FP-DATA$CI I V X86$C)
                     (!FP-DATA$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'FP-DATA 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-fp-data-update-fp-data))))

  (DEFRULEL !FP-DATAI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 8)
                  (UNSIGNED-BYTE-P 80 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (FP-DATA$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 80 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !FP-DATAI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I 8)
                  (UNSIGNED-BYTE-P 80 V))
             (X86$AP (!FP-DATA$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL FP-CTRL*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-CTRL$C X86$C)
                    (FP-CTRL$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-ctrl$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !FP-CTRL*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (UNSIGNED-BYTE-P 16 V))
               (CORR (!FP-CTRL$C V X86$C)
                     (!FP-CTRL$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'FP-CTRL 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !FP-CTRL*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!FP-CTRL$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL FP-STATUS*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-STATUS$C X86$C)
                    (FP-STATUS$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-status$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !FP-STATUS*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (UNSIGNED-BYTE-P 16 V))
               (CORR (!FP-STATUS$C V X86$C)
                     (!FP-STATUS$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'FP-STATUS 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !FP-STATUS*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!FP-STATUS$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL FP-TAG*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-TAG$C X86$C) (FP-TAG$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-tag$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !FP-TAG*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (UNSIGNED-BYTE-P 16 V))
               (CORR (!FP-TAG$C V X86$C)
                     (!FP-TAG$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'FP-TAG 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !FP-TAG*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!FP-TAG$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL FP-LAST-INST*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-LAST-INST$C X86$C)
                    (FP-LAST-INST$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-last-inst$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !FP-LAST-INST*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (UNSIGNED-BYTE-P 48 V))
               (CORR (!FP-LAST-INST$C V X86$C)
                     (!FP-LAST-INST$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'FP-LAST-INST 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !FP-LAST-INST*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 48 V))
             (X86$AP (!FP-LAST-INST$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL FP-LAST-DATA*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-LAST-DATA$C X86$C)
                    (FP-LAST-DATA$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-last-data$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !FP-LAST-DATA*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (UNSIGNED-BYTE-P 48 V))
               (CORR (!FP-LAST-DATA$C V X86$C)
                     (!FP-LAST-DATA$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'FP-LAST-DATA 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !FP-LAST-DATA*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 48 V))
             (X86$AP (!FP-LAST-DATA$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL FP-OPCODE*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-OPCODE$C X86$C)
                    (FP-OPCODE$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-opcode$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !FP-OPCODE*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (UNSIGNED-BYTE-P 11 V))
               (CORR (!FP-OPCODE$C V X86$C)
                     (!FP-OPCODE$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'FP-OPCODE 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !FP-OPCODE*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 11 V))
             (X86$AP (!FP-OPCODE$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL ZMMI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 32))
             (EQUAL (ZMM$CI I X86$C) (ZMM$AI I X86)))
    :hints (("Goal" :use ((:instance ZMMI{CORRESPONDENCE}-helper-2 (j 31)))
             :in-theory (e/d (corr-zmm) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFRULEL ZMMI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 32))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (ZMM$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !ZMMI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I 32)
                    (UNSIGNED-BYTE-P 512 V))
               (CORR (!ZMM$CI I V X86$C)
                     (!ZMM$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'ZMM 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-zmm-update-zmm))))

  (DEFRULEL !ZMMI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 32)
                  (UNSIGNED-BYTE-P 512 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (ZMM$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 512 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !ZMMI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I 32)
                  (UNSIGNED-BYTE-P 512 V))
             (X86$AP (!ZMM$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL MXCSR*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (MXCSR$C X86$C) (MXCSR$A X86)))
    :hints (("Goal" :in-theory (e/d (mxcsr$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !MXCSR*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (UNSIGNED-BYTE-P 32 V))
               (CORR (!MXCSR$C V X86$C)
                     (!MXCSR$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'MXCSR 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !MXCSR*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 32 V))
             (X86$AP (!MXCSR$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL MSRI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *model-specific-register-names-len*))
             (EQUAL (MSR$CI I X86$C) (MSR$AI I X86)))
    :hints
    (("Goal"
      :use ((:instance msri{correspondence}-helper-2
                       (j (1- *model-specific-register-names-len*))))
      :in-theory (e/d (corr-msr) (x86$ap corr-msr-aux))))
    :RULE-CLASSES NIL)

  (DEFRULEL MSRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *model-specific-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (MSR$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !MSRI*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (NATP I)
                    (< I *model-specific-register-names-len*)
                    (UNSIGNED-BYTE-P 64 V))
               (CORR (!MSR$CI I V X86$C)
                     (!MSR$AI I V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'MSR 'array)
      :RULE-CLASSES NIL))

  (local (in-theory (e/d () (corr-msr-update-msr))))

  (DEFRULEL !MSRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *model-specific-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (MSR$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 64 V)))
    :RULE-CLASSES NIL)

  (DEFRULEL !MSRI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *model-specific-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (X86$AP (!MSR$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL MS*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (MS$C X86$C) (MS$A X86)))
    :hints (("Goal" :in-theory (e/d (ms$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !MS*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
               (CORR (!MS$C V X86$C) (!MS$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'MS 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !MS*{PRESERVED}
    (IMPLIES (X86$AP X86)
             (X86$AP (!MS$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL FAULT*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FAULT$C X86$C) (FAULT$A X86)))
    :hints (("Goal" :in-theory (e/d (fault$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !FAULT*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
               (CORR (!FAULT$C V X86$C)
                     (!FAULT$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'FAULT 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !FAULT*{PRESERVED}
    (IMPLIES (X86$AP X86)
             (X86$AP (!FAULT$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL ENV*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (ENV$C X86$C)
                    (ENV$A X86)))
    :hints (("Goal" :in-theory (e/d (env$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !ENV*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (ENV-ALISTP V))
               (CORR (!ENV$C V X86$C)
                     (!ENV$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'ENV 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !ENV*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (ENV-ALISTP V))
             (X86$AP (!ENV$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL UNDEF*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (UNDEF$C X86$C) (UNDEF$A X86)))
    :hints (("Goal" :in-theory (e/d (undef$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !UNDEF*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
               (CORR (!UNDEF$C V X86$C)
                     (!UNDEF$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'UNDEF 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !UNDEF*{PRESERVED}
    (IMPLIES (X86$AP X86)
             (X86$AP (!UNDEF$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL APP-VIEW*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (APP-VIEW$C X86$C)
                    (APP-VIEW$A X86)))
    :hints (("Goal" :in-theory (e/d (app-view$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !APP-VIEW*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (BOOLEANP V))
               (CORR (!APP-VIEW$C V X86$C)
                     (!APP-VIEW$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'APP-VIEW 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !APP-VIEW*{PRESERVED}
    (IMPLIES (AND (X86$AP X86) (BOOLEANP V))
             (X86$AP (!APP-VIEW$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL MARKING-VIEW*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (MARKING-VIEW$C X86$C)
                    (MARKING-VIEW$A X86)))
    :hints (("Goal" :in-theory (e/d (marking-view$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !MARKING-VIEW*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (BOOLEANP V))
               (CORR (!MARKING-VIEW$C V X86$C)
                     (!MARKING-VIEW$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'MARKING-VIEW 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !MARKING-VIEW*{PRESERVED}
    (IMPLIES (AND (X86$AP X86) (BOOLEANP V))
             (X86$AP (!MARKING-VIEW$A V X86)))
    :RULE-CLASSES NIL)

  (DEFRULEL OS-INFO*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (OS-INFO$C X86$C)
                    (OS-INFO$A X86)))
    :hints (("Goal" :in-theory (e/d (os-info$c) ())))
    :RULE-CLASSES NIL)

  (make-event
   `(DEFRULEL !OS-INFO*{CORRESPONDENCE}
      (IMPLIES (AND (CORR X86$C X86)
                    (X86$AP X86)
                    (KEYWORDP V))
               (CORR (!OS-INFO$C V X86$C)
                     (!OS-INFO$A V X86)))
      :hints ,(hints-for-updater-correspondence-lemmas 'OS-INFO 'simple)
      :RULE-CLASSES NIL))

  (DEFRULEL !OS-INFO*{PRESERVED}
    (IMPLIES (AND (X86$AP X86) (KEYWORDP V))
             (X86$AP (!OS-INFO$A V X86)))
    :RULE-CLASSES NIL)

  (encapsulate
    ()

    (local (include-book "arithmetic/top-with-meta" :dir :system))

    (defthm corr-mem-suff
      (let ((i (corr-mem-witness x alist)))
        (implies (equal (mem$ci i x) (gz i alist))
                 (corr-mem x alist)))
      :hints (("Goal" :in-theory (enable corr-mem))))

    (defthm nth-!mem$ci-is-no-op
      (implies (and (not (equal n *mem-tablei*))
                    (not (equal n *mem-arrayi*))
                    (not (equal n *mem-array-next-addr*)))
               (equal (nth n (!mem$ci i v x86$c))
                      (nth n x86$c)))
      :hints (("Goal" :in-theory (e/d
                                  (!mem$ci
                                   !mem-arrayi
                                   !mem-tablei
                                   !mem-array-next-addr
                                   add-page-x86$c)
                                  (natp-mem-tablep-when-valid-mem-table-index
                                   force (force))))))

    (in-theory (disable corr-mem-necc))

    (defthm corr-mem-necc-rewrite
      (implies (and (corr-mem x86$c field)
                    (x86$cp x86$c)
                    (force (integerp i))
                    (force (<= 0 i))
                    (force (< i *2^52*)))
               (equal (mem$ci i x86$c)
                      (loghead 8 (gz i field))))
      :hints (("Goal"
               :in-theory (e/d ()
                               (corr-mem-necc
                                n08p-mem$ci))
               :use ((:instance corr-mem-necc)
                     (:instance n08p-mem$ci
                                (addr i))))))

    (local
     (defthmd corr-mem-necc-rewrite-simple
       (implies (and (corr-mem x86$c field)
                     (force (integerp i))
                     (force (<= 0 i))
                     (force (< i *2^52*)))
                (equal (mem$ci i x86$c)
                       (gz i field)))
       :hints (("Goal"
                :in-theory (e/d ()
                                (corr-mem-necc))
                :use ((:instance corr-mem-necc))))))


    (defthm !memi{correspondence}-1
      (implies (and (x86$cp-pre x86$c)
                    (good-memp x86$c)
                    (corr-mem x86$c
                              (nth *memi* x86))
                    (natp i)
                    (< i 4503599627370496)
                    (n08p v))
               (corr-mem (!mem$ci i v x86$c)
                         (sz i v (nth *memi* x86))))
      :hints (("Goal"
               :in-theory (e/d (x86$cp
                                corr-mem-necc-rewrite-simple)
                               (memp mem-table-length mem-array-length
                                     good-memp good-mem-arrayp
                                     unsigned-byte-p))
               :expand ((corr-mem (!mem$ci i v x86$c)
                                  (sz i v (nth *memi* x86)))))))

    (defthm !memi{correspondence}-2
      (implies (and (corr x86$c x86)
                    (x86$ap x86)
                    (natp i)
                    (< i 4503599627370496)
                    (n08p v))
               (corr-mem (!mem$ci i v x86$c)
                         (nth *memi* (!mem$ai i v x86))))
      :hints (("Goal"
               :in-theory
               (e/d (x86$cp corr-mem-necc-rewrite-simple)
                    (memp mem-table-length mem-array-length good-memp
                          good-mem-arrayp)))))

    ) ;; End of encapsulate

  (DEFRULEL MEMI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 4503599627370496))
             (EQUAL (MEM$CI I X86$C)
                    (MEM$AI I X86)))
    :RULE-CLASSES NIL)

  (DEFTHM MEMI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 4503599627370496))
             (AND (UNSIGNED-BYTE-P 52 I)
                  (X86$CP X86$C)))
    :RULE-CLASSES NIL)

  (defthm memp-s
    (implies (and (memp mem)
                  ;; i should not be an ill-formed-key.
                  (integerp i)
                  ;; (n52p i)
                  (n08p v))
             (memp (sz i v mem)))
    :hints (("Goal"
             :in-theory (e/d (gz-of-sz-redux)
                             (memp-aux))
             :use ((:instance memp-aux-necc
                              (i (memp-aux-witness (sz i v mem)))
                              (x mem)))
             :expand ((memp-aux (sz i v mem))))))

  (DEFRULEL x86$ap-!mem$ai
    (IMPLIES (AND (CORR x86$C x86)
                  (x86$AP x86)
                  (NATP I)
                  (< I 4503599627370496)
                  (N08P V))
             (X86$AP (!MEM$AI I V x86)))
    :hints (("Goal" :in-theory (e/d (memp)))))

  (defun create-mem-correspondence-corr-lemmas-1 (x86-model-field)
    (let* ((name (car x86-model-field))
           (type (caddr x86-model-field)))
      (cond ((and (consp type)
                  (equal (car type) 'array))
             (let* ((length (caaddr (caddr x86-model-field)))
                    (stripped-name (mk-name
                                    (subseq (symbol-name name) 0
                                            (search "$C"
                                                    (symbol-name name)))))
                    (constant (mk-name "*" stripped-name "I*"))
                    (getter (mk-name stripped-name "$CI"))
                    (corr-name (mk-name "CORR-" stripped-name))
                    (corr-name-aux (mk-name corr-name "-AUX")))

               `((LOCAL
                  (DEFTHMD ,(mk-name getter "-!MEM$CI")
                    (IMPLIES (AND (NATP I)
                                  (< I *MEM-SIZE-IN-BYTES*)
                                  (NATP J)
                                  (< J ,length)
                                  (N08P V)
                                  (X86$CP X86$C))
                             (EQUAL (,getter J (!MEM$CI I V X86$C))
                                    (,getter J X86$C)))
                    :HINTS (("GOAL" :IN-THEORY (E/D (,getter)
                                                    ())))))

                 (LOCAL
                  (DEFTHMD ,(mk-name corr-name-aux "-!MEMI")
                    (IMPLIES (AND (,corr-name-aux J X86$C (NTH ,constant X86))
                                  (X86$CP X86$C)
                                  (X86$AP X86)
                                  (INTEGERP I)
                                  (<= 0 I)
                                  (< I *MEM-SIZE-IN-BYTES*)
                                  (N08P V)
                                  (NATP J)
                                  (< J ,length))
                             (,corr-name-aux J (!MEM$CI I V X86$C)
                                             (NTH ,constant (!MEM$AI I V X86))))
                    :HINTS (("GOAL" :IN-THEORY (E/D (,(mk-name getter "-!MEM$CI"))
                                                    (X86$AP))
                             :INDUCT (,corr-name-aux J X86$C (NTH ,constant X86))))))

                 (DEFRULEL ,(mk-name corr-name "-!MEMI")
                   (IMPLIES (AND (,corr-name X86$C (NTH ,constant X86))
                                 (X86$CP X86$C)
                                 (X86$AP X86)
                                 (INTEGERP I)
                                 (<= 0 I)
                                 (< I *MEM-SIZE-IN-BYTES*)
                                 (N08P V))
                            (,corr-name (!MEM$CI I V X86$C)
                                        (NTH ,constant (!MEM$AI I V X86))))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,corr-name)
                                                   (X86$AP))
                            :USE ((:INSTANCE ,(mk-name corr-name-aux "-!MEMI")
                                             (J (1- ,length)))))))
                 )))
            (t
             nil))))

  (defun create-mem-correspondence-corr-lemmas-2 (pruned-x86-model)
    (cond ((endp pruned-x86-model)
           '())
          (t
           `(,@(create-mem-correspondence-corr-lemmas-1 (car pruned-x86-model))
             ,@(create-mem-correspondence-corr-lemmas-2
                (cdr pruned-x86-model))))))

  ;; (create-mem-correspondence-corr-lemmas-2 *pruned-x86-model*)

  (defmacro create-mem-correspondence-corr-lemmas ()
    (cons 'progn
          (create-mem-correspondence-corr-lemmas-2 *pruned-x86-model*)))

  (create-mem-correspondence-corr-lemmas)

  (DEFRULEL !MEMI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR x86$C x86)
                  (x86$AP x86)
                  (NATP I)
                  (< I 4503599627370496)
                  (UNSIGNED-BYTE-P 8 V))
             (CORR (!MEM$CI I V X86$C)
                   (!MEM$AI I V X86)))
    :hints (("Goal"
             :in-theory (e/d ()
                             (nth-!mem$ci-is-no-op
                              nth
                              x86$ap
                              !mem$ai
                              x86$ap-!mem$ai
                              force
                              (force)))
             :expand (corr (!mem$ci i v x86$c)
                           (!mem$ai i v x86)))
            ;; No hints for Goal', Goal'', and Goal'''.
            (if (and (equal (car id) '(0))
                     (equal (cadr id) nil)
                     (not (equal (cddr id) 0)))
                '(:no-op t)
              nil)
            '(:in-theory (e/d (!mem$ai) ())))
    :RULE-CLASSES NIL)

  (DEFTHM !MEMI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 4503599627370496)
                  (UNSIGNED-BYTE-P 8 V))
             (AND (UNSIGNED-BYTE-P 52 I)
                  (UNSIGNED-BYTE-P 8 V)
                  (N08P V)
                  (X86$CP X86$C)))
    :RULE-CLASSES NIL)

  (DEFRULEL !MEMI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I 4503599627370496)
                  (UNSIGNED-BYTE-P 8 V))
             (X86$AP (!MEM$AI I V X86)))
    :RULE-CLASSES NIL)

  ;; x86
  (create-x86-abstract-stobj))

;; ======================================================================

;; Disabling some functions/rules:

(in-theory (disable memp-aux))

;; Mechanism to disable abstract stobj functions (via rulesets):

(defun disable-abs-stobj-fns-fn (x86-model)
  (cond ((endp x86-model)
         '())
        (t
         (let* ((name (car (car x86-model)))
                (name (mk-name (subseq (symbol-name name) 0
                                       (search "$C" (symbol-name name)))))
                (type (caddr (car x86-model))))
           (cond ((and (consp type)
                       (equal (car type) 'array))
                  (let* ((namei*    (mk-name name "I*"))
                         (getter    namei*)
                         (setter    (mk-name "!" namei*))
                         (recognizer (mk-name name "P")))
                    (append `(,getter
                              ,setter
                              ,recognizer)
                            (disable-abs-stobj-fns-fn (cdr x86-model)))))
                 (t
                  (let* ((name* (mk-name name "*"))
                         (getter  name*)
                         (setter  (mk-name "!" name*))
                         (recognizer (mk-name name "P")))
                    (append `(,getter ,setter ,recognizer)
                            (disable-abs-stobj-fns-fn
                             (cdr x86-model))))))))))

(defmacro create-abstract-stobj-fns-ruleset (x86-model)
  `(DEF-RULESET abstract-stobj-fns-ruleset
     (quote ,(disable-abs-stobj-fns-fn x86-model))))

(make-event
 `(create-abstract-stobj-fns-ruleset
   ,*pruned-x86-model-modified-mem*))

;; ======================================================================

;; Uniform accessor and updater functions:

(defsection x86-state-accessor-and-updater

  :parents (abstract-state)

  :short "Definitions of the top-level accessor and updater functions
  for the x86 state"

  (define xr ((fld symbolp) (index natp) x86)
    :enabled t
    :guard (and (member fld *x86-field-names-as-keywords*)
                (case fld
                  (:rgf
                   (< index #.*64-bit-general-purpose-registers-len*))
                  ((:seg-visible
                    :seg-hidden-base :seg-hidden-limit :seg-hidden-attr)
                   (< index #.*segment-register-names-len*))
                  (:str
                   (< index #.*gdtr-idtr-names-len*))
                  ((:ssr-visible
                    :ssr-hidden-base :ssr-hidden-limit :ssr-hidden-attr)
                   (< index #.*ldtr-tr-names-len*))
                  (:ctr
                   (< index #.*control-register-names-len*))
                  (:dbg
                   (< index #.*debug-register-names-len*))
                  (:fp-data
                   (< index #.*fp-data-register-names-len*))
                  (:zmm
                   (< index #.*zmm-register-names-len*))
                  (:msr
                   (< index #.*model-specific-register-names-len*))
                  (:mem
                   (< index #.*mem-size-in-bytes*))
                  (otherwise
                   (equal index 0))))

    (case fld
      (:rgf                         (rgfi* index x86))
      (:rip                         (rip* x86))
      (:rflags                      (rflags* x86))
      (:seg-visible                 (seg-visiblei* index x86))
      (:seg-hidden-base             (seg-hidden-basei* index x86))
      (:seg-hidden-limit            (seg-hidden-limiti* index x86))
      (:seg-hidden-attr             (seg-hidden-attri* index x86))
      (:str                         (stri* index x86))
      (:ssr-visible                 (ssr-visiblei* index x86))
      (:ssr-hidden-base             (ssr-hidden-basei* index x86))
      (:ssr-hidden-limit            (ssr-hidden-limiti* index x86))
      (:ssr-hidden-attr             (ssr-hidden-attri* index x86))
      (:ctr                         (ctri* index x86))
      (:dbg                         (dbgi* index x86))
      (:fp-data                     (fp-datai* index x86))
      (:fp-ctrl                     (fp-ctrl* x86))
      (:fp-status                   (fp-status* x86))
      (:fp-tag                      (fp-tag* x86))
      (:fp-last-inst                (fp-last-inst* x86))
      (:fp-last-data                (fp-last-data* x86))
      (:fp-opcode                   (fp-opcode* x86))
      (:zmm                         (zmmi* index x86))
      (:mxcsr                       (mxcsr* x86))
      (:msr                         (msri* index x86))
      (:ms                          (ms* x86))
      (:fault                       (fault* x86))
      (:env                         (env* x86))
      (:undef                       (undef* x86))
      (:app-view                    (app-view* x86))
      (:marking-view                (marking-view* x86))
      (:os-info                     (os-info* x86))
      (:mem                         (memi* index x86))
      (otherwise                    nil)))

  (define xw ((fld symbolp)
              (index natp)
              value x86)
    :enabled t
    :guard (and (member fld *x86-field-names-as-keywords*)
                (case fld
                  (:rgf
                   (and (< index #.*64-bit-general-purpose-registers-len*)
                        (signed-byte-p 64 value)))
                  (:rip
                   (and (equal index 0)
                        (signed-byte-p 48 value)))
                  (:rflags
                   (and (equal index 0)
                        (unsigned-byte-p 32 value)))
                  (:seg-visible
                   (and (< index #.*segment-register-names-len*)
                        (unsigned-byte-p 16 value)))
                  (:seg-hidden-base
                   (and (< index #.*segment-register-names-len*)
                        (unsigned-byte-p 64 value)))
                  (:seg-hidden-limit
                   (and (< index #.*segment-register-names-len*)
                        (unsigned-byte-p 32 value)))
                  (:seg-hidden-attr
                   (and (< index #.*segment-register-names-len*)
                        (unsigned-byte-p 16 value)))
                  (:str
                   (and (< index #.*gdtr-idtr-names-len*)
                        (unsigned-byte-p 80 value)))
                  (:ssr-visible
                   (and (< index #.*ldtr-tr-names-len*)
                        (unsigned-byte-p 16 value)))
                  (:ssr-hidden-base
                   (and (< index #.*ldtr-tr-names-len*)
                        (unsigned-byte-p 64 value)))
                  (:ssr-hidden-limit
                   (and (< index #.*ldtr-tr-names-len*)
                        (unsigned-byte-p 32 value)))
                  (:ssr-hidden-attr
                   (and (< index #.*ldtr-tr-names-len*)
                        (unsigned-byte-p 16 value)))
                  (:ctr
                   (and (< index #.*control-register-names-len*)
                        (unsigned-byte-p 64 value)))
                  (:dbg
                   (and (< index #.*debug-register-names-len*)
                        (unsigned-byte-p 64 value)))
                  (:fp-data
                   (and (< index #.*fp-data-register-names-len*)
                        (unsigned-byte-p 80 value)))
                  (:fp-ctrl
                   (and (equal index 0)
                        (unsigned-byte-p 16 value)))
                  (:fp-status
                   (and (equal index 0)
                        (unsigned-byte-p 16 value)))
                  (:fp-tag
                   (and (equal index 0)
                        (unsigned-byte-p 16 value)))
                  (:fp-last-inst
                   (and (equal index 0)
                        (unsigned-byte-p 48 value)))
                  (:fp-last-data
                   (and (equal index 0)
                        (unsigned-byte-p 48 value)))
                  (:fp-opcode
                   (and (equal index 0)
                        (unsigned-byte-p 11 value)))
                  (:zmm
                   (and (< index #.*zmm-register-names-len*)
                        (unsigned-byte-p 512 value)))
                  (:mxcsr
                   (and (equal index 0)
                        (unsigned-byte-p 32 value)))
                  (:msr
                   (and (< index #.*model-specific-register-names-len*)
                        (unsigned-byte-p 64 value)))
                  (:ms
                   (equal index 0))
                  (:fault
                   (equal index 0))
                  (:env
                   (and (equal index 0)
                        (env-alistp value)))
                  (:undef
                   (equal index 0))
                  (:app-view
                   (and (equal index 0)
                        (booleanp value)))
                  (:marking-view
                   (and (equal index 0)
                        (booleanp value)))
                  (:os-info
                   (and (equal index 0)
                        (keywordp value)))
                  (:mem
                   (and (< index #.*mem-size-in-bytes*)
                        (unsigned-byte-p 8 value)))
                  (otherwise
                   (equal index 0))))

    (case fld
      (:rgf                         (!rgfi* index value x86))
      (:rip                         (!rip* value x86))
      (:rflags                      (!rflags* value x86))
      (:seg-visible                 (!seg-visiblei* index value x86))
      (:seg-hidden-base             (!seg-hidden-basei* index value x86))
      (:seg-hidden-limit            (!seg-hidden-limiti* index value x86))
      (:seg-hidden-attr             (!seg-hidden-attri* index value x86))
      (:str                         (!stri* index value x86))
      (:ssr-visible                 (!ssr-visiblei* index value x86))
      (:ssr-hidden-base             (!ssr-hidden-basei* index value x86))
      (:ssr-hidden-limit            (!ssr-hidden-limiti* index value x86))
      (:ssr-hidden-attr             (!ssr-hidden-attri* index value x86))
      (:ctr                         (!ctri* index value x86))
      (:dbg                         (!dbgi* index value x86))
      (:fp-data                     (!fp-datai* index value x86))
      (:fp-ctrl                     (!fp-ctrl* value x86))
      (:fp-status                   (!fp-status* value x86))
      (:fp-tag                      (!fp-tag* value x86))
      (:fp-last-inst                (!fp-last-inst* value x86))
      (:fp-last-data                (!fp-last-data* value x86))
      (:fp-opcode                   (!fp-opcode* value x86))
      (:zmm                         (!zmmi* index value x86))
      (:mxcsr                       (!mxcsr* value x86))
      (:msr                         (!msri* index value x86))
      (:ms                          (!ms* value x86))
      (:fault                       (!fault* value x86))
      (:env                         (!env* value x86))
      (:undef                       (!undef* value x86))
      (:app-view                    (!app-view* value x86))
      (:marking-view                (!marking-view* value x86))
      (:os-info                     (!os-info* value x86))
      (:mem                         (!memi* index value x86))
      (otherwise                    x86)))

  ;; Keep all the individual accessor and updater functions below
  ;; enabled and the universal accessor and updater functions (xr and
  ;; xw, respectively) disabled. The idea is that we will reason using
  ;; xr and xw (e.g., proving RoW/WoW theorems), but the execution will
  ;; be done using the fast concrete stobj functions.

  (defun x86-top-accessors-and-updaters-1 (x86-model-field)
    ;; This function assumes that x86-model-field is defined using the
    ;; same syntax as that for a field in a defstobj definition.
    (let ((name (car x86-model-field))
          (type (caddr x86-model-field)))

      (cond

       ((and (consp type)
             (equal (car type) 'array)
             (consp (cadr type)))
        ;; We assume that there is no resizable array.  The memory was a
        ;; resizable array in the concrete stobj, but we handle memory
        ;; differently in the abstract stobj.
        (b* ((name     (subseq (symbol-name name) 0
                               (search "$C" (symbol-name name))))
             (sname     (mk-name name))
             (getter    (mk-name sname "I"))
             (setter    (mk-name "!" sname "I"))
             (getter*   (mk-name getter "*"))
             (setter*   (mk-name setter "*"))
             (keyword   (intern name "KEYWORD"))
             (size      (cadr (cadr type)))
             (length    (caaddr (caddr x86-model-field))))
          `((DEFINE ,getter ((I :TYPE (INTEGER 0 ,(1- length)))
                             X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XR ,keyword I X86)
                   :EXEC (,getter* I X86)))

            (DEFINE ,setter ((I :TYPE (INTEGER 0 ,(1- length)))
                             (V :TYPE (,(car (cadr type)) ,size))
                             X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XW ,keyword I V X86)
                   :EXEC (,setter* I V X86))))))

       ((and (consp type)
             (or (equal (car type) 'unsigned-byte)
                 (equal (car type) 'signed-byte)))
        (b* ((name      (subseq (symbol-name name) 0
                                (search "$C" (symbol-name
                                              name))))
             (sname     (mk-name name))
             (getter    sname)
             (setter    (mk-name "!" sname))
             (getter*   (mk-name sname "*"))
             (setter*   (mk-name "!" sname "*"))
             (keyword   (intern name "KEYWORD"))
             (size      (cadr type)))
          `((DEFINE ,getter (X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XR ,keyword 0 X86)
                   :EXEC (,getter* X86)))
            (DEFINE ,setter ((V :TYPE (,(car type) ,size))
                             X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XW ,keyword 0 V X86)
                   :EXEC (,setter* V X86))))))

       ((and (consp type)
             (equal (car type) 'integer))
        (b* ((name      (subseq (symbol-name name) 0
                                (search "$C" (symbol-name
                                              name))))
             (sname     (mk-name name))
             (getter    sname)
             (setter    (mk-name "!" sname))
             (getter*   (mk-name getter "*"))
             (setter*   (mk-name setter "*"))
             (keyword   (intern name "KEYWORD"))
             (min      (cadr type))
             (max      (caddr type)))
          `((DEFINE ,getter (X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XR ,keyword 0 X86)
                   :EXEC (,getter* X86)))
            (DEFINE ,setter ((V :TYPE (INTEGER ,min ,max))
                             X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XW ,keyword 0 V X86)
                   :EXEC (,setter* V X86))))))

       ((and (consp type)
             (equal (car type) 'satisfies))
        ;; E.g.: env field
        (b* ((name      (subseq (symbol-name name) 0
                                (search "$C" (symbol-name
                                              name))))
             (sname      (mk-name name))
             (predicate  (cadr type))
             (getter     sname)
             (setter     (mk-name "!" sname))
             (getter*    (mk-name getter "*"))
             (setter*    (mk-name setter "*"))
             (keyword    (intern name "KEYWORD")))
          `((DEFINE ,getter (X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XR ,keyword 0 X86)
                   :EXEC (,getter* X86)))
            (DEFINE ,setter ((V :TYPE (SATISFIES ,predicate))
                             X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XW ,keyword 0 V X86)
                   :EXEC (,setter* V X86))))))

       (t
        ;; type is T
        (b* ((name      (subseq (symbol-name name) 0
                                (search "$C" (symbol-name
                                              name))))
             (sname     (mk-name name))
             (getter    sname)
             (setter    (mk-name "!" sname))
             (getter*   (mk-name getter "*"))
             (setter*   (mk-name setter "*"))
             (keyword   (intern name "KEYWORD")))
          `((DEFINE ,getter (X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XR ,keyword 0 X86)
                   :EXEC (,getter* X86)))
            (DEFINE ,setter (V X86)
              :PARENTS NIL
              :INLINE T
              :NO-FUNCTION T
              :ENABLED T
              (MBE :LOGIC (XW ,keyword 0 V X86)
                   :EXEC (,setter* V X86)))))))))

  (defun x86-top-accessors-and-updaters-2 (x86-model)
    (cond ((endp x86-model)
           '())
          (t
           `(,@(x86-top-accessors-and-updaters-1 (car x86-model))
             ,@(x86-top-accessors-and-updaters-2
                (cdr x86-model))))))

  (defmacro x86-top-accessors-and-updaters ()
    (cons 'progn
          (x86-top-accessors-and-updaters-2 *pruned-x86-model-modified-mem*)))


  ;; See the end of x86-state-field-thms.lisp.
  (local (in-theory (e/d* () (abstract-stobj-fns-ruleset x86p))))

  (x86-top-accessors-and-updaters))

;; ======================================================================

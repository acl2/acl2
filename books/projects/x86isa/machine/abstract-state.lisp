;; Authors:
;; Shilpi Goel <shigoel@cs.utexas.edu>
;; Matt Kaufmann <kaufmann@cs.utexas.edu>

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
                                (#.*MEM-SIZE-IN-BYTES*))))))

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
       (len-const-names (+ 1 (len abstract-const-names))))
      `(defconsts
         ,(append abstract-const-names `(*x86-abs-stobj-len*))
         ,(b* ((lst (gl-int 0 1 len-const-names)))
              (cons 'mv lst)))))

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
                    (size      (cadr (cadr type)))
                    (size (symbol-name (if (< size 10)
                                           (acl2::packn (list 0 size))
                                         (acl2::packn (list size))))))

               `((DEFUN-SK ,recognizer-aux (X)
                   (FORALL I
                           (,(if (equal (car (cadr type))
                                        'unsigned-byte)
                                 (mk-name "N" size "P")
                               (mk-name "I" size "P"))
                            (G I X))))
                 (DEFN ,recognizer (X)
                   (AND (GOOD-ALISTP X)
                        (EC-CALL (,recognizer-aux X)))))))

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

  (x86$a-recognizers)

  ;; Since we never want to execute these predicates, we disable their
  ;; executable counterparts.

  (globally-disable '((:executable-counterpart rgfp)
                      (:executable-counterpart rflagsp)
                      (:executable-counterpart seg-visiblep)
                      (:executable-counterpart seg-hiddenp)
                      (:executable-counterpart strp)
                      (:executable-counterpart ssr-visiblep)
                      (:executable-counterpart ssr-hiddenp)
                      (:executable-counterpart ctrp)
                      (:executable-counterpart msrp)
                      (:executable-counterpart dbgp)
                      (:executable-counterpart fp-datap)
                      (:executable-counterpart xmmp)
                      (:executable-counterpart memp)))

  )

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
               `((,predicate
                  (NTH
                   ,constant
                   X)))))
            (t
             (let* ((stripped-name (mk-name
                                    (subseq (symbol-name name) 0
                                            (search "$C" (symbol-name name)))))
                    (constant (mk-name "*" stripped-name "*"))
                    (predicate (mk-name stripped-name "P")))
               `((,predicate
                  (NTH
                   ,constant
                   X
                   )))
               )))))

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
  (create-x86-abstract-stobj-recognizer)

  )

;; ======================================================================
;; Abstract stobj creator create-x86$a
;; ======================================================================

(defsection abstract-stobj-creator

  :parents (abstract-state)

  :short "Definition of @('create-x86$a')"

  (make-event (define-abstract-stobj-indices))

  ;; When adding a "field" to the abstract stobj, remember the order;
  ;; see the function define-abstract-stobj-indices for this order.
  ;; Also, the values here match the :initially values in the defstobj
  ;; definition.  So I could get them programmatically if I wanted to.

  (defn create-x86$a ()
    (list '0      ;; rgfi
          '0      ;; rip
          '2      ;; rflags
          '0      ;; seg-visiblei
          '0      ;; seg-hiddeni
          '0      ;; stri
          '0      ;; ssr-visiblei
          '0      ;; ssr-hiddeni
          '0      ;; ctri
          '0      ;; dbgi
          '0      ;; fp-datai
          '0      ;; fp-ctrl
          '0      ;; fp-status
          '0      ;; fp-tag
          '0      ;; fp-last-inst
          '0      ;; fp-last-data
          '0      ;; fp-opcode
          '0      ;; xmmi
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
          ))

  )

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
              (G I (NTH ,constant x86)))
            (DEFUN ,(mk-name setter) (I V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (NATP I)
                                          (< I ,length)
                                          (UNSIGNED-BYTE-P ,size V))))
              (UPDATE-NTH ,constant (S I V (NTH ,constant x86)) x86)))))

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
              (G I (NTH ,constant x86)))
            (DEFUN ,(mk-name setter) (I V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (NATP I)
                                          (< I ,length)
                                          (SIGNED-BYTE-P ,size V))))
              (UPDATE-NTH ,constant (S I V (NTH ,constant x86)) x86)))))

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
              (NTH ,constant x86))
            (DEFUN ,setter (V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (UNSIGNED-BYTE-P ,size V))))
              (UPDATE-NTH ,constant V x86)))))

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
              (NTH ,constant x86))
            (DEFUN ,setter (V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (SIGNED-BYTE-P ,size V))))
              (UPDATE-NTH ,constant V x86)))))

       ((and (consp type)
             (equal (car type) 'integer))
        (let* ((name      (mk-name (subseq (symbol-name name) 0
                                           (search "$C" (symbol-name
                                                         name)))))
               (constant  (mk-name "*" name "*"))
               (getter    (mk-name name "$A"))
               (setter    (mk-name "!" name "$A"))
               (min      (cadr type))
               (max      (caddr type)))
          `((DEFUN ,getter (x86)
              (DECLARE (XARGS :GUARD (x86$AP x86)))
              (NTH ,constant x86))
            (DEFUN ,setter (V x86)
              (DECLARE (XARGS :GUARD (AND (x86$AP x86)
                                          (INTEGERP V)
                                          (<= ,min V)
                                          (<= V ,max))))
              (UPDATE-NTH ,constant V x86)))))

       ((and (consp type)
             (equal (car type) 'satisfies))
        ;; env field
        (let* ((name      (mk-name (subseq (symbol-name name) 0
                                           (search "$C" (symbol-name
                                                         name)))))
               (predicate (cadr type))
               (constant  (mk-name "*" name "*"))
               (getter    (mk-name name "$A"))
               (setter    (mk-name "!" name "$A")))
          `((DEFUN ,getter (x86)
              (DECLARE (XARGS :GUARD (X86$AP X86)))
              (NTH ,constant X86))
            (DEFUN ,setter (V X86)
              (DECLARE (XARGS :GUARD (AND (X86$AP X86)
                                          (,predicate V))))
              (UPDATE-NTH ,constant V X86)))))

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
              (UPDATE-NTH ,constant V x86)))
          )))))

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

  (x86$a-accessors-and-updaters)

  )

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
                  (EQUAL (,getter I X86$c) (G I FIELD))
                  (AND (EQUAL (,getter I X86$c) (G I FIELD))
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
                            (g i field)))))

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
                      corr-seg-hidden
                      corr-str
                      corr-ssr-visible
                      corr-ssr-hidden
                      corr-ctr
                      corr-dbg
                      corr-fp-data
                      corr-xmm
                      corr-msr
                      corr-mem))

  )

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
       :CONCRETE X86$C
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

   (defthml onesp-mem-table-implies-mem$ci-is-0-lemma
     (implies (and (onesp-mem-table k mem-table)
                   (integerp i)
                   (<= 0 i)
                   (integerp k)
                   (< i k))
              (equal (nth (logtail *2^x-byte-pseudo-page* i) mem-table)
                     1)))

   (defthml onesp-mem-table-implies-mem$ci-is-0
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

   (defthml ash-monotone-2-lemma
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

  (DEFTHML CREATE-X86{CORRESPONDENCE}
    (CORR (CREATE-X86$C)
          (CREATE-X86$A))
    :hints (("Goal"
             :use (x86$cp-create-x86$c
                   corr-rgf-init
                   corr-seg-visible-init
                   corr-seg-hidden-init
                   corr-str-init
                   corr-ssr-visible-init
                   corr-ssr-hidden-init
                   corr-ctr-init
                   corr-dbg-init
                   corr-msr-init
                   corr-mem-init
                   corr-fp-data-init
                   corr-xmm-init)))
    :RULE-CLASSES NIL)

  (DEFTHML CREATE-X86{PRESERVED}
    (X86$AP (CREATE-X86$A))
    ;; Note that we disable the executable counterpart of x86$ap.
    :hints (("Goal" :in-theory (disable (x86$ap))))
    :RULE-CLASSES NIL)

  (in-theory (disable rgfp-aux
                      seg-visiblep-aux
                      seg-hiddenp-aux
                      strp-aux
                      ssr-visiblep-aux
                      ssr-hiddenp-aux
                      ctrp-aux     dbgp-aux
                      msrp-aux     fp-datap-aux
                      xmmp-aux     memp-aux))

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
                                               (G J (NTH ,constant X86)))
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
                                   (G I (NTH ,constant X86))))
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
             :in-theory (disable corr-mem mem$ci !mem$ci g)
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

  (create-updater-correspondence-lemmas)

  (local (in-theory (disable update-nth)))

  (defun create-updater-$a-corr-lemmas-1 (x86-model-field)
    ;; STR and SSR are dealt in a different case.  Something to do with
    ;; the length of these fields (2), and proofs proceeding
    ;; differently...
    (let* ((name (car x86-model-field))
           (type (caddr x86-model-field)))
      (cond ((and (not (equal name 'STR-VISIBLE$C))
                  (not (equal name 'SSR-VISIBLE$C))
                  (not (equal name 'STR-HIDDEN$C))
                  (not (equal name 'SSR-HIDDEN$C))
                  (consp type)
                  (equal (car type) 'array))
             (let* ((length (caaddr (caddr x86-model-field)))
                    (size (cadr (cadr  type)))
                    (size (symbol-name (if (< size 10)
                                           (acl2::packn (list 0 size))
                                         (acl2::packn (list size)))))
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
                            (,recognizer (S I V ,stripped-name)))
                   :HINTS (("GOAL"
                            :IN-THEORY (E/D (G-OF-S-REDUX)
                                            (,recognizer-aux))
                            :USE ((:INSTANCE ,recognizer-aux-necc
                                             (I (,recognizer-aux-witness
                                                 (S I V ,stripped-name)))
                                             (X ,stripped-name)))
                            :EXPAND ((,recognizer-aux (S I V ,stripped-name))))))

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
                              V
                              (,a-getter I X86)))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,a-getter ,a-setter) ()))))

                 (DEFTHMLD ,(mk-name corr-name "-UPDATE-" stripped-name "-1")
                   (IMPLIES (AND (,corr-name-aux J X86$C (NTH ,new-constant X86))
                                 (NATP J)
                                 (NATP I))
                            (,corr-name-aux J (,setter I V X86$C)
                                            (S I V (NTH ,new-constant X86))))
                   :HINTS (("GOAL"
                            :INDUCT (,corr-name-aux J X86$C (NTH ,new-constant X86))
                            :IN-THEORY (e/d () (X86$AP)))))

                 (DEFTHMLD ,(mk-name corr-name "-UPDATE-" stripped-name "-2")
                   (IMPLIES (AND (,corr-name-aux J X86$C (NTH ,new-constant X86))
                                 (NATP J)
                                 (NATP I))
                            (,corr-name-aux J
                                            (UPDATE-NTH ,constant
                                                        (UPDATE-NTH
                                                         I V
                                                         (NTH ,constant X86$C))
                                                        X86$C)
                                            (S I V (NTH ,new-constant X86))))
                   :HINTS (("GOAL"
                            :IN-THEORY (e/d (,(mk-name corr-name "-UPDATE-"
                                                       stripped-name "-1")
                                             ,setter)
                                            (X86$AP))
                            :USE ((:INSTANCE ,(mk-name corr-name "-UPDATE-"
                                                       stripped-name "-1"))
                                  ))))

                 (DEFTHML ,(mk-name corr-name "-UPDATE-" stripped-name)
                   (IMPLIES (AND (,corr-name X86$C (NTH ,new-constant X86))
                                 (NATP I))
                            (,corr-name
                             (UPDATE-NTH ,constant
                                         (UPDATE-NTH
                                          I V
                                          (NTH ,constant X86$C))
                                         X86$C)
                             (S I V (NTH ,new-constant X86))))
                   :HINTS (("GOAL"
                            :IN-THEORY (e/d (,setter
                                             ,corr-name)
                                            (X86$AP))
                            :USE ((:INSTANCE ,(mk-name corr-name "-UPDATE-"
                                                       stripped-name "-2")
                                             (j (1- ,length))))
                            )))
                 )))
            ((and (or (equal name 'STR-VISIBLE$C)
                      (equal name 'SSR-VISIBLE$C)
                      (equal name 'STR-HIDDEN$C)
                      (equal name 'SSR-HIDDEN$C))
                  (consp type)
                  (equal (car type) 'array))
             (let* ((length (caaddr (caddr x86-model-field)))
                    (size (cadr (cadr  type)))
                    (size (symbol-name (if (< size 10)
                                           (acl2::packn (list 0 size))
                                         (acl2::packn (list size)))))
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
                            (,recognizer (S I V ,stripped-name)))
                   :HINTS (("GOAL"
                            :IN-THEORY (E/D (G-OF-S-REDUX)
                                            (,recognizer-aux))
                            :USE ((:INSTANCE ,recognizer-aux-necc
                                             (I (,recognizer-aux-witness
                                                 (S I V ,stripped-name)))
                                             (X ,stripped-name)))
                            :EXPAND ((,recognizer-aux (S I V ,stripped-name))))))

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
                              V
                              (,a-getter I X86)))
                   :HINTS (("GOAL" :IN-THEORY (E/D (,a-getter ,a-setter) ()))))

                 (DEFTHML ,(mk-name corr-name "-UPDATE-" stripped-name)
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
                             (S I V (NTH ,new-constant X86))))
                   :HINTS (("GOAL"
                            :IN-THEORY (e/d (,setter
                                             ,getter
                                             ,corr-name)
                                            (X86$AP))
                            )))
                 )))
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

  (DEFTHML RGFI*{CORRESPONDENCE}
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

  (DEFTHML RGFI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *64-bit-general-purpose-registers-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (RGF$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !RGFI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *64-bit-general-purpose-registers-len*)
                  (SIGNED-BYTE-P 64 V))
             (CORR (!RGF$CI I V X86$C)
                   (!RGF$AI I V X86)))
    :hints (("Goal" :in-theory (e/d (!rgf$ci x86$cp x86$cp-pre good-memp)
                                    ())
             :expand (CORR (!RGF$CI I V X86$C)
                           (!RGF$AI I V X86))
             :use ((:instance corr-rgf-update-rgf)
                   (:instance corr-seg-visible-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *RGF$CI*)
                              (x (UPDATE-NTH I V (CAR X86$C)))
                              (x86 X86$C)
                              (field (nth *xmmi* x86)))
                   )))
    :RULE-CLASSES NIL)

  (local (in-theory (e/d () (corr-rgf-update-rgf))))

  (DEFTHML !RGFI*{GUARD-THM}
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

  (DEFTHML !RGFI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *64-bit-general-purpose-registers-len*)
                  (SIGNED-BYTE-P 64 V))
             (X86$AP (!RGF$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML RIP*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (RIP$C X86$C) (RIP$A X86)))
    :hints (("Goal" :in-theory (e/d (rip$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !RIP*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (SIGNED-BYTE-P 48 V))
             (CORR (!RIP$C V X86$C) (!RIP$A V X86)))
    :hints (("Goal" :in-theory (e/d (rip$cp !rip$c x86$cp x86$cp-pre good-memp)
                                    ())
             :use ((:instance corr-rgf-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *RIP$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *xmmi* x86)))
                   )))
    :RULE-CLASSES NIL)

  (DEFTHML !RIP*{PRESERVED}
    (IMPLIES (AND (X86$AP X86) (SIGNED-BYTE-P 48 V))
             (X86$AP (!RIP$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHM RFLAGS*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (RFLAGS$C X86$C) (RFLAGS$A X86)))
    :hints (("Goal" :in-theory (e/d (rflags$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHM !RFLAGS*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (UNSIGNED-BYTE-P 32 V))
             (CORR (!RFLAGS$C V X86$C)
                   (!RFLAGS$A V X86)))
    :hints (("Goal" :in-theory (e/d (rflags$cp !rflags$c x86$cp x86$cp-pre good-memp)
                                    ())
             :use ((:instance corr-rgf-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *RFLAGS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *xmmi* x86)))
                   )))
    :RULE-CLASSES NIL)

  (DEFTHM !RFLAGS*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 32 V))
             (X86$AP (!RFLAGS$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML SEG-VISIBLEI*{CORRESPONDENCE}
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

  (DEFTHML SEG-VISIBLEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-VISIBLE$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !SEG-VISIBLEI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (CORR (!SEG-VISIBLE$CI I V X86$C)
                   (!SEG-VISIBLE$AI I V X86)))
    :hints
    (("Goal" :in-theory (e/d (!seg-visible$ci x86$cp x86$cp-pre good-memp) nil)
      :expand (corr (!seg-visible$ci i v x86$c)
                    (!seg-visible$ai i v x86))
      :use ((:instance corr-rgf-update-nth (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-hidden-update-nth (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth (n *seg-visible$ci*)
                       (x (update-nth i v (nth *seg-visible$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *xmmi* x86))))))
    :rule-classes nil)

  (local (in-theory (e/d () (corr-seg-visible-update-seg-visible))))

  (DEFTHML !SEG-VISIBLEI*{GUARD-THM}
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

  (DEFTHML !SEG-VISIBLEI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!SEG-VISIBLE$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML SEG-HIDDENI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (EQUAL (SEG-HIDDEN$CI I X86$C) (SEG-HIDDEN$AI I X86)))
    :HINTS (("Goal"
             :use ((:instance seg-hiddeni{correspondence}-helper-2
                              (j (1- *segment-register-names-len*))))
             :in-theory (e/d (x86$ap corr-seg-hidden) ())))
    :RULE-CLASSES NIL)

  (DEFTHML SEG-HIDDENI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-HIDDEN$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !SEG-HIDDENI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 112 V))
             (CORR (!SEG-HIDDEN$CI I V X86$C)
                   (!SEG-HIDDEN$AI I V X86)))
    :hints
    (("Goal" :in-theory (e/d (!seg-hidden$ci x86$cp x86$cp-pre good-memp) nil)
      :expand (corr (!seg-hidden$ci i v x86$c)
                    (!seg-hidden$ai i v x86))
      :use ((:instance corr-rgf-update-nth (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-str-update-nth (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth (n *seg-hidden$ci*)
                       (x (update-nth i v (nth *seg-hidden$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *xmmi* x86))))))
    :rule-classes nil)

  (local (in-theory (e/d () (corr-seg-hidden-update-seg-hidden))))

  (DEFTHML !SEG-HIDDENI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 112 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SEG-HIDDEN$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 112 V)))
    :RULE-CLASSES NIL)

  (DEFTHML !SEG-HIDDENI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *segment-register-names-len*)
                  (UNSIGNED-BYTE-P 112 V))
             (X86$AP (!SEG-HIDDEN$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML STRI*{CORRESPONDENCE}
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

  (DEFTHML STRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *gdtr-idtr-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (STR$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !STRI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *gdtr-idtr-names-len*)
                  (UNSIGNED-BYTE-P 80 V))
             (CORR (!STR$CI I V X86$C)
                   (!STR$AI I V X86)))
    :hints
    (("Goal" :in-theory (e/d (!str$ci x86$cp x86$cp-pre good-memp)
                             (corr-str-aux))
      :expand (corr (!str$ci i v x86$c)
                    (!str$ai i v x86))
      :use ((:instance corr-rgf-update-nth (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-ssr-visible-update-nth (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-ssr-hidden-update-nth (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth (n *str$ci*)
                       (x (update-nth i v (nth *str$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (local (in-theory (e/d () (corr-str-update-str))))

  (DEFTHML !STRI*{GUARD-THM}
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

  (DEFTHML !STRI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *gdtr-idtr-names-len*)
                  (UNSIGNED-BYTE-P 80 V))
             (X86$AP (!STR$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML SSR-VISIBLEI*{CORRESPONDENCE}
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

  (DEFTHML SSR-VISIBLEI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-VISIBLE$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !SSR-VISIBLEI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (CORR (!SSR-VISIBLE$CI I V X86$C)
                   (!SSR-VISIBLE$AI I V X86)))
    :hints
    (("Goal" :in-theory (e/d (!ssr-VISIBLE$ci x86$cp x86$cp-pre good-memp) nil)
      :expand (corr (!ssr-VISIBLE$ci i v x86$c)
                    (!ssr-VISIBLE$ai i v x86))
      :use ((:instance corr-rgf-update-nth (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-hidden-update-nth (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth (n *ssr-VISIBLE$ci*)
                       (x (update-nth i v (nth *ssr-VISIBLE$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (local (in-theory (e/d () (corr-ssr-VISIBLE-update-ssr-VISIBLE))))

  (DEFTHML !SSR-VISIBLEI*{GUARD-THM}
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

  (DEFTHML !SSR-VISIBLEI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!SSR-VISIBLE$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML SSR-HIDDENI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (EQUAL (SSR-HIDDEN$CI I X86$C) (SSR-HIDDEN$AI I X86)))
    :HINTS
    (("Goal"
      :use ((:instance ssr-HIDDENi{correspondence}-helper-2
                       (j (1- *ldtr-tr-names-len*))))
      :in-theory (e/d (corr-ssr-HIDDEN) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFTHML SSR-HIDDENI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-HIDDEN$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !SSR-HIDDENI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 112 V))
             (CORR (!SSR-HIDDEN$CI I V X86$C)
                   (!SSR-HIDDEN$AI I V X86)))
    :hints
    (("Goal" :in-theory (e/d (!ssr-HIDDEN$ci x86$cp x86$cp-pre good-memp) nil)
      :expand (corr (!ssr-HIDDEN$ci i v x86$c)
                    (!ssr-HIDDEN$ai i v x86))
      :use ((:instance corr-rgf-update-nth (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ctr-update-nth (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth (n *ssr-HIDDEN$ci*)
                       (x (update-nth i v (nth *ssr-HIDDEN$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (local (in-theory (e/d () (corr-ssr-HIDDEN-update-ssr-HIDDEN))))

  (DEFTHML !SSR-HIDDENI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 112 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (SSR-HIDDEN$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 112 V)))
    :RULE-CLASSES NIL)

  (DEFTHML !SSR-HIDDENI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *ldtr-tr-names-len*)
                  (UNSIGNED-BYTE-P 112 V))
             (X86$AP (!SSR-HIDDEN$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML CTRI*{CORRESPONDENCE}
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

  (DEFTHML CTRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *control-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (CTR$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !CTRI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *control-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (CORR (!CTR$CI I V X86$C)
                   (!CTR$AI I V X86)))
    :hints
    (("Goal"
      :in-theory (e/d (!ctr$ci x86$cp x86$cp-pre good-memp) nil)
      :expand (corr (!ctr$ci i v x86$c)
                    (!ctr$ai i v x86))
      :use ((:instance corr-rgf-update-nth (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-dbg-update-nth
                       (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth
                       (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth (n *ctr$ci*)
                       (x (update-nth i v (nth *ctr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (local (in-theory (e/d () (corr-ctr-update-ctr))))

  (DEFTHML !CTRI*{GUARD-THM}
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

  (DEFTHML !CTRI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *control-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (X86$AP (!CTR$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML DBGI*{CORRESPONDENCE}
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

  (DEFTHML DBGI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *debug-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (DBG$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !DBGI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *debug-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (CORR (!DBG$CI I V X86$C)
                   (!DBG$AI I V X86)))
    :hints
    (("Goal"
      :in-theory (e/d (!dbg$ci x86$cp x86$cp-pre good-memp) nil)
      :expand (corr (!dbg$ci i v x86$c)
                    (!dbg$ai i v x86))
      :use ((:instance corr-rgf-update-nth (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ctri* x86)))
            (:instance corr-msr-update-nth (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth (n *dbg$ci*)
                       (x (update-nth i v (nth *dbg$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (local (in-theory (e/d () (corr-dbg-update-dbg))))

  (DEFTHML !DBGI*{GUARD-THM}
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

  (DEFTHML !DBGI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *debug-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (X86$AP (!DBG$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML FP-DATAI*{CORRESPONDENCE}
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

  (DEFTHML FP-DATAI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 8))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (FP-DATA$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)


  (DEFTHML !FP-DATAI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 8)
                  (UNSIGNED-BYTE-P 80 V))
             (CORR (!FP-DATA$CI I V X86$C)
                   (!FP-DATA$AI I V X86)))
    :hints
    (("Goal"
      :in-theory (e/d (!fp-data$ci x86$cp x86$cp-pre good-memp) nil)
      :expand (corr (!fp-data$ci i v x86$c)
                    (!fp-data$ai i v x86))
      :use ((:instance corr-rgf-update-nth (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-dbg-update-nth
                       (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth
                       (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *msri* x86)))
            (:instance corr-ctr-update-nth
                       (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 X86$C)
                       (field (nth *ctri* x86)))
            (:instance corr-xmm-update-nth (n *fp-data$ci*)
                       (x (update-nth i v (nth *fp-data$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (local (in-theory (e/d () (corr-fp-data-update-fp-data))))

  (DEFTHML !FP-DATAI*{GUARD-THM}
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

  (DEFTHML !FP-DATAI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I 8)
                  (UNSIGNED-BYTE-P 80 V))
             (X86$AP (!FP-DATA$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML FP-CTRL*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-CTRL$C X86$C)
                    (FP-CTRL$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-ctrl$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-CTRL*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (UNSIGNED-BYTE-P 16 V))
             (CORR (!FP-CTRL$C V X86$C)
                   (!FP-CTRL$A V X86)))
    :hints (("Goal" :in-theory (e/d (fp-ctrl$cp !fp-ctrl$c x86$cp
                                                x86$cp-pre good-memp)
                                    ())
             :expand (CORR (!FP-CTRL$C V X86$C)
                           (!FP-CTRL$A V X86))
             :use ((:instance corr-rgf-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *fp-ctrl$c*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *FP-CTRL$C*)
                              (x v)
                              (x86 x86$c)
                              (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-CTRL*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!FP-CTRL$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML FP-STATUS*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-STATUS$C X86$C)
                    (FP-STATUS$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-status$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-STATUS*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (UNSIGNED-BYTE-P 16 V))
             (CORR (!FP-STATUS$C V X86$C)
                   (!FP-STATUS$A V X86)))
    :hints (("Goal" :in-theory (e/d (fp-status$cp !fp-status$c x86$cp
                                                  x86$cp-pre good-memp)
                                    ())
             :expand (CORR (!FP-STATUS$C V X86$C)
                           (!FP-STATUS$A V X86))
             :use ((:instance corr-rgf-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *fp-status$c*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *FP-STATUS$C*)
                              (x v)
                              (x86 x86$c)
                              (field (nth *xmmi* x86)))
                   )))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-STATUS*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!FP-STATUS$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML FP-TAG*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-TAG$C X86$C) (FP-TAG$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-tag$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-TAG*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (UNSIGNED-BYTE-P 16 V))
             (CORR (!FP-TAG$C V X86$C)
                   (!FP-TAG$A V X86)))
    :hints (("Goal" :in-theory (e/d (fp-tag$cp !fp-tag$c x86$cp good-memp x86$cp-pre)
                                    ())
             :expand (CORR (!FP-TAG$C V X86$C)
                           (!FP-TAG$A V X86))
             :use ((:instance corr-rgf-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *fp-tag$c*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *FP-TAG$C*)
                              (x v)
                              (x86 x86$c)
                              (field (nth *xmmi* x86)))
                   )))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-TAG*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 16 V))
             (X86$AP (!FP-TAG$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML FP-LAST-INST*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-LAST-INST$C X86$C)
                    (FP-LAST-INST$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-last-inst$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-LAST-INST*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (UNSIGNED-BYTE-P 48 V))
             (CORR (!FP-LAST-INST$C V X86$C)
                   (!FP-LAST-INST$A V X86)))
    :hints (("Goal" :in-theory (e/d (fp-last-inst$cp !fp-last-inst$c
                                                     x86$cp good-memp x86$cp-pre)
                                    ())
             :expand (CORR (!FP-LAST-INST$C V X86$C)
                           (!FP-LAST-INST$A V X86))
             :use ((:instance corr-rgf-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *fp-last-inst$c*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *FP-LAST-INST$C*)
                              (x v)
                              (x86 x86$c)
                              (field (nth *xmmi* x86)))
                   )))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-LAST-INST*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 48 V))
             (X86$AP (!FP-LAST-INST$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML FP-LAST-DATA*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-LAST-DATA$C X86$C)
                    (FP-LAST-DATA$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-last-data$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-LAST-DATA*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (UNSIGNED-BYTE-P 48 V))
             (CORR (!FP-LAST-DATA$C V X86$C)
                   (!FP-LAST-DATA$A V X86)))
    :hints (("Goal" :in-theory (e/d (fp-last-data$cp !fp-last-data$c
                                                     x86$cp good-memp x86$cp-pre)
                                    ())
             :expand (CORR (!FP-LAST-DATA$C V X86$C)
                           (!FP-LAST-DATA$A V X86))
             :use ((:instance corr-rgf-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *fp-last-data$c*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *FP-LAST-DATA$C*)
                              (x v)
                              (x86 x86$c)
                              (field (nth *xmmi* x86)))
                   )))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-LAST-DATA*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 48 V))
             (X86$AP (!FP-LAST-DATA$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML FP-OPCODE*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FP-OPCODE$C X86$C)
                    (FP-OPCODE$A X86)))
    :hints (("Goal" :in-theory (e/d (fp-opcode$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-OPCODE*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (UNSIGNED-BYTE-P 11 V))
             (CORR (!FP-OPCODE$C V X86$C)
                   (!FP-OPCODE$A V X86)))
    :hints (("Goal" :in-theory (e/d (fp-opcode$cp !fp-opcode$c x86$cp
                                                  good-memp x86$cp-pre)
                                    ())
             :expand (CORR (!FP-OPCODE$C V X86$C)
                           (!FP-OPCODE$A V X86))
             :use ((:instance corr-rgf-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *fp-opcode$c*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *FP-OPCODE$C*)
                              (x v)
                              (x86 x86$c)
                              (field (nth *xmmi* x86)))
                   )))
    :RULE-CLASSES NIL)

  (DEFTHML !FP-OPCODE*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 11 V))
             (X86$AP (!FP-OPCODE$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML XMMI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 16))
             (EQUAL (XMM$CI I X86$C) (XMM$AI I X86)))
    :hints (("Goal" :use ((:instance XMMI{CORRESPONDENCE}-helper-2 (j 15)))
             :in-theory (e/d (corr-xmm) (x86$ap))))
    :RULE-CLASSES NIL)

  (DEFTHML XMMI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 16))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (XMM$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !XMMI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 16)
                  (UNSIGNED-BYTE-P 128 V))
             (CORR (!XMM$CI I V X86$C)
                   (!XMM$AI I V X86)))
    :hints (("Goal" :in-theory (e/d (!xmm$ci x86$cp good-memp x86$cp-pre)
                                    ())
             :expand (CORR (!XMM$CI I V X86$C)
                           (!XMM$AI I V X86))
             :use ((:instance corr-xmm-update-xmm)
                   (:instance corr-rgf-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 x86$c)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *xmm$ci*)
                              (x (update-nth i v (nth *xmm$ci* x86$c)))
                              (x86 X86$C)
                              (field (nth *fp-datai* x86))))))
    :RULE-CLASSES NIL)

  (local (in-theory (e/d () (corr-xmm-update-xmm))))

  (DEFTHML !XMMI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I 16)
                  (UNSIGNED-BYTE-P 128 V))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (XMM$C-LENGTH X86$C))
                  (UNSIGNED-BYTE-P 128 V)))
    :RULE-CLASSES NIL)

  (DEFTHML !XMMI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I 16)
                  (UNSIGNED-BYTE-P 128 V))
             (X86$AP (!XMM$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML MXCSR*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (MXCSR$C X86$C) (MXCSR$A X86)))
    :hints (("Goal" :in-theory (e/d (mxcsr$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !MXCSR*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (UNSIGNED-BYTE-P 32 V))
             (CORR (!MXCSR$C V X86$C)
                   (!MXCSR$A V X86)))
    :hints (("Goal" :in-theory (e/d (mxcsr$cp !mxcsr$c x86$cp x86$cp-pre
                                              good-memp)
                                    ())
             :expand (CORR (!MXCSR$C V X86$C)
                           (!MXCSR$A V X86))
             :use ((:instance corr-rgf-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *rgfi* x86)))
                   (:instance corr-seg-visible-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-visiblei* x86)))
                   (:instance corr-seg-hidden-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *seg-hiddeni* x86)))
                   (:instance corr-str-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *stri* x86)))
                   (:instance corr-ssr-visible-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-visiblei* x86)))
                   (:instance corr-ssr-hidden-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ssr-hiddeni* x86)))
                   (:instance corr-ctr-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *ctri* x86)))
                   (:instance corr-dbg-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *dbgi* x86)))
                   (:instance corr-msr-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *msri* x86)))
                   (:instance corr-fp-data-update-nth
                              (n *mxcsr$c*)
                              (x v)
                              (x86 X86$C)
                              (field (nth *fp-datai* x86)))
                   (:instance corr-xmm-update-nth
                              (n *MXCSR$C*)
                              (x v)
                              (x86 X86$c)
                              (field (nth *xmmi* x86)))
                   )))
    :RULE-CLASSES NIL)

  (DEFTHML !MXCSR*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (UNSIGNED-BYTE-P 32 V))
             (X86$AP (!MXCSR$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML MSRI*{CORRESPONDENCE}
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

  (DEFTHML MSRI*{GUARD-THM}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *model-specific-register-names-len*))
             (AND (INTEGERP I)
                  (<= 0 I)
                  (< I (MSR$C-LENGTH X86$C))))
    :RULE-CLASSES NIL)

  (DEFTHML !MSRI*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (NATP I)
                  (< I *model-specific-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (CORR (!MSR$CI I V X86$C)
                   (!MSR$AI I V X86)))
    :hints
    (("Goal"
      :in-theory (e/d (!msr$ci x86$cp good-memp x86$cp-pre) nil)
      :expand (corr (!msr$ci i v x86$c)
                    (!msr$ai i v x86))
      :use ((:instance corr-rgf-update-nth (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *dbgi* x86)))
            (:instance corr-fp-data-update-nth
                       (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth (n *msr$ci*)
                       (x (update-nth i v (nth *msr$ci* x86$c)))
                       (x86 x86$c)
                       (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (local (in-theory (e/d () (corr-msr-update-msr))))

  (DEFTHML !MSRI*{GUARD-THM}
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

  (DEFTHML !MSRI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I *model-specific-register-names-len*)
                  (UNSIGNED-BYTE-P 64 V))
             (X86$AP (!MSR$AI I V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML MS*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (MS$C X86$C) (MS$A X86)))
    :hints (("Goal" :in-theory (e/d (ms$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !MS*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (CORR (!MS$C V X86$C) (!MS$A V X86)))
    :hints
    (("Goal" :in-theory (e/d (ms$cp !ms$c x86$cp good-memp x86$cp-pre)
                             ())
      :expand (CORR (!MS$C V X86$C)
                    (!MS$A V X86))
      :use ((:instance corr-rgf-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *ms$c*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth
                       (n *MS$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *xmmi* x86)))
            )))
    :RULE-CLASSES NIL)

  (DEFTHML !MS*{PRESERVED}
    (IMPLIES (X86$AP X86)
             (X86$AP (!MS$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML FAULT*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (FAULT$C X86$C) (FAULT$A X86)))
    :hints (("Goal" :in-theory (e/d (fault$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !FAULT*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (CORR (!FAULT$C V X86$C)
                   (!FAULT$A V X86)))
    :hints
    (("Goal" :in-theory (e/d (fault$cp !fault$c x86$cp good-memp x86$cp-pre)
                             ())
      :use ((:instance corr-rgf-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth
                       (n *FAULT$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *xmmi* x86)))
            )))
    :RULE-CLASSES NIL)

  (DEFTHML !FAULT*{PRESERVED}
    (IMPLIES (X86$AP X86)
             (X86$AP (!FAULT$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML ENV*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (ENV$C X86$C)
                    (ENV$A X86)))
    :hints (("Goal" :in-theory (e/d (env$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !ENV*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (ENV-ALISTP V))
             (CORR (!ENV$C V X86$C)
                   (!ENV$A V X86)))
    :hints
    (("Goal" :in-theory (e/d (env$cp !env$c x86$cp good-memp x86$cp-pre)
                             ())
      :use ((:instance corr-rgf-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth
                       (n *ENV$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (DEFTHML !ENV*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (ENV-ALISTP V))
             (X86$AP (!ENV$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML UNDEF*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (UNDEF$C X86$C) (UNDEF$A X86)))
    :hints (("Goal" :in-theory (e/d (undef$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !UNDEF*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (CORR (!UNDEF$C V X86$C)
                   (!UNDEF$A V X86)))
    :hints
    (("Goal" :in-theory (e/d (undef$cp !undef$c x86$cp good-memp x86$cp-pre)
                             ())
      :use ((:instance corr-rgf-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth
                       (n *UNDEF$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *xmmi* x86))))))
    :RULE-CLASSES NIL)

  (DEFTHML !UNDEF*{PRESERVED}
    (IMPLIES (X86$AP X86)
             (X86$AP (!UNDEF$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML APP-VIEW*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (APP-VIEW$C X86$C)
                    (APP-VIEW$A X86)))
    :hints (("Goal" :in-theory (e/d (app-view$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !APP-VIEW*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (BOOLEANP V))
             (CORR (!APP-VIEW$C V X86$C)
                   (!APP-VIEW$A V X86)))
    :hints
    (("Goal" :in-theory (e/d (app-view$cp !app-view$c
                                                       x86$cp good-memp x86$cp-pre)
                             ())
      :use ((:instance corr-rgf-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth
                       (n *APP-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *xmmi* x86)))
            )))
    :RULE-CLASSES NIL)

  (DEFTHML !APP-VIEW*{PRESERVED}
    (IMPLIES (AND (X86$AP X86) (BOOLEANP V))
             (X86$AP (!APP-VIEW$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML MARKING-VIEW*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (MARKING-VIEW$C X86$C)
                    (MARKING-VIEW$A X86)))
    :hints (("Goal" :in-theory (e/d (marking-view$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !MARKING-VIEW*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (BOOLEANP V))
             (CORR (!MARKING-VIEW$C V X86$C)
                   (!MARKING-VIEW$A V X86)))
    :hints
    (("Goal" :in-theory (e/d (marking-view$cp !marking-view$c
                                                       x86$cp good-memp x86$cp-pre)
                             ())
      :use ((:instance corr-rgf-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth
                       (n *MARKING-VIEW$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *xmmi* x86)))
            )))
    :RULE-CLASSES NIL)

  (DEFTHML !MARKING-VIEW*{PRESERVED}
    (IMPLIES (AND (X86$AP X86) (BOOLEANP V))
             (X86$AP (!MARKING-VIEW$A V X86)))
    :RULE-CLASSES NIL)

  (DEFTHML OS-INFO*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86) (X86$AP X86))
             (EQUAL (OS-INFO$C X86$C)
                    (OS-INFO$A X86)))
    :hints (("Goal" :in-theory (e/d (os-info$c) ())))
    :RULE-CLASSES NIL)

  (DEFTHML !OS-INFO*{CORRESPONDENCE}
    (IMPLIES (AND (CORR X86$C X86)
                  (X86$AP X86)
                  (KEYWORDP V))
             (CORR (!OS-INFO$C V X86$C)
                   (!OS-INFO$A V X86)))
    :hints
    (("Goal" :in-theory (e/d (os-info$cp !os-info$c
                                         x86$cp good-memp x86$cp-pre)
                             ())
      :use ((:instance corr-rgf-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *rgfi* x86)))
            (:instance corr-seg-visible-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-visiblei* x86)))
            (:instance corr-seg-hidden-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *seg-hiddeni* x86)))
            (:instance corr-str-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *stri* x86)))
            (:instance corr-ssr-visible-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-visiblei* x86)))
            (:instance corr-ssr-hidden-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ssr-hiddeni* x86)))
            (:instance corr-ctr-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *ctri* x86)))
            (:instance corr-dbg-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *dbgi* x86)))
            (:instance corr-msr-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *msri* x86)))
            (:instance corr-fp-data-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *fp-datai* x86)))
            (:instance corr-xmm-update-nth
                       (n *OS-INFO$C*)
                       (x v)
                       (x86 X86$C)
                       (field (nth *xmmi* x86)))
            )))
    :RULE-CLASSES NIL)

  (DEFTHML !OS-INFO*{PRESERVED}
    (IMPLIES (AND (X86$AP X86) (KEYWORDP V))
             (X86$AP (!OS-INFO$A V X86)))
    :RULE-CLASSES NIL)

  (encapsulate
   ()

   (local (include-book "arithmetic/top-with-meta" :dir :system))

   (defthm corr-mem-suff
     (let ((i (corr-mem-witness x alist)))
       (implies (equal (mem$ci i x) (g i alist))
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
                   (force (integerp i))
                   (force (<= 0 i))
                   (force (< i *2^52*)))
              (equal (mem$ci i x86$c)
                     (g i field)))
     :hints (("Goal" :use corr-mem-necc)))

   ) ;; End of encapsulate

  (DEFTHML MEMI*{CORRESPONDENCE}
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
             (memp (s i v mem)))
    :hints (("Goal"
             :in-theory (e/d (g-of-s-redux)
                             (memp-aux))
             :use ((:instance memp-aux-necc
                              (i (memp-aux-witness (s i v mem)))
                              (x mem)))
             :expand ((memp-aux (s i v mem))))))

  (DEFTHML x86$ap-!mem$ai
    (IMPLIES (AND (CORR x86$C x86)
                  (x86$AP x86)
                  (NATP I)
                  (< I 4503599627370496)
                  (N08P V))
             (X86$AP (!MEM$AI I V x86)))
    :hints (("Goal" :in-theory (e/d (memp)))))

  (defthm !memi{correspondence}-1
    (implies (and (x86$cp-pre x86$c)
                  (good-memp x86$c)
                  (corr-mem x86$c
                            (nth *memi* x86)) ;; 11
                  (natp i)
                  (< i 4503599627370496)
                  (n08p v))
             (corr-mem (!mem$ci i v x86$c)
                       (s i v (nth *memi* x86))))
    :hints (("Goal"
             :in-theory (e/d (x86$cp)
                             (memp mem-table-length mem-array-length
                                   good-memp good-mem-arrayp))
             :expand ((corr-mem (!mem$ci i v x86$c)
                                (s i v (nth *memi* x86)))))))

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
             (e/d (x86$cp)
                  (memp mem-table-length mem-array-length good-memp
                        good-mem-arrayp)))))

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

                 (DEFTHML ,(mk-name corr-name "-!MEMI")
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

  (DEFTHML !MEMI*{CORRESPONDENCE}
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

  (DEFTHML !MEMI*{PRESERVED}
    (IMPLIES (AND (X86$AP X86)
                  (NATP I)
                  (< I 4503599627370496)
                  (UNSIGNED-BYTE-P 8 V))
             (X86$AP (!MEM$AI I V X86)))
    :RULE-CLASSES NIL)

  ;; x86
  (create-x86-abstract-stobj)

  )

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
                  (:rgf         (< index *64-bit-general-purpose-registers-len*))
                  (:seg-visible (< index *segment-register-names-len*))
                  (:seg-hidden  (< index *segment-register-names-len*))
                  (:str         (< index *gdtr-idtr-names-len*))
                  (:ssr-visible (< index *ldtr-tr-names-len*))
                  (:ssr-hidden  (< index *ldtr-tr-names-len*))
                  (:ctr         (< index *control-register-names-len*))
                  (:dbg         (< index *debug-register-names-len*))
                  (:fp-data     (< index *fp-data-register-names-len*))
                  (:xmm         (< index *xmm-register-names-len*))
                  (:msr         (< index *model-specific-register-names-len*))
                  (:mem         (< index *mem-size-in-bytes*))
                  (otherwise    (equal index 0))))

    (case fld
      (:rgf                         (rgfi* index x86))
      (:rip                         (rip* x86))
      (:rflags                      (rflags* x86))
      (:seg-visible                 (seg-visiblei* index x86))
      (:seg-hidden                  (seg-hiddeni* index x86))
      (:str                         (stri* index x86))
      (:ssr-visible                 (ssr-visiblei* index x86))
      (:ssr-hidden                  (ssr-hiddeni* index x86))
      (:ctr                         (ctri* index x86))
      (:dbg                         (dbgi* index x86))
      (:fp-data                     (fp-datai* index x86))
      (:fp-ctrl                     (fp-ctrl* x86))
      (:fp-status                   (fp-status* x86))
      (:fp-tag                      (fp-tag* x86))
      (:fp-last-inst                (fp-last-inst* x86))
      (:fp-last-data                (fp-last-data* x86))
      (:fp-opcode                   (fp-opcode* x86))
      (:xmm                         (xmmi* index x86))
      (:mxcsr                       (mxcsr* x86))
      (:msr                         (msri* index x86))
      (:ms                          (ms* x86))
      (:fault                       (fault* x86))
      (:env                         (env* x86))
      (:undef                       (undef* x86))
      (:app-view       (app-view* x86))
      (:marking-view (marking-view* x86))
      (:os-info                     (os-info* x86))
      (:mem                         (memi* index x86))
      (otherwise                    nil)))

  (define xw ((fld symbolp)
              (index natp)
              value x86)
    :enabled t
    :guard (and (member fld *x86-field-names-as-keywords*)
                (case fld
                  (:rgf          (and (< index *64-bit-general-purpose-registers-len*)
                                      (signed-byte-p 64 value)))
                  (:rip          (and (equal index 0)
                                      (signed-byte-p 48 value)))
                  (:rflags       (and (equal index 0)
                                      (unsigned-byte-p 32 value)))
                  (:seg-visible  (and (< index *segment-register-names-len*)
                                      (unsigned-byte-p 16 value)))
                  (:seg-hidden   (and (< index *segment-register-names-len*)
                                      (unsigned-byte-p 112 value)))
                  (:str          (and (< index *gdtr-idtr-names-len*)
                                      (unsigned-byte-p 80 value)))
                  (:ssr-visible  (and (< index *ldtr-tr-names-len*)
                                      (unsigned-byte-p 16 value)))
                  (:ssr-hidden   (and (< index *ldtr-tr-names-len*)
                                      (unsigned-byte-p 112 value)))
                  (:ctr          (and (< index *control-register-names-len*)
                                      (unsigned-byte-p 64 value)))
                  (:dbg          (and (< index *debug-register-names-len*)
                                      (unsigned-byte-p 64 value)))
                  (:fp-data      (and (< index *fp-data-register-names-len*)
                                      (unsigned-byte-p 80 value)))
                  (:fp-ctrl      (and (equal index 0)
                                      (unsigned-byte-p 16 value)))
                  (:fp-status    (and (equal index 0)
                                      (unsigned-byte-p 16 value)))
                  (:fp-tag       (and (equal index 0)
                                      (unsigned-byte-p 16 value)))
                  (:fp-last-inst (and (equal index 0)
                                      (unsigned-byte-p 48 value)))
                  (:fp-last-data (and (equal index 0)
                                      (unsigned-byte-p 48 value)))
                  (:fp-opcode    (and (equal index 0)
                                      (unsigned-byte-p 11 value)))
                  (:xmm          (and (< index *xmm-register-names-len*)
                                      (unsigned-byte-p 128 value)))
                  (:mxcsr        (and (equal index 0)
                                      (unsigned-byte-p 32 value)))
                  (:msr          (and (< index *model-specific-register-names-len*)
                                      (unsigned-byte-p 64 value)))
                  (:ms           (equal index 0))
                  (:fault        (equal index 0))
                  (:env          (and (equal index 0)
                                      (env-alistp value)))
                  (:undef        (equal index 0))
                  (:app-view
                   (and (equal index 0)
                        (booleanp value)))
                  (:marking-view
                   (and (equal index 0)
                        (booleanp value)))
                  (:os-info      (and (equal index 0)
                                      (keywordp value)))
                  (:mem          (and (< index *mem-size-in-bytes*)
                                      (unsigned-byte-p 8 value)))
                  (otherwise     (equal index 0))))

    (case fld
      (:rgf                         (!rgfi* index value x86))
      (:rip                         (!rip* value x86))
      (:rflags                      (!rflags* value x86))
      (:seg-visible                 (!seg-visiblei* index value x86))
      (:seg-hidden                  (!seg-hiddeni* index value x86))
      (:str                         (!stri* index value x86))
      (:ssr-visible                 (!ssr-visiblei* index value x86))
      (:ssr-hidden                  (!ssr-hiddeni* index value x86))
      (:ctr                         (!ctri* index value x86))
      (:dbg                         (!dbgi* index value x86))
      (:fp-data                     (!fp-datai* index value x86))
      (:fp-ctrl                     (!fp-ctrl* value x86))
      (:fp-status                   (!fp-status* value x86))
      (:fp-tag                      (!fp-tag* value x86))
      (:fp-last-inst                (!fp-last-inst* value x86))
      (:fp-last-data                (!fp-last-data* value x86))
      (:fp-opcode                   (!fp-opcode* value x86))
      (:xmm                         (!xmmi* index value x86))
      (:mxcsr                       (!mxcsr* value x86))
      (:msr                         (!msri* index value x86))
      (:ms                          (!ms* value x86))
      (:fault                       (!fault* value x86))
      (:env                         (!env* value x86))
      (:undef                       (!undef* value x86))
      (:app-view       (!app-view* value x86))
      (:marking-view (!marking-view* value x86))
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
              :ENABLED T
              (MBE :LOGIC (XR ,keyword I X86)
                   :EXEC (,getter* I X86)))

            (DEFINE ,setter ((I :TYPE (INTEGER 0 ,(1- length)))
                             (V :TYPE (,(car (cadr type)) ,size))
                             X86)
              :PARENTS NIL
              :INLINE T
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
              :ENABLED T
              (MBE :LOGIC (XR ,keyword 0 X86)
                   :EXEC (,getter* X86)))
            (DEFINE ,setter ((V :TYPE (,(car type) ,size))
                             X86)
              :PARENTS NIL
              :INLINE T
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
              :ENABLED T
              (MBE :LOGIC (XR ,keyword 0 X86)
                   :EXEC (,getter* X86)))
            (DEFINE ,setter ((V :TYPE (INTEGER ,min ,max))
                             X86)
              :PARENTS NIL
              :INLINE T
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
              :ENABLED T
              (MBE :LOGIC (XR ,keyword 0 X86)
                   :EXEC (,getter* X86)))
            (DEFINE ,setter ((V :TYPE (SATISFIES ,predicate))
                             X86)
              :PARENTS NIL
              :INLINE T
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
              :ENABLED T
              (MBE :LOGIC (XR ,keyword 0 X86)
                   :EXEC (,getter* X86)))
            (DEFINE ,setter (V X86)
              :PARENTS NIL
              :INLINE T
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

  (x86-top-accessors-and-updaters)

  )

;; ======================================================================

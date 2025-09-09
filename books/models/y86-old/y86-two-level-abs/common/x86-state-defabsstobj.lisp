;; x86-state-defabsstobj.lisp

;; In this book, we define the abstract stobj x86-32$a and discharge proof
;; obligations that arise from it.

;; The proofs in this book have been adapted from Matt Kaufmann's work in
;; x86-64-abs.

(in-package "ACL2")

#||

; [Jared]: fool make_cert_help.pl into allowing more memory for this
; book. We would just include centaur/misc/memory-mgmt, but that has a ttag.

(set-max-mem (* 6 (expt 2 30)))

||#

(include-book "x86-memory-low")
(include-book "defexec/other-apps/records/records" :dir :system)

;; ======================================================================

;; Constants and function renaming stuff:

(defmacro g (&rest args)
  `(mget ,@args))

(defmacro s (&rest args)
  `(mset ,@args))

(defmacro defthml (&rest args)
  `(local (defthm ,@args)))

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

(defconst *pruned-x86-32-model*
  (prune-x86-model '(MEM-TABLE MEM-ARRAY MEM-ARRAY-NEXT-ADDR)
                   *x86-32-model*))

(defun create-x86-32-constant-renaming-fn-1 (x86-32-model-field)
  ;; Renaming the constants associated with the concrete stobj

  (let ((name (car x86-32-model-field))
        (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array))
           (let* ((old-constant (mk-name "*" name "I*"))
                  (new-constant (mk-name "*"
                                         (subseq (symbol-name name) 0
                                                 (search "$C" (symbol-name
                                                               name)))
                                         "I*")))
             `(defconst ,new-constant
                ,old-constant)))
          (t
           (let* ((old-constant (mk-name "*" name "*"))
                  (new-constant (mk-name "*"
                                         (subseq (symbol-name name) 0
                                                 (search "$C" (symbol-name
                                                               name)))
                                         "*")))
             `(defconst ,new-constant
                ,old-constant))))))

(defun create-x86-32-constant-renaming-fn (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         `(,(create-x86-32-constant-renaming-fn-1 (car x86-32-model))
           ,@(create-x86-32-constant-renaming-fn (cdr x86-32-model))))))

(defmacro x86-32-constant-renaming ()
  (cons 'progn
        (create-x86-32-constant-renaming-fn *pruned-x86-32-model*)))

(x86-32-constant-renaming)

;; Special case: This constant is the reason why we want the memory fields in
;; the concrete stobj to appear at the end.  The mem field in the abstract
;; stobj occurs at the same position as the memory fields (all three taken
;; together) in the concrete stobj.

(defconst *memi* *mem-tablei*)

;; =====================================================================

;; Definition of the :logic events of the abstract stobj follow: we
;; try to automate the generation of these events as much as possible
;; so that we can reuse this in our X86 model as well.

(defun-sk memp-aux (x)
  (forall i
          (implies (g i x)
                   (and (n32p i)
                        (n08p (g i x))))))

(defn memp (x)
  (and (good-map x)
       (ec-call (memp-aux x))))

;; Since we never want to execute memp, we disable its
;; executable counterpart.
(in-theory (disable (memp)))

;; ======================================================================
;; Abstract stobj recognizer: X86-32$AP
;; ======================================================================

(defun create-x86-32-abs-stobj-recognizer-1 (x86-32-model-field)
  (let ((name (car x86-32-model-field))
        (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array))
           (let* ((stripped-name (mk-name
                                  (subseq (symbol-name name) 0
                                          (search "$C" (symbol-name name)))))
                  (constant (mk-name "*" stripped-name "I*"))
                  (size     (caaddr (caddr x86-32-model-field)))
                  (predicate (mk-name stripped-name "P")))
             `((,predicate
                (NTH
                 ,constant
                 X))

               (EQUAL (LEN (NTH
                            ,constant
                            X))
                      ,size))))
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

(defun create-x86-32-abs-stobj-recognizer-2 (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         `(,(create-x86-32-abs-stobj-recognizer-1
             (car x86-32-model))
           ,@(create-x86-32-abs-stobj-recognizer-2
              (cdr x86-32-model))))))

(defun append-elements (x acc)
  (cond ((endp x)
         acc)
        (t
         (append-elements (cdr x) (append acc (car x))))))

;; (append-elements (create-x86-32-abs-stobj-recognizer-2
;;                   *pruned-x86-32-model*) nil)

(defun create-x86-32-abstract-stobj-recognizer-1
  (x86-32-model pruned-x86-32-model-list)

  `(DEFUN X86-32$AP (X)
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T))
     ;; From :pe x86-32$cp-pre
     (AND (TRUE-LISTP X)
          ;; We subtract two to account for the 3 memory fields that have been
          ;; replaced by a single field in this abstract stobj.
          (= (LENGTH X) ,(- (LEN x86-32-model) 2))
          ,@pruned-x86-32-model-list
          (MEMP (NTH *MEMI* X))
          T)))

(defmacro create-x86-32-abstract-stobj-recognizer ()
  (create-x86-32-abstract-stobj-recognizer-1
   *x86-32-model*
   (append-elements (create-x86-32-abs-stobj-recognizer-2
                     *pruned-x86-32-model*) nil)
   ))

;; X86-32$AP:
(create-x86-32-abstract-stobj-recognizer)

;; ======================================================================
;; Abstract stobj creator: CREATE-X86-32$A:
;; ======================================================================

(defun create-x86-32-abs-stobj-creator-1 (x86-32-model-field)
  (let* ( ;(name (car x86-32-model-field))
         (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array))
           ;; Array fields
           (let* ((initial-val (car (cddddr x86-32-model-field)))
                  (size     (caaddr (caddr x86-32-model-field))))
             `(MAKE-LIST
               ,size
               :INITIAL-ELEMENT
               ,initial-val)))
          ((consp type)
           ;; Non-array fields
           (let* ((initial-val (car (cddddr x86-32-model-field))))
             `(quote ,initial-val)))
          (t
           ;; Fields of type t
           `(quote NIL))
          )))

(defun create-x86-32-abs-stobj-creator-2 (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         `(,(create-x86-32-abs-stobj-creator-1
             (car x86-32-model))
           ,@(create-x86-32-abs-stobj-creator-2
              (cdr x86-32-model))))))

;; (create-x86-32-abs-stobj-creator-2 *pruned-x86-32-model*)

(defun create-x86-32-abstract-stobj-creator-1 (pruned-x86-32-model-list)

  `(DEFUN CREATE-X86-32$A ()
     (DECLARE (XARGS :GUARD T :VERIFY-GUARDS T))
     ;; From :pe create-x86-32$c
     (LIST
      ,@pruned-x86-32-model-list
      'NIL)))

(defmacro create-x86-32-abstract-stobj-creator ()
  (create-x86-32-abstract-stobj-creator-1
   (create-x86-32-abs-stobj-creator-2 *pruned-x86-32-model*)))

;; CREATE-X86-32$A
(create-x86-32-abstract-stobj-creator)

;; ======================================================================
;; Abstract Stobj Accessors and Updaters:
;; ======================================================================

; Next we define the :logic functions for our abstract stobj.  These are the
; same as the logical definitions for the concrete stobj, except for the
; signatures.  We could perhaps avoid replicating those definitions here by
; using defun-nx and simply calling the $c functions -- but we really do want
; to be able to execute the :logic functions, for example in reasoning about
; small stobjs during proofs and in reasoning symbolically with GL (which can
; call functions on concrete data).

(defun x86-32$a-accessors-and-updaters-1 (x86-32-model-field)
  ;; This function is rather brittle, in that it assumes that the
  ;; elements of the x86-32-model are defined in a rigid manner.
  (let ((name (car x86-32-model-field))
        (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
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
                  (length    (caaddr (caddr x86-32-model-field))))
             `((DEFUN ,(mk-name getter) (I X86-32)
                 (DECLARE (XARGS :GUARD (AND (X86-32$AP X86-32)
                                             (NATP I)
                                             (< I ,length))))
                 (NTH I (NTH ,constant X86-32)))
               (DEFUN ,(mk-name setter) (I V X86-32)
                 (DECLARE (XARGS :GUARD (AND (X86-32$AP X86-32)
                                             (NATP I)
                                             (< I ,length)
                                             (UNSIGNED-BYTE-P ,size V))))
                 (UPDATE-NTH-ARRAY ,constant I V X86-32)))))
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
                  (length    (caaddr (caddr x86-32-model-field))))
             `((DEFUN ,(mk-name getter) (I X86-32)
                 (DECLARE (XARGS :GUARD (AND (X86-32$AP X86-32)
                                             (NATP I)
                                             (< I ,length))))
                 (NTH I (NTH ,constant X86-32)))
               (DEFUN ,(mk-name setter) (I V X86-32)
                 (DECLARE (XARGS :GUARD (AND (X86-32$AP X86-32)
                                             (NATP I)
                                             (< I ,length)
                                             (SIGNED-BYTE-P ,size V)))
                          (UPDATE-NTH-ARRAY ,constant I V X86-32)))))
           )
          ((and (consp type)
                (equal (car type) 'unsigned-byte))
           (let* ((name      (mk-name (subseq (symbol-name name) 0
                                              (search "$C" (symbol-name
                                                            name)))))
                  (constant  (mk-name "*" name "*"))
                  (getter    (mk-name name "$A"))
                  (setter    (mk-name "!" name "$A"))
                  (size      (cadr type)))
             `((DEFUN ,getter (X86-32)
                 (DECLARE (XARGS :GUARD (X86-32$AP X86-32)))
                 (NTH ,constant X86-32))
               (DEFUN ,setter (V X86-32)
                 (DECLARE (XARGS :GUARD (AND (X86-32$AP X86-32)
                                             (UNSIGNED-BYTE-P ,size V))))
                 (UPDATE-NTH ,constant V X86-32))
               )))
          ((and (consp type)
                (equal (car type) 'signed-byte))
           (let* ((name      (mk-name (subseq (symbol-name name) 0
                                              (search "$C" (symbol-name
                                                            name)))))
                  (constant  (mk-name "*" name "*"))
                  (getter    (mk-name name "$A"))
                  (setter    (mk-name "!" name "$A"))
                  (size      (cadr type)))
             `((DEFUN ,getter (X86-32)
                 (DECLARE (XARGS :GUARD (X86-32$AP X86-32)))
                 (NTH ,constant X86-32))
               (DEFUN ,setter (V X86-32)
                 (DECLARE (XARGS :GUARD (AND (X86-32$AP X86-32)
                                             (SIGNED-BYTE-P ,size V))))
                 (UPDATE-NTH ,constant V X86-32))
               ))
           )
          ((and (consp type)
                (equal (car type) 'integer))
           (let* ((name      (mk-name (subseq (symbol-name name) 0
                                              (search "$C" (symbol-name
                                                            name)))))
                  (constant  (mk-name "*" name "*"))
                  (getter    (mk-name name "$A"))
                  (setter    (mk-name "!" name "$A"))
                  (size      (cadr type)))
             `((DEFUN ,getter (X86-32)
                 (DECLARE (XARGS :GUARD (X86-32$AP X86-32)))
                 (NTH ,constant X86-32))
               (DEFUN ,setter (V X86-32)
                 (DECLARE (XARGS :GUARD (AND (X86-32$AP X86-32)
                                             (INTEGER 0 ,size V))))
                 (UPDATE-NTH ,constant V X86-32))
               ))
           )
          (t
           ;; type is presumably 'T
           (let* ((name      (mk-name (subseq (symbol-name name) 0
                                              (search "$C" (symbol-name
                                                            name)))))
                  (constant  (mk-name "*" name "*"))
                  (getter    (mk-name name "$A"))
                  (setter    (mk-name "!" name "$A")))
             `((DEFUN ,getter (X86-32)
                 (DECLARE (XARGS :GUARD (X86-32$AP X86-32)))
                 (NTH ,constant X86-32))
               (DEFUN ,setter (V X86-32)
                 (DECLARE (XARGS :GUARD (X86-32$AP X86-32)))
                 (UPDATE-NTH ,constant V X86-32)))
             )))))

(defun x86-32$a-accessors-and-updaters-2 (pruned-x86-32-model)
  (cond ((endp pruned-x86-32-model)
         '())
        (t
         `(,@(x86-32$a-accessors-and-updaters-1 (car pruned-x86-32-model))
           ,@(x86-32$a-accessors-and-updaters-2
              (cdr pruned-x86-32-model))))))

;; (x86-32$a-accessors-and-updaters-2 *pruned-x86-32-model*)

(defmacro x86-32$a-accessors-and-updaters ()
  (cons 'progn
        (x86-32$a-accessors-and-updaters-2 *pruned-x86-32-model*)))

(x86-32$a-accessors-and-updaters)

;; "Special" memory field:

(defun g0 (key alist)
  ;; Either get a non-nil value or return 0
  (declare (xargs :guard (good-map alist)))
  (or (g key alist) 0))

(defun mem$ai (i x86-32)
  (declare (xargs :guard (and (x86-32$ap x86-32)
                              (n32p i))))
  (g0 i (nth *memi* x86-32)))

(defun !mem$ai (i v x86-32)
  (declare (xargs :guard (and (x86-32$ap x86-32)
                              (n32p i)
                              (n08p v))))
  (update-nth *memi*
              (s i v (nth *memi* x86-32))
              x86-32))

;; ======================================================================
;; Correspondence Predicate:
;; ======================================================================

(defun-sk corr-mem (x86-32$c alist)
  ;; corr-mem is our memory correspondence predicate --- it says that
  ;; looking up the memory in the concrete stobj returns the same value
  ;; as looking it up in the abstract stobj.
  (forall i
          (implies (and (natp i)
                        (< i *mem-size-in-bytes*))
                   (equal (mem$ci i x86-32$c)
                          (g0 i alist)))))

(defun create-x86-32-correspondence-predicate-1 (x86-32-model-field)
  (let ((name (car x86-32-model-field))
        (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array))
           (let* ((constant (mk-name "*"
                                     (subseq (symbol-name name) 0
                                             (search "$C" (symbol-name
                                                           name)))
                                     "I*")))
             `(EQUAL (NTH ,constant X)
                     (NTH ,constant Y))))
          (t
           (let* ((constant (mk-name "*"
                                     (subseq (symbol-name name) 0
                                             (search "$C" (symbol-name
                                                           name)))
                                     "*")))
             `(EQUAL (NTH ,constant X)
                     (NTH ,constant Y)))))))

(defun create-x86-32-correspondence-predicate-2 (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         `(,(create-x86-32-correspondence-predicate-1 (car x86-32-model))
           ,@(create-x86-32-correspondence-predicate-2 (cdr x86-32-model))))))

(defun create-x86-32-correspondence-predicate-fn (pruned-x86-32-model)

  ;; This is our correspondence predicate, used in the defabsstobj
  ;; event that is below.  It says that x and y satisfy their
  ;; respective (strong) invariants, and that the fields correspond.
  ;; Here, for fields to correspond means that they are equal, except
  ;; in the mem case, where corr-mem is used to specify that the values
  ;; in the two memories are in agreement.

  `(DEFUN-NX CORR (X Y)
     (AND (X86-32$CP X)
          (X86-32$AP Y)
          ,@pruned-x86-32-model
          (CORR-MEM X (NTH *MEMI* Y)))))

(defmacro create-x86-32-correspondence-predicate ()
  (create-x86-32-correspondence-predicate-fn
   (create-x86-32-correspondence-predicate-2 *pruned-x86-32-model*)))

(create-x86-32-correspondence-predicate)

;; ======================================================================
;; Defabsstobj (X86-32) and proof obligations:
;; ======================================================================

(defun create-x86-32-abstract-stobj-exports-1 (x86-32-model-field)
  (let ((name (car x86-32-model-field))
        (type (caddr x86-32-model-field)))
    (cond ((and (consp type)
                (equal (car type) 'array))
           (let* ((name (mk-name (subseq (symbol-name name) 0
                                         (search "$C" (symbol-name
                                                       name)))))
                  (getter (mk-name name "I"))
                  (setter (mk-name "!" name "I"))
                  (abs-getter (mk-name name "$AI"))
                  (con-getter (mk-name name "$CI"))
                  (abs-setter (mk-name "!" name "$AI"))
                  (con-setter (mk-name "!" name "$CI")))
             `((,getter :LOGIC ,abs-getter
                        :EXEC ,con-getter)
               (,setter :LOGIC ,abs-setter
                        :EXEC ,con-setter))))
          (t
           (let* ((name (mk-name (subseq (symbol-name name) 0
                                         (search "$C" (symbol-name
                                                       name)))))
                  (getter name)
                  (setter (mk-name "!" name))
                  (abs-getter (mk-name name "$A"))
                  (con-getter (mk-name name "$C"))
                  (abs-setter (mk-name "!" name "$A"))
                  (con-setter (mk-name "!" name "$C")))
             `((,getter :LOGIC ,abs-getter
                        :EXEC ,con-getter)
               (,setter :LOGIC ,abs-setter
                        :EXEC ,con-setter)))))))

(defun create-x86-32-abstract-stobj-exports-2 (x86-32-model)
  (cond ((endp x86-32-model)
         '())
        (t
         `(,(create-x86-32-abstract-stobj-exports-1
             (car x86-32-model))
           ,@(create-x86-32-abstract-stobj-exports-2
              (cdr x86-32-model))))))

;; (append-elements (create-x86-32-abstract-stobj-exports-2
;;                   *pruned-x86-32-model*) nil)

(defun create-x86-32-abstract-stobj-fn
  (pruned-x86-32-model-list)

  `(DEFABSSTOBJ X86-32
               :FOUNDATION X86-32$C
               :RECOGNIZER (X86-32P
                            :LOGIC X86-32$AP
                            :EXEC X86-32$CP-PRE)
               :CREATOR (CREATE-X86-32
                         :LOGIC CREATE-X86-32$A
                         :EXEC CREATE-X86-32$C)
               :CORR-FN CORR
               :EXPORTS
               ,(append
                 pruned-x86-32-model-list
                 `((MEMI  :LOGIC  MEM$AI :EXEC MEM$CI))
                 `((!MEMI :LOGIC !MEM$AI :EXEC !MEM$CI :PROTECT T)))))

(defmacro create-x86-32-abstract-stobj ()
  (create-x86-32-abstract-stobj-fn
   (append-elements (create-x86-32-abstract-stobj-exports-2
                     *pruned-x86-32-model*) nil)
   ))

; At this point during development, we evaluated the defabsstobj
; event (obtained by (create-x86-32-abstract-stobj)) below) in order
; to print to the terminal all of its proof obligation events.  We
; pasted those in below -- the parts in caps are the parts that were
; automatically generated (with obvious exceptions, when suffixes
; such as "-1" are added after "}") -- and then put ourselves to the
; task of admitting them all.

; Start proof of CREATE-X86-32@{CORRESPONDENCE}.

; Here comes a trick for avoiding executing make-list-ac on large lists
; (especially mem-table and mem-array in our model).  This will be useful when
; proving subgoals about field recognizers for the concrete stobj.

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
  (implies (and (unsigned-byte-p 32 val)
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
                           (create-x86-32$c)
                           (create-x86-32$a))))

(encapsulate ()

(local
 (defun hack ()
   (with-local-stobj
    x86-32$c
    (mv-let (result x86-32$c)
            (mv (x86-32$cp x86-32$c) x86-32$c)
            result))))

; The :use hint below creates this goal

; (implies (equal (hack) (with-local-stobj ...))
;          (x86-32$cp (create-x86-32$c)))

; which in turn reduces to the following.

; (implies (equal t (x86-32$cp (create-x86-32$c)))
;          (x86-32$cp (create-x86-32$c)))

(defthm x86-32$cp-create-x86-32$c
  (x86-32$cp (create-x86-32$c))
  :hints (("Goal" :use (hack)
           :in-theory (union-theories
                       '((hack))
                       (theory 'minimal-theory))))
  :rule-classes nil)

) ;; End of encapsulate

; Start proof of corr-mem-init (which takes too long using the above
; with-local-stobj approach).

(defun onesp-mem-table (k lst)
; Omit guard; this is only used for helping with the proofs.  Note that lst
; refers to the mem-table.  See the definition of mem$ci to see where (ash k
; -24) comes from.

  (cond ((zp k) t)
        (t (let ((k (1- k)))
             (and (eql (nth (ash k -24) lst) 1)
                  (onesp-mem-table k lst))))))

(encapsulate
 ()
(local (include-book "arithmetic/top" :dir :system))

(local
 (defthm onesp-mem-table-implies-mem$ci-is-0-lemma
   (implies (and (onesp-mem-table k mem-table)
                 (integerp i)
                 (<= 0 i)
                 (integerp k)
                 (< i k))
            (equal (nth (ash i -24) mem-table)
                   1))))

(local
 (defthm onesp-mem-table-implies-mem$ci-is-0
   (implies (and (onesp-mem-table k (nth *mem-tablei* x86-32$c))
                 (integerp i)
                 (<= 0 i)
                 (natp k)
                 (< i k))
            (equal (mem$ci i x86-32$c) 0))
   :hints (("Goal" :in-theory (enable mem$ci mem-tablei)))))

(defthm corr-mem-for-all-ones-in-mem-table
  (implies (onesp-mem-table *mem-size-in-bytes*
                            (nth *mem-tablei* x86-32$c))
           (corr-mem x86-32$c nil))
  :hints (("Goal" :in-theory (enable corr-mem))))
) ;; End of encapsulate

(encapsulate ()

(local (include-book "arithmetic-5/top" :dir :system))

(defthm nth-make-list-ac
  (implies (and (natp k)
                (natp n))
           (equal (nth k (make-list-ac n val ac))
                  (cond ((< k n) val)
                        (t (nth (- k n) ac)))))
  :hints (("Goal" :in-theory (enable nth make-list-ac))))

(local (defthm ash-monotone-2-lemma
         (implies (and (integerp x)
                       (<= 0 x)
                       (integerp y)
                       (<= 0 y)
                       (<= x y)
                       (integerp z))
                  (<= (* x (expt 2 z))
                      (* y (expt 2 z))))
         :rule-classes :linear))

(defthm ash-monotone-2
  (implies (and (natp x)
                (natp y)
                (<= x y)
                (integerp z))
           (<= (ash x z) (ash y z)))
  :rule-classes :linear)

(defthm onesp-mem-table-make-list-ac
  (implies (and (posp k1)
                (natp k2)
                (< (ash (1- k1) -24)
                   k2))
           (onesp-mem-table k1 ; *2^32*
                            (make-list-ac k2 ; *2^24*
                                          1 nil))))
) ;; End of encapsulate

(defthm corr-mem-init
  (corr-mem (create-x86-32$c) nil)
  :rule-classes nil)

(DEFTHML CREATE-X86-32{CORRESPONDENCE}
  (CORR (CREATE-X86-32$C)
        (CREATE-X86-32$A))
  :hints (("Goal" :use (x86-32$cp-create-x86-32$c
                        corr-mem-init))))

(DEFTHML CREATE-X86-32{PRESERVED}
  (X86-32$AP (CREATE-X86-32$A))
  ;; Note that we disable the executable counterpart of x86-32$ap.
  :hints (("Goal" :in-theory (disable (x86-32$ap)))))

(DEFTHML RGFI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 8))
           (EQUAL (RGF$CI I X86-32$C)
                  (RGF$AI I X86-32)))
  :hints (("Goal" :in-theory (enable rgf$ci))))

(DEFTHML RGFI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 8))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (RGF$C-LENGTH X86-32$C)))))

;; Lemmas needed for the "!" correspondence theorems:

(defthm mem-tablei-update-nth
  (implies (not (equal n *mem-tablei*))
           (equal (mem-tablei i (update-nth n x x86-32))
                  (mem-tablei i x86-32)))
  :hints (("Goal" :in-theory (enable mem-tablei))))

(defthm mem-arrayi-update-nth
  (implies (not (equal n *mem-arrayi*))
           (equal (mem-arrayi i (update-nth n x x86-32))
                  (mem-arrayi i x86-32)))
  :hints (("Goal" :in-theory (enable mem-arrayi))))

(defthm mem-array-next-addr-update-nth
  (implies (not (equal n *mem-array-next-addr*))
           (equal (mem-array-next-addr (update-nth n x x86-32))
                  (mem-array-next-addr x86-32)))
  :hints (("Goal" :in-theory (enable mem-array-next-addr))))
(defthm memi$c-update-nth
  (implies (and (not (equal n *mem-tablei*))
                (not (equal n *mem-arrayi*))
                (not (equal n *mem-array-next-addr*)))
           (equal (mem$ci i (update-nth n x x86-32))
                  (mem$ci i x86-32)))
  :hints (("Goal" :in-theory (enable mem$ci))))

(in-theory (disable corr-mem))

(defthm corr-mem-update-nth
  (implies (and (not (equal n *mem-tablei*))
                (not (equal n *mem-arrayi*))
                (not (equal n *mem-array-next-addr*)))
           (iff (corr-mem (update-nth n x x86-32) alist)
                (corr-mem x86-32 alist)))
  :hints (("Goal"
           :in-theory (disable corr-mem mem$ci !mem$ci g0)
           :use ((:instance corr-mem
                            (x86-32$c (update-nth n x x86-32)))
                 (:instance corr-mem-necc
                            (x86-32$c x86-32)
                            (i (corr-mem-witness (update-nth n x x86-32)
                                                 alist)))
                 (:instance corr-mem
                            (x86-32$c x86-32))
                 (:instance corr-mem-necc
                            (x86-32$c (update-nth n x x86-32))
                            (i (corr-mem-witness x86-32 alist)))))))

(local (in-theory (disable update-nth)))

(DEFTHML !RGFI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 8)
                (UNSIGNED-BYTE-P 32 V))
           (CORR (!RGF$CI I V X86-32$C)
                 (!RGF$AI I V X86-32)))
  :hints (("Goal" :in-theory (enable !rgf$ci x86-32$cp x86-32$cp-pre))))

(DEFTHML !RGFI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 8)
                (UNSIGNED-BYTE-P 32 V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (RGF$C-LENGTH X86-32$C))
                (UNSIGNED-BYTE-P 32 V))))

(DEFTHML !RGFI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (NATP I)
                (< I 8)
                (UNSIGNED-BYTE-P 32 V))
           (X86-32$AP (!RGF$AI I V X86-32))))

(DEFTHML EIP{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32))
           (EQUAL (EIP$C X86-32$C)
                  (EIP$A X86-32)))
  :hints (("Goal" :in-theory (enable eip$c))))

(DEFTHML !EIP{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (UNSIGNED-BYTE-P 32 V))
           (CORR (!EIP$C V X86-32$C)
                 (!EIP$A V X86-32)))
  :hints (("Goal" :in-theory (enable eipp !eip$c x86-32$cp x86-32$cp-pre))))

(DEFTHML !EIP{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (UNSIGNED-BYTE-P 32 V))
           (X86-32$AP (!EIP$A V X86-32)))
  :hints(("Goal" :in-theory (enable eipp))))

(DEFTHML FLG{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32))
           (EQUAL (FLG$C X86-32$C)
                  (FLG$A X86-32)))
  :hints (("Goal" :in-theory (enable flg$c))))

(DEFTHML !FLG{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (UNSIGNED-BYTE-P 32 V))
           (CORR (!FLG$C V X86-32$C)
                 (!FLG$A V X86-32)))
  :hints (("Goal" :in-theory (enable flgp !flg$c x86-32$cp x86-32$cp-pre))))

(DEFTHML !FLG{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (UNSIGNED-BYTE-P 32 V))
           (X86-32$AP (!FLG$A V X86-32)))
  :hints (("Goal" :in-theory (enable flgp))))

(DEFTHML SEGI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6))
           (EQUAL (SEG$CI I X86-32$C)
                  (SEG$AI I X86-32)))
  :hints (("Goal" :in-theory (enable seg$ci))))

(DEFTHML SEGI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SEG$C-LENGTH X86-32$C)))))

(DEFTHML !SEGI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 16 V))
           (CORR (!SEG$CI I V X86-32$C)
                 (!SEG$AI I V X86-32)))
  :hints (("Goal" :in-theory (enable !seg$ci x86-32$cp x86-32$cp-pre))))

(DEFTHML !SEGI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 16 V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SEG$C-LENGTH X86-32$C))
                (UNSIGNED-BYTE-P 16 V))))

(DEFTHML !SEGI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 16 V))
           (X86-32$AP (!SEG$AI I V X86-32))))

(DEFTHML STRI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 2))
           (EQUAL (STR$CI I X86-32$C)
                  (STR$AI I X86-32)))
  :hints (("Goal" :in-theory (enable str$ci))))


(DEFTHML STRI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 2))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (STR$C-LENGTH X86-32$C)))))

(DEFTHML !STRI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 2)
                (UNSIGNED-BYTE-P 48 V))
           (CORR (!STR$CI I V X86-32$C)
                 (!STR$AI I V X86-32)))
  :hints (("Goal" :in-theory (enable !str$ci x86-32$cp x86-32$cp-pre))))

(DEFTHML !STRI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 2)
                (UNSIGNED-BYTE-P 48 V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (STR$C-LENGTH X86-32$C))
                (UNSIGNED-BYTE-P 48 V))))

(DEFTHML !STRI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (NATP I)
                (< I 2)
                (UNSIGNED-BYTE-P 48 V))
           (X86-32$AP (!STR$AI I V X86-32))))

(DEFTHML SSRI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 2))
           (EQUAL (SSR$CI I X86-32$C)
                  (SSR$AI I X86-32)))
  :hints (("Goal" :in-theory (enable ssr$ci))))

(DEFTHML SSRI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 2))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SSR$C-LENGTH X86-32$C)))))

(DEFTHML !SSRI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 2)
                (UNSIGNED-BYTE-P 16 V))
           (CORR (!SSR$CI I V X86-32$C)
                 (!SSR$AI I V X86-32)))
  :hints (("Goal" :in-theory (enable !ssr$ci x86-32$cp x86-32$cp-pre))))

(DEFTHML !SSRI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 2)
                (UNSIGNED-BYTE-P 16 V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SSR$C-LENGTH X86-32$C))
                (UNSIGNED-BYTE-P 16 V))))

(DEFTHML !SSRI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (NATP I)
                (< I 2)
                (UNSIGNED-BYTE-P 16 V))
           (X86-32$AP (!SSR$AI I V X86-32))))

(DEFTHML CTRI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 18))
           (EQUAL (CTR$CI I X86-32$C)
                  (CTR$AI I X86-32)))
  :hints (("Goal" :in-theory (enable ctr$ci))))

(DEFTHML CTRI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 18))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (CTR$C-LENGTH X86-32$C)))))

(DEFTHML !CTRI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 18)
                (UNSIGNED-BYTE-P 32 V))
           (CORR (!CTR$CI I V X86-32$C)
                 (!CTR$AI I V X86-32)))
  :hints (("Goal" :in-theory (enable !ctr$ci x86-32$cp x86-32$cp-pre))))

(DEFTHML !CTRI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 18)
                (UNSIGNED-BYTE-P 32 V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (CTR$C-LENGTH X86-32$C))
                (UNSIGNED-BYTE-P 32 V))))

(DEFTHML !CTRI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (NATP I)
                (< I 18)
                (UNSIGNED-BYTE-P 32 V))
           (X86-32$AP (!CTR$AI I V X86-32))))

(DEFTHML DBGI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 8))
           (EQUAL (DBG$CI I X86-32$C)
                  (DBG$AI I X86-32)))
  :hints (("Goal" :in-theory (enable dbg$ci))))

(DEFTHML DBGI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 8))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (DBG$C-LENGTH X86-32$C)))))

(DEFTHML !DBGI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 8)
                (UNSIGNED-BYTE-P 32 V))
           (CORR (!DBG$CI I V X86-32$C)
                 (!DBG$AI I V X86-32)))
  :hints (("Goal" :in-theory (enable !dbg$ci x86-32$cp x86-32$cp-pre))))

(DEFTHML !DBGI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 8)
                (UNSIGNED-BYTE-P 32 V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (DBG$C-LENGTH X86-32$C))
                (UNSIGNED-BYTE-P 32 V))))

(DEFTHML !DBGI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (NATP I)
                (< I 8)
                (UNSIGNED-BYTE-P 32 V))
           (X86-32$AP (!DBG$AI I V X86-32))))

(DEFTHML SEG-BASEI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6))
           (EQUAL (SEG-BASE$CI I X86-32$C)
                  (SEG-BASE$AI I X86-32)))
  :hints (("Goal" :in-theory (enable seg-base$ci))))

(DEFTHML SEG-BASEI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SEG-BASE$C-LENGTH X86-32$C)))))

(DEFTHML !SEG-BASEI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 32 V))
           (CORR (!SEG-BASE$CI I V X86-32$C)
                 (!SEG-BASE$AI I V X86-32)))
  :hints (("Goal" :in-theory (enable !seg-base$ci x86-32$cp x86-32$cp-pre))))

(DEFTHML !SEG-BASEI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 32 V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SEG-BASE$C-LENGTH X86-32$C))
                (UNSIGNED-BYTE-P 32 V))))

(DEFTHML !SEG-BASEI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 32 V))
           (X86-32$AP (!SEG-BASE$AI I V X86-32))))

(DEFTHML SEG-LIMITI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6))
           (EQUAL (SEG-LIMIT$CI I X86-32$C)
                  (SEG-LIMIT$AI I X86-32)))
  :hints (("Goal" :in-theory (enable seg-limit$ci))))

(DEFTHML SEG-LIMITI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SEG-LIMIT$C-LENGTH X86-32$C)))))

(DEFTHML !SEG-LIMITI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 20 V))
           (CORR (!SEG-LIMIT$CI I V X86-32$C)
                 (!SEG-LIMIT$AI I V X86-32)))
  :hints (("Goal" :in-theory (enable !seg-limit$ci x86-32$cp x86-32$cp-pre))))

(DEFTHML !SEG-LIMITI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 20 V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SEG-LIMIT$C-LENGTH X86-32$C))
                (UNSIGNED-BYTE-P 20 V))))

(DEFTHML !SEG-LIMITI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 20 V))
           (X86-32$AP (!SEG-LIMIT$AI I V X86-32))))

(DEFTHML SEG-ACCESSI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6))
           (EQUAL (SEG-ACCESS$CI I X86-32$C)
                  (SEG-ACCESS$AI I X86-32)))
  :hints (("Goal" :in-theory (enable seg-access$ci))))

(DEFTHML SEG-ACCESSI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SEG-ACCESS$C-LENGTH X86-32$C)))))

(DEFTHML !SEG-ACCESSI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 12 V))
           (CORR (!SEG-ACCESS$CI I V X86-32$C)
                 (!SEG-ACCESS$AI I V X86-32)))
  :hints (("Goal" :in-theory (enable !seg-access$ci x86-32$cp x86-32$cp-pre))))

(DEFTHML !SEG-ACCESSI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 12 V))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I (SEG-ACCESS$C-LENGTH X86-32$C))
                (UNSIGNED-BYTE-P 12 V))))

(DEFTHML !SEG-ACCESSI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (NATP I)
                (< I 6)
                (UNSIGNED-BYTE-P 12 V))
           (X86-32$AP (!SEG-ACCESS$AI I V X86-32))))

(DEFTHML MS{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32))
           (EQUAL (MS$C X86-32$C) (MS$A X86-32)))
  :hints (("Goal" :in-theory (enable ms$c))))

(DEFTHML !MS{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32))
           (CORR (!MS$C V X86-32$C)
                 (!MS$A V X86-32)))
  :hints (("Goal" :in-theory (enable !ms$c x86-32$cp x86-32$cp-pre))))

(DEFTHML !MS{PRESERVED}
  (IMPLIES (X86-32$AP X86-32)
           (X86-32$AP (!MS$A V X86-32))))


(encapsulate ()

(local (include-book "arithmetic/top-with-meta" :dir :system))

(defthm corr-mem-suff
  (let ((i (corr-mem-witness x alist)))
    (implies (equal (mem$ci i x) (g0 i alist))
             (corr-mem x alist)))
  :hints (("Goal" :in-theory (enable corr-mem))))

(defthm nth-!mem$ci-is-no-op
  (implies (and (not (equal n *mem-tablei*))
                (not (equal n *mem-arrayi*))
                (not (equal n *mem-array-next-addr*)))
           (equal (nth n (!mem$ci i v x86-32$c))
                  (nth n x86-32$c)))
  :hints (("Goal" :in-theory (e/d
                              (!mem$ci
                               !mem-arrayi
                               !mem-tablei
                               !mem-array-next-addr)
                              (natp-mem-tablep-when-valid-mem-table-index)))))

(in-theory (disable corr-mem-necc))

(defthm corr-mem-necc-rewrite
  (implies (and (corr-mem x86-32$c alist)
                (force (integerp i))
                (force (<= 0 i))
                (force (< i *2^32*)))
           (equal (mem$ci i x86-32$c)
                  (g0 i alist)))
  :hints (("Goal" :use corr-mem-necc)))
) ;; End of encapsulate

(DEFTHML MEMI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (INTEGERP I)
                (<= 0 I)
                (< I 4294967296))
           (EQUAL (MEM$CI I X86-32$C)
                  (MEM$AI I X86-32))))

(DEFTHML MEMI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (INTEGERP I)
                (<= 0 I)
                (< I 4294967296))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I 4294967296)
                (X86-32$CP X86-32$C))))

(defthm memp-s
  (implies (and (memp mem)
                (n32p i)
                (n08p v))
           (memp (s i v mem)))
  :hints (("Goal"
           :in-theory (e/d (mget-of-mset-redux)
                           (memp-aux))
           :use ((:instance memp-aux-necc
                            (i (memp-aux-witness (s i v mem)))
                            (x mem)))
           :expand ((memp-aux (s i v mem))))))

(DEFTHML !MEMI{CORRESPONDENCE}-1
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (INTEGERP I)
                (<= 0 I)
                (< I 4294967296)
                (INTEGERP V)
                (<= 0 V)
                (< V 256))
           (X86-32$AP (!MEM$AI I V X86-32)))
  :hints (("Goal" :in-theory (disable memp))))

(DEFTHML !MEMI{CORRESPONDENCE}-2
  (IMPLIES (AND (CORR X86-32$C X86-32)
                ;; (x86-32$c x86-32$c) is taken care
                ;; of by (CORR X86-32$C X86-32).
                (X86-32$AP X86-32)
                (INTEGERP I)
                (<= 0 I)
                (< I 4294967296)
                (INTEGERP V)
                (<= 0 V)
                (< V 256)
                (natp k)
                (< k *memi*)) ;; 12
           (EQUAL (NTH k X86-32$C)
                  (NTH k (!MEM$AI I V X86-32))))
  :hints (("Goal" :cases ((member k '(0 1 2 3 4 5 6 7 8 9 10 11))))))

(defthm !memi{correspondence}-3-1
  (implies (and (x86-32$cp-pre x86-32$c)
                (good-memp x86-32$c)
                (true-listp x86-32)
                (equal (len x86-32) 13)
                (memp (nth *memi* x86-32))
                (corr-mem x86-32$c
                          (nth *memi* x86-32)) ;; 12
                (n32p i)
                (n08p v))
           (corr-mem (!mem$ci i v x86-32$c)
                     (s i v (nth *memi* x86-32))))
  :hints (("Goal"
           :in-theory (e/d (x86-32$cp)
                           (memp mem-table-length mem-array-length
                                 good-memp good-mem-arrayp))
           :expand ((corr-mem (!mem$ci i v x86-32$c)
                              (s i v (nth *memi* x86-32)))))))

(defthm !memi{correspondence}-3
  (implies (and (corr x86-32$c x86-32)
                (x86-32$ap x86-32)
                (n32p i)
                (n08p v))
           (corr-mem (!mem$ci i v x86-32$c)
                     (nth *memi* (!mem$ai i v x86-32))))
  :hints (("Goal"
           :in-theory
           (e/d (x86-32$cp)
                (memp mem-table-length mem-array-length good-memp
                      good-mem-arrayp)))))

(DEFTHML !MEMI{CORRESPONDENCE}-4
  (IMPLIES (AND (CORR X86-32$C X86-32)
                ;; (x86-32$c x86-32$c) is taken care
                ;; of by (CORR X86-32$C X86-32).
                (X86-32$AP X86-32)
                (INTEGERP I)
                (<= 0 I)
                (< I 4294967296)
                (INTEGERP V)
                (<= 0 V)
                (< V 256)
                (natp k)
                (< k *memi*)) ;; 12
           (EQUAL (NTH k (!mem$ci i v X86-32$C))
                  (NTH k (!MEM$AI I V X86-32))))
  :hints (("Goal" :cases ((member k '(0 1 2 3 4 5 6 7 8 9 10 11))))))

(DEFTHML !MEMI{CORRESPONDENCE}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (INTEGERP I)
                (<= 0 I)
                (< I *2^32*)
                (INTEGERP V)
                (<= 0 V)
                (< V 256))
           (CORR (!MEM$CI I V X86-32$C)
                 (!MEM$AI I V X86-32)))
  :hints (("Goal"
           :in-theory (disable corr !mem$ai x86-32$ap nth-!mem$ci-is-no-op)
           :use ((:instance nth-!mem$ci-is-no-op
                            (i i)
                            (v v)))
           :expand ((corr (!mem$ci i v x86-32$c)
                          (!mem$ai i v x86-32))))))

(DEFTHML !MEMI{GUARD-THM}
  (IMPLIES (AND (CORR X86-32$C X86-32)
                (X86-32$AP X86-32)
                (INTEGERP I)
                (<= 0 I)
                (< I 4294967296)
                (INTEGERP V)
                (<= 0 V)
                (< V 256))
           (AND (INTEGERP I)
                (<= 0 I)
                (< I 4294967296)
                (INTEGERP V)
                (<= 0 V)
                (< V 256)
                (X86-32$CP X86-32$C))))

(DEFTHML !MEMI{PRESERVED}
  (IMPLIES (AND (X86-32$AP X86-32)
                (INTEGERP I)
                (<= 0 I)
                (< I 4294967296)
                (INTEGERP V)
                (<= 0 V)
                (< V 256))
           (X86-32$AP (!MEM$AI I V X86-32))))

;; X86-32
(create-x86-32-abstract-stobj)

;; ======================================================================

;; Disabling some functions/rules:

(in-theory (disable memp-aux))

;; ======================================================================

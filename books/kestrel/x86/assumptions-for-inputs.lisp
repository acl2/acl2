; Generating assumptions about inputs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2025 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "portcullis")
(include-book "kestrel/memory/memory48" :dir :system) ; since this book knows about disjoint-regions48p
(include-book "std/util/bstar" :dir :system)
(include-book "kestrel/utilities/map-symbol-name" :dir :system)
(include-book "kestrel/utilities/pack" :dir :system)
(include-book "kestrel/utilities/forms" :dir :system)
(include-book "kestrel/alists-light/lookup-equal" :dir :system)
(include-book "kestrel/strings-light/string-ends-withp" :dir :system)
(include-book "kestrel/strings-light/strip-suffix-from-string" :dir :system)
(include-book "kestrel/strings-light/split-string" :dir :system)
(include-book "kestrel/strings-light/parse-decimal-digits" :dir :system)
(local (include-book "kestrel/utilities/doublet-listp" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/typed-lists-light/symbol-listp" :dir :system))

(in-theory (disable mv-nth))

;; Returns (mv assumptions input-assumption-vars-rev) where the input-assumption-vars-rev are in reverse order.
;; Makes assumptions to introduce a variable for each element of the array, from INDEX up to ELEMENT-COUNT - 1.
;; TODO: Support expressing bytes in terms of single bit-vars
;; TODO: Support expressing the whole array as a single value (a byte-list)
;; todo: rename because this now also puts in non-null assumptions
(defund var-intro-assumptions-for-array-input (index element-count bytes-per-element pointer-name var-name-base type-assumptions-for-array-varsp assumptions-acc vars-acc)
  (declare (xargs :guard (and (natp index)
                              (natp element-count)
                              (posp bytes-per-element)
                              (symbolp pointer-name)
                              (symbolp var-name-base)
                              (booleanp type-assumptions-for-array-varsp)
                              (true-listp assumptions-acc)
                              (symbol-listp vars-acc))
                  :measure (nfix (+ 1 (- element-count index)))))
  (if (or (not (mbt (and (natp element-count)
                         (natp index))))
          (<= element-count index))
      (mv assumptions-acc vars-acc) ; will be reversed later
    (let ((var (acl2::pack-in-package "X" var-name-base index) ; todo: consider this (acl2::pack-in-package "X" var-name-base "[" index "]").  better if the var-name-base ends in a number
               )
          (element-offset (* index bytes-per-element))
          )
      (var-intro-assumptions-for-array-input (+ 1 index) element-count bytes-per-element pointer-name var-name-base type-assumptions-for-array-varsp
                                             (cons `(equal (read ,bytes-per-element
                                                                 ,(if (= 0 index)
                                                                      pointer-name ; special case (offset of 0)
                                                                    `(+ ,element-offset ,pointer-name) ; todo: option to use bvplus here?
                                                                    )
                                                                 x86)
                                                           ,var)
                                                   (cons (if (= 0 index)
                                                             ;; or should the size here be 48?
                                                             `(not (equal '0 (bvchop '64 ,pointer-name)))
                                                           `(not (equal '0 (bvplus '64 ',element-offset ,pointer-name))) ; may get simplified later
                                                           )
                                                         (if type-assumptions-for-array-varsp
                                                             (cons `(unsigned-byte-p ',(* 8 bytes-per-element) ,var)
                                                                   assumptions-acc)
                                                           assumptions-acc)))
                                             (cons var vars-acc)))))

(local
  (defthm true-listp-of-mv-nth-0-of-var-intro-assumptions-for-array-input
    (implies (true-listp assumptions-acc)
             (true-listp (mv-nth 0 (var-intro-assumptions-for-array-input index element-count bytes-per-element pointer-name var-name-base type-assumptions-for-array-varsp assumptions-acc vars-acc))))
    :hints (("Goal" :in-theory (enable var-intro-assumptions-for-array-input)))))

(local
  (defthm symbol-listp-of-mv-nth-1-of-var-intro-assumptions-for-array-input
    (implies (symbol-listp vars-acc)
             (symbol-listp (mv-nth 1 (var-intro-assumptions-for-array-input index element-count bytes-per-element pointer-name var-name-base type-assumptions-for-array-varsp assumptions-acc vars-acc))))
    :hints (("Goal" :in-theory (enable var-intro-assumptions-for-array-input)))))

;; (var-intro-assumptions-for-array-input '0 '6 '4 'foo-ptr 'foo)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make assertions that the region at ADDRESS with length LEN is separate from all the
;; regions represented by ADDRESSES-AND-LENS.
;; Not sure what order is better for the args in disjoint-regions48p
(defund make-separate-claims (address len addresses-and-lens)
  (declare (xargs :guard (alistp addresses-and-lens)
                  :guard-hints (("Goal" :in-theory (enable alistp)))))
  (if (endp addresses-and-lens)
      nil
    (let* ((pair (first addresses-and-lens))
           (this-address (car pair))
           (this-len (cdr pair)))
      ;; (cons `(separate :r ,len ,address
      ;;                  :r ,this-len ,this-address)
      (cons `(disjoint-regions48p ,len ,address
                                  ,this-len ,this-address)
            (make-separate-claims address len (rest addresses-and-lens)))
      ;)
      )))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; todo: think about signed (i) vs unsigned (u)
(defconst *scalar-type-to-bytes-alist*
  '(("U8" . 1)
    ("I8" . 1)
    ("U16" . 2)
    ("I16" . 2)
    ("U32" . 4)
    ("I32" . 4)
    ("U64" . 8)
    ("I64" . 8)
    ;; anything larger would not fit in register
    ))

(defund bytes-in-scalar-type (type)
  (declare (xargs :guard (stringp type)))
  (let ((res (lookup-equal type *scalar-type-to-bytes-alist*)))
    (if res
        res
      (prog2$ (er hard? 'bytes-in-scalar-type "Unsupported type: ~x0." type)
              ;; for guard proof:
              1))))

(defthm posp-of-bytes-in-scalar-type
  (posp (bytes-in-scalar-type type))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable bytes-in-scalar-type lookup-equal))))

(defun parsed-typep (ty)
  (declare (xargs :guard t))
  (or (and (stringp ty) ; for a scalar type ; todo: use a symbol instead?!
           (if (assoc-equal ty *scalar-type-to-bytes-alist*) t nil))
      (and (call-of :pointer ty)
           (= 1 (len (fargs ty)))
           (parsed-typep (farg1 ty)))
      (and (call-of :array ty)
           (= 2 (len (fargs ty)))
           (parsed-typep (farg1 ty))
           (posp (farg2 ty)))))

;; Returns a parsed-type or :error.
;; Types are parsed right-to-left, with the rightmost thing being the top construct.
(defund parse-type-string (type-str)
  (declare (xargs :guard (stringp type-str)
                  :measure (length type-str)
                  :hints (("Goal" :in-theory (disable length)))))
  (if (acl2::string-ends-withp type-str "*")
      (b* ((parsed-inner-type (parse-type-string (acl2::strip-suffix-from-string "*" type-str)))
           ((when (eq :error parsed-inner-type)) :error))
        `(:pointer ,parsed-inner-type))
    (if (acl2::string-ends-withp type-str "]")
        (b* (((mv foundp element-type-str rest) (acl2::split-string type-str #\[))
             ((when (not foundp)) :error)
             (element-count-string (acl2::strip-suffix-from-string "]" rest))
             (element-count (acl2::parse-string-as-decimal-number element-count-string))
             ((when (not (posp element-count))) :error)
             (parsed-element-type (parse-type-string element-type-str))
             ((when (eq :error parsed-element-type)) :error))
          `(:array ,parsed-element-type ,element-count))
      ;; a scalar type:
      (if (assoc-equal type-str *scalar-type-to-bytes-alist*)
          type-str ; why not convert back to symbol?
        :error))))

(defthm parsed-typep-of-parse-type-string
  (implies (and (not (equal :error (parse-type-string type-str)))
                (stringp type-str))
           (parsed-typep (parse-type-string type-str)))
  :hints (("Goal" :in-theory (enable parse-type-string))))

;; Returns a parsed-type or :error.
;; Types are parsed right-to-left, with the rightmost thing being the top construct.
(defund parse-type (sym)
  (declare (xargs :guard (symbolp sym)))
  (parse-type-string (symbol-name sym)))

(defthm parsed-typep-of-parse-type
  (implies (not (equal :error (parse-type sym)))
           (parsed-typep (parse-type sym)))
  :hints (("Goal" :in-theory (enable parse-type))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; todo: strengthen: what are the allowed types?  todo: Allow float types?
(defun names-and-typesp (names-and-types)
  (declare (xargs :guard t))
  (and (doublet-listp names-and-types)
       (let ((names (strip-cars names-and-types))
             (types (strip-cadrs names-and-types)))
         (and (symbol-listp names)
              (no-duplicatesp-eq names) ; can't use the same name for multiple inputs
              ;; Can't use the same name as a register (would make the output-indicator ambiguous):
              ;; todo: print a message when this check fails:
              (not (intersection-equal (acl2::map-symbol-name names) '("RAX" "EAX" "ZMM0" "YMM0" "XMM0"))) ; todo: keep in sync with wrap-in-normal-output-extractor
              ;; Types are symbols, e.g., u8[64]:
              (symbol-listp types)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv assumptions input-assumption-vars-rev) where the input-assumption-vars-rev are in reverse order.
;; todo: check for repeated vars, or prove they can't occur
(defund assumptions-and-vars-for-input (input-name
                                        input-type ;; examples: u32 or u32* or u32[4]
                                        state-component
                                        stack-slots
                                        existing-stack-slots
                                        disjoint-chunk-addresses-and-lens
                                        type-assumptions-for-array-varsp)
  (declare (xargs :guard (and (symbolp input-name)
                              (symbolp input-type)
                              ;;state-component might be rdi or (rdi x86)
                              (natp stack-slots)
                              (natp existing-stack-slots)
                              (alistp disjoint-chunk-addresses-and-lens) ; cars are terms
                              (nat-listp (strip-cdrs disjoint-chunk-addresses-and-lens))
                              (booleanp type-assumptions-for-array-varsp))))
  (let ((type (parse-type input-type)))
    (if (eq :error type)
        (prog2$ (er hard? 'assumptions-and-vars-for-input "Bad input type: ~x0." type)
                (mv nil nil))
      (if (atom type) ; scalar (e.g., "U32")
          ;; just put in the var name for the state component:
          ;; todo: what about signed/unsigned?
          ;; todo: add type hyps for the var?
          (mv `((equal ,state-component ,input-name))
              `(,input-name))
        (let ((stack-byte-count (* 8 stack-slots)) ; each stack element is 64-bits
              (existing-stack-byte-count (* 8 existing-stack-slots)))
          (if (call-of :pointer type)
              (if (not (stringp (farg1 type))) ; for guards? ; todo: what about a pointer to something else? ; todo: give this check a name, e.g., scalar-typep
                  ;; TODO: Handle pointer to array, or struct, or pointer
                  (prog2$ (er hard? 'assumptions-and-vars-for-input "Unsupported input type: ~x0." type)
                          (mv nil nil))
                (let* ((base-type (farg1 type))
                       (numbytes (bytes-in-scalar-type base-type))
                       (pointer-name (acl2::pack-in-package "X" input-name '_ptr)) ;todo: watch for clashes; todo: should this be the main name and the other the "contents"?
                       )
                  (mv `(;; Rewriting will replace the state component with the pointer's name:
                        (equal ,state-component ,pointer-name)
                        ;; todo: what about reading individual bytes?:  don't trim down reads?
                        (equal (read ,numbytes ,pointer-name x86) ,input-name)
                        ;; The pointer, and subsequent bytes, are canonical:
                        (canonical-regionp ,numbytes ,pointer-name)
                        (integerp ,pointer-name)
                        ;; The input is disjoint from the space into which the stack will grow:
                        (disjoint-regions48p ,numbytes ,pointer-name
                                             ,stack-byte-count
                                             (bvplus 48 ,(bvchop 48 (- stack-byte-count)) (rsp x86)))
                        ;; The input is disjoint from the code:
                        ,@(make-separate-claims pointer-name numbytes disjoint-chunk-addresses-and-lens)
                        ;; The input is disjoint from the saved return address:
                        (disjoint-regions48p ,existing-stack-byte-count (rsp x86)
                                             ,numbytes ,pointer-name))
                      ;; will be reversed later:
                      (list input-name pointer-name))))
            (if (and (call-of :array type) ; (:array <base-type> <element-count>)
                     (stringp (farg1 type)) ; for guards? ; todo name this ; todo relax this
                     (natp (farg2 type))    ; for guards ; todo: must be true?
                     )
                ;; TODO: What if the whole array fits in a register?
                (b* ((base-type (farg1 type))
                     (element-count (farg2 type)) ; todo: consider 0
                     (bytes-per-element (bytes-in-scalar-type base-type))
                     (numbytes (* element-count bytes-per-element))
                     (pointer-name (acl2::pack-in-package "X" input-name '_ptr)) ;todo: watch for clashes; todo: should this be the main name and the other the "contents"?
                     ((mv assumptions input-assumption-vars-rev)
                      (var-intro-assumptions-for-array-input 0 element-count bytes-per-element pointer-name input-name type-assumptions-for-array-varsp nil nil)))
                  (mv ;;todo: think about the order here (it will be reversed!):
                    (append assumptions
                            `(;; Rewriting will replace the state component with the pointer's name:
                              (equal ,state-component ,pointer-name)
                              ;; The base adddress of the array, and subsequent bytes, are canonical:
                              (canonical-regionp ,numbytes ,pointer-name)
                              (integerp ,pointer-name)
                              ;; The input is disjoint from the space into which the stack will grow:
                              (separate :r ,numbytes ,pointer-name
                                        :r ,stack-byte-count
                                        (+ ,(- stack-byte-count) (rsp x86)))
                              (disjoint-regions48p ,numbytes ,pointer-name
                                                   ,stack-byte-count
                                                   (bvplus 48 ,(bvchop 48 (- stack-byte-count)) (rsp x86)))
                              ;; The input is disjoint from the code:
                              ,@(make-separate-claims pointer-name numbytes disjoint-chunk-addresses-and-lens)
                              ;; The input is disjoint from the saved return address:
                              ;; todo: reorder args?
                              (separate :r ,existing-stack-byte-count (rsp x86)
                                        :r ,numbytes ,pointer-name)
                              (disjoint-regions48p ,existing-stack-byte-count (rsp x86)
                                                   ,numbytes ,pointer-name)))
                    ;; will be reversed later:
                    (append input-assumption-vars-rev (list pointer-name))))
              (prog2$ (er hard? 'assumptions-and-vars-for-input "Bad type: ~x0." type)
                      (mv nil nil)))))))))

(local
  (defthm true-listp-of-mv-nth-0-of-assumptions-and-vars-for-input
    (implies (true-listp assumptions-acc)
             (true-listp (mv-nth 0 (assumptions-and-vars-for-input input-name input-type state-component stack-slots existing-stack-slots disjoint-chunk-addresses-and-lens type-assumptions-for-array-varsp))))
    :hints (("Goal" :in-theory (enable assumptions-and-vars-for-input)))))

(local
  (defthm symbol-listp-of-mv-nth-1-of-assumptions-and-vars-for-input
    (implies (and (symbol-listp vars-acc)
                  (symbolp input-name))
             (symbol-listp (mv-nth 1 (assumptions-and-vars-for-input input-name input-type state-component stack-slots existing-stack-slots disjoint-chunk-addresses-and-lens type-assumptions-for-array-varsp))))
    :hints (("Goal" :in-theory (enable assumptions-and-vars-for-input)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns (mv assumptions input-assumption-vars).
;; might have extra, unneeded items in state-components
(defund assumptions-and-vars-for-inputs (input-names-and-types state-components stack-slots existing-stack-slots disjoint-chunk-addresses-and-lens type-assumptions-for-array-varsp assumptions-acc vars-acc)
  (declare (xargs :guard (and (names-and-typesp input-names-and-types)
                              (true-listp state-components)
                              (natp stack-slots)
                              (natp existing-stack-slots)
                              (alistp disjoint-chunk-addresses-and-lens) ; cars are terms
                              (nat-listp (strip-cdrs disjoint-chunk-addresses-and-lens))
                              (booleanp type-assumptions-for-array-varsp)
                              (true-listp assumptions-acc)
                              (symbol-listp vars-acc))
                  :guard-hints (("Goal" :in-theory (enable acl2::true-listp-when-symbol-listp-rewrite-unlimited)))))
  (if (endp input-names-and-types)
      (mv (reverse assumptions-acc)
          (reverse vars-acc))
    (b* ((name-and-type (first input-names-and-types))
         (input-name (first name-and-type))
         (input-type (second name-and-type))
         (state-component (first state-components))
         ((mv assumptions-for-first vars-for-first-rev)
          (assumptions-and-vars-for-input input-name input-type state-component stack-slots existing-stack-slots disjoint-chunk-addresses-and-lens type-assumptions-for-array-varsp)))
      (assumptions-and-vars-for-inputs (rest input-names-and-types)
                                       (rest state-components) stack-slots existing-stack-slots disjoint-chunk-addresses-and-lens
                                       type-assumptions-for-array-varsp
                                       (append assumptions-for-first assumptions-acc)
                                       (append vars-for-first-rev vars-acc) ; todo: check for dups
                                       ))))

;; Example: (assumptions-and-vars-for-inputs '((v1 :u32*) (v2 :u32*)) '((rdi x86) (rsi x86)))

(defthm true-listp-of-mv-nth-0-of-assumptions-and-vars-for-inputs-type
  (implies (true-listp assumptions-acc)
           (true-listp (mv-nth 0 (assumptions-and-vars-for-inputs input-names-and-types state-components stack-slots existing-stack-slots disjoint-chunk-addresses-and-lens type-assumptions-for-array-varsp assumptions-acc vars-acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable assumptions-and-vars-for-inputs))))

(defthm true-listp-of-mv-nth-1-of-assumptions-and-vars-for-inputs-type
  (implies (true-listp vars-acc)
           (true-listp (mv-nth 1 (assumptions-and-vars-for-inputs input-names-and-types state-components stack-slots existing-stack-slots disjoint-chunk-addresses-and-lens type-assumptions-for-array-varsp assumptions-acc vars-acc))))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable assumptions-and-vars-for-inputs))))

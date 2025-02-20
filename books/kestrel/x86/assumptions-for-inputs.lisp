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

;; Makes assumptions to introduce a variable for each element of the array, from INDEX up to ELEMENT-COUNT - 1.
;; TODO: Support expressing bytes in terms of single bit-vars
;; TODO: Support expressing the whole array as a single value (a byte-list)
(defund var-intro-assumptions-for-array-input (index element-count bytes-per-element pointer-name var-name-base)
  (declare (xargs :guard (and (natp index)
                              (natp element-count)
                              (posp bytes-per-element)
                              (symbolp pointer-name)
                              (symbolp var-name-base))
                  :measure (nfix (+ 1 (- element-count index)))))
  (if (or (not (mbt (and (natp element-count)
                         (natp index))))
          (<= element-count index))
      nil
    (cons `(equal (read ,bytes-per-element
                        ,(if (= 0 index)
                             pointer-name ; special case (offset of 0)
                           `(+ ,(* index bytes-per-element) ,pointer-name) ; todo: option to use bvplus here?
                           )
                        x86)
                  ,(acl2::pack-in-package "X" var-name-base index))
          (var-intro-assumptions-for-array-input (+ 1 index) element-count bytes-per-element pointer-name var-name-base))))

;; (var-intro-assumptions-for-array-input '0 '6 '4 'foo-ptr 'foo)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Make assertions that the region at ADDRESS with length LEN is separate from all the
;; regions represented by ADDRESSES-AND-LENS.
;; Not sure what order is better for the args of SEPARATE.
(defund make-separate-claims (address len addresses-and-lens)
  (declare (xargs :guard (alistp addresses-and-lens)
                  :guard-hints (("Goal" :in-theory (enable alistp)))))
  (if (endp addresses-and-lens)
      nil
    (let* ((pair (first addresses-and-lens))
           (this-address (car pair))
           (this-len (cdr pair)))
      (cons `(separate :r ,len ,address
                       :r ,this-len ,this-address)
            (make-separate-claims address len (rest addresses-and-lens))))))

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
              ;; Can't use the same name as a register (would make the output-indicator ambiguous):
              ;; todo: print a message when this check fails:
              (not (intersection-equal (acl2::map-symbol-name names) '("RAX" "EAX" "ZMM0" "YMM0" "XMM0"))) ; todo: keep in sync with normal-output-indicatorp
              ;; Types are symbols, e.g., u8[64]:
              (symbol-listp types)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Returns a list of assumptions.
(defund assumptions-for-input (input-name
                               input-type ;; examples: u32 or u32* or u32[4]
                               state-component
                               stack-slots
                               disjoint-chunk-addresses-and-lens)
  (declare (xargs :guard (and (symbolp input-name)
                              (symbolp input-type)
                              ;;state-component might be rdi or (rdi x86)
                              (natp stack-slots)
                              (alistp disjoint-chunk-addresses-and-lens) ; cars are terms
                              (nat-listp (strip-cdrs disjoint-chunk-addresses-and-lens)))))
  (let ((type (parse-type input-type)))
    (if (eq :error type)
        (er hard? 'assumptions-for-input "Bad input type: ~x0." type)
      (if (atom type) ; scalar (e.g., "U32")
          ;; just put in the var name for the state component:
          ;; todo: what about signed/unsigned?
          ;; todo: add type hyps for the var?
          `((equal ,state-component ,input-name))
        (let ((stack-byte-count (* 8 stack-slots))) ; each stack element is 64-bits
          (if (call-of :pointer type)
              (if (not (stringp (farg1 type))) ; for guards? ; todo: what about a pointer to something else? ; todo: give this check a name, e.g., scalar-typep
                  ;; TODO: Handle pointer to array, or struct, or pointer
                  (er hard? 'assumptions-for-input "Unsupported input type: ~x0." type)
                (let* ((base-type (farg1 type))
                       (numbytes (bytes-in-scalar-type base-type))
                       (pointer-name (acl2::pack-in-package "X" input-name '_ptr)) ;todo: watch for clashes; todo: should this be the main name and the other the "contents"?
                       )
                  `(;; Rewriting will replace the state component with the pointer's name:
                    (equal ,state-component ,pointer-name)
                    ;; todo: what about reading individual bytes?:  don't trim down reads?
                    (equal (read ,numbytes ,pointer-name x86) ,input-name)
                    (canonical-address-p ,pointer-name) ; first address
                    (canonical-address-p (+ ,(- numbytes 1) ,pointer-name)) ; last address (size of a scalar type can't be 0)
                    ;; The input is disjoint from the space into which the stack will grow:
                    (separate :r ,numbytes ,pointer-name
                              :r ,stack-byte-count
                              (+ ,(- stack-byte-count) (rsp x86)))
                    ;; The input is disjoint from the code:
                    ,@(make-separate-claims pointer-name numbytes disjoint-chunk-addresses-and-lens)
                    ;; The input is disjoint from the saved return address:
                    ;; todo: reorder args?
                    (separate :r 8 (rsp x86)
                              :r ,numbytes ,pointer-name))))
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
                     )
                  (append (var-intro-assumptions-for-array-input 0 element-count bytes-per-element pointer-name input-name)
                          `(;; Rewriting will replace the state component with the pointer's name:
                            (equal ,state-component ,pointer-name)
                            (canonical-address-p$inline ,pointer-name) ; first address
                            (canonical-address-p (+ ,(- numbytes 1) ,pointer-name)) ; last address (todo: consider numbytes=0)
                            ;; The input is disjoint from the space into which the stack will grow:
                            (separate :r ,numbytes ,pointer-name
                                      :r ,stack-byte-count
                                      (+ ,(- stack-byte-count) (rsp x86)))
                            ;; The input is disjoint from the code:
                            ,@(make-separate-claims pointer-name numbytes disjoint-chunk-addresses-and-lens)
                            ;; The input is disjoint from the saved return address:
                            ;; todo: reorder args?
                            (separate :r 8 (rsp x86)
                                      :r ,numbytes ,pointer-name))))
              (er hard? 'assumptions-for-input "Bad type: ~x0." type))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; might have extra, unneeded items in state-components
(defun assumptions-for-inputs (input-names-and-types state-components stack-slots disjoint-chunk-addresses-and-lens)
  (declare (xargs :guard (and (names-and-typesp input-names-and-types)
                              (true-listp state-components)
                              (natp stack-slots)
                              (alistp disjoint-chunk-addresses-and-lens) ; cars are terms
                              (nat-listp (strip-cdrs disjoint-chunk-addresses-and-lens)))))
  (if (endp input-names-and-types)
      nil
    (let* ((name-and-type (first input-names-and-types))
           (input-name (first name-and-type))
           (input-type (second name-and-type))
           (state-component (first state-components))
           )
      (append (assumptions-for-input input-name input-type state-component stack-slots disjoint-chunk-addresses-and-lens)
              (assumptions-for-inputs (rest input-names-and-types) (rest state-components) stack-slots disjoint-chunk-addresses-and-lens)))))

;; Example: (assumptions-for-inputs '((v1 :u32*) (v2 :u32*)) '((rdi x86) (rsi x86)))

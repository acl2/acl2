; Generating assumptions about inputs
;
; Copyright (C) 2016-2019 Kestrel Technology, LLC
; Copyright (C) 2020-2024 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "X")

(include-book "assumptions") ;reduce?
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

;; todo: strengthen:   what are the allowed types?  todo: Allow float types?
(defun names-and-typesp (names-and-types)
  (declare (xargs :guard t))
  (and (doublet-listp names-and-types)
       (let ((names (strip-cars names-and-types))
             (types (acl2::strip-cadrs names-and-types)))
         (and (symbol-listp names)
              ;; Can't use the same name as a register (would make the output-indicator ambiguous):
              (not (intersection-equal (acl2::map-symbol-name names) '("RAX" "EAX" "ZMM0" "YMM0" "XMM0"))) ; todo: keep in sync with normal-output-indicatorp
              (acl2::symbol-listp types)))))

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
  (let ((res (acl2::lookup-equal type *scalar-type-to-bytes-alist*)))
    (if res
        res
      (prog2$ (er hard? 'bytes-in-scalar-type "Unsupported type: ~x0." type)
              ;; for guard proof:
              1))))

(defthm posp-of-bytes-in-scalar-type
  (posp (bytes-in-scalar-type type))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable bytes-in-scalar-type ACL2::LOOKUP-EQUAL))))

(defund var-intro-assumptions-for-array-input (index len element-size pointer-name var-name)
  (declare (xargs :guard (and (natp index)
                              (natp len)
                              (posp element-size)
                              (symbolp pointer-name)
                              (symbolp var-name))
                  :measure (nfix (+ 1 (- len index)))))
  (if (or (not (mbt (and (natp len)
                         (natp index))))
          (<= len index))
      nil
    (cons `(equal (read ,element-size
                        ,(if (posp index)
                            `(+ ,(* index element-size) ,pointer-name)
                          pointer-name)
                        x86)
                  ,(acl2::pack-in-package "X" var-name index))
          (var-intro-assumptions-for-array-input (+ 1 index) len element-size pointer-name var-name))))

;; (var-intro-assumptions-for-array-input '0 '6 '4 'foo-ptr 'foo)

;; Returns a parsed-type or :error.
;; Types are parsed right-to-left, with the rightmost thing being the top construct.
(defund parse-type-string (type-str)
  (declare (xargs :guard (stringp type-str)
                  :measure (length type-str)
                  :hints (("Goal" :in-theory (disable length)))))
  (if (acl2::string-ends-withp type-str "*")
      `(:pointer ,(parse-type-string (acl2::strip-suffix-from-string "*" type-str)))
    (if (acl2::string-ends-withp type-str "]")
        (b* (((mv foundp base-type rest) (acl2::split-string type-str #\[))
             ((when (not foundp)) :error)
             (element-count-string (acl2::strip-suffix-from-string "]" rest))
             (element-count (acl2::parse-string-as-decimal-number element-count-string))
             ((when (not (posp element-count))) :error))
          `(:array ,(parse-type-string base-type) ,element-count))
      ;; a scalar type:
      (if (assoc-equal type-str *scalar-type-to-bytes-alist*)
          type-str
        :error))))

;; Returns a parsed-type or :error.
;; Types are parsed right-to-left, with the rightmost thing being the top construct.
(defund parse-type (sym)
  (declare (xargs :guard (symbolp sym)))
  (parse-type-string (symbol-name sym)))

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

;; Returns a list of assumptions.
(defund assumptions-for-input (input-name
                               input-type ;; examples: :u32 or :u32* or :u32[4]
                               state-component
                               stack-slots
                               text-offset
                               code-length)
  (declare (xargs :guard (and (symbolp input-name)
                              (symbolp input-type)
                              ;;state-component might be rdi or (rdi x86)
                              (natp stack-slots)
                              ;; text-offset is a term
                              (natp code-length))))
  (let ((type (parse-type input-type)))
    (if (eq :error type)
        (er hard? 'assumptions-for-input "Bad type: ~x0." type)
      (if (atom type) ; scalar
          ;; just put in the var name for the state component:
          ;; todo: what about signed/unsigned?
          `((equal ,state-component ,input-name))
        (let ((stack-byte-count (* 8 stack-slots))) ; each stack element is 64-bits
          (if (and (call-of :pointer type)
                   (stringp (farg1 type)) ; for guards
                   )
              (let* ((base-type (farg1 type))
                     (numbytes (bytes-in-scalar-type base-type))
                     (pointer-name (acl2::pack-in-package "X" input-name '_ptr)) ;todo: watch for clashes; todo: should this be the main name and the other the "contents"?
                     )
                `((equal ,state-component ,pointer-name)
                  ;; todo: what about reading individual bytes?:  don't trim down reads?
                  (equal (read ,numbytes ,pointer-name x86) ,input-name)
                  (canonical-address-p$inline ,pointer-name) ; first address
                  (canonical-address-p (+ ,(- numbytes 1) ,pointer-name)) ; last address
                  ;; The input is disjount from the space into which the stack will grow:
                  (separate :r ,numbytes ,pointer-name
                            :r ,stack-byte-count
                            (+ ,(- stack-byte-count) (rsp x86)))
                  ;; The input is disjoint from the code:
                  ,@(make-separate-claims pointer-name numbytes (acons text-offset code-length nil))
                  ;; The input is disjoint from the saved return address:
                  ;; todo: reorder args?
                  (separate :r 8 (rsp x86)
                            :r ,numbytes ,pointer-name)))
            (if (and (call-of :array type)
                     (stringp (farg1 type)) ; for guards
                     (natp (farg2 type)) ; for guards
                     )
                ;; must be an :array type:  ; TODO: What if the whole array fits in a register?
                (b* ((base-type (farg1 type))
                     (element-count (farg2 type))
                     (element-size (bytes-in-scalar-type base-type))
                     (numbytes (* element-count element-size))
                     (pointer-name (acl2::pack-in-package "X" input-name '_ptr)) ;todo: watch for clashes; todo: should this be the main name and the other the "contents"?
                     )
                  (append (var-intro-assumptions-for-array-input 0 element-count element-size pointer-name input-name)
                          `((equal ,state-component ,pointer-name)
                            (canonical-address-p$inline ,pointer-name) ; first address
                            (canonical-address-p (+ ,(- numbytes 1) ,pointer-name)) ; last address
                            ;; The input is disjount from the space into which the stack will grow:
                            (separate :r ,numbytes ,pointer-name
                                      :r ,stack-byte-count
                                      (+ ,(- stack-byte-count) (rsp x86)))
                            ;; The input is disjoint from the code:
                            ,@(make-separate-claims pointer-name numbytes (acons text-offset code-length nil))
                            ;; The input is disjoint from the saved return address:
                            ;; todo: reorder args?
                            (separate :r 8 (rsp x86)
                                      :r ,numbytes ,pointer-name))))
              (er hard? 'assumptions-for-input "Bad type: ~x0." type))))))))

;; might have extra, unneeded items in state-components
(defun assumptions-for-inputs (input-names-and-types state-components stack-slots text-offset code-length)
  (declare (xargs :guard (and (names-and-typesp input-names-and-types)
                              (true-listp state-components)
                              (natp stack-slots)
                              ;; text-offset is a term
                              (natp code-length))))
  (if (endp input-names-and-types)
      nil
    (let* ((name-and-type (first input-names-and-types))
           (input-name (first name-and-type))
           (input-type (second name-and-type))
           (state-component (first state-components))
           )
      (append (assumptions-for-input input-name input-type state-component stack-slots text-offset code-length)
              (assumptions-for-inputs (rest input-names-and-types) (rest state-components) stack-slots text-offset code-length)))))

;; Example: (assumptions-for-inputs '((v1 :u32*) (v2 :u32*)) '((rdi x86) (rsi x86)))

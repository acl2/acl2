; Utilities for unrolling Java code
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "kestrel/jvm/load-class" :dir :system)
(include-book "rule-lists-jvm")
(include-book "rules-in-rule-lists-jvm")
(include-book "../util2") ;; for bit-blasted-symbolic-array
(include-book "../math-rules")
(include-book "lifter-utilities") ; for field-pair-okayp, etc
(include-book "../step-increments")
(include-book "kestrel/std/system/fresh-namep" :dir :system)
(include-book "kestrel/jvm/method-designator-strings" :dir :system)
(include-book "kestrel/jvm/symbolic-execution" :dir :system)
(include-book "kestrel/utilities/progn" :dir :system)
(include-book "kestrel/bv/rules2" :dir :system) ; for sbvlt-of-bvsx
(include-book "kestrel/utilities/strip-stars-from-name" :dir :system)
(include-book "kestrel/utilities/system/fresh-names" :dir :system)
(include-book "kestrel/alists-light/assoc-equal" :dir :system)
(local (include-book "kestrel/utilities/acl2-count" :dir :system))

(local (in-theory (enable member-equal-becomes-memberp))) ;todo

;; Rules used to simplify terms during unrolling.  TODO: Add these to more
;; basic rule sets.
(defun unroll-java-code-rules ()
  (append '(nth-of-myif ;todo: drop? or add to amazing-rules - needed to handle myifs properly...  or should we instead use myif of 2 update-nth-locals terms?
            nth-becomes-bv-array-read ;why?
            bvif-of-myif-arg1
            bvif-of-myif-arg2
            getbit-of-myif
            not-equal-of-nil-and-s ;drop
            not-equal-nil-when-array-refp
            sbvlt-of-bvsx
            sbvlt-of-bvcat-and-0
            jvm::not-equal-nil-when-java-boolean-as-int-p
            jvm::not-equal-nil-when-java-byte-as-int-p
            jvm::not-equal-nil-when-java-short-as-int-p
            jvm::not-equal-nil-when-java-char-as-int-p ;todo: what about ints and longs?
            ;; These 3 seem safe even though if-lifting is dangerous in general.  TODO: Add these 3 to a more fundamental rule set?  Or do we still need them?
            thread-top-frame-of-myif ;this causes the thread id to be duplicated, but usually it's a constant
            stack-of-myif
            jvm::top-operand-of-myif
            jvm::pop-operand-of-myif
            jvm::top-long-of-myif
            jvm::pop-long-of-myif
            )
          (map-rules)
          (amazing-rules-spec-and-dag)
          (jvm-semantics-rules)
          (jvm-simplification-rules)))

(ensure-rules-known (unroll-java-code-rules))

;todo: compare to output-extraction-term
(mutual-recursion
 ;;TTTODO: Add support for :param-field (or just replace this with output-extraction-term!)
 ;; TODO: Add support for :all
 ;; TODO: Merge with output-extraction-term or just use that?
 ;; TODO: The lambdas here may be problematic.
 (defun wrap-term-with-output-extractor (output-indicator
                                         original-locals
                                         term
                                         class-alist)
   (declare (xargs :guard (and (output-indicatorp-aux output-indicator)
                               (class-table-alistp class-alist))))
   (if (eq :all output-indicator)
       term
     (if (eq :return-value output-indicator)
         `(jvm::top-operand (jvm::stack (jvm::thread-top-frame (th) ,term)))
       (if (eq :return-value-long output-indicator)
           `(jvm::top-long (jvm::stack (jvm::thread-top-frame (th) ,term)))
         (if (eq :array-return-value output-indicator) ;TODO: add support for this wherever output-indicators are used
             `((lambda (XXX) ; since XXX appears twice
                 (get-field (jvm::top-operand (jvm::stack (jvm::thread-top-frame (th) xxx)))
                            ',(array-contents-pair)
                            (jvm::heap xxx)))
               ,term)
           (if (eq (car output-indicator) :array-local) ;;this means "get the final value of the array that was initially pointed to be array local N.  TODO: This could be an abbreviation for a :field of a :local...
               (let ((local-num (cadr output-indicator)))
                 `(get-field (jvm::nth-local ',local-num ,original-locals) ;;note: these are the original locals
                             ',(array-contents-pair)
                             (jvm::heap ,term)))
             (if (eq (car output-indicator) :field)
                 (b* ((pair (farg1 output-indicator))
                      ((when (not (field-pair-okayp pair class-alist)))
                       (er hard? 'wrap-term-with-output-extractor "Bad field: ~x0." pair))
                      (obj-indicator (farg2 output-indicator))
                      (obj (wrap-term-with-output-extractor obj-indicator ;return-type
                                                            original-locals term class-alist)))
                   `(get-field ,obj ',pair (jvm::heap ,term)))
               (if (eq (car output-indicator) :tuple)
                   ;; TODO: Introduce a let?
                   (wrap-term-with-output-extractors (fargs output-indicator) ;return-type
                                                     original-locals term class-alist)
                 ;; FIXME: Handle :param-field
                 (er hard? 'wrap-term-with-output-extractor "Unsupported case: ~x0" output-indicator)))))))))

 (defun wrap-term-with-output-extractors (output-indicators original-locals term class-alist)
   (declare (xargs :guard (and (output-indicatorp-aux-lst output-indicators)
                               (class-table-alistp class-alist))))
   (if (endp output-indicators)
       *nil*
     ;; not a lambda (hope that is okay):
     `(cons ,(wrap-term-with-output-extractor (first output-indicators) ;return-type
                                              original-locals term class-alist)
            ,(wrap-term-with-output-extractors (rest output-indicators) ;return-type
                                               original-locals term class-alist)))))

;; ;; Wrap initial-term in a list of calls to S, setting each class name to its corresponding class-info.
;; (defun make-class-table-term (class-alist initial-term)
;;   (if (endp class-alist)
;;       initial-term
;;     (let* ((entry (first class-alist))
;;            (class-name (car entry))
;;            (class-info (cdr entry)))
;;       (make-class-table-term (rest class-alist)
;;                              `(s ',class-name ',class-info ,initial-term)))))

(defun make-class-table-term-compact (class-alist initial-term)
  `(jvm::set-classes ',class-alist ,initial-term))

;; (defun bit-width-from-type (type)
;;   (declare (xargs :guard (member-eq type '(:byte :char ;:float
;;                                                  :int :short :boolean
;;                                                  ;:double
;;                                                  :long))))
;;   (case type
;;     (:boolean 1) ;TODO: Think about this
;;     (:byte 8)
;;     ((:char :short) 16)
;;     (:int 32)
;;     (:long 64)))

;; An array-length-alist maps arrays (indicated by symbol names) to their types.
;; TODO: Should the keys in array-length-alist be strings?
;; TODO: Also, throw an error if an invalid key is given (the set of valid names depends on whether we have debugging info?)
(defun array-length-alistp (alist)
  (declare (xargs :guard t))
  (and (symbol-alistp alist)
       (all-natp (strip-cdrs alist))))

;; assumes locals-term is a term that represents the locals in the appropriate state
;; TODO: Compare to make-input-assumptions and param-assumptions-and-vars-aux
;; TOOD: Should we assume that params that are references are non-null?  We do for arrays...
;; TODO: Add an option to avoid generating non-null assumptions for arrays (implied by array-refp) and references.
;; TODO: Add option for stricter assumptions about subtypes of int
(defun parameter-assumptions-aux (current-slot parameter-types param-slot-to-name-alist array-length-alist locals-term heap-term vars-for-array-elements method-designator-string)
  (declare (xargs :guard (and (natp current-slot)
                              (true-listp parameter-types)
                              (jvm::all-typep parameter-types)
                              (param-slot-to-name-alistp param-slot-to-name-alist)
                              (array-length-alistp array-length-alist)
                              (pseudo-termp locals-term)
                              (pseudo-termp heap-term)
                              (member-eq vars-for-array-elements '(t nil :bits))
                              (method-designator-stringp method-designator-string))))
  (if (endp parameter-types)
      nil
    (let* ((type (first parameter-types))
           (parameter-name (lookup current-slot param-slot-to-name-alist))
           (local-term `(jvm::nth-local ',current-slot ,locals-term))
           ;; Generate an assumption to replace a param with a symbolic variable (or an array of such):
           (assumptions (if (jvm::primitive-typep type)
                            ;; If it's a primitive type, we generate
                            ;; an equality assumption to cause the
                            ;; local to be replaced with the
                            ;; corresponding variable, and a type
                            ;; hypothesis about that variable.
                            `((equal ,local-term ,parameter-name)
                              ,@(type-assumptions-for-param type parameter-name))
                          ;; Reference type:
                          (if (jvm::class-or-interface-namep type)
                              `((equal ,local-term ,parameter-name)
                                (address-or-nullp ,parameter-name))
                            (if (jvm::is-one-dim-array-typep type)
                                ;; One-dimensional array (TODO: Consider if we get NULL -- should it be an option to assume non-null?):
                                (let ((component-type (jvm::get-array-component-type type))
                                      (maybe-len (lookup-eq parameter-name array-length-alist))
                                      (contents-term `(get-field ,local-term ',(array-contents-pair) ,heap-term)))
                                  (if (jvm::bit-vector-typep component-type) ;could weaken to primitive-typep if we generalize symbolic-array and check (eq :bits vars-for-array-elements) or treat :bits as t
                                      ;; but first add support for more types
                                      ;; in array-refp If it's an 1-d array
                                      ;; type of a handled type (and we
                                      ;; know the length), we generate an
                                      ;; array-refp hyp for the local and a
                                      ;; hyp to replace a lookup of the
                                      ;; contents with a symbolic array term
                                      (if maybe-len
                                          ;; One-dimensional array of BVS of known (constant) length:
                                          (append (if vars-for-array-elements ;fixme: what about arrays of floats and doubles!
                                                      `((equal ,contents-term
                                                               ,(if (eq :bits vars-for-array-elements) ;todo: what if the element type is not blastable?
                                                                    (bit-blasted-symbolic-array parameter-name maybe-len (jvm::size-of-array-element component-type))
                                                                  (symbolic-array parameter-name maybe-len (jvm::size-of-array-element component-type)))))
                                                    ;; Don't put in individual vars for array elements:
                                                    `((equal ,contents-term
                                                             ,parameter-name)
                                                      (equal (len ,parameter-name)
                                                             ',maybe-len)
                                                      (true-listp ,parameter-name)))
                                                  ;;todo: what about type assumptions for individual vars?:
                                                  `((array-refp ,local-term
                                                                (cons ',maybe-len 'nil) ;; here we use the constant known length
                                                                ',component-type
                                                                ,heap-term)))
                                        ;; One-dimensional array of BVS of unknown length:
                                        `((equal ,contents-term ,parameter-name) ;; replaces the array contents with the var
                                          (true-listp ,parameter-name) ;todo: add all-unsigned-byte-p ?
                                          (array-refp ,local-term
                                                      (cons (len ,parameter-name) 'nil) ;; no constant length to use here
                                                      ',component-type
                                                      ,heap-term)))
                                    (if (member-eq component-type '(:float :double))
                                        ;; One-dimensional array of floats/doubles:
                                        (if maybe-len
                                            ;; One-dimensional array of floats/doubles of known (constant) length:
                                            (append (if vars-for-array-elements ;fixme: what about arrays of floats and doubles!
                                                        (prog2$ (er hard? 'parameter-assumptions-aux "Unsupported case: float array param with known length and vars-for-array-elements requested.")
                                                                nil
                                                        ;; `((equal ,contents-term
                                                                ;;          ,(symbolic-array parameter-name maybe-len (jvm::size-of-array-element component-type))))
                                                                )
                                                      ;; Don't put in individual vars for array elements:
                                                      `((equal ,contents-term ,parameter-name)
                                                        (equal (len ,parameter-name) ',maybe-len)
                                                        (true-listp ,parameter-name)))
                                                    ;;todo: what about type assumptions for individual vars?:
                                                    `((array-refp ,local-term
                                                                  (cons ',maybe-len 'nil) ;; here we use the constant known length
                                                                  ',component-type
                                                                  ,heap-term)))
                                          ;; One-dimensional array of floats/doubles of unknown length:
                                          `((equal ,contents-term ,parameter-name) ;; replaces the array contents with the var
                                            (true-listp ,parameter-name) ;todo: add all-floatp or something?
                                            (array-refp ,local-term
                                                        (cons (len ,parameter-name) 'nil) ;; no constant length to use here
                                                        ',component-type
                                                        ,heap-term)))
                                      ;; (prog2$ (cw "NOTE: We do not yet fully support generating parameter assumptions for arrays of floats or doubles but ~x0 in method ~x1 method-designator-string is such a param" parameter-name method-designator-string)
                                      ;;           nil)
                                      ;; One-dimensional array of references (TODO: handle this better):
                                      `((equal ,local-term ,parameter-name)
                                        (address-or-nullp ,parameter-name)))))
                              ;; Multi-dimensional array (TODO: Handle):
                              nil))))
           (slot-count (jvm::type-slot-count type)))
      (append assumptions
              (parameter-assumptions-aux (+ current-slot slot-count)
                                         (rest parameter-types)
                                         param-slot-to-name-alist
                                         array-length-alist
                                         locals-term
                                         heap-term
                                         vars-for-array-elements
                                         method-designator-string)))))

;; Make assumptions for the parameters of the given method.  These will be
;; terms over LOCALS-TERM and HEAP-TERM (TODO: and the names of local vars...). ARRAY-LENGTH-ALIST is an alist from
;; parameter names to naturals representing the lengths of the
;; corresponding arrays.
;; TODO: Should we use strings for parameter names?
;; TODO: What if two params of the method have names that differ only in case?
(defun parameter-assumptions (method-info array-length-alist locals-term heap-term vars-for-array-elements param-slot-to-name-alist method-designator-string)
  (declare (xargs :guard (and (jvm::method-infop method-info)
                              (array-length-alistp array-length-alist)
                              (pseudo-termp locals-term)
                              (pseudo-termp heap-term)
                              (member-eq vars-for-array-elements '(t nil :bits))
                              (param-slot-to-name-alistp param-slot-to-name-alist)
                              (method-designator-stringp method-designator-string))))
  (let* ((parameter-types (lookup-eq :parameter-types method-info)) ;does not include "this"
         (staticp (jvm::method-staticp method-info))
         (first-param-slot (if staticp 0 1)) ;skip a slot for "this" if it's an instance method
         ;; If it's an instance method, we assume that "this" is an address (and in particular is not null):
         (assumptions-about-this (if staticp nil `((addressp (jvm::nth-local '0 ,locals-term))
                                                   ;; This actually follows from the above, but the rule to show that can cause loops:
                                                   (not (null-refp (jvm::nth-local '0 ,locals-term)))))))
    (append assumptions-about-this
            (parameter-assumptions-aux first-param-slot parameter-types param-slot-to-name-alist array-length-alist locals-term heap-term vars-for-array-elements method-designator-string))))


;; ;move and use more (or just trans this stuff?)
;; (defun pseudo-terms-with-correct-arities (terms state)
;;   (declare (xargs :stobjs state))
;;   (and (pseudo-term-listp terms)
;;        (all-arities-okayp terms state)))

;does array-refp even support class-names as the type?
;; (DEFTHM GET-CLASS-of-nth-WHEN-ARRAY-REFp-one-dim
;;   (IMPLIES (AND (ARRAY-REFp-aux REF (LIST len) TYPE HEAP nil)
;;                 (jvm::class-namep type)
;;                 (natp n)
;;                 (< n len))
;;            (EQUAL (GET-FIELD (NTH n (GET-FIELD ref (array-contents-pair) HEAP))
;;                              '(:SPECIAL-DATA . :CLASS)
;;                              HEAP)
;;                   type)))

;; What was this attached to?
;; Returns (mv erp dag state)
;; TODO: Run some static initializers?
;; TODO: Add support for additional inputs, such as fields of local vars.
;; parameter-assumptions could return a map from the names of params to their
;; expressions.  then the user could specify that an additional input of
;; interest is (:field ... x)

(in-theory (disable CDR-OF-TAKE-BECOMES-SUBRANGE-BETTER))

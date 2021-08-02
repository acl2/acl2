; Utilities supporting the lifter(s)
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

(include-book "kestrel/utilities/defmergesort" :dir :system)
(include-book "../make-axe-rules") ; for make-axe-rules-from-theorem
;(include-book "../jvm/heap0")
(include-book "kestrel/jvm/jvm" :dir :system) ;for JVM::CALL-STACK-SIZE
(include-book "kestrel/jvm/method-designator-strings" :dir :system)
(include-book "kestrel/utilities/quote" :dir :system)

;;These rules just get rid of all branches with exception/error states (totally
;;unsound, but helpful to guess an invariant to be checked later). ffffffixme:
;;get rid of all uses of this that affect soundness (some uses might be okay,
;;e.g., for guessing invariants)

(defconst *ignore-exception-pseudo-rule-1*
  '(equal (myif test (jvm::obtain-and-throw-exception exception-class-name debug-info th s1) s2)
          s2))

(defconst *ignore-exception-pseudo-rule-2*
  '(equal (myif test s1 (jvm::obtain-and-throw-exception exception-class-name debug-info th s2))
          s1))

;; Note that these rules do not correspond to true theorems!  So we cannot make
;; them from theorems in the usual way.  TODO: Arrange to have a message
;; printed when these fire?
(make-event
 `(defconst *ignore-exception-axe-rule-set*
    ',(append (make-axe-rules-from-theorem! *ignore-exception-pseudo-rule-1* 'ignore-exceptions-1 nil nil t (w state))
              (make-axe-rules-from-theorem! *ignore-exception-pseudo-rule-2* 'ignore-exceptions-2 nil nil t (w state)))))

;want these to fire before we lift the if
(table axe-rule-priorities-table 'ignore-exceptions-1 -1)
(table axe-rule-priorities-table 'ignore-exceptions-2 -1)

;; TODO: Pull these out as above.  We need a way to refer to named terms that are not actually theorems.
;; Note that these rules do not correspond to true theorems!  So we cannot make
;; them from theorems in the usual way.  TODO: Arrange to have a message
;; printed when these fire?
(make-event
 `(defconst *ignore-error-state-axe-rule-set*
    ',(append (make-axe-rules-from-theorem! '(equal (myif test (jvm::error-state msg s) s2)
                                                    s2)
                                            'ignore-error-state-1 nil nil t (w state))
              (make-axe-rules-from-theorem! '(equal (myif test s1 (jvm::error-state msg s))
                                                    s1)
                                            'ignore-error-state-2 nil nil t (w state))
              (make-axe-rules-from-theorem! '(equal (run-until-exit-segment-or-hit-loop-header segment-stack-height segment-pcs loop-headers (jvm::error-state msg state))
                                                    (jvm::error-state msg state))
                                            'run-until-exit-segment-or-hit-loop-header-of-error-state nil nil t (w state))
              (make-axe-rules-from-theorem! '(equal (run-until-exit-segment SEGMENT-STACK-HEIGHT SEGMENT-PCS (jvm::error-state msg state))
                                                    (jvm::error-state msg state))
                                            'run-until-exit-segment-of-error-state nil nil t (w state)))))

;want these to fire before we lift the if
(table axe-rule-priorities-table 'ignore-error-state-1 -1)
(table axe-rule-priorities-table 'ignore-error-state-2 -1)

;; (defun ignore-exceptions-and-errors-runes ()
;;   (prog2$ (cw "(WARNING: Ignoring exceptions and errors!)~%")
;;           (append (ignore-error-state-runes)
;;                   (ignore-exceptions-runes))))

(defun standard-hyps-basic0 (state-term)
  `((equal (alistp (jvm::thread-table ,state-term))
           't)
    ;;new:
    (equal (jvm::method-synchronizedp (jvm::method-info (jvm::thread-top-frame (th) ,state-term)))
           'nil)))

;todo: why not say statep?  maybe it needs to be expanded?
;these are for the state *after* the invoke instruction
(defun standard-hyps-basic (state-term)
  (append (standard-hyps-basic0 state-term)
          `(;; the call stack has at least one frame (redundant?): drop this?:
            (equal (equal '0 (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table ,state-term))) ;(len (jvm::call-stack (th) ,state-term))
                          )
                   'nil)
            ;;actually we need a caller frame for the driver too
            (equal (< '1 (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table ,state-term)) ;(jvm::call-stack (th) ,state-term)
                                               ))
                   't))))

(defun standard-hyps-basic-before-invoke (state-term)
  (append (standard-hyps-basic0 state-term)
          `((equal (equal '0 (jvm::call-stack-size (jvm::binding (th) (jvm::thread-table ,state-term))) ;(len (jvm::call-stack (th) ,state-term))
                          )
                   'nil))))

;TODO: switch to just using alists
(defun class-table-hyps (state-var class-table-map)
  (if (endp class-table-map)
      nil
    (append (let* ((entry (car class-table-map))
                   (class-name (car entry))
                   (class-info (cdr entry)))
              `((jvm::bound-in-class-tablep ',class-name (jvm::class-table ,state-var))
                (equal (jvm::get-class-info ',class-name (jvm::class-table ,state-var))
                       ',class-info)))
            (class-table-hyps state-var (cdr class-table-map)))))

;TODO: Switch to just using this version everywhere?  The result contains untranslated terms!
(defun class-table-hyps2 (state-var class-alist)
  (if (endp class-alist)
      nil
    (append (let* ((entry (car class-alist))
                   (class-name (car entry))
                   ;;(class-info (cdr entry))
                   )
              `((equal (jvm::get-class-info ',class-name (jvm::class-table ,state-var))
                       ,(pack$ "*" class-name "-CLASS-INFO*"))
                (jvm::bound-in-class-tablep ',class-name (jvm::class-table ,state-var))))
            (class-table-hyps2 state-var (cdr class-alist)))))

(defun class-table-alistp (class-table-alist)
  (declare (xargs :guard t))
  (if (atom class-table-alist)
      (null class-table-alist)
    (let* ((entry (first class-table-alist)))
      (and (consp entry)
           (let* ((class-name (car entry))
                  (class-info (cdr entry)))
             (and (jvm::class-namep class-name)
                  (jvm::class-infop class-info class-name)
                  (class-table-alistp (rest class-table-alist))))))))

(defthmd alistp-when-class-table-alistp
  (implies (class-table-alistp class-table-alist)
           (alistp class-table-alist)))

;; (defthmd alistp-when-class-infop
;;   (implies (jvm::class-infop class-info class-name)
;;            (alistp class-info))
;;   :hints (("Goal" :in-theory (enable jvm::class-infop alistp)))))

;; (thm
;;  (IMPLIES (CLASS-TABLE-ALISTP CLASS-TABLE-ALIST)
;;           (ALISTP (LOOKUP-EQUAL class-name CLASS-TABLE-ALIST)))
;;  :hints (("Goal" :in-theory (enable LOOKUP-EQUAL assoc-equal))))

(defund field-pair-okayp (pair class-table-alist)
  (declare (xargs :guard (and (class-name-field-id-pairp pair)
                              (class-table-alistp class-table-alist))))
  (or (equal pair (array-contents-pair))
      (let* ((class-name (car pair))
             (field-id (cdr pair))
             (class-info (lookup-equal class-name class-table-alist)))
        (if (not (jvm::class-infop class-info class-name))
            (er hard? 'field-pair-okayp "Ill-formed or missing class-info for ~x0" class-name)
          (let ((class-fields (jvm::class-decl-non-static-fields class-info)))
            (if (not (alistp class-fields)) ;for guards
                (er hard? 'field-pair-okayp "Ill-formed class-table alist")
              (let ((class-field-ids (strip-cars class-fields)))
                (member-equal field-id class-field-ids))))))))

;; A dummy function that has special meaning when used in invariants (it gets
; replaced by a term representing the array contents of the given expression in
; the heap of the given overarching state).
(defstub contents (x) x)

;replace things like (contents <blah>) with (GET-FIELD <blah> '("ARRAY" "contents" . "dummy-descriptor") (JVM::HEAP <state-var>))
(mutual-recursion
 (defun desugar-calls-of-contents-in-term (term heap-term)
   (declare (xargs :guard (pseudo-termp term)))
   (if (atom term)
       term
     (if (quotep term)
         term
       (let ((new-args (desugar-calls-of-contents-in-terms (fargs term) heap-term))
             (fn (ffn-symb term)))
         (if (consp fn)
             ;;lambda:
             (let ((formals (farg1 (ffn-symb term)))
                   (body (farg2 (ffn-symb term))))
               `((lambda ,formals ,(desugar-calls-of-contents-in-term body heap-term)) ,@new-args))
           (if (eq 'contents fn)
               ;; Special treatment for contents:
               (let* ((arg (first new-args)))
                 `(get-field ,arg '("ARRAY" "contents" . "dummy-descriptor") ,heap-term))
             ;;normal case:
             (cons fn new-args)))))))
 (defun desugar-calls-of-contents-in-terms (terms heap-term)
   (declare (xargs :guard (pseudo-term-listp terms)))
   (if (endp terms)
       nil
     (cons (desugar-calls-of-contents-in-term (first terms) heap-term)
           (desugar-calls-of-contents-in-terms (rest terms) heap-term)))))

; A dummy function that has special meaning when used in invariants (it gets
; replaced by a term representing the local var with the given name in the
; given over-arching state).
(defstub var (x) x)

; A dummy function that has special meaning when used in invariants (it gets
; replaced by a term representing the field of the given object with the given
; class-name-field-name pair in the headp of the over-arching state).
(defstub field (address pair) t)

;; ; A dummy function that has special meaning when used in invariants (it gets
;; ; replaced by a term representing the static field of the given object with the given
;; ; class-name-field-name pair in the over-arching state).
(defstub static-field (class-name field-id) t)

;todo: rename
;replace things like (var "i") with things like (JVM::NTH-LOCAL '4 (JVM::LOCALS (JVM::thread-top-frame (th) <state-var>)))
;todo: what is the form of the input (an untranslated term with no fancy macros?)?
(mutual-recursion
 (defun desugar-invars (terms state-var local-vars-for-pc)
   ;; (declare (xargs :guard (and (pseudo-term-listp terms)
   ;;                             (alistp local-vars-for-pc))))
   (if (endp terms)
       nil
     (cons (desugar-invar (first terms) state-var local-vars-for-pc)
           (desugar-invars (rest terms) state-var local-vars-for-pc))))
 (defun desugar-invar (term state-var local-vars-for-pc)
   ;; (declare (xargs :guard (and (pseudo-termp term)
   ;;                             (alistp local-vars-for-pc))))
   (if (atom term)
       term
     (if (quotep term)
         term
       (let ((new-args (desugar-invars (fargs term) state-var local-vars-for-pc))
             (fn (ffn-symb term)))
         (if (consp fn)
             ;;lambda:
             (let ((formals (farg1 (ffn-symb term)))
                   (body (farg2 (ffn-symb term))))
               `((lambda ,formals ,(desugar-invar body state-var local-vars-for-pc)) ,@new-args))
           (if (eq 'var fn)
               ;; Special treatment for var:
               (let* ((string (unquote (first new-args)))
                      (match (assoc-equal string local-vars-for-pc)))
                 (if (not match)
                     (hard-error 'desugar-invar "No match in local variable table for ~x0.~%" (acons #\0 string nil))
                   (let ((local-num (second match)))
                     `(jvm::NTH-local ',local-num (JVM::LOCALS (JVM::thread-top-frame (th) ,state-var))))))
             (if (eq 'field fn)
                 ;; If it's a call of FIELD, we put in the heap term and make
                 ;; it into a call of GET-FIELD.  TODO: Consider adding support
                 ;; for just a field name, instead of a pair, when that is
                 ;; unambiguous (but how will we know the class?)?
                 `(get-field ,(nth 0 new-args) ,(nth 1 new-args) (jvm::heap ,state-var))
               (if (eq 'static-field fn)
                   ;; If it's a call of STATIC-FIELD, we put in the
                   ;; static-field-map term and make it into a call of
                   ;; JVM::GET-STATIC-FIELD.
                   `(jvm::get-static-field ,(nth 0 new-args) ,(nth 1 new-args) (jvm::static-field-map ,state-var))
                 ;; normal case:
                 (cons fn new-args))))))))))

;; For making things more human readable.  Replaces make-states with :good and
;; run-until... with :bad.
(defun clarify-lifter-branches (term)
  (if (not (consp term))
      term
    (let ((fn (ffn-symb term)))
      (if (eq 'quote fn)
          term
        (if (eq 'myif fn)
            `(myif ,(clarify-lifter-branches (farg1 term))
                   ,(clarify-lifter-branches (farg2 term))
                   ,(clarify-lifter-branches (farg3 term)))
          (if (eq 'JVM::MAKE-STATE fn)
              :good
            (if (member-eq fn '(RUN-UNTIL-EXIT-SEGMENT-OR-HIT-LOOP-HEADER ;for the non-unrolling lifter
                                RUN-UNTIL-RETURN-FROM-STACK-HEIGHT ;for the unrolling lifter
                                ))
                :bad
              term)))))))

(defun check-quotep (obj)
  (if (quotep obj)
      obj
    (hard-error 'check-quotep "expected the object to be a quotep: ~x0." (acons #\0 obj nil))))

;; Make an assumption about term. This is for values stored in stack slots,
;; local vars, instance fields, and static fields.  Not for arrays.
;;
;; ;TODO: Think about inputs that are fields of objects, including "this"
;;  Make an assumption about term
;TODO Flesh out (support floats, etc.)
;TODO: Does this exist elsewhere?
;; ;see also descriptor-to-predicate
(defun type-assumptions-for-param (type term)
  (declare (xargs :guard (jvm::primitive-typep type))) ;todo: gen? perhaps use addressp.
  (if (member-eq type '(:byte :boolean :char :short :int))
      ;; We can't say anything tighter for any of these (e.g.,
      ;; acl2::java-char-as-int-p), since they are represented as ints and we
      ;; can't really constrain the bit patterns.
      `((unsigned-byte-p '32 ,term)) ;use java-intp?
    (if (eq type :long)
        `((unsigned-byte-p '64 ,term)) ;use java-longp?
      (if (eq type :float)
          `((jvm::java-floatp ,term))
        (if (eq type :double)
            `((jvm::java-doublep ,term))
          (er hard 'type-assumptions-for-param "Unrecognized type: ~x0." type))))))

;; Sort vars by putting all vars that are also in guide-vars first (in
;; the same order as in guide-vars), then the order used by symbol<.
(defun sort-vars-with-guidance (vars guide-vars)
  (declare (xargs :guard (and (symbol-listp guide-vars)
                              (symbol-listp vars))))
  (if (endp guide-vars)
      (merge-sort-symbol< vars)
    (let ((guide-var (first guide-vars)))
      (if (member-eq guide-var vars)
          (cons guide-var (sort-vars-with-guidance (remove-eq guide-var vars) (rest guide-vars)))
        (sort-vars-with-guidance vars (rest guide-vars))))))

;; Stub to be used in :assumptions passed to the lifter, to wrap a string naming a parameter.
(defstub param (x) t)

(in-theory (disable string-upcase to-string))

;; Desugar things like (param "foo") to an appropriate term about the locals of STATE-VAR.
(mutual-recursion
 (defun desugar-params-in-assumption-terms (terms state-var param-name-to-slot-alist)
   (declare (xargs :guard (and (pseudo-term-listp terms)
                               (symbol-alistp param-name-to-slot-alist))))
   (if (endp terms)
       nil
     (cons (desugar-params-in-assumption-term (first terms) state-var param-name-to-slot-alist)
           (desugar-params-in-assumption-terms (rest terms) state-var param-name-to-slot-alist))))
 (defun desugar-params-in-assumption-term (term state-var param-name-to-slot-alist)
   (declare (xargs :guard (and (pseudo-termp term)
                               (symbol-alistp param-name-to-slot-alist))))
   (if (atom term)
       term
     (if (quotep term)
         term
       (let ((new-args (desugar-params-in-assumption-terms (fargs term) state-var param-name-to-slot-alist))
             (fn (ffn-symb term)))
         (if (consp fn)
             ;;lambda:
             (let ((formals (farg1 (ffn-symb term)))
                   (body (farg2 (ffn-symb term))))
               `((lambda ,formals ,(desugar-params-in-assumption-term body state-var param-name-to-slot-alist)) ,@new-args))
           (if (eq 'param fn)
               (if (and (eql 1 (len (fargs term)))
                        (myquotep (farg1 term))
                        (stringp (unquote (farg1 term)))
                        (standard-char-listp (coerce (unquote (farg1 term)) 'list)) ;gross: justifies calling string-upcase
                        )
                   ;; Special treatment for a call of PARAM:
                   (let* ((string (unquote (first new-args)))
                          (param-name (pack$ (string-upcase string)))
                          (match (assoc-equal param-name param-name-to-slot-alist)))
                     (if (not match)
                         (hard-error 'desugar-params-in-assumption-term "No match in local variable table for ~x0.~%" (acons #\0 string nil))
                       (let ((local-num (cdr match)))
                         `(jvm::nth-local ',local-num (jvm::locals (jvm::thread-top-frame (th) ,state-var))))))
                 (er hard? 'desugar-params-in-assumption-term "Ill-formed call of param: ~x0." term))
             ;; (if (eq 'field fn)
             ;;     ;; If it's a call of FIELD, we put in the heap assumption and make
             ;;     ;; it into a call of GET-FIELD. TODO: Consider adding support
             ;;     ;; for just a field name, instead of a pair, when that is
             ;;     ;; unambiguous (but how will we know the class?)?
             ;;     `(get-field ,(nth 0 new-args) ,(nth 1 new-args) (jvm::heap ,))
             ;;   (if (eq 'static-field fn)
             ;;       ;; If it's a call of STATIC-FIELD, we put in the
             ;;       ;; static-field-map assumption and make it into a call of
             ;;       ;; JVM::GET-STATIC-FIELD.
             ;;       `(jvm::get-static-field ,(nth 0 new-args) ,(nth 1 new-args) (jvm::static-field-map ,))
             ;;     ;; normal case:
             (cons fn new-args))))))))

(in-theory (disable JVM::PRIMITIVE-TYPEP
                    JVM::REFERENCE-TYPEP
                    JVM::LOCAL-VARIABLE-TABLEP))

(defund param-slot-to-name-alistp (alist)
  (declare (xargs :guard t))
  (and (alistp alist)
       (nat-listp (strip-cars alist))
       (symbol-listp (strip-cdrs alist))))

(defthm param-slot-to-name-alistp-forward-to-alistp
  (implies (param-slot-to-name-alistp alist)
           (alistp alist))
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (enable param-slot-to-name-alistp))))

(defthmd symbolp-of-lookup-equal-when-param-slot-to-name-alistp
  (implies (param-slot-to-name-alistp alist)
           (symbolp (lookup-equal slot alist)))
  :hints (("Goal" :in-theory (enable param-slot-to-name-alistp lookup-equal assoc-equal))))

;; todo: use :auto as the default for param-names, not nil
(defun make-param-slot-to-name-alist-aux (parameter-types slot local-variable-table param-names)
  (declare (xargs :guard (and (true-listp parameter-types)
                              (jvm::all-typep parameter-types)
                              (natp slot)
                              (jvm::local-variable-tablep local-variable-table)
                              (symbol-listp param-names))
                  :verify-guards nil ;;done below
                  ))
  (if (endp parameter-types)
      (if (not (endp param-names))
          (er hard? 'make-param-slot-to-name-alist-aux "Extra param-names given: ~x0." param-names)
        nil)
    (b* ((type (first parameter-types))
         (slot-count (jvm::type-slot-count type))
         ((mv erp name) (if param-names ;use user-supplied param-names, if given
                            (mv (erp-nil) (first param-names))
                          (if local-variable-table
                              (let ((name-and-type
                                     (lookup-in-local-variable-table slot 0 ;PC 0 means the start of the method
                                                                     local-variable-table)))
                                (if (not name-and-type)
                                    (prog2$ (er hard? 'make-param-slot-to-name-alist-aux "No binding found in the local var table for param ~x0." slot)
                                            (mv (erp-t) nil))
                                  (if (not (STANDARD-CHAR-LISTP (COERCE (car name-and-type) 'LIST)))
                                      (prog2$ (er hard? 'make-param-slot-to-name-alist-aux "Name contains non-standard characters: ~x0." (car name-and-type))
                                              (mv (erp-t) nil))
                                    (mv (erp-nil)
                                        (pack$ (string-upcase (car name-and-type)))))))
                            ;; There is no local variable table, so just call it PARAM<N>:
                            ;;todo: should param numbering start at 1 here?
                            (mv (erp-nil) (pack$ 'param slot)))))
         ((when erp) nil) ;could return the error...
         (res (make-param-slot-to-name-alist-aux (rest parameter-types) (+ slot-count slot) local-variable-table (rest param-names))))
      (if (member-eq name (strip-cdrs res))
          ;; Can happen if two param names differe only in case:
          (er hard? 'make-param-slot-to-name-alist-aux "Parameter name clash on ~x0." name)
        (acons slot name res)))))

(defthm alistp-of-make-param-slot-to-name-alist-aux
  (alistp (make-param-slot-to-name-alist-aux parameter-types slot local-variable-table param-names)))

(verify-guards make-param-slot-to-name-alist-aux)

(defthm param-slot-to-name-alistp-of-make-param-slot-to-name-alist-aux
  (implies (and (true-listp parameter-types)
                (jvm::all-typep parameter-types)
                (natp slot)
                (jvm::local-variable-tablep local-variable-table)
                (symbol-listp param-names))
           (param-slot-to-name-alistp (make-param-slot-to-name-alist-aux parameter-types slot local-variable-table param-names)))
  :hints (("Goal" :induct (make-param-slot-to-name-alist-aux parameter-types slot local-variable-table param-names)
           :in-theory (enable param-slot-to-name-alistp STRIP-CARS))))

;; Make an alist from param/local slots to names.  Use the user-supplied
;; param-names if given, else use the local-variable-table if present,
;; otherwise, call them param0, param1, etc.  If this is an instance method, we
;; skip param0 because it would represent "this".
;todo: this duplicates code in parameter-assumptions
(defun make-param-slot-to-name-alist (method-info
                                      param-names ;often nil
                                      )
  (declare (xargs :guard (and (jvm::method-infop method-info)
                              (symbol-listp param-names))))
  (b* ((parameter-types (lookup-eq :parameter-types method-info)) ;does not include "this"
       ((when (and param-names
                   (not (eql (len param-names) (len parameter-types)))))
        (er hard? 'parameter-names "Wrong number of parameter names given.  Names: ~x0.  Types: ~x1." param-names parameter-types))
       (local-variable-table (lookup-eq :local-variable-table method-info)) ;may be nil
       (staticp (jvm::method-staticp method-info))
       (first-param-slot (if staticp 0 1)) ;skip a slot for "this" if it's an instance method
       )
    (make-param-slot-to-name-alist-aux parameter-types first-param-slot local-variable-table param-names))) ;todo: refactor to not call make-param-slot-to-name-alist twice?

(defthm param-slot-to-name-alistp-of-make-param-slot-to-name-alist
  (implies (and (jvm::method-infop method-info)
                (symbol-listp param-names))
           (param-slot-to-name-alistp (make-param-slot-to-name-alist method-info param-names))))


;; A triple of name, index, and type, e.g., ("i" 4 :INT).
(defund local-var-for-pcp (x)
  (declare (xargs :guard t))
  (and (true-listp x)
       (eql 3 (len x))
       (stringp (first x))
       (natp (second x))
       (jvm::typep (third x))))

(defun <-local-vars-for-pc (x y)
  (declare (xargs :guard (and (local-var-for-pcp x)
                              (local-var-for-pcp y))
                  :guard-hints (("Goal" :in-theory (enable local-var-for-pcp)))))
  (< (second x) (second y)))

;; Introduces all-local-var-for-pcp:
(defforall-simple local-var-for-pcp)

;todo: defmergesort should do this:
(defthm all-local-var-for-pcp-of-rev
  (equal (all-local-var-for-pcp (rev acc))
         (all-local-var-for-pcp acc))
  :hints (("Goal" :in-theory (enable all-local-var-for-pcp rev))))
(defmergesort merge-local-vars-for-pc merge-sort-local-vars-for-pc <-local-vars-for-pc local-var-for-pcp)

;show the local vars in scope for this PC:
(defun local-vars-for-pc (pc local-variable-table)
  (if (endp local-variable-table)
      nil
    (let* ((entry (first local-variable-table))
           (start-pc (nth 1 entry))
           (end-pc (nth 2 entry)))
      (if (and
           ;; the spec seems unclear as to whether start and length indicate the interval:
           ;; [start,start+length], which would have actually be length+1 elements (!)
           ;; or the interval [start,start+length-1].  this code assumes the latter:
           (<= start-pc pc)
           (<= pc end-pc))
          (let ((index (nth 0 entry))
                (name (nth 3 entry))
                (type (nth 4 entry)))
            (cons (list name index type)
                  (local-vars-for-pc pc (rest local-variable-table))))
        (local-vars-for-pc pc (rest local-variable-table))))))

;todo: this must already exist somewhere
(defun reflect-alist (alist)
  (declare (xargs :guard (alistp alist)))
  (if (endp alist)
      nil
    (let ((entry (first alist)))
      (acons (cdr entry) (car entry) (reflect-alist (rest alist))))))

(defun assumptions-that-classes-are-initialized (class-names state-var)
  (if (endp class-names)
      nil
    (cons `(memberp ',(first class-names) (jvm::initialized-classes ,state-var))
          (assumptions-that-classes-are-initialized (rest class-names) state-var))))

(defun assumptions-that-classes-are-uninitialized (class-names state-var)
  (if (endp class-names)
      nil
    (cons `(not (memberp ',(first class-names) (jvm::initialized-classes ,state-var)))
          (assumptions-that-classes-are-uninitialized (rest class-names) state-var))))

(defun add-stack-pops-for-parameters-above (parameter-types-above ;; these are in parameter order (early ones correspond to deeper stack items)
                                            stack-term)
  (declare (xargs :guard (and (jvm::all-typep parameter-types-above)
                              (true-listp parameter-types-above))))
  (if (endp parameter-types-above)
      stack-term
    (let* ((parameter-type-just-above (first parameter-types-above))
           (stack-term (if (member-eq parameter-type-just-above jvm::*two-slot-types*)
                           `(jvm::pop-long ,stack-term)
                         `(jvm::pop-operand ,stack-term))))
      (add-stack-pops-for-parameters-above (rest parameter-types-above) stack-term))))

;;(add-stack-pops-for-parameters-above '(:long :int :int) 'foo) = (JVM::POP-OPERAND (JVM::POP-OPERAND (JVM::POP-LONG FOO)))

(defun stack-item-term (type ;the type of this stack item
                        parameter-types-above ;; these are in parameter order (early ones correspond to deeper stack items)
                        stack-term)
  (declare (xargs :guard (and (jvm::all-typep parameter-types-above)
                              (true-listp parameter-types-above)
                              (jvm::typep type))))
  (if (member-eq type jvm::*two-slot-types*)
      `(jvm::top-long ,(add-stack-pops-for-parameters-above parameter-types-above stack-term))
    `(jvm::top-operand ,(add-stack-pops-for-parameters-above parameter-types-above stack-term))))

;; TODO: Compare to parameter-assumptions-aux
(defun assumptions-about-parameters-on-stack (parameter-types
                                              slot
                                              param-slot-to-name-alist array-length-alist th state-var)
  (if (endp parameter-types)
      nil
    (let* ((type (first parameter-types))
           (parameter-types-above (rest parameter-types))
           (stack-term `(jvm::stack (jvm::thread-top-frame ,th ,state-var))) ;todo: don't repeatedly make this?
           (stack-item-term (stack-item-term type parameter-types-above stack-term))
           (parameter-name (lookup slot param-slot-to-name-alist))
           (assumptions (if (member-eq type jvm::*primitive-types*)
                            (type-assumptions-for-param ;-type
                             type stack-item-term) ;todo: may want to expand things like java-short-as-intp
                          (if (and (jvm::is-one-dim-array-typep type)
                                   (member-eq (farg1 type) jvm::*bv-types*))
                              ;;todo: handle other types
                              ;; but first add support for more types
                              ;; in array-refp If it's an 1-d array
                              ;; type of a handled type (and we
                              ;; know the length), we generate an
                              ;; array-refp hyp for the local
                              (let* ((len (lookup-eq parameter-name array-length-alist))
                                     (array-dims (if len
                                                     `',(list len) ;need a constant here, not something like (cons '55 'nil)
                                                   (prog2$ (cw "(Note: Array parameter with unknown length: ~x0.)~%" parameter-name)
                                                           ;;todo: I had a call of array-contents here and it didn't get expanded (does the simplifier assume terms coming from assumptions are already simplified?!)
                                                           `(cons (len (get-field ,stack-item-term '("ARRAY" "contents" . "dummy-descriptor") (jvm::heap ,state-var)))
                                                                  'nil))))
                                     (component-type (farg1 type)))
                                `((array-refp ,stack-item-term
                                              ,array-dims
                                              ',component-type
                                              (jvm::heap ,state-var))))
                            ;;TODO: Handle params that are refs to instances:
                            (cw  "(Note: Unhandled parameter type (generating no assumptions): ~x0.)~%" type)))))
      (append assumptions
              (assumptions-about-parameters-on-stack (rest parameter-types)
                                                     (+ slot (jvm::type-slot-count type))
                                                     param-slot-to-name-alist array-length-alist th state-var)))))


(defun make-poised-assumptions (staticp method-class method-name method-descriptor parameter-types state-var)
  (let* ((specialp (equal "<init>" method-name) ;;todo: what about super calls that use invokespecial? always make 2 theorems, one for invokespecial and one for invokevirtual
                   )
         (invoke-opcode (if staticp
                            :invokestatic
                          (if specialp
                              :invokespecial
                            :invokevirtual)))
         (interface-args (if (or staticp specialp)
                             (list nil) ;fixme: this assumes all static and special methods are from classes, not interfaces!
                           nil)))
    ;;TODO add 1 for "this" if it's an instance method? or not?  I think not..
    `((equal (lookup-equal (jvm::pc (jvm::thread-top-frame (th) ,state-var))
                           ;; what's the normal form here?
                           (jvm::method-program (jvm::method-info (jvm::thread-top-frame (th) ,state-var))))
             '(,invoke-opcode
               ,method-class ,method-name ,method-descriptor ,parameter-types ,@interface-args)))))

(defforall-simple method-designator-stringp)
(verify-guards all-method-designator-stringp)

(defun param-slot-to-stack-item-alist (parameter-types slot th state-var)
  (if (endp parameter-types)
      nil
    (let* ((type (first parameter-types))
           (parameter-types-above (rest parameter-types))
           (stack-term `(jvm::stack (jvm::thread-top-frame ,th ,state-var))) ;todo: don't repeatedly make this?
           (stack-item-term (stack-item-term type parameter-types-above stack-term)))
      (acons slot stack-item-term
             (param-slot-to-stack-item-alist (rest parameter-types)
                                             (+ slot (jvm::type-slot-count type))
                                             th
                                             state-var)))))

(defforall-simple alistp)
(verify-guards all-alistp)

(defun lookup-eq-in-all (key alists)
  (declare (xargs :guard (and (symbolp key)
                              (all-alistp alists))))
  (if (atom alists)
      nil
    (cons (lookup-eq key (first alists))
          (lookup-eq-in-all key (rest alists)))))

;; Used by Axe
(defthm natp-of-call-stack-size
  (natp (jvm::call-stack-size jvm::stack)))

;a variant of step that we always open
(defun jvm::step-always-open (jvm::th s)
  (declare (xargs :guard (and (jvm::thread-designatorp jvm::th)
                              (jvm::jvm-statep s))
                  :verify-guards nil))
  (let ((jvm::inst (jvm::current-inst jvm::th s)))
    (jvm::do-inst (jvm::op-code jvm::inst)
                  jvm::inst jvm::th s)))

(defthmd step-always-open-correct
  (equal (jvm::step-always-open th s)
         (jvm::step th s))
  :hints (("Goal" :in-theory (enable jvm::step))))

;;;
;;; output-indicators
;;;

;; This indicates what output to extract from the state during decompilation.
;; :return-value means the value on top of the stack.
;; (:array-local <local-num>) means the final contents of the array that was initially referenced by local <local-num>.
;TODO: allow any chain of :field and :array-contents and bv-array-read bottoming out in :return-value or (:param n)...
;TODO: Allow static fields?
;TODO: Should bottom out in a scalar or array, not an object...
(mutual-recursion
 (defun output-indicatorp-aux (x)
   (declare (xargs :guard t
                   :measure (acl2-count x)
                   :ruler-extenders :all ;TODO: Why was this needed?
                   ))
   (or (eq :all x) ;; return the whole final JVM state
       (eq :return-value x)
       (eq :return-value-long x) ;todo: drop?  tool knows the type of the RV?
       (eq :array-return-value x) ;todo: drop?  tool knows the type of the RV?
;      (eq :return-value-byte x) ;trim down to 1 byte (TODO: Should be able to tell this from the return type!) ;TODO: Think through if this is negative
       (and (true-listp x)
            (eql 1 (len (fargs x)))
            (eq :array-local (ffn-symb x)) ;(:array-local <local-num>) ;;TODO: rename to array-param
            (natp (farg1 x)))
       ;; TODO: Remove this one?  or improve all this to allow chains of field and contents calls
       (and (true-listp x) ;;(:field <pair> <indicator-for-object>)
            (eql 2 (len (fargs x)))
            (eq :field (ffn-symb x))
            (class-name-field-id-pairp (farg1 x))
            (output-indicatorp-aux (farg2 x)))
       (and (true-listp x) ;;(:param-field <pair> <local-num>)
            (eql 2 (len (fargs x)))
            (eq :param-field (ffn-symb x))
            (class-name-field-id-pairp (farg1 x))
            (natp (farg2 x)))
       (and (true-listp x) ;;(:tuple ...)
            (<= 1 (len (fargs x))) ;disallow the empty tuple
            (eq :tuple (ffn-symb x))
            (output-indicatorp-aux-lst (fargs x)))))
 (defun output-indicatorp-aux-lst (x)
   (declare (xargs :measure (acl2-count x)))
   (if (atom x)
       (null x)
     (and (output-indicatorp-aux (first x))
          (output-indicatorp-aux-lst (rest x))))))

(defun output-indicatorp (x)
  (declare (xargs :guard t))
  (or (eq :auto x)
      (output-indicatorp-aux x)))

;; If the output-indicator is :auto, do something sensible if we can.  Returns
;; an output-indicatorp-aux, or nil to indicate failure.
;; TODO: Prove that this always returns an output-indicatorp
(defun resolve-auto-output-indicator (return-type)
  (declare (xargs :guard (or (eq :void return-type)
                             (jvm::typep return-type))))
  (if (eq :void return-type)
      ;; If it is void, throw an error for now (TODO: maybe take the last param that can return a value?  what if it's a field?)
      (er hard? 'resolve-auto-output-indicator "No output-indicator given and method is void.")
    ;; If it's not void, we'll use the return type as the output:
    (if (member-eq return-type jvm::*primitive-types*)
        (if (member-eq return-type jvm::*two-slot-types*)
            :return-value-long
          :return-value)
      ;;not a primitive type.  for now, the only reference we handle is a 1-D array
      ;; TODO: Add support for 2-D arrays.
      ;; for any other kind of object, it's not clear what field to return (we probably don't want just the address)
      (if (jvm::is-one-dim-array-typep return-type)
          :array-return-value
        (er hard? 'output-extraction-term "Can't figure out which output to return: method returns a reference that is not a 1-D array.")))))

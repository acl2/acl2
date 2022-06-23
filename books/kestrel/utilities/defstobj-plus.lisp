; A drop-in replacement for defstobj that proves many helpful theorems
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; See example in defstobj-plus-tests.lisp.

;; TODO: Add support for hash table fields!
;; TODO: Add support for stobj table fields!
;; TODO: Consider not disabling recognizers for non-array fields
;; TODO: Restrict the theories used in the hints

(include-book "split-keyword-args")
(include-book "pack") ; todo: reduce or drop?

;; Try to generate an equivalent predicate for a type-spec, or just the default-name if we can't do better.
;; TODO: Add more cases
(defun type-spec-to-name (type-spec default-name)
  (cond ((eq type-spec 'atom) 'atom)
        ((eq type-spec 'bit) 'bitp)
        ((eq type-spec 'character) 'characterp)
        ((eq type-spec 'cons) 'consp)
        ((eq type-spec 'integer) 'integerp)
        ;; todo: handle nil?
        ((eq type-spec 'null) 'not)
        ((eq type-spec 'rational) 'rationalp)
        ((and (consp type-spec)
              (eq 'satisfies (car type-spec)))
         (cadr type-spec))
        ((eq type-spec 'signed-byte) 'integerp)
        ((eq type-spec 'standard-char) 'standard-charp)
        ((eq type-spec 'string) 'stringp)
        ((eq type-spec 'symbol) 'symbolp)
        ;; todo: handle t?
        ((eq type-spec 'unsigned-byte) 'natp)
        ;; Special cases:
        ((equal type-spec '(integer * *)) 'integerp)
        ((equal type-spec '(integer 0 *)) 'natp)
        ((equal type-spec '(integer 1 *)) 'posp)
        (t default-name)))

;; Checks whether nil satisfies the predicate PRED.
(defun nil-satisfies-predp (pred state)
  (declare (xargs :stobjs state))
  (mv-let (erp value)
    ;; Apply pred to nil
    (magic-ev-fncall pred (list nil) state t nil)
    (if erp
        (er hard? 'nil-satisfies-predp "Error evaluating ~x0 on nil." pred)
      (if value t nil))))

(defun maybe-rename-symbol (sym alist)
  (declare (xargs :guard (and (symbolp sym)
                              (symbol-alistp alist))))
  (let ((res (assoc-eq sym alist)))
    (if res
        (cdr res)
      sym)))

(defund assoc-keyword-with-default (key keyword-value-list default)
  (declare (xargs :guard (and (keywordp key)
                              (keyword-value-listp keyword-value-list))))
  (let ((res (assoc-keyword key keyword-value-list)))
    (if res
        (cadr res)
      default)))

;; Theorems about operations wrapped around inner scalar updaters
(defun interaction-theorems-for-scalar-field (all-field-infos other-field-num stobj-name renaming this-field-num this-updater-fn)
  (if (endp all-field-infos)
      nil
    (if (= this-field-num other-field-num)
        ;; no theorems about this field interacting with itself (that's handled elsewhere):
        (interaction-theorems-for-scalar-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-updater-fn)
      (let* ((other-field-info (first all-field-infos))
             (name (if (consp other-field-info)
                   (car other-field-info)
                 ;; the entire arg is the field name:
                   other-field-info))
             ;; These are all for the other field, since their names don't contain "this"
             (keyword-value-list (if (consp other-field-info) (cdr other-field-info) nil))
             (type (assoc-keyword-with-default :type keyword-value-list t))
             (type-kind (if (consp type) (car type) type)))
        (cond
         ((eq 'array type-kind)
          (let* (;(initial-value (assoc-keyword-with-default :initially keyword-value-list nil))
                 ;(resizable (assoc-keyword-with-default :resizable keyword-value-list nil))
                 ;(element-type (cadr type))
                 ;; is (nth n l) here okay (not a variable)?
                 ;(type-claim-for-nth-n-l (translate-declaration-to-guard-gen element-type '(nth n l) t nil))
                 (length-fn (defstobj-fnname name :length :array renaming))
                 (resize-fn (defstobj-fnname name :resize :array renaming))
                 (accessor-fn (defstobj-fnname name :accessor :array renaming))
                 (updater-fn (defstobj-fnname name :updater :array renaming))
                 ;; todo: suppress these if they are 't:
                 ;(type-claim-for-default-value (translate-declaration-to-guard-gen element-type 'default-value t nil))
                 ;(type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
                 ;(type-claim-for-v (translate-declaration-to-guard-gen element-type 'v t nil))
                 ;(type-claim-for-accessor (translate-declaration-to-guard-gen element-type `(,accessor-fn i ,stobj-name) t nil))
                 )
            ;; Array operations wrapped around scalar update
            (append `((defthm ,(pack$ accessor-fn '-of- this-updater-fn)
                        (equal (,accessor-fn i (,this-updater-fn v ,stobj-name))
                               (,accessor-fn i ,stobj-name))
                        :hints (("Goal" :in-theory '(,accessor-fn
                                                     ,this-updater-fn
                                                     nth-update-nth
                                                     (:e nfix)))))

                      (defthm ,(pack$ length-fn '-of- this-updater-fn)
                        (equal (,length-fn (,this-updater-fn v ,stobj-name))
                               (,length-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,length-fn ,this-updater-fn))))
                      ,@(and (< this-field-num other-field-num) ; bring inner writes outward since field number is lower
                             `((defthm ,(pack$ updater-fn '-of- this-updater-fn)
                                 (equal (,updater-fn i v1 (,this-updater-fn v2 ,stobj-name))
                                        (,this-updater-fn v2 (,updater-fn i v1 ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,updater-fn ,this-updater-fn))))
                               (defthm ,(pack$ resize-fn '-of- this-updater-fn)
                                 (equal (,resize-fn i (,this-updater-fn v2 ,stobj-name))
                                        (,this-updater-fn v2 (,resize-fn i ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,resize-fn ,this-updater-fn)))))))
                    (interaction-theorems-for-scalar-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-updater-fn))))
         ((eq 'hash-table type-kind)
          (progn$ ;(cw "NOTE: Hash table fields are not yet supported by defstobj+.")
           nil))
         ((eq 'stobj-table type-kind)
          (progn$ ;(cw "NOTE: Stobj table fields are not yet supported by defstobj+.")
           nil))
         (t ;must be a scalar type (possibly TYPE is t)
          (let* ( ;; (initial-value (assoc-keyword-with-default :initially keyword-value-list nil))
                 (accessor-fn (defstobj-fnname name :accessor :scalar renaming))
                 (updater-fn (defstobj-fnname name :updater :scalar renaming))
                 ;; todo: suppress these if they are 't:
                 ;; (type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
                 ;(type-claim-for-v (translate-declaration-to-guard-gen type 'v t nil))
                 ;(type-claim-for-accessor (translate-declaration-to-guard-gen type `(,accessor-fn ,stobj-name) t nil))
                 )
            ;; Scalar operations wrapped around scalar update
            (append `((defthm ,(pack$ accessor-fn '-of- this-updater-fn)
                        (equal (,accessor-fn (,this-updater-fn v ,stobj-name))
                               (,accessor-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-updater-fn))))
                      ,@(and (< this-field-num other-field-num) ; bring inner writes outward since field number is lower
                             `((defthm ,(pack$ updater-fn '-of- this-updater-fn)
                                (equal (,updater-fn v1 (,this-updater-fn v2 ,stobj-name))
                                       (,this-updater-fn v2 (,updater-fn v1 ,stobj-name)))
                                :hints (("Goal" :in-theory (enable ,updater-fn ,this-updater-fn)))))))
                    (interaction-theorems-for-scalar-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-updater-fn)))))))))

;; Theorems about operations wrapped around inner array updaters
(defun interaction-theorems-for-array-field (all-field-infos other-field-num stobj-name renaming this-field-num this-updater-fn this-resize-fn)
  (if (endp all-field-infos)
      nil
    (if (= this-field-num other-field-num)
        ;; no theorems about this field interacting with itself (that's handled elsewhere):
        (interaction-theorems-for-array-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-updater-fn this-resize-fn)
      (let* ((other-field-info (first all-field-infos))
             (name (if (consp other-field-info)
                   (car other-field-info)
                 ;; the entire arg is the field name:
                   other-field-info))
             ;; These are all for the other field, since their names don't contain "this"
             (keyword-value-list (if (consp other-field-info) (cdr other-field-info) nil))
             (type (assoc-keyword-with-default :type keyword-value-list t))
             (type-kind (if (consp type) (car type) type)))
        (cond
         ((eq 'array type-kind)
          (let* (;(initial-value (assoc-keyword-with-default :initially keyword-value-list nil))
                 ;(resizable (assoc-keyword-with-default :resizable keyword-value-list nil))
                 ;(element-type (cadr type))
                 ;; is (nth n l) here okay (not a variable)?
                 ;;(type-claim-for-nth-n-l (translate-declaration-to-guard-gen element-type '(nth n l) t nil))
                 (length-fn (defstobj-fnname name :length :array renaming))
                 (resize-fn (defstobj-fnname name :resize :array renaming))
                 (accessor-fn (defstobj-fnname name :accessor :array renaming))
                 (updater-fn (defstobj-fnname name :updater :array renaming))
                 ;; todo: suppress these if they are 't:
                 ;(type-claim-for-default-value (translate-declaration-to-guard-gen element-type 'default-value t nil))
                 ;(type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
                 ;(type-claim-for-v (translate-declaration-to-guard-gen element-type 'v t nil))
                 ;(type-claim-for-accessor (translate-declaration-to-guard-gen element-type `(,accessor-fn i ,stobj-name) t nil))
                 )
            ;; Array operations wrapped around array updates
            (append `((defthm ,(pack$ accessor-fn '-of- this-updater-fn)
                        (equal (,accessor-fn i1 (,this-updater-fn i2 v ,stobj-name))
                               (,accessor-fn i1 ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-updater-fn))))

                      (defthm ,(pack$ length-fn '-of- this-updater-fn)
                        (equal (,length-fn (,this-updater-fn i v ,stobj-name))
                               (,length-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,length-fn ,this-updater-fn))))

                      (defthm ,(pack$ accessor-fn '-of- this-resize-fn)
                        (equal (,accessor-fn i1 (,this-resize-fn i2 ,stobj-name))
                               (,accessor-fn i1 ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-resize-fn))))

                      (defthm ,(pack$ length-fn '-of- this-resize-fn)
                        (equal (,length-fn (,this-resize-fn i ,stobj-name))
                               (,length-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,length-fn ,this-resize-fn))))

                      ,@(and (< this-field-num other-field-num) ; bring inner writes outward since field number is lower
                             `((defthm ,(pack$ updater-fn '-of- this-updater-fn)
                                 (equal (,updater-fn i1 v1 (,this-updater-fn i2 v2 ,stobj-name))
                                        (,this-updater-fn i2 v2 (,updater-fn i1 v1 ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,updater-fn ,this-updater-fn))))
                               (defthm ,(pack$ resize-fn '-of- this-updater-fn)
                                 (equal (,resize-fn i1 (,this-updater-fn i2 v ,stobj-name))
                                        (,this-updater-fn i2 v (,resize-fn i1 ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,resize-fn ,this-updater-fn))))
                               (defthm ,(pack$ updater-fn '-of- this-resize-fn)
                                 (equal (,updater-fn i1 v (,this-resize-fn i2 ,stobj-name))
                                        (,this-resize-fn i2 (,updater-fn i1 v ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,updater-fn ,this-resize-fn))))
                               (defthm ,(pack$ resize-fn '-of- this-resize-fn)
                                 (equal (,resize-fn i1 (,this-resize-fn i2 ,stobj-name))
                                        (,this-resize-fn i2 (,resize-fn i1 ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,resize-fn ,this-resize-fn)))))))
                    (interaction-theorems-for-array-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-updater-fn this-resize-fn))))
         ((eq 'hash-table type-kind)
          (progn$ ;(cw "NOTE: Hash table fields are not yet supported by defstobj+.")
           nil))
         ((eq 'stobj-table type-kind)
          (progn$ ;(cw "NOTE: Stobj table fields are not yet supported by defstobj+.")
           nil))
         (t ;must be a scalar type (possibly TYPE is t)
          (let* ( ;; (initial-value (assoc-keyword-with-default :initially keyword-value-list nil))
                 (accessor-fn (defstobj-fnname name :accessor :scalar renaming))
                 (updater-fn (defstobj-fnname name :updater :scalar renaming))
                 ;; todo: suppress these if they are 't:
                 ;; (type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
                 ;(type-claim-for-v (translate-declaration-to-guard-gen type 'v t nil))
                 ;(type-claim-for-accessor (translate-declaration-to-guard-gen type `(,accessor-fn ,stobj-name) t nil))
                 )
            ;; Scalar operations wrapped around array updates
            (append `((defthm ,(pack$ accessor-fn '-of- this-updater-fn)
                        (equal (,accessor-fn (,this-updater-fn i v ,stobj-name))
                               (,accessor-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-updater-fn))))
                      (defthm ,(pack$ accessor-fn '-of- this-resize-fn)
                        (equal (,accessor-fn (,this-resize-fn i ,stobj-name))
                               (,accessor-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-resize-fn))))
                      ,@(and (< this-field-num other-field-num) ; bring inner writes outward since field number is lower
                             `((defthm ,(pack$ updater-fn '-of- this-updater-fn)
                                (equal (,updater-fn v1 (,this-updater-fn i v2 ,stobj-name))
                                       (,this-updater-fn i v2 (,updater-fn v1 ,stobj-name)))
                                :hints (("Goal" :in-theory (enable ,updater-fn ,this-updater-fn))))
                               (defthm ,(pack$ updater-fn '-of- this-resize-fn)
                                 (equal (,updater-fn v (,this-resize-fn i ,stobj-name))
                                        (,this-resize-fn i (,updater-fn v ,stobj-name)))
                                :hints (("Goal" :in-theory (enable ,updater-fn ,this-resize-fn)))))))
                    (interaction-theorems-for-array-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-updater-fn this-resize-fn)))))))))

;; Returns (mv theorems names).
(defun theorems-for-defstobj-field (field-info field-num stobj-name top-recognizer renaming all-field-infos state)
  (declare (xargs :mode :program ;because of translate-declaration-to-guard-gen
                  :stobjs state))
  (let* ((name (if (consp field-info)
                   (car field-info)
                 ;; the entire arg is the field name:
                 field-info))
         (recognizer (defstobj-fnname name :recognizer :scalar renaming)) ; same for all kinds of fields
         (keyword-value-list (if (consp field-info) (cdr field-info) nil))
         (type (assoc-keyword-with-default :type keyword-value-list t))
         (type-kind (if (consp type) (car type) type)))
    (cond
     ((eq 'array type-kind)
      (let* ((initial-value (assoc-keyword-with-default :initially keyword-value-list nil))
             (resizable (assoc-keyword-with-default :resizable keyword-value-list nil))
             (element-type (cadr type))
             (element-type-pred (type-spec-to-name element-type 'element-type))
             (nil-obviously-satisfies-element-typep (and (not (eq 'element-type element-type-pred)) ; todo: perhaps use the result of translate-declaration-to-guard-gen here?
                                                         (nil-satisfies-predp element-type-pred state)))
             ;; is (nth n l) here okay (not a variable)?
             (type-claim-for-nth-n-l (translate-declaration-to-guard-gen element-type '(nth n l) t nil))
             (length-fn (defstobj-fnname name :length :array renaming))
             (resize-fn (defstobj-fnname name :resize :array renaming))
             (accessor-fn (defstobj-fnname name :accessor :array renaming))
             (updater-fn (defstobj-fnname name :updater :array renaming))
             ;; todo: suppress these if they are 't:
             ;; TODO: For scalar fields, when do we want to phrase things in terms of the RECOGNIZER?
             ;; If the type is (satisfies ...), RECOGNIZER is likely unnecessary.
             (type-claim-for-default-value (translate-declaration-to-guard-gen element-type 'default-value t nil))
             (type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
             (type-claim-for-v (translate-declaration-to-guard-gen element-type 'v t nil))
             ;; TODO: Is the type is not a trivial alias of another type, we might want to keep it closed up?:
             (type-claim-for-accessor (translate-declaration-to-guard-gen element-type `(,accessor-fn i ,stobj-name) t nil))
             )
        (mv `(;; Helper theorem:
              (defthm ,(pack$ recognizer '-of-make-list-ac)
                (implies (,recognizer acc)
                         (,recognizer (make-list-ac n ',initial-value acc)))
                ;; TODO: Tighten this theory, but note that we need to be able to show that the initial value satisfies the element predicate:
                :hints (("Goal" :in-theory (enable ,recognizer
                                                   make-list-ac
                                                   (:i make-list-ac)
                                                   )
                         :induct (make-list-ac n ',initial-value acc))))

              ;; Helper theorem:
              (defthm ,(pack$ recognizer '-of-update-nth)
                (implies (and (,recognizer l)
                              (natp key)
                              (< key (len l))
                              ,type-claim-for-val)
                         (,recognizer (update-nth key val l)))
                :hints (("Goal" :induct (update-nth key val l)
                         :in-theory (e/d (len update-nth ,recognizer)
                                         (;len-of-cdr
                                          )))))

              ;; Updating the array field preserves well-formedness:
              (defthm ,(pack$ top-recognizer '-of- updater-fn)
                (implies (and (,top-recognizer ,stobj-name)
                              (< i (,length-fn ,stobj-name))
                              (natp i)
                              ,type-claim-for-v)
                         (,top-recognizer (,updater-fn i v ,stobj-name)))
                :hints (("Goal" :in-theory (enable ,top-recognizer ,updater-fn ,length-fn ,recognizer))))

              ;; Updating an element doesn't affect the length:
              (defthm ,(pack$ length-fn '-of- updater-fn)
                (implies (and (< i (,length-fn ,stobj-name))
                              (natp i))
                         (equal (,length-fn (,updater-fn i v ,stobj-name))
                                (,length-fn ,stobj-name)))
                :hints (("Goal" :in-theory (enable ,length-fn ,updater-fn))))

              (local
               (defthm ,(pack$ accessor-fn '-when-not-natp)
                 (implies (not (natp i))
                          (equal (,accessor-fn i ,stobj-name)
                                 (,accessor-fn 0 ,stobj-name)))
                 :hints (("Goal" :in-theory (enable ,accessor-fn)))))

              (local
               (defthm ,(pack$ updater-fn '-when-not-natp)
                 (implies (not (natp i))
                          (equal (,updater-fn i v ,stobj-name)
                                 (,updater-fn 0 v ,stobj-name)))
                 :hints (("Goal" :in-theory (enable ,updater-fn)))))

              ;; First read-over-write rule:
              (defthm ,(pack$ accessor-fn '-of- updater-fn '-same)
                (equal (,accessor-fn i (,updater-fn i v ,stobj-name))
                       v)
                :hints (("Goal" :in-theory (enable ,accessor-fn ,length-fn ,updater-fn))))

              ;; Second read-over-write rule:
              (defthm ,(pack$ accessor-fn '-of- updater-fn '-diff)
                (implies (not (equal (nfix i1) (nfix i2)))
                         (equal (,accessor-fn i1 (,updater-fn i2 v ,stobj-name))
                                (,accessor-fn i1 ,stobj-name)))
                :hints (("Goal" :in-theory (enable ,accessor-fn ,length-fn ,updater-fn))))

              ;; Third read-over-write rule.  Disabled, since it can cause case splits:
              (defthmd ,(pack$ accessor-fn '-of- updater-fn '-split)
                (equal (,accessor-fn i1 (,updater-fn i2 v ,stobj-name))
                       (if (equal (nfix i1) (nfix i2))
                           v
                         (,accessor-fn i1 ,stobj-name))))

              ;; First write-over-write rule:
              (defthm ,(pack$ updater-fn '-of- updater-fn '-same)
                (equal (,updater-fn i v1 (,updater-fn i v2 ,stobj-name))
                       (,updater-fn i v1 ,stobj-name))
                :hints (("Goal" :in-theory (enable ,updater-fn))))

              ;; Second write-over-write rule:
              (defthm ,(pack$ updater-fn '-of- updater-fn '-diff)
                (implies (and (syntaxp (not (term-order i1 i2))) ; i2 is a smaller term than i1
                              (not (equal (nfix i1) (nfix i2))))
                         (equal (,updater-fn i1 v1 (,updater-fn i2 v2 ,stobj-name))
                                (,updater-fn i2 v2 (,updater-fn i1 v1 ,stobj-name))))
                :hints (("Goal" :in-theory (enable ,updater-fn))))

              ;; Third write-over-write rule:
              (defthm ,(pack$ updater-fn '-of- updater-fn '-split)
                (implies (syntaxp (not (term-order i1 i2))) ; i2 is a smaller term than i1
                         (equal (,updater-fn i1 v1 (,updater-fn i2 v2 ,stobj-name))
                                (if (equal (nfix i1) (nfix i2))
                                    (,updater-fn i1 v1 ,stobj-name)
                                  (,updater-fn i2 v2 (,updater-fn i1 v1 ,stobj-name)))))
                :hints (("Goal" :in-theory (enable ,updater-fn))))

              ;;  Fourth write-over-write rule (special case when the values are the same):
              (defthm ,(pack$ updater-fn '-of- updater-fn '-same-values)
                (implies (syntaxp (not (term-order i1 i2))) ; i2 is a smaller term than i1
                         (equal (,updater-fn i1 v (,updater-fn i2 v ,stobj-name))
                                (,updater-fn i2 v (,updater-fn i1 v ,stobj-name))))
                :hints (("Goal" :in-theory (enable ,updater-fn))))

              ,@(and (not (equal element-type t)) ; rewrite rules would be illegal
                     `(;; Helper theorem, disabled since may be hung on a common function:
                       (defthmd ,(pack$ element-type-pred '-of-nth-when- recognizer)
                         (implies (and (,recognizer l)
                                       ,@(and (not nil-obviously-satisfies-element-typep) ; some hyps can be dropped if nil satisfies the element recognizer
                                              `((natp n)
                                                (< n (len l)))))
                                  ,type-claim-for-nth-n-l)
                         :hints (("Goal" :in-theory (enable (:d len) (:i nth) ,recognizer))))

                       ;; The accessor gives an element of the right type:
                       (defthm ,(pack$ element-type-pred '-of- accessor-fn)
                         (implies (and (,top-recognizer ,stobj-name)
                                       ,@(and (not nil-obviously-satisfies-element-typep) ; some hyps can be dropped if nil satisfies the element recognizer
                                              `((natp i)
                                                (< i (,length-fn ,stobj-name)))))
                                  ,type-claim-for-accessor)
                         :hints (("Goal"
                                  :use (:instance ,(pack$ element-type-pred '-of-nth-when- recognizer)
                                                  (n i)
                                                  (l (nth ,field-num ,stobj-name)))
                                  :in-theory (e/d (,top-recognizer ,accessor-fn ,length-fn)
                                                  (,(pack$ element-type-pred '-of-nth-when- recognizer))))))))

              ,@(and resizable
                     `(;; Helper theorem:
                       (defthm ,(pack$ recognizer '-of-resize-list)
                         (implies (and (,recognizer lst)
                                       ,type-claim-for-default-value ; todo: can we compute this?
                                       )
                                  (,recognizer (resize-list lst n default-value)))
                         :hints (("Goal" :in-theory (enable resize-list ,recognizer)
                                  :induct (resize-list lst n default-value))))

                       ;; Resizing the array field preserves well-formedness:
                       (defthm ,(pack$ top-recognizer '-of- resize-fn)
                         (implies (,top-recognizer ,stobj-name)
                                  (,top-recognizer (,resize-fn i ,stobj-name)))
                         :hints (("Goal" :in-theory (enable ,resize-fn ,top-recognizer))))

                       ;; Resizing sets the length as expected:
                       (defthm ,(pack$ length-fn '-of- resize-fn)
                         (equal (,length-fn (,resize-fn i ,stobj-name))
                                (nfix i))
                         :hints (("Goal" :in-theory (enable ,length-fn ,resize-fn))))

                       ;; TODO: Make safe versions that don't case split:
                       ;; Resizing may or may not affect reading an element:
                       (defthm ,(pack$ accessor-fn '-of- resize-fn)
                         (implies (and (natp i) ; move hyps to conclusion?
                                       (natp new-size))
                                  (equal (,accessor-fn i (,resize-fn new-size ,stobj-name))
                                         (if (< i new-size)
                                             (if (< i (,length-fn ,stobj-name))
                                                 (,accessor-fn i ,stobj-name)
                                               ',initial-value)
                                           nil)))
                         :hints (("Goal" :in-theory (enable ,accessor-fn ,resize-fn ,length-fn))))

                       ;; TODO: Make safe versions that don't case split:
                       (defthm ,(pack$ resize-fn '-of- updater-fn)
                         (implies (and (natp i) ; move hyps to conclusion?
                                       (natp new-size)
                                       (< i (,length-fn ,stobj-name)))
                                  (equal (,resize-fn new-size (,updater-fn i v ,stobj-name))
                                         (if (< i new-size)
                                             (,updater-fn i v (,resize-fn new-size ,stobj-name))
                                           (,resize-fn new-size ,stobj-name))))
                         :hints (("Goal" :in-theory (enable ,updater-fn ,resize-fn ,length-fn))))
                       ))
              ,@(interaction-theorems-for-array-field all-field-infos 0 stobj-name renaming field-num updater-fn resize-fn)
              )
            ;; names:
            (list recognizer accessor-fn updater-fn length-fn resize-fn))))
     ((eq 'hash-table type-kind)
      (prog2$ (cw "NOTE: Hash table fields are not yet supported by defstobj+.")
              (mv nil
                  nil ;; (list recognizer)
                  )))
     ((eq 'stobj-table type-kind)
      (prog2$ (cw "NOTE: Stobj table fields are not yet supported by defstobj+.")
              (mv nil
                  nil ;; (list recognizer)
                  )))
     (t ;must be a scalar type (possibly TYPE is t)
      (let* (;; (initial-value (assoc-keyword-with-default :initially keyword-value-list nil))
             (field-type-name (type-spec-to-name type 'field-type))
             (accessor-fn (defstobj-fnname name :accessor :scalar renaming))
             (updater-fn (defstobj-fnname name :updater :scalar renaming))
             ;; todo: suppress these if they are 't:
             ;; (type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
             (type-claim-for-v (translate-declaration-to-guard-gen type 'v t nil))
             (type-claim-for-accessor (translate-declaration-to-guard-gen type `(,accessor-fn ,stobj-name) t nil))
             )
        (mv `(;; Updating the scalar field preserves well-formedness:
              (defthm ,(pack$ top-recognizer '-of- updater-fn)
                (implies (and (,top-recognizer ,stobj-name)
                              ,type-claim-for-v)
                         (,top-recognizer (,updater-fn v ,stobj-name)))
                :hints (("Goal" :in-theory (enable ,top-recognizer ,updater-fn ,recognizer))))

              ;; Read-over-write rule:
              ;; proof uses nth-update-nth, which is built in
              (defthm ,(pack$ accessor-fn '-of- updater-fn)
                (equal (,accessor-fn (,updater-fn v ,stobj-name))
                       v)
                :hints (("Goal" :in-theory (enable ,updater-fn ,accessor-fn))))

              ;; Write-over-write rule:
              (defthm ,(pack$ updater-fn '-of- updater-fn)
                (equal (,updater-fn v2 (,updater-fn v1 ,stobj-name))
                       (,updater-fn v2 ,stobj-name))
                :hints (("Goal" :in-theory (enable ,updater-fn))))

              ;; The accessor of the scalar field returns a value of the appropriate type:
              ,@(and (not (equal type t)) ; rewrite rule would be illegal
                     `((defthm ,(pack$ field-type-name '-of- accessor-fn)
                         (implies (,top-recognizer ,stobj-name)
                                  ,type-claim-for-accessor)
                         :hints (("Goal" :in-theory (enable ,top-recognizer ,accessor-fn ,recognizer))))))

              ,@(interaction-theorems-for-scalar-field all-field-infos 0 stobj-name renaming field-num updater-fn)
              )
            (list recognizer accessor-fn updater-fn)))))))

;; Returns (mv theorems names).
(defun theorems-and-names-for-defstobj-fields (field-infos field-num stobj-name top-recognizer renaming all-field-infos theorems-acc names-acc state)
  (declare (xargs :mode :program
                  :stobjs state))
  (if (endp field-infos)
      (mv (reverse theorems-acc) (reverse names-acc))
    (mv-let (theorems names)
      (theorems-for-defstobj-field (first field-infos) field-num stobj-name top-recognizer renaming all-field-infos state)
      (theorems-and-names-for-defstobj-fields (rest field-infos)
                                              (+ 1 field-num)
                                              stobj-name top-recognizer renaming all-field-infos
                                              (append (reverse theorems) ; since the acc will get reversed at the very end
                                                      theorems-acc)
                                              (append (reverse names) ; since the acc will get reversed at the very end
                                                      names-acc)
                                              state))))

;; Returns an event
(defun defstobj+-fn (stobj-name args state)
  (declare (xargs :mode :program
                  :stobjs state))
  (mv-let (field-infos keyword-value-list)
    (split-keyword-args args)
    (let* ((renaming (cadr (assoc-keyword :renaming keyword-value-list)))
           ;; Make the renaming into an alist:
           ;; (renaming (pairlis$ (strip-cars renaming) (strip-cadrs renaming)))
           (top-recognizer (defstobj-fnname stobj-name :recognizer :top renaming))
           (creator (defstobj-fnname stobj-name :creator :top renaming)))
      (mv-let (theorems-for-fields names-for-fields) ; the names-for-fields include recognizers, accessors, updaters, etc.
        (theorems-and-names-for-defstobj-fields field-infos 0 stobj-name top-recognizer renaming field-infos nil nil state)
        `(encapsulate ()
           (local (include-book "kestrel/lists-light/resize-list" :dir :system))
           (local (include-book "kestrel/lists-light/make-list-ac" :dir :system))
           (local (include-book "kestrel/lists-light/update-nth" :dir :system))
           (local (include-book "kestrel/lists-light/nth" :dir :system))
           ;; (local (include-book "kestrel/lists-light/len" :dir :system))

           (defstobj ,stobj-name ,@args)

           (local (in-theory (disable
                              ;; Prevents making huge lists of copies of the default value:
                              make-list-ac
                              (:executable-counterpart make-list-ac)

                              len nth)))

           ;; Disable all names introduced by defstobj:
           (in-theory (disable ,top-recognizer ,creator ,@names-for-fields))

           ,@theorems-for-fields

           ;; Has to come after the theorems-for-fields, since this need rules about MAKE-LIST-AC.
           ;; The stobj creation function returns a well-formed stobj:
           (defthm ,(pack$ top-recognizer '-of- creator)
             (,top-recognizer (,creator))
             :hints (("Goal" :in-theory (enable ,top-recognizer
                                                ,creator
                                                LENGTH
                                                len
                                                (:i nth))))))))))

(defmacro defstobj+ (name &rest args)
  `(make-event (defstobj+-fn ',name ',args state)))

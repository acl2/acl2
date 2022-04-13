; A drop-in replacement for defstobj that proves many helpful theorems
;
; Copyright (C) 2022 Kestrel Institute
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; TODO: Add support for hash table fields!
;; TODO: Add support for stobj table fields!

(include-book "split-keyword-args")
(include-book "pack") ; todo: reduce or drop?

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
(defun interaction-theorems-for-scalar-field (all-field-infos other-field-num stobj-name renaming this-field-num this-update-fn)
  (if (endp all-field-infos)
      nil
    (if (= this-field-num other-field-num)
        ;; no theorems about this field interacting with itself (that's handled elsewhere):
        (interaction-theorems-for-scalar-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-update-fn)
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
                 (default-length-fn (pack$ name '-length))
                 (length-fn (maybe-rename-symbol default-length-fn renaming))
                 (default-resize-fn (pack$ 'resize- name))
                 (resize-fn (maybe-rename-symbol default-resize-fn renaming))
                 (default-accessor-fn (pack$ name 'i))
                 (accessor-fn (maybe-rename-symbol default-accessor-fn renaming))
                 (default-update-fn (pack$ 'update- name 'i))
                 (update-fn (maybe-rename-symbol default-update-fn renaming))
                 ;; todo: suppress these if they are 't:
                 ;(type-claim-for-default-value (translate-declaration-to-guard-gen element-type 'default-value t nil))
                 ;(type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
                 ;(type-claim-for-v (translate-declaration-to-guard-gen element-type 'v t nil))
                 ;(type-claim-for-accessor (translate-declaration-to-guard-gen element-type `(,accessor-fn i ,stobj-name) t nil))
                 )
            ;; Array operations wrapped around scalar update
            (append `((defthm ,(pack$ accessor-fn '-of- this-update-fn)
                        (equal (,accessor-fn i (,this-update-fn v ,stobj-name))
                               (,accessor-fn i ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-update-fn))))

                      (defthm ,(pack$ length-fn '-of- this-update-fn)
                        (equal (,length-fn (,this-update-fn v ,stobj-name))
                               (,length-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,length-fn ,this-update-fn))))
                      ,@(and (< this-field-num other-field-num) ; bring inner writes outward since field number is lower
                             `((defthm ,(pack$ update-fn '-of- this-update-fn)
                                 (equal (,update-fn i v1 (,this-update-fn v2 ,stobj-name))
                                        (,this-update-fn v2 (,update-fn i v1 ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,update-fn ,this-update-fn))))
                               (defthm ,(pack$ resize-fn '-of- this-update-fn)
                                 (equal (,resize-fn i v1 (,this-update-fn v2 ,stobj-name))
                                        (,this-update-fn v2 (,update-fn i v1 ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,update-fn ,this-update-fn)))))))
                    (interaction-theorems-for-scalar-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-update-fn))))
         ((eq 'hash-table type-kind)
          (progn$ ;(cw "NOTE: Hash table fields are not yet supported by defstobj+.")
           nil))
         ((eq 'stobj-table type-kind)
          (progn$ ;(cw "NOTE: Stobj table fields are not yet supported by defstobj+.")
           nil))
         (t ;must be a scalar type (possibly TYPE is t)
          (let* ( ;; (initial-value (assoc-keyword-with-default :initially keyword-value-list nil))
                 (default-accessor-fn name)
                 (accessor-fn (maybe-rename-symbol default-accessor-fn renaming))
                 (default-update-fn (pack$ 'update- name))
                 (update-fn (maybe-rename-symbol default-update-fn renaming))
                 ;; todo: suppress these if they are 't:
                 ;; (type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
                 ;(type-claim-for-v (translate-declaration-to-guard-gen type 'v t nil))
                 ;(type-claim-for-accessor (translate-declaration-to-guard-gen type `(,accessor-fn ,stobj-name) t nil))
                 )
            ;; Scalar operations wrapped around scalar update
            (append `((defthm ,(pack$ accessor-fn '-of- this-update-fn)
                        (equal (,accessor-fn (,this-update-fn v ,stobj-name))
                               (,accessor-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-update-fn))))
                      ,@(and (< this-field-num other-field-num) ; bring inner writes outward since field number is lower
                             `((defthm ,(pack$ update-fn '-of- this-update-fn)
                                (equal (,update-fn v1 (,this-update-fn v2 ,stobj-name))
                                       (,this-update-fn v2 (,update-fn v1 ,stobj-name)))
                                :hints (("Goal" :in-theory (enable ,update-fn ,this-update-fn)))))))
                    (interaction-theorems-for-scalar-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-update-fn)))))))))

;; Theorems about operations wrapped around inner array updaters
(defun interaction-theorems-for-array-field (all-field-infos other-field-num stobj-name renaming this-field-num this-update-fn this-resize-fn)
  (if (endp all-field-infos)
      nil
    (if (= this-field-num other-field-num)
        ;; no theorems about this field interacting with itself (that's handled elsewhere):
        (interaction-theorems-for-array-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-update-fn this-resize-fn)
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
                 (default-length-fn (pack$ name '-length))
                 (length-fn (maybe-rename-symbol default-length-fn renaming))
                 (default-resize-fn (pack$ 'resize- name))
                 (resize-fn (maybe-rename-symbol default-resize-fn renaming))
                 (default-accessor-fn (pack$ name 'i))
                 (accessor-fn (maybe-rename-symbol default-accessor-fn renaming))
                 (default-update-fn (pack$ 'update- name 'i))
                 (update-fn (maybe-rename-symbol default-update-fn renaming))
                 ;; todo: suppress these if they are 't:
                 ;(type-claim-for-default-value (translate-declaration-to-guard-gen element-type 'default-value t nil))
                 ;(type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
                 ;(type-claim-for-v (translate-declaration-to-guard-gen element-type 'v t nil))
                 ;(type-claim-for-accessor (translate-declaration-to-guard-gen element-type `(,accessor-fn i ,stobj-name) t nil))
                 )
            ;; Array operations wrapped around array updates
            (append `((defthm ,(pack$ accessor-fn '-of- this-update-fn)
                        (equal (,accessor-fn i1 (,this-update-fn i2 v ,stobj-name))
                               (,accessor-fn i1 ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-update-fn))))

                      (defthm ,(pack$ length-fn '-of- this-update-fn)
                        (equal (,length-fn (,this-update-fn i v ,stobj-name))
                               (,length-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,length-fn ,this-update-fn))))

                      (defthm ,(pack$ accessor-fn '-of- this-resize-fn)
                        (equal (,accessor-fn i1 (,this-resize-fn i2 ,stobj-name))
                               (,accessor-fn i1 ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-resize-fn))))

                      (defthm ,(pack$ length-fn '-of- this-resize-fn)
                        (equal (,length-fn (,this-resize-fn i ,stobj-name))
                               (,length-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,length-fn ,this-resize-fn))))

                      ,@(and (< this-field-num other-field-num) ; bring inner writes outward since field number is lower
                             `((defthm ,(pack$ update-fn '-of- this-update-fn)
                                 (equal (,update-fn i1 v1 (,this-update-fn i2 v2 ,stobj-name))
                                        (,this-update-fn i2 v2 (,update-fn i1 v1 ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,update-fn ,this-update-fn))))
                               (defthm ,(pack$ resize-fn '-of- this-update-fn)
                                 (equal (,resize-fn i1 (,this-update-fn i2 v ,stobj-name))
                                        (,this-update-fn i2 v (,resize-fn i1 ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,resize-fn ,this-update-fn))))
                               (defthm ,(pack$ update-fn '-of- this-resize-fn)
                                 (equal (,update-fn i1 v (,this-resize-fn i2 ,stobj-name))
                                        (,this-resize-fn i2 (,update-fn i1 v ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,update-fn ,this-resize-fn))))
                               (defthm ,(pack$ resize-fn '-of- this-resize-fn)
                                 (equal (,resize-fn i1 (,this-resize-fn i2 ,stobj-name))
                                        (,this-resize-fn i2 (,resize-fn i1 ,stobj-name)))
                                 :hints (("Goal" :in-theory (enable ,resize-fn ,this-resize-fn)))))))
                    (interaction-theorems-for-array-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-update-fn this-resize-fn))))
         ((eq 'hash-table type-kind)
          (progn$ ;(cw "NOTE: Hash table fields are not yet supported by defstobj+.")
           nil))
         ((eq 'stobj-table type-kind)
          (progn$ ;(cw "NOTE: Stobj table fields are not yet supported by defstobj+.")
           nil))
         (t ;must be a scalar type (possibly TYPE is t)
          (let* ( ;; (initial-value (assoc-keyword-with-default :initially keyword-value-list nil))
                 (default-accessor-fn name)
                 (accessor-fn (maybe-rename-symbol default-accessor-fn renaming))
                 (default-update-fn (pack$ 'update- name))
                 (update-fn (maybe-rename-symbol default-update-fn renaming))
                 ;; todo: suppress these if they are 't:
                 ;; (type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
                 ;(type-claim-for-v (translate-declaration-to-guard-gen type 'v t nil))
                 ;(type-claim-for-accessor (translate-declaration-to-guard-gen type `(,accessor-fn ,stobj-name) t nil))
                 )
            ;; Scalar operations wrapped around array updates
            (append `((defthm ,(pack$ accessor-fn '-of- this-update-fn)
                        (equal (,accessor-fn (,this-update-fn i v ,stobj-name))
                               (,accessor-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-update-fn))))
                      (defthm ,(pack$ accessor-fn '-of- this-resize-fn)
                        (equal (,accessor-fn (,this-resize-fn i ,stobj-name))
                               (,accessor-fn ,stobj-name))
                        :hints (("Goal" :in-theory (enable ,accessor-fn ,this-resize-fn))))
                      ,@(and (< this-field-num other-field-num) ; bring inner writes outward since field number is lower
                             `((defthm ,(pack$ update-fn '-of- this-update-fn)
                                (equal (,update-fn v1 (,this-update-fn i v2 ,stobj-name))
                                       (,this-update-fn i v2 (,update-fn v1 ,stobj-name)))
                                :hints (("Goal" :in-theory (enable ,update-fn ,this-update-fn))))
                               (defthm ,(pack$ update-fn '-of- this-resize-fn)
                                 (equal (,update-fn v (,this-resize-fn i ,stobj-name))
                                        (,this-resize-fn i (,update-fn v ,stobj-name)))
                                :hints (("Goal" :in-theory (enable ,update-fn ,this-resize-fn)))))))
                    (interaction-theorems-for-array-field (rest all-field-infos) (+ 1 other-field-num) stobj-name renaming this-field-num this-update-fn this-resize-fn)))))))))

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

;; Returns (mv theorems names).
(defun theorems-for-defstobj-field (field-info field-num stobj-name top-recognizer renaming all-field-infos state)
  (declare (xargs :mode :program ;because of translate-declaration-to-guard-gen
                  :stobjs state))
  (let* ((name (if (consp field-info)
                   (car field-info)
                 ;; the entire arg is the field name:
                 field-info))
         (default-recognizer (pack$ name 'p)) ; same for all kinds of fields
         (recognizer (maybe-rename-symbol default-recognizer renaming))
         (keyword-value-list (if (consp field-info) (cdr field-info) nil))
         (type (assoc-keyword-with-default :type keyword-value-list t))
         (type-kind (if (consp type) (car type) type)))
    (cond
     ((eq 'array type-kind)
      (let* ((initial-value (assoc-keyword-with-default :initially keyword-value-list nil))
             (resizable (assoc-keyword-with-default :resizable keyword-value-list nil))
             (element-type (cadr type))
             (element-type-pred (type-spec-to-name element-type 'element-type))
             (nil-obviously-satisfies-element-typep (and (not (eq 'element-type element-type-pred))
                                                         (nil-satisfies-predp element-type-pred state)))
             ;; is (nth n l) here okay (not a variable)?
             (type-claim-for-nth-n-l (translate-declaration-to-guard-gen element-type '(nth n l) t nil))
             (default-length-fn (pack$ name '-length))
             (length-fn (maybe-rename-symbol default-length-fn renaming))
             (default-resize-fn (pack$ 'resize- name))
             (resize-fn (maybe-rename-symbol default-resize-fn renaming))
             (default-accessor-fn (pack$ name 'i))
             (accessor-fn (maybe-rename-symbol default-accessor-fn renaming))
             (default-update-fn (pack$ 'update- name 'i))
             (update-fn (maybe-rename-symbol default-update-fn renaming))
             ;; todo: suppress these if they are 't:
             (type-claim-for-default-value (translate-declaration-to-guard-gen element-type 'default-value t nil))
             (type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
             (type-claim-for-v (translate-declaration-to-guard-gen element-type 'v t nil))
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

              ;; Updating gives a well-formed stobj:
              (defthm ,(pack$ top-recognizer '-of- update-fn)
                (implies (and (,top-recognizer ,stobj-name)
                              (< i (,length-fn ,stobj-name))
                              (natp i)
                              ,type-claim-for-v)
                         (,top-recognizer (,update-fn i v ,stobj-name)))
                :hints (("Goal" :in-theory (enable ,top-recognizer ,update-fn ,length-fn))))

              ;; Updating an element doesn't affect the length:
              (defthm ,(pack$ length-fn '-of- update-fn)
                (implies (and (< i (,length-fn ,stobj-name))
                              (natp i))
                         (equal (,length-fn (,update-fn i v ,stobj-name))
                                (,length-fn ,stobj-name)))
                :hints (("Goal" :in-theory (enable ,length-fn ,update-fn))))

              (local
               (defthm ,(pack$ accessor-fn '-when-not-natp)
                 (implies (not (natp i))
                          (equal (,accessor-fn i ,stobj-name)
                                 (,accessor-fn 0 ,stobj-name)))
                 :hints (("Goal" :in-theory (enable ,accessor-fn)))))

              (local
               (defthm ,(pack$ update-fn '-when-not-natp)
                 (implies (not (natp i))
                          (equal (,update-fn i v ,stobj-name)
                                 (,update-fn 0 v ,stobj-name)))
                 :hints (("Goal" :in-theory (enable ,update-fn)))))

              ;; First read-over-write rule:
              (defthm ,(pack$ accessor-fn '-of- update-fn '-same)
                (equal (,accessor-fn i (,update-fn i v ,stobj-name))
                       v)
                :hints (("Goal" :in-theory (enable ,accessor-fn ,length-fn ,update-fn))))

              ;; Second read-over-write rule:
              (defthm ,(pack$ accessor-fn '-of- update-fn '-diff)
                (implies (not (equal (nfix i1) (nfix i2)))
                         (equal (,accessor-fn i1 (,update-fn i2 v ,stobj-name))
                                (,accessor-fn i1 ,stobj-name)))
                :hints (("Goal" :in-theory (enable ,accessor-fn ,length-fn ,update-fn))))

              ;; Third read-over-write rule.  Disabled, since it can cause case splits:
              (defthmd ,(pack$ accessor-fn '-of- update-fn '-split)
                (equal (,accessor-fn i1 (,update-fn i2 v ,stobj-name))
                       (if (equal (nfix i1) (nfix i2))
                           v
                         (,accessor-fn i1 ,stobj-name))))

              ;; First write-over-write rule:
              (defthm ,(pack$ update-fn '-of- update-fn '-same)
                (implies t;(natp i)
                         (equal (,update-fn i v1 (,update-fn i v2 ,stobj-name))
                                (,update-fn i v1 ,stobj-name)))
                :hints (("Goal" :in-theory (enable ,update-fn))))

              ;; Second write-over-write rule:
              (defthm ,(pack$ update-fn '-of- update-fn '-diff)
                (implies (and (syntaxp (not (term-order i1 i2))) ; i2 is a smaller term than i1
                              (not (equal (nfix i1) (nfix i2))))
                         (equal (,update-fn i1 v1 (,update-fn i2 v2 ,stobj-name))
                                (,update-fn i2 v2 (,update-fn i1 v1 ,stobj-name))))
                :hints (("Goal" :in-theory (enable ,update-fn))))

              ;; Third write-over-write rule:
              (defthm ,(pack$ update-fn '-of- update-fn '-split)
                (implies (syntaxp (not (term-order i1 i2))) ; i2 is a smaller term than i1
                         (equal (,update-fn i1 v1 (,update-fn i2 v2 ,stobj-name))
                                (if (equal (nfix i1) (nfix i2))
                                    (,update-fn i1 v1 ,stobj-name)
                                  (,update-fn i2 v2 (,update-fn i1 v1 ,stobj-name)))))
                :hints (("Goal" :in-theory (enable ,update-fn))))

              ;;  Fourth write-over-write rule (special case when the values are the same):
              (defthm ,(pack$ update-fn '-of- update-fn '-same-values)
                (implies (syntaxp (not (term-order i1 i2))) ; i2 is a smaller term than i1
                         (equal (,update-fn i1 v (,update-fn i2 v ,stobj-name))
                                (,update-fn i2 v (,update-fn i1 v ,stobj-name))))
                :hints (("Goal" :in-theory (enable ,update-fn))))

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
                                       ,type-claim-for-default-value)
                                  (,recognizer (resize-list lst n default-value)))
                         :hints (("Goal" :in-theory (enable resize-list ,recognizer)
                                  :induct (resize-list lst n default-value))))

                       ;; Resizing gives a well-formed stobj:
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
                         :hints (("Goal" :in-theory (enable ,accessor-fn ,resize-fn ,length-fn))))))
              ,@(interaction-theorems-for-array-field all-field-infos 0 stobj-name renaming field-num update-fn resize-fn)
              )
            ;; names:
            (list recognizer accessor-fn update-fn length-fn resize-fn))))
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
             (default-accessor-fn name)
             (accessor-fn (maybe-rename-symbol default-accessor-fn renaming))
             (default-update-fn (pack$ 'update- name))
             (update-fn (maybe-rename-symbol default-update-fn renaming))
             ;; todo: suppress these if they are 't:
             ;; (type-claim-for-val (translate-declaration-to-guard-gen element-type 'val t nil))
             (type-claim-for-v (translate-declaration-to-guard-gen type 'v t nil))
             (type-claim-for-accessor (translate-declaration-to-guard-gen type `(,accessor-fn ,stobj-name) t nil))
             )
        (mv `((defthm ,(pack$ top-recognizer '-of- update-fn)
                (implies (and (,top-recognizer ,stobj-name)
                              ,type-claim-for-v)
                         (,top-recognizer (,update-fn v ,stobj-name)))
                :hints (("Goal" :in-theory (enable ,top-recognizer ,update-fn))))

              ;; Read-over-write rule:
              ;; proof uses nth-update-nth, which is built in
              (defthm ,(pack$ accessor-fn '-of- update-fn)
                (equal (,accessor-fn (,update-fn v ,stobj-name))
                       v)
                :hints (("Goal" :in-theory (enable ,update-fn ,accessor-fn))))

              ;; Write-over-write rule:
              (defthm ,(pack$ update-fn '-of- update-fn)
                (equal (,update-fn v2 (,update-fn v1 ,stobj-name))
                       (,update-fn v2 ,stobj-name))
                :hints (("Goal" :in-theory (enable ,update-fn))))

              ,@(and (not (equal type t)) ; rewrite rule would be illegal
                     `((defthm ,(pack$ field-type-name '-of- accessor-fn)
                         (implies (,top-recognizer ,stobj-name)
                                  ,type-claim-for-accessor)
                         :hints (("Goal" :in-theory (enable ,top-recognizer ,accessor-fn))))))

              ,@(interaction-theorems-for-scalar-field all-field-infos 0 stobj-name renaming field-num update-fn)
              )
            (list recognizer accessor-fn update-fn)))))))

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
           (renaming (pairlis$ (strip-cars renaming) (strip-cadrs renaming)))
           (default-top-recognizer (pack$ stobj-name 'p))
           (default-creator (pack$ 'create- stobj-name))
           (top-recognizer (maybe-rename-symbol default-top-recognizer renaming))
           (creator (maybe-rename-symbol default-creator renaming)))
      (mv-let (theorems-for-fields names-for-fields) ; the names-for-fields include recgonizrers, accessors, updaters, etc.
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

           (defthm ,(pack$ top-recognizer '-of- creator)
             (,top-recognizer (,creator))
             :hints (("Goal" :in-theory (enable ,top-recognizer
                                                ,creator
                                                LENGTH
                                                len
                                                (:i nth))))))))))

(defmacro defstobj+ (name &rest args)
  `(make-event (defstobj+-fn ',name ',args state)))

; Tools for defining predicates that recognize arrays of typed values
;
; Copyright (C) 2019-2020 Kestrel Institute
; Copyright (C) 2019-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

;; A utility to define typed ACL2 arrays, where the type is expressed as a
;; predicate over the value and its index.

;; TODO: Consider what to do when the array's default value does / doesn't satisfy the pred (for all indices, if the index is mentioned?). Would like a theorem about make-empty-array.

(include-book "acl2-arrays")
(include-book "expandable-arrays")
(include-book "kestrel/utilities/pack" :dir :system)

(defthm not-<-of-if-of-<-same
  (not (< x (if (< x y) x y))))

(defun def-array-checker-fn (checker-fn pred extra-vars extra-guards)
  (declare (xargs :guard (and (symbolp checker-fn)
                              (symbol-listp extra-vars))))
  `(encapsulate ()

     (local (in-theory (disable assoc-keyword))) ;prevent inductions

     ;; Checks that the values at indices from index down to 0 are
     ;; correct.
     (defund ,checker-fn (array-name array index ,@extra-vars)
       (declare (xargs :measure (nfix (+ 1 index))
                       :hints (("Goal" :in-theory (enable natp)))
                       :guard (and (array1p array-name array)
                                   (integerp index)
                                   (< index (alen1 array-name array))
                                   ,@extra-guards)))
       (if (not (natp index))
           t
         (let ((val (aref1 array-name array index)))
           (and ,pred ;some check on val (may also mention index)
                (,checker-fn array-name array (+ -1 index) ,@extra-vars)))))

     ;; No values to check
     (defthm ,(pack$ checker-fn '-of-minus1)
       (,checker-fn array-name array -1 ,@extra-vars)
       :hints (("Goal" :in-theory (enable ,checker-fn))))

     ;; Only one value (at index 0) to check
     (defthm ,(pack$ checker-fn '-of-0)
       (equal (,checker-fn array-name array 0 ,@extra-vars)
              (let ((index 0))
                (let ((val (aref1 array-name array index)))
                  ,pred)))
       :hints (("Goal" :in-theory (enable ,checker-fn))))

     (defthm ,(pack$ checker-fn '-monotone)
       (implies (and (,checker-fn array-name array n ,@extra-vars)
                     (<= m n)
                     (integerp m)
                     (integerp n))
                (,checker-fn array-name array m ,@extra-vars))
       :hints (("Goal" :in-theory (enable ,checker-fn))))

     ;; todo: improve the name here:
     (defthm ,(pack$ 'type-of-aref1-when- checker-fn)
       (implies (and (,checker-fn array-name array top-index ,@extra-vars)
                     (<= index top-index)
                     (natp index)
                     (integerp top-index))
                (let ((val (aref1 array-name array index)))
                  ,pred))
       :hints (("Goal" :induct (,checker-fn array-name array top-index ,@extra-vars)
                :in-theory (enable ,checker-fn))))

     (defthm ,(pack$ checker-fn '-of-aset1-too-high)
       (implies (and (< index index2) ;index2 is above the part of the array we are checking
                     (< index2 (alen1 array-name array)) ;drop?
                     (array1p array-name array)
                     (integerp index)
                     (integerp index2))
                (equal (,checker-fn array-name (aset1 array-name array index2 val) index ,@extra-vars)
                       (,checker-fn array-name array index ,@extra-vars)))
       :hints (("Goal" :in-theory (enable ,checker-fn))))

     ;; todo: combine with the one below?
     ;; index2 can be above or below index, as long as the val being written is good
     (defthm ,(pack$ checker-fn '-of-aset1)
       (implies (and (,checker-fn array-name array index ,@extra-vars)
                     (let ((index index2)) (declare (ignorable index)) ,pred) ; constrains val
                     (< index (alen1 array-name array))
                     (< index2 (alen1 array-name array))
                     (array1p array-name array)
                     (integerp index)
                     (natp index2))
                (,checker-fn array-name (aset1 array-name array index2 val) index ,@extra-vars))
       :hints (("Goal" :induct (,checker-fn array-name array index ,@extra-vars)
                :expand ((:free (val) (,checker-fn array-name (aset1 array-name array index2 val) top-index ,@extra-vars)))
                :in-theory (enable ,checker-fn))))

     ;; Special case for extending the range of checked elements by 1
     (defthm ,(pack$ checker-fn '-of-aset1-at-end)
       (implies (and (,checker-fn array-name array (+ -1 index) ,@extra-vars) ;the item at index is being written
                     ,pred ;over index and val
                     (< index (alen1 array-name array))
                     (array1p array-name array)
                     (natp index))
                (,checker-fn array-name (aset1 array-name array index val) index ,@extra-vars))
       :hints (("Goal" :in-theory (enable ,checker-fn))))

     (defthm ,(pack$ checker-fn '-of-compress1)
       (implies (and (force (array1p array-name array))
                     (< index (alen1 array-name array)))
                (equal (,checker-fn array-name (compress1 array-name array) index ,@extra-vars)
                       (,checker-fn array-name array index ,@extra-vars)))
       :hints (("Goal" :do-not '(generalize eliminate-destructors)
                :in-theory (enable ,checker-fn))))

     (defthm ,(pack$ checker-fn '-of-cons-of-cons-of-header)
       (implies (and ;(force (array1p array-name array))
                     ;(< index (alen1 array-name array))
                     (,checker-fn array-name array index ,@extra-vars)
                     ;; default value must not change
                     (equal (default array-name array)
                            (cadr (assoc-keyword :default header-args))))
                (,checker-fn array-name (cons (cons :header header-args) array) index ,@extra-vars))
       :hints (("Goal" :do-not '(generalize eliminate-destructors)
                :in-theory (e/d (,checker-fn)
                                (aref1-of-cons-of-cons-of-header)))))

     (defthm ,(pack$ checker-fn '-of-cons-of-cons-of-header-irrel)
       (implies (and (natp index)
                     ;; default value must not change:
                     (equal (default array-name array)
                            (cadr (assoc-keyword :default header-args))))
                (equal (,checker-fn array-name (cons (cons :header header-args) array) index ,@extra-vars)
                       (,checker-fn array-name array index ,@extra-vars)))
       :hints (("Goal" :do-not '(generalize eliminate-destructors)
                :in-theory (e/d (,checker-fn)
                                (aref1-of-cons-of-cons-of-header)))))))

;; pred should be an expression over at most the vars INDEX and VAL and the EXTRA-VARS
(defmacro def-array-checker (fn pred &key
                                (extra-vars 'nil)
                                (extra-guards 'nil))
  (def-array-checker-fn fn pred extra-vars extra-guards))

;;;
;;; def-typed-acl2-array (this version takes an argument that specifies how many values to check, starting at index 0)
;;;

;; pred should be an expression over at most the vars INDEX and VAL and the EXTRA-VARS
(defun def-typed-acl2-array-fn (fn pred default default-satisfies-predp extra-vars extra-guards)
  (declare (xargs :guard (and (symbolp fn)
                              (booleanp default-satisfies-predp)
                              (symbol-listp extra-vars))))
  (let ((aux-fn (pack$ fn '-aux)))
    `(encapsulate ()

       ;; The -aux function
       (def-array-checker ,aux-fn ,pred :extra-vars ,extra-vars :extra-guards ,extra-guards)

       ,@(and default-satisfies-predp
              `((local
                 (defthm ensure-default-satisfies-pred
                   (implies (natp index) ;strengthen?
                            (let ((val ,default))
                              ,pred))
                   :rule-classes nil))

                ;; only works if the default works for all indices (see above)
                (defthm ,(pack$ aux-fn '-of-make-empty-array-with-default)
                  (implies (and (< index len)
                                (natp index)
                                (posp len)
                                (< len 2147483647)
                                (symbolp array-name))
                           (,aux-fn array-name (make-empty-array-with-default array-name len ,default) index ,@extra-vars))
                  :hints (("Goal" :in-theory (enable ,aux-fn))))))

       ;;
       ;; The main function
       ;;

       ;; Checks that the values at indices from (num-valid-nodes)-1 down to 0 are
       ;; correct.
       ;; We could have this constrain the default value of the array, but I'm
       ;; not sure we need to (maybe if the array is to be expanded?).
       (defund ,fn (array-name array num-valid-nodes ,@extra-vars)
         ,(if extra-guards
              `(declare (xargs :guard (and ,@extra-guards)))
            '(declare (xargs :guard t)))
         (and (array1p array-name array)
              (natp num-valid-nodes) ;allowing 0 lets us talk about empty arrays
              (<= num-valid-nodes (alen1 array-name array))
              (,aux-fn array-name array (+ -1 num-valid-nodes) ,@extra-vars)
              (equal (default array-name array) ,default) ; needed to support expandable arrays
              ))

       (defthm ,(pack$ 'array1p-when- fn)
         (implies (,fn array-name array num-valid-nodes ,@extra-vars)
                  (array1p array-name array))
         :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(pack$ fn '-forward-to-array1p)
         (implies (,fn array-name array num-valid-nodes ,@extra-vars)
                  (array1p array-name array))
         :rule-classes :forward-chaining
         :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(pack$ fn '-forward-to-len-bound fn)
         (implies (,fn array-name array num-valid-nodes ,@extra-vars)
                  (<= num-valid-nodes (alen1 array-name array)))
         :rule-classes :forward-chaining
         :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(pack$ fn '-forward-to-len-bound-2 fn)
         (implies (,fn array-name array num-valid-nodes ,@extra-vars)
                  (<= 0 (alen1 array-name array)))
         :rule-classes :forward-chaining
         :hints (("Goal" :in-theory (enable ,fn))))

       ;; todo: improve the name here:
       (defthm ,(pack$ 'type-of-aref1-when- fn)
         (implies (and (,fn array-name array num-valid-nodes ,@extra-vars)
                       (< index num-valid-nodes)
                       (natp index))
                  (let ((val (aref1 array-name array index)))
                    ,pred))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of-aref1-when- aux-fn)
                                         (top-index (+ -1 num-valid-nodes)))
                  :in-theory (e/d (,fn) (,(pack$ 'type-of-aref1-when- aux-fn))))))

       (defthm ,(pack$ fn '-monotone)
         (implies (and (,fn array-name array n ,@extra-vars)
                       (<= m n)
                       (natp m)
                       (integerp n) ;(natp n)
                       )
                  (,fn array-name array m ,@extra-vars))
         :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(pack$ fn '-of-aset1)
         (implies (and (,fn array-name array num-valid-nodes ,@extra-vars)
                       ,pred ;over index and val
                       (< index (alen1 array-name array))
                       (natp index))
                  (,fn array-name (aset1 array-name array index val) num-valid-nodes ,@extra-vars))
         :hints (("Goal" :in-theory (enable ,aux-fn ,fn))))

       (defthm ,(pack$ fn '-of-aset1-at-end)
         (implies (and (,fn array-name array index ,@extra-vars)
                       ,pred ;over index and val
                       (< index (alen1 array-name array))
                       (natp index))
                  (,fn array-name (aset1 array-name array index val) (+ 1 index) ,@extra-vars))
         :hints (("Goal" :in-theory (enable ,aux-fn ,fn))))

       ,@(and default-satisfies-predp
              `((defthm ,(pack$ fn '-of-make-empty-array-with-default)
                  (implies (symbolp array-name)
                           (equal (,fn array-name (make-empty-array-with-default array-name len ,default) len ,@extra-vars)
                                  (and (posp len)
                                       (<= len 2147483646))))
                  :hints (("Goal" :in-theory (enable ,fn))))))

       ,@(and default-satisfies-predp
              (equal default nil)
              `((defthm ,(pack$ fn '-of-make-empty-array)
                  (implies (symbolp array-name)
                           (equal (,fn array-name (make-empty-array array-name len) len ,@extra-vars)
                                  (and (posp len)
                                       (<= len 2147483646))))
                  :hints (("Goal" :in-theory (enable make-empty-array))))))

       ,@(and (equal default nil) ;since make-empty-array puts in nil
              ;; true even if the default does not satisfy the pred, because the 0
              ;; means no elements are checked
              `((defthm ,(pack$ fn '-of-make-empty-array-and-0)
                  (implies (and (posp len)
                                (symbolp array-name)
                                (<= len 2147483646))
                           (,fn array-name
                                (make-empty-array array-name len)
                                0
                                ,@extra-vars))
                  :hints (("Goal" :in-theory (enable ,fn make-empty-array)))))))))

;; pred should be an expression over at most the vars INDEX and VAL and the EXTRA-VARS
;; default-satisfies-predp indicates whether a value of NIL satisfies default-satisfies-predp.
(defmacro def-typed-acl2-array (fn pred &key
                                   (default 'nil)
                                   (default-satisfies-predp 't)
                                   (extra-vars 'nil)
                                   (extra-guards 'nil))
  (def-typed-acl2-array-fn fn pred default default-satisfies-predp extra-vars extra-guards))

;;;
;;; def-typed-acl2-array2 (this version checks every value up to index length-1)
;;;

;; pred should be an expression over at most the vars INDEX and VAL and the EXTRA-VARS
(defun def-typed-acl2-array2-fn (fn pred default default-satisfies-predp extra-vars extra-guards)
  (declare (xargs :guard (and (symbolp fn)
                              (booleanp default-satisfies-predp)
                              (symbol-listp extra-vars))))
  (let ((aux-fn (pack$ fn '-aux)))
    `(encapsulate ()

       ;; The -aux function
       (def-array-checker ,aux-fn ,pred :extra-vars ,extra-vars :extra-guards ,extra-guards)

       ,@(and default-satisfies-predp
              `((local
                 (defthm ensure-default-satisfies-pred
                   (implies (natp index) ;strengthen?
                            (let ((val ,default))
                              ,pred))
                   :rule-classes nil))

                ;;todo clash
                (local
                 (defthm <-of-if-arg1-alt
                  (equal (< x (if test tp ep))
                         (if test
                             (< x tp)
                           (< x ep)))))

                ;; only works if the default works for all indices (see above)
                (defthm ,(pack$ aux-fn '-of-make-empty-array-with-default)
                  (implies (and (< index len)
                                (natp index)
                                (posp len)
                                (< len 2147483647)
                                (symbolp array-name))
                           (,aux-fn array-name (make-empty-array-with-default array-name len ,default) index ,@extra-vars))
                  :hints (("Goal" :in-theory (enable ,aux-fn))))

                (defthm ,(pack$ aux-fn '-beyond-length)
                  (implies (and (,aux-fn array-name array (+ -1 (alen1 array-name array)) ,@extra-vars)
                                (array1p array-name array)
                                (natp index)
                                (equal ,default (default array-name array)))
                           (,aux-fn array-name array index ,@extra-vars))
                  :hints (("Goal" :induct (,aux-fn array-name array index ,@extra-vars)
                           :in-theory (enable ,aux-fn))
                          (and stable-under-simplificationp
                               '(:cases ((<= index (+ -1 (alen1 array-name array))))
                                        :use (:instance ,(pack$ 'type-of-aref1-when- aux-fn)
                                                        (top-index (+ -1 (ALEN1 ARRAY-NAME ARRAY))))
                                        :in-theory (e/d (aref1-when-too-large)
                                                        (,(pack$ 'type-of-aref1-when- aux-fn)))))))

                (defthm ,(pack$ aux-fn '-of-expand-array-helper)
                  (implies (and (<= (alen1 array-name array) index2) ;or we wouldn't be calling expand-array
                                (,aux-fn array-name array index ,@extra-vars)
                                (array1p array-name array)
                                (natp index)
                                (< index 2147483646)
                                (natp index2)
                                (< index2 2147483646)
                                (equal header-args (cdr (header array-name array)))
                                (equal current-length (alen1 array-name array))
                                (equal ,default (default array-name array)))
                           (,aux-fn array-name
                                    (expand-array array-name array header-args index2 current-length)
                                    index
                                    ,@extra-vars))
                  :hints (("Goal" :in-theory (e/d (,aux-fn expand-array
                                                           ;; default
                                                           ;; header
                                                           array1p-of-cons-when-header-and-expanding)
                                                  (alen1-of-expand-array
                                                   ;keyword-value-listp
                                                   ;;len
                                                   )))))

                (defthm ,(pack$ aux-fn '-of-expand-array)
                  (implies (and (<= (alen1 array-name array) index2) ;or we wouldn't be calling expand-array
                                (,aux-fn array-name array (+ -1 (alen1 array-name array)) ,@extra-vars)
                                (array1p array-name array)
                                (natp index2)
                                (< index2 2147483646)
                                (equal header-args (cdr (header array-name array)))
                                (equal current-length (alen1 array-name array))
                                (equal ,default (default array-name array)))
                           (,aux-fn array-name
                                    (expand-array array-name array header-args index2 current-length)
                                    (+ -1 (alen1 array-name (expand-array array-name array header-args index2 current-length)))
                                    ,@extra-vars))
                  :hints (("Goal" :in-theory (e/d (,aux-fn expand-array
                                                           ;; default
                                                           ;; header
                                                           array1p-of-cons-when-header-and-expanding)
                                                  (alen1-of-expand-array)))))))

       ;;
       ;; The main function
       ;;

       ;; Checks that the values at all valid indices satisfy the pred.
       ;; We could have this constrain the default value of the array, but I'm
       ;; not sure we need to (maybe if the array is to be expanded?).
       (defund ,fn (array-name array ,@extra-vars)
         ,(if extra-guards
              `(declare (xargs :guard (and ,@extra-guards)))
            '(declare (xargs :guard t)))
         (and (array1p array-name array)
              (,aux-fn array-name array (+ -1 (alen1 array-name array)) ,@extra-vars)
              (equal (default array-name array) ,default) ; needed to support expandable arrays
              ))

       (defthm ,(pack$ 'array1p-when- fn)
         (implies (,fn array-name array ,@extra-vars)
                  (array1p array-name array))
         :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(pack$ fn '-forward-to-<=-of-alen1)
         (implies (,fn array-name array ,@extra-vars)
                  (<= 0 (alen1 array-name array)))
         :rule-classes :forward-chaining
         :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(pack$ fn '-forward-to-array1p)
         (implies (,fn array-name array ,@extra-vars)
                  (array1p array-name array))
         :rule-classes :forward-chaining
         :hints (("Goal" :in-theory (enable ,fn))))

       ;; todo: improve the name here:
       (defthm ,(pack$ 'type-of-aref1-when- fn)
         (implies (and (,fn array-name array ,@extra-vars)
                       (< index (alen1 array-name array))
                       (natp index))
                  (let ((val (aref1 array-name array index)))
                    ,pred))
         :hints (("Goal" :use (:instance ,(pack$ 'type-of-aref1-when- aux-fn)
                                         (top-index (+ -1 (alen1 array-name array))))
                  :in-theory (e/d (,fn) (,(pack$ 'type-of-aref1-when- aux-fn))))))

       ;; (defthm ,(pack$ fn '-monotone)
       ;;   (implies (and (,fn array-name array n ,@extra-vars)
       ;;                 (<= m n)
       ;;                 (natp m)
       ;;                 (integerp n) ;(natp n)
       ;;                 )
       ;;            (,fn array-name array m ,@extra-vars))
       ;;   :hints (("Goal" :in-theory (enable ,fn))))

       (defthm ,(pack$ fn '-of-aset1)
         (implies (and (,fn array-name array ,@extra-vars)
                       ,pred ;over index and val
                       (< index (alen1 array-name array))
                       (natp index))
                  (,fn array-name (aset1 array-name array index val) ,@extra-vars))
         :hints (("Goal" :in-theory (enable ,aux-fn ,fn))))

       ;; (defthm ,(pack$ fn '-of-aset1-at-end)
       ;;   (implies (and (,fn array-name array index ,@extra-vars)
       ;;                 ,pred ;over index and val
       ;;                 (< index (alen1 array-name array))
       ;;                 (natp index))
       ;;            (,fn array-name (aset1 array-name array index val) (+ 1 index) ,@extra-vars))
       ;;   :hints (("Goal" :in-theory (enable ,aux-fn ,fn))))

       ,@(and default-satisfies-predp ;todo: think
              `((defthm ,(pack$ fn '-of-make-empty-array-with-default)
                  (implies (symbolp array-name)
                           (equal (,fn array-name (make-empty-array-with-default array-name len ,default) ,@extra-vars)
                                  (and (posp len)
                                       (<= len 2147483646))))
                  :hints (("Goal" :in-theory (enable ,fn))))

                (defthm ,(pack$ fn '-of-expand-array)
                  (implies (and (<= (alen1 array-name array) index) ;or we wouldn't be calling expand-array
                                (,fn array-name array ,@extra-vars)
                                (natp index)
                                (< index 2147483646)
                                (equal header-args (cdr (header array-name array)))
                                (equal current-length (alen1 array-name array)))
                           (,fn array-name (expand-array array-name array header-args index current-length) ,@extra-vars))
                  :hints (("Goal" :in-theory (enable ,fn))))

                (defthm ,(pack$ fn '-of-maybe-expand-array)
                  (implies (and (,fn array-name array ,@extra-vars)
                                (natp index)
                                (< index 2147483646))
                           (,fn array-name (maybe-expand-array array-name array index) ,@extra-vars))
                  :hints (("Goal" :in-theory (enable maybe-expand-array))))))

       ,@(and default-satisfies-predp ;todo: think
              (equal default nil)
              `((defthm ,(pack$ fn '-of-make-empty-array)
                  (implies (symbolp array-name)
                           (equal (,fn array-name (make-empty-array array-name len) ,@extra-vars)
                                  (and (posp len)
                                       (<= len 2147483646))))
                  :hints (("Goal" :in-theory (enable make-empty-array))))))

       ;; ;; true even if the default does not satisfy the pred, because the 0
       ;; ;; means no elements are checked
       ;; (defthm ,(pack$ fn '-of-make-empty-array-and-0)
       ;;   (implies (and (posp len)
       ;;                 (symbolp array-name)
       ;;                 (<= len 2147483646))
       ;;            (,fn array-name
       ;;                 (make-empty-array array-name len)
       ;;                 0
       ;;                 ,@extra-vars))
       ;;   :hints (("Goal" :in-theory (enable ,fn make-empty-array))))
       )))

;; PRED should be an expression over at most the vars INDEX and VAL and the
;; EXTRA-VARS.  DEFAULT-SATISFIES-PREDP indicates whether DEFAULT always
;; satisfies the PRED (for all values of the index and the EXTRA-VARS).  Note
;; that, for some preds (such as (equal index val)), there is no constant
;; default value that always satisfies the pred.
(defmacro def-typed-acl2-array2 (fn pred &key
                                    (default 'nil)
                                    (default-satisfies-predp 't)
                                    (extra-vars 'nil)
                                    (extra-guards 'nil))
  (def-typed-acl2-array2-fn fn pred default default-satisfies-predp extra-vars extra-guards))

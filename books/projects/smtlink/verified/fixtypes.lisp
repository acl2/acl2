;; Copyright (C) 2015, University of British Columbia
;; Written by Yan Peng (July 3rd 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2
;;

(in-package "SMT")
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "centaur/fty/top" :dir :system)
(include-book "misc/eval" :dir :system)
(include-book "smt-hint-table")

(defprod prod-function
  ((name symbolp)
   (return-type symbolp)
   (type-thm symbolp)
   (destructor-thm symbolp)))

(deflist prod-function-list
  :elt-type prod-function-p
  :true-listp t)

(defprod prodkeywords
  ((name symbolp)
   (constructor prod-function-p)
   (destructors prod-function-list-p)))

(define symbol-list-to-prod-function ((sym-lst symbol-listp))
  :returns (prod prod-function-p)
  (b* ((sym-lst (symbol-list-fix sym-lst))
       ((unless (and (>= (len sym-lst) 1)
                     (<= (len sym-lst) 4)))
        (prog2$ (er hard? 'fixtypes=>symbol-list-to-prod-function
                    "~p0 is not of the right format. It needs to be a
                     symbol-list with 1-4 elements.~%" sym-lst)
                (make-prod-function)))
       ((list name type type-thm destructor-thm) sym-lst))
    (make-prod-function :name name
                        :return-type type
                        :type-thm type-thm
                        :destructor-thm destructor-thm)))

(define symbol-list-list-to-prod-function-list ((sym-lst-lst
                                                 symbol-list-listp))
  :returns (prod-lst prod-function-list-p)
  :measure (len sym-lst-lst)
  (b* ((sym-lst-lst (symbol-list-list-fix sym-lst-lst))
       ((unless (consp sym-lst-lst)) nil)
       ((cons first rest) sym-lst-lst))
    (cons (symbol-list-to-prod-function first)
          (symbol-list-list-to-prod-function-list rest))))

(define symbols-to-prodkeywords ((name symbolp)
                                 (constructor symbol-listp)
                                 (destructors symbol-list-listp))
  :returns (p prodkeywords-p)
  (b* ((name (symbol-fix name))
       (constructor (symbol-list-fix constructor))
       (destructors (symbol-list-list-fix destructors))
       (structured-constructor
        (symbol-list-to-prod-function constructor))
       (structured-destructors
        (symbol-list-list-to-prod-function-list destructors)))
    (prodkeywords name structured-constructor structured-destructors)))

(deflist prodkeywords-list
  :elt-type prodkeywords-p
  :true-listp t)

(defprod sumkeywords
  ((name symbolp)
   (rec symbolp)
   (fix symbolp)
   (fix-thm symbolp)
   (kind-fn symbolp)
   (basicp symbolp)
   (prods prodkeywords-list-p)))

(defprod arraykeywords
  ((name symbolp)
   (rec symbolp)
   (fix symbolp)
   (fix-thm symbolp)
   (basicp symbolp)
   (k symbolp)
   (store symbolp)
   (select symbolp)
   (key-type symbolp)
   (val-type symbolp)
   (array-thm symbolp)))

(defprod abstractkeywords
  ((name symbolp)
   (rec symbolp)
   (fix symbolp)
   (fix-thm symbolp)
   (basicp symbolp)))

(define def-destructors ((destructors prod-function-list-p))
  :returns (fn-lst type-function-list-p)
  :measure (len destructors)
  (b* ((destructors (prod-function-list-fix destructors))
       ((unless (consp destructors)) nil)
       ((cons first rest) destructors)
       ((prod-function f) first))
    (cons (make-type-function :name f.name
                              :return-type f.return-type
                              :type-of-function-thm
                              (make-type-thm :name f.type-thm)
                              :destructor-of-constructor-thm
                              (make-type-thm :name f.destructor-thm))
          (def-destructors rest))))

(define def-prod ((prod prodkeywords-p))
  :returns (p prod-p)
  (b* ((prod (prodkeywords-fix prod))
       ((prodkeywords p) prod)
       ((prod-function f) p.constructor)
       (constructor (make-type-function :name f.name
                                        :return-type f.return-type
                                        :type-of-function-thm
                                        (make-type-thm :name f.type-thm)))
       (destructors (def-destructors p.destructors)))
    (make-prod :kind p.name
               :constructor constructor
               :destructors destructors)))

(define def-prod-list ((prod-lst prodkeywords-list-p))
  :returns (pd-lst prod-list-p)
  :measure (len prod-lst)
  :hints (("Goal"
           :in-theory (enable prodkeywords-list-fix)))
  (b* ((prod-lst (prodkeywords-list-fix prod-lst))
       ((unless (consp prod-lst)) nil)
       ((cons first rest) prod-lst))
    (cons (def-prod first)
          (def-prod-list rest))))

(define def-sum-kind ((kind-fn symbolp)
                      (prod-lst prodkeywords-list-p))
  :returns (sum smt-type-p)
  (b* ((kind-fn (symbol-fix kind-fn))
       (prod-lst (prodkeywords-list-fix prod-lst)))
    (make-smt-type-sum :kind-fn kind-fn
                       :prods (def-prod-list prod-lst))))

(define def-sum-fixtype ((keywords sumkeywords-p))
  (b* ((keywords (sumkeywords-fix keywords))
       ((sumkeywords s) keywords)
       (fix-thm
        `(type-thm ',s.fix-thm
                   '(:expand ((,s.rec x) (,s.fix x))
                             :in-theory (disable ,s.rec ,s.fix))
                   ))
       (type-event
        `(smt-fixtype ',s.name ',s.rec ',s.fix ,fix-thm ',s.basicp
                      (def-sum-kind ',s.kind-fn ',s.prods)))
       (update-table
        `((add-type :default ,type-event (w state)))))
    `(with-output
       (progn ,@update-table))))

(defmacro defsmtlist (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil)
                           (basicp 'nil) (cons 'nil) (car 'nil) (cdr 'nil)
                           (nil-fn 'nil) (elt-type 'nil) (type-of-nil 'nil)
                           (type-of-cons 'nil) (type-of-car 'nil)
                           (car-of-cons 'nil) (type-of-cdr 'nil)
                           (cdr-of-cons 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp)
                              (symbolp cons)
                              (symbolp car)
                              (symbolp cdr)
                              (symbolp nil-fn)
                              (symbolp elt-type)
                              (symbolp type-of-nil)
                              (symbolp type-of-cons)
                              (symbolp type-of-car)
                              (symbolp car-of-cons)
                              (symbolp type-of-cdr)
                              (symbolp cdr-of-cons))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)
                  (null ',cons) (null ',car) (null ',cdr) (null ',nil-fn)
                  (null ',elt-type)))
          (er hard? 'fixtypes=>defsmtlist "Mandatory Keywords for defsmtlist are :rec,
  :fix, :fix-thm, :basicp, :cons, :car, :cdr, :nil-fn and :elt-type. ~%Optional
                           keywords for defsmtlist are :type-of-nil,
                           :type-of-cons, :type-of-car, :car-of-cons,
                           :type-of-cdr, :cdr-of-cons.~%"))
         (cons-prod (symbols-to-prodkeywords
                     'cons
                     (list ',cons ',rec ',type-of-cons nil)
                     (list (list ',car ',elt-type ',type-of-car ',car-of-cons)
                           (list ',cdr ',rec ',type-of-cdr ',cdr-of-cons))))
         (nil-prod (symbols-to-prodkeywords
                    'nil-kind
                    (list ',nil-fn ',rec ',type-of-nil nil)
                    nil)))
    (def-sum-fixtype (sumkeywords ',name ',rec ',fix ',fix-thm nil ',basicp
                                  (list cons-prod nil-prod))))))

;; this is a test
(must-succeed
(defsmtlist int-list
  :rec int-list-p
  :fix int-list-fix
  :fix-thm int-list-fix-when-int-list-p
  :cons int-list-cons
  :car int-list-car
  :cdr int-list-cdr
  :nil-fn int-list-nil
  :elt-type integerp
  )
)

(defmacro defsmtprod (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil) (basicp 'nil)
                           (constructor 'nil) (destructors 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp)
                              (symbol-listp constructor)
                              (symbol-list-listp destructors))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)
                  (null ',constructor) (null ',destructors)))
          (er hard? 'fixtypes=>defsmtprod "Mandatory Keywords for defsmtprod are :rec,
  :fix, :fix-thm, :basicp, :constructor and :destructors. ~%"))
         (prod-list
          (symbols-to-prodkeywords ',name ',constructor ',destructors)))
      (def-sum-fixtype (sumkeywords ',name ',rec ',fix ',fix-thm nil ',basicp
                                    (list prod-list))))))

;; this is a test
(must-succeed
 (defsmtprod animal
   :rec animal-p
   :fix animal-fix
   :fix-thm animal-fix-when-animal-p
   :constructor (animal animal-p)
   :destructors ((body body-p) (legs leg-list-p))
   )
 )

(defmacro defsmtoption (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil) (basicp 'nil)
                             (some-constructor 'nil) (some-destructor 'nil)
                             (none-constructor 'nil) (some-type 'nil)
                             (type-of-none 'nil) (type-of-some 'nil)
                             (type-of-destructor 'nil) (destructor-of-some 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp)
                              (symbolp some-constructor)
                              (symbolp some-destructor)
                              (symbolp none-constructor)
                              (symbolp some-type)
                              (symbolp type-of-none)
                              (symbolp type-of-some)
                              (symbolp type-of-destructor)
                              (symbolp destructor-of-some))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)
                  (null ',some-constructor) (null ',some-destructor)
                  (null ',none-constructor) (null ',some-type)))
          (er hard? 'fixtypes=>defsmtoption "Mandatory keywords for defsmtprod are :rec,
  :fix, :fix-thm, :basicp, :some-constructor, :some-destructor,
                             :none-constructor and :some-type.~% Optional
                             keywords are :type-of-none, :type-of-some,
                             :type-of-destructor, and :destructor-of-some.~%"))
         (some-prod
          (symbols-to-prodkeywords
           'some
           (list ',some-constructor ',rec ',type-of-some nil)
           (list (list ',some-destructor ',some-type ',type-of-destructor
                       ',destructor-of-some))))
         (none-prod (symbols-to-prodkeywords
                     'none
                     (list ',none-constructor ',rec ',type-of-none nil)
                     nil)))
      (def-sum-fixtype (sumkeywords ',name ',rec ',fix ',fix-thm nil ',basicp
                                    (list some-prod none-prod))))))

;; this is a test
(must-succeed
 (defsmtoption maybe-int
   :rec maybe-int-p
   :fix maybe-int-fix
   :fix-thm maybe-int-fix-when-maybe-int-p
   :some-constructor maybe-int-some
   :some-destructor maybe-int-some->val
   :none-constructor maybe-int-none
   :some-type integerp
   )
 )

(define input-prods-to-keywords ((prods))
  :returns (pl prodkeywords-list-p)
  (b* (((unless (consp prods)) nil)
       ((cons first rest) prods)
       ((unless (equal (len first) 5))
        (input-prods-to-keywords rest))
       ((list name & constructor & destructors) first)
       ((unless (and (symbolp name)
                     (symbol-listp constructor)
                     (symbol-list-listp destructors)))
        (input-prods-to-keywords rest)))
    (cons (symbols-to-prodkeywords name constructor destructors)
          (input-prods-to-keywords rest))))

(defmacro defsmtsum (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil)
                          (kind-function 'nil) (basicp 'nil) (prods 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp kind-function)
                              (symbolp basicp))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm) (null ',kind-function)))
          (er hard? 'fixtypes=>defsmtsum "Keywords for defsmtsum are :rec,
  :fix, :fix-thm, :kind-function, :basicp and :prods.~%"))
         (prodkeyword-lst (input-prods-to-keywords ',prods)))
      (def-sum-fixtype (sumkeywords ',name ',rec ',fix ',fix-thm
                                    ',kind-function ',basicp
                                    prodkeyword-lst)))))

(must-succeed
 (defsmtsum arithtm
   :rec arithtm-p
   :fix arithtm-fix
   :fix-thm arithtm-fix-when-arithtm-p
   :kind-function arithtm-kind
   :prods ((:num :constructor (arithtm-num arithtm-p)
                 :destructors ((val integerp)))
           (:plus :constructor (arithtm-plus arithtm-p)
                  :destructors ((left arithtm-p)
                                (right arithtm-p)))
           (:minus :constructor (arithtm-minus arithtm-p)
                   :destructors ((arg arithtm-p))))
   )
 )

(define def-array-fixtype ((keywords arraykeywords-p))
  (b* ((keywords (arraykeywords-fix keywords))
       ((arraykeywords a) keywords)
       (fix-thm
        `(type-thm ',a.fix-thm
                   '(:expand ((,a.rec x) (,a.fix x))
                             :in-theory (disable ,a.rec ,a.fix))))
       (store-fn (make-type-function :name a.store))
       (select-fn (make-type-function :name a.select))
       (k (make-type-function :name a.k))
       (array-kind (make-smt-type-array :store store-fn
                                        :select select-fn
                                        :k k
                                        :key-type a.key-type
                                        :val-type a.val-type
                                        :array-thm (make-type-thm :name a.array-thm)))
       (type-event
        `(smt-fixtype ',a.name ',a.rec ',a.fix ,fix-thm ',a.basicp
                      ',array-kind))
       (update-table
        `((add-type :default ,type-event (w state)))))
    `(with-output
       (progn ,@update-table))))

(defmacro defsmtarray (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil) (basicp 'nil)
                            (store 'nil) (select 'nil) (k 'nil) (key-type 'nil)
                            (val-type 'nil) (array-thm 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp)
                              (symbolp k)
                              (symbolp store)
                              (symbolp select)
                              (symbolp key-type)
                              (symbolp val-type)
                              (symbolp array-thm))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm) (null ',k)
                  (null ',store) (null ',select) (null ',key-type) (null ',val-type)))
          (er hard? 'fixtypes=>defsmtarray "Keywords for defsmtsum are :rec,
  :fix, :fix-thm, :basicp, :k, :store, :select, :key-type, :val-type and :array-thm.~%")))
      (def-array-fixtype (arraykeywords ',name ',rec ',fix ',fix-thm ',basicp
                                        ',k ',store ',select ',key-type
                                        ',val-type ',array-thm)))))

(must-succeed
 (defsmtarray int-int-array
   :rec int-int-array-p
   :fix int-int-array-fix
   :fix-thm int-int-array-fix-when-int-int-array-p
   :k k
   :store int-int-array-store
   :select int-int-array-select
   :key-type integerp
   :val-type integerp
   )
 )

(define def-abstract-fixtype ((keywords abstractkeywords-p))
  (b* ((keywords (abstractkeywords-fix keywords))
       ((abstractkeywords a) keywords)
       (fix-thm
        `(type-thm ',a.fix-thm
                   '(:expand ((,a.rec x) (,a.fix x))
                             :in-theory (disable ,a.rec ,a.fix))))
       (type-event
        `(smt-fixtype ',a.name ',a.rec ',a.fix ,fix-thm ',a.basicp
                      (make-smt-type-abstract)))
       (update-table
        `((add-type :default ,type-event (w state)))))
    `(with-output
       (progn ,@update-table))))

(defmacro defsmtabstract (name &key (rec 'nil) (fix 'nil) (fix-thm 'nil)
                               (basicp 'nil))
  (declare (xargs :guard (and (symbolp name)
                              (symbolp rec)
                              (symbolp fix)
                              (symbolp fix-thm)
                              (symbolp basicp))))
  `(make-event
    (b* (((if (or (null ',rec) (null ',fix) (null ',fix-thm)))
          (er hard? 'fixtypes=>defsmtabstract "Keywords for defsmtabstract are :rec,
  :fix, :fix-thm and :basicp.~%")))
      (def-abstract-fixtype (abstractkeywords ',name ',rec ',fix ',fix-thm ',basicp)))))

(must-succeed
 (defsmtabstract abstract
   :rec abstract-p
   :fix abstract-fix
   :fix-thm abstract-fix-when-abstract-p
   )
 )

;; ------------------------------------------------------
;; When certifying this book, several basic types are put into the
;; smt-hint-table :default smtlink-hint

(defthm ifix-when-integerp
  (implies (integerp x)
           (equal (ifix x) x)))
(defsmtabstract integer
  :rec integerp
  :fix ifix
  :fix-thm ifix-when-integerp
  :basicp t)

(defthm bool-fix$inline-when-booleanp
  (implies (booleanp x)
           (equal (bool-fix$inline x) x)))
(defsmtabstract boolean
  :rec booleanp
  :fix bool-fix$inline
  :fix-thm bool-fix$inline-when-booleanp
  :basicp t)

(defthm symbol-fix-when-symbolp
  (implies (symbolp x)
           (equal (symbol-fix x) x)))
(defsmtabstract symbol
  :rec symbolp
  :fix symbol-fix
  :fix-thm symbol-fix-when-symbolp
  :basicp t)

(defthm rfix-when-rationalp
  (implies (rationalp x)
           (equal (rfix x) x)))
(defsmtabstract rational
  :rec rationalp
  :fix rfix
  :fix-thm rfix-when-rationalp
  :basicp t)

(defthm realfix-when-real/rationalp
  (implies (real/rationalp x)
           (equal (realfix x) x)))
(defsmtabstract real
  :rec realp
  :fix realfix
  :fix-thm realfix-when-realp
  :basicp t)
(defsmtabstract real/rational
  :rec real/rationalp
  :fix realfix
  :fix-thm realfix-when-real/rationalp
  :basicp t)

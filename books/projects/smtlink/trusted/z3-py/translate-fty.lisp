;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (23rd May, 2018)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "../../verified/hint-interface")
(include-book "../../verified/basics")
(include-book "./datatypes")

(local (in-theory (enable string-or-symbol-p)))

(define translate-symbol ((sym symbolp) (nil-type symbolp))
  :returns (translated paragraphp
                       :hints (("Goal" :in-theory (enable paragraphp wordp))))
  (cond
   ;; Boolean: nil
   ((and (equal sym 'nil)
         (equal nil-type nil))
    (list "False"))
   ;; A fty nil
   ((equal sym 'nil)
    (list (concatenate 'string (lisp-to-python-names nil-type) ".nil")))
   ;; Boolean: t
   ((equal sym 't) (list "True"))
   ;; A variable
   (t (list (lisp-to-python-names sym)))))

(define translate-symbol-lst ((formals symbol-listp))
  :returns (translated paragraphp
                       :hints (("Goal" :in-theory (enable translate-symbol
                                                          paragraphp))))
  :measure (len formals)
  (b* ((formals (symbol-list-fix formals))
       ((unless (consp (cdr formals)))
        (list (translate-symbol (car formals) nil)))
       ((cons first rest) formals)
       (translated-name (translate-symbol first nil)))
    (cons translated-name `(#\, #\Space ,@(translate-symbol-lst rest)))))

(define translate-type ((type symbolp)
                        (int-to-rat booleanp)
                        (flag symbolp))
  :returns (translated stringp)
  (b* ((type (symbol-fix type))
       (item (cond ((equal flag 'uninterpreted)
                    (assoc-equal type *SMT-uninterpreted-types*))
                   ((and (equal type 'integerp) int-to-rat)
                    (assoc-equal 'rationalp *SMT-types*))
                   (t (assoc-equal type *SMT-types*))))
       ((unless (endp item)) (cdr item)))
    (lisp-to-python-names type)))

(define translate-fty-field-lst ((fields fty-field-alist-p)
                                 (int-to-rat booleanp))
  :returns (translated paragraphp
                       :hints (("Goal" :in-theory (enable translate-type
                                                          translate-symbol
                                                          paragraphp))))
  :measure (len fields)
  :hints (("Goal" :in-theory (e/d (fty-field-alist-fix) ())))
  (b* ((fields (fty-field-alist-fix fields))
       ((unless (consp fields)) nil)
       ((cons first rest) fields)
       (name (translate-symbol (car first) nil))
       (type (translate-type (cdr first) int-to-rat nil))
       (translated-field `(", ('" ,name "', " ,type ")")))
    (cons translated-field
          (translate-fty-field-lst rest int-to-rat))))

(define translate-fty-prod ((name symbolp)
                            (fields fty-field-alist-p)
                            (int-to-rat booleanp))
  :returns (translated paragraphp
                       :hints (("Goal"
                                :in-theory (enable paragraphp wordp))))
  (b* ((name (symbol-fix name))
       (name (translate-symbol name nil))
       (datatype-line `(,name "= Datatype" #\( #\' #\" ,name #\' #\) #\Newline))
       (translated-fields (translate-fty-field-lst fields int-to-rat))
       (fields-line `(,name ".declare('" ,name "'" ,@translated-fields ")"
                            #\Newline)))
    `(,datatype-line
      ,fields-line)))

(define translate-fty-prod-lst ((prod-lst fty-prod-alist-p)
                                (int-to-rat booleanp))
  :returns (translated paragraphp)
  :measure (len prod-lst)
  :hints (("Goal" :in-theory (e/d (fty-prod-alist-fix) ())))
  (b* ((prod-lst (fty-prod-alist-fix prod-lst))
       ((unless (consp prod-lst)) nil)
       ((cons first rest) prod-lst))
    (cons (translate-fty-prod (car first) (cdr first) int-to-rat)
          (translate-fty-prod-lst rest int-to-rat))))

(define translate-fty-option ((name symbolp)
                              (some-type symbolp)
                              (int-to-rat booleanp))
  :returns (translated paragraphp
                       :hints (("Goal"
                                :in-theory (enable paragraphp wordp))))
  (b* ((name (symbol-fix name))
       (name (translate-symbol name nil))
       (datatype-line
        `(,name "= Datatype" #\( #\' #\" ,name #\' #\) #\Newline))
       (translated-type (translate-type some-type int-to-rat nil))
       (declare-line1
        `(,name ".declare('some', ('val', " ,translated-type "))" #\Newline))
       (declare-line2
        `(,name ".declare('nil')" #\Newline)))
    `(,datatype-line
      ,declare-line1
      ,declare-line2)))

(define translate-fty-option-lst ((option-lst fty-option-alist-p)
                                  (int-to-rat booleanp))
  :returns (translated paragraphp)
  :measure (len option-lst)
  :hints (("Goal" :in-theory (e/d (fty-option-alist-fix) ())))
  (b* ((option-lst (fty-option-alist-fix option-lst))
       ((unless (consp option-lst)) nil)
       ((cons first rest) option-lst))
    (cons (translate-fty-option (car first) (cdr first) int-to-rat)
          (translate-fty-option-lst rest int-to-rat))))

(define translate-fty-list ((name symbolp)
                            (elt-type symbolp)
                            (int-to-rat booleanp))
  :returns (translated paragraphp
                       :hints (("Goal"
                                :in-theory (enable paragraphp wordp))))
  (b* ((name (symbol-fix name))
       (name (translate-symbol name nil))
       (datatype-line
        `(,name "= Datatype" #\( #\' #\" ,name #\' #\) #\Newline))
       (translated-elt-type (translate-type elt-type int-to-rat nil))
       (declare-line1
        `(,name ".declare('cons', ('car', " ,translated-elt-type "), "
                "('cdr', " ,name "))" #\Newline))
       (declare-line2
        `(,name ".declare('nil')" #\Newline)))
    `(,datatype-line
      ,declare-line1
      ,declare-line2)))

(define translate-fty-list-lst ((list-lst fty-list-alist-p)
                                (int-to-rat booleanp))
  :returns (translated paragraphp)
  :measure (len list-lst)
  :hints (("Goal" :in-theory (e/d (fty-list-alist-fix) ())))
  (b* ((list-lst (fty-list-alist-fix list-lst))
       ((unless (consp list-lst)) nil)
       ((cons first rest) list-lst))
    (cons (translate-fty-option (car first) (cdr first) int-to-rat)
          (translate-fty-list-lst rest int-to-rat))))

(define translate-fty-alist-assoc-return ((key-type symbolp)
                                          (val-type symbolp)
                                          (assoc-return paragraphp)
                                          (int-to-rat booleanp))
  :returns (translated paragraphp
                       :hints (("Goal"
                                :in-theory (enable paragraphp wordp))))
  (b* ((key-type (symbol-fix key-type))
       (key-type (translate-type key-type int-to-rat nil))
       (val-type (symbol-fix val-type))
       (val-type (translate-type val-type int-to-rat nil))
       (assoc-return (paragraph-fix assoc-return))
       (datatype-line `(,assoc-return "= Datatype('" ,assoc-return "')"
                                          #\Newline))
       (declare-line1 `(,assoc-return ".declare('cons', ('car', " ,key-type
                                      "), ('cdr', " ,val-type "))" #\Newline))
       (declare-line2 `(,assoc-return ".declare('nil')" #\Newline))
       )
    `(,@datatype-line
      ,@declare-line1
      ,@declare-line2)))

(define translate-fty-alist-acons ((name symbolp))
  :returns (translated paragraphp
                       :hints (("Goal"
                                :in-theory (enable paragraphp wordp))))
  (b* ((name (symbol-fix name))
       (name (translate-symbol name nil))
       (fn-name `(,name "_acons")))
    `("def " ,fn-name "(key, value, alist): return Store(alist, key, value)")))

(define translate-fty-alist-assoc ((name symbolp)
                                   (maybe-val symbolp)
                                   (assoc-return paragraphp))
  :returns (translated paragraphp
                       :hints (("Goal"
                                :in-theory (enable paragraphp wordp))))
  (b* ((name (symbol-fix name))
       (name (translate-symbol name nil))
       (maybe-val (symbol-fix maybe-val))
       (maybe-val (translate-symbol maybe-val nil))
       (assoc-return (paragraph-fix assoc-return))
       (fn-name `(,name "_assoc")))
    `("def " ,fn-name "(key, alist): return If(Select(alist, key) == "
                                   ,maybe-val ".nil, " ,assoc-return ".nil, "
                                   ,assoc-return ".cons(key, " ,maybe-val
                                   ".val(Select(alist, key))))")))

(define translate-fty-alist-type ((key-type symbolp)
                                  (val-type symbolp)
                                  (maybe-val symbolp)
                                  (int-to-rat booleanp))
  :returns (translated paragraphp
                       :hints (("Goal"
                                :in-theory (enable paragraphp wordp))))
  (b* ((key-type (symbol-fix key-type))
       (key-type (translate-type key-type int-to-rat nil))
       (val-type (symbol-fix val-type))
       (val-type (translate-type val-type int-to-rat nil))
       (maybe-val (symbol-fix maybe-val))
       (fn-name `(,key-type "_" ,val-type "_alist")))
    `("def " ,fn-name "(): return ArraySort(" ,key-type ", " ,maybe-val ")")))

(define translate-fty-alist ((name symbolp)
                             (alist-pair fty-alist-p)
                             (int-to-rat booleanp))
  :returns (translated paragraphp
                       :hints (("Goal"
                                :in-theory (enable paragraphp wordp))))
  :guard-hints (("Goal" :in-theory (e/d (paragraphp wordp) ())))
  :guard-debug t
  (b* ((name (symbol-fix name))
       (alist-pair (fty-alist-fix alist-pair))
       (key-type (fty-alist->key-type alist-pair))
       (val-type (fty-alist->val-type alist-pair))
       (val-type-pkg (symbol-package-name val-type))
       (val-type-str (translate-type val-type int-to-rat nil))
       (maybe-val-str (concatenate 'string "maybe_" val-type-str))
       (maybe-val (intern$ maybe-val-str val-type-pkg))
       (maybe-val-type
        (translate-fty-option maybe-val val-type int-to-rat))
       (assoc-return `(,key-type "_" ,val-type))
       (assoc-return-type
        (translate-fty-alist-assoc-return key-type val-type assoc-return
                             int-to-rat))
       (acons-fn (translate-fty-alist-acons name))
       (assoc-fn
        (translate-fty-alist-assoc name maybe-val assoc-return))
       (alist-fn
        (translate-fty-alist-type key-type val-type maybe-val int-to-rat))
       )
    `(,maybe-val-type
      ,assoc-return-type
      ,acons-fn
      ,assoc-fn
      ,alist-fn)))

(define translate-fty-alist-lst ((alist-lst fty-alist-alist-p)
                                 (int-to-rat booleanp))
  :returns (translated paragraphp)
  :measure (len alist-lst)
  :hints (("Goal" :in-theory (e/d (fty-alist-alist-fix) ())))
  (b* ((alist-lst (fty-alist-alist-fix alist-lst))
       ((unless (consp alist-lst)) nil)
       ((cons first rest) alist-lst))
    (cons (translate-fty-alist (car first) (cdr first) int-to-rat)
          (translate-fty-alist-lst rest int-to-rat))))

(local
 (defthm symbol-listp-of-strip-cars-fty-prod-alist-p
   (implies (fty-prod-alist-p prod)
            (symbol-listp (strip-cars prod))))
 )

(local
 (defthm symbol-listp-of-strip-cars-fty-option-alist-p
   (implies (fty-option-alist-p option)
            (symbol-listp (strip-cars option))))
 )

(local
 (defthm symbol-listp-of-strip-cars-fty-list-alist-p
   (implies (fty-list-alist-p list)
            (symbol-listp (strip-cars list))))
 )

(local
 (defthm symbol-listp-of-strip-cars-fty-alist-alist-p
   (implies (fty-alist-alist-p alist)
            (symbol-listp (strip-cars alist))))
 )

(local
 (defthm member-of-fty-types-p
   (implies (fty-types-p f)
            (and (fty-prod-alist-p (fty-types->prod f))
                 (fty-option-alist-p (fty-types->option f))
                 (fty-list-alist-p (fty-types->list f))
                 (fty-alist-alist-p (fty-types->alist f))))))

(local
 (defthm symbol-listp-of-append
   (implies (and (symbol-listp a)
                 (symbol-listp b))
            (symbol-listp (append a b))))
 )

(define translate-fty-types ((fty-types fty-types-p)
                             (int-to-rat booleanp))
  :returns (translated paragraphp)
  :guard-hints (("Goal"
                 :in-theory (e/d ()
                                 (symbol-listp-of-strip-cars-fty-prod-alist-p
                                  symbol-listp-of-strip-cars-fty-option-alist-p
                                  symbol-listp-of-strip-cars-fty-list-alist-p
                                  symbol-listp-of-strip-cars-fty-alist-alist-p
                                  member-of-fty-types-p
                                  ))
                 :use ((:instance symbol-listp-of-strip-cars-fty-prod-alist-p
                                  (prod (fty-types->prod fty-types)))
                       (:instance symbol-listp-of-strip-cars-fty-option-alist-p
                                  (option (fty-types->option fty-types)))
                       (:instance symbol-listp-of-strip-cars-fty-list-alist-p
                                  (list (fty-types->list fty-types)))
                       (:instance symbol-listp-of-strip-cars-fty-alist-alist-p
                                  (alist (fty-types->alist fty-types)))
                       (:instance member-of-fty-types-p
                                  (f fty-types)))
                 ))
  (b* ((fty-types (fty-types-fix fty-types))
       ((fty-types f) fty-types)
       (prod (translate-fty-prod-lst f.prod int-to-rat))
       (prod-names (strip-cars f.prod))
       (option (translate-fty-option-lst f.option int-to-rat))
       (option-names (strip-cars f.option))
       (list (translate-fty-list-lst f.list int-to-rat))
       (list-names (strip-cars f.list))
       (alist (translate-fty-alist-lst f.alist int-to-rat))
       (alist-names (strip-cars f.alist))
       (symbol-lst `(,@prod-names ,@option-names ,@list-names ,@alist-names))
       (translated-symbol-lst (translate-symbol-lst symbol-lst))
       (create `(,@translated-symbol-lst "= CreateDatatypes"
                                         #\( ,@translated-symbol-lst #\)
                                         #\Newline)))
    `(,@prod ,@option ,@list ,@alist ,@create)))

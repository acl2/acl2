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
       ((unless (consp formals)) nil)
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
  :returns (mv (translated paragraphp
                           :hints (("Goal"
                                    :in-theory (enable paragraphp wordp))))
               (extended-extra-fn paragraphp))
  (b* ((name (symbol-fix name))
       (name (translate-symbol name nil))
       (datatype-line `(,name "= Datatype" #\( #\' #\" ,name #\' #\) #\Newline))
       (translated-fields (translate-fty-field-lst fields int-to-rat))
       (fields-line `(,name ".declare('" ,name "'" ,@translated-fields ")"
                            #\Newline)))
    (mv `(,datatype-line
          ,fields-line)
        nil)))

(define translate-fty-option ((name symbolp)
                              (some-type symbolp)
                              (int-to-rat booleanp))
  :returns (mv (translated paragraphp
                           :hints (("Goal"
                                    :in-theory (enable paragraphp wordp))))
               (extended-extra-fn paragraphp))
  (b* ((name (symbol-fix name))
       (name (translate-symbol name nil))
       (datatype-line
        `(,name "= Datatype" #\( #\' ,name #\' #\) #\Newline))
       (translated-type (translate-type some-type int-to-rat nil))
       (declare-line1
        `(,name ".declare('some', ('val', " ,translated-type "))" #\Newline))
       (declare-line2
        `(,name ".declare('nil')" #\Newline)))
    (mv `(,datatype-line
          ,declare-line1
          ,declare-line2)
        nil)))

(define translate-fty-list ((name symbolp)
                            (elt-type symbolp)
                            (int-to-rat booleanp))
  :returns (mv (translated paragraphp
                           :hints (("Goal"
                                    :in-theory (enable paragraphp wordp))))
               (extended-extra-fn paragraphp))
  (b* ((name (symbol-fix name))
       (name (translate-symbol name nil))
       (datatype-line
        `(,name "= Datatype" #\( #\' ,name #\' #\) #\Newline))
       (translated-elt-type (translate-type elt-type int-to-rat nil))
       (declare-line1
        `(,name ".declare('cons', ('car', " ,translated-elt-type "), "
                "('cdr', " ,name "))" #\Newline))
       (declare-line2
        `(,name ".declare('nil')" #\Newline))
       (consp-fn `("def " ,name "_consp(l): return Not(l == " ,name ".nil)"
                       #\Newline)))
    (mv `(,datatype-line
          ,declare-line1
          ,declare-line2)
        `(,consp-fn))))

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
                             (key-type symbolp)
                             (val-type symbolp)
                             (int-to-rat booleanp))
  :returns (mv (translated paragraphp
                           :hints (("Goal"
                                    :in-theory (enable paragraphp wordp))))
               (extended-extra-fn paragraphp))
  :guard-hints (("Goal" :in-theory (e/d (paragraphp wordp) ())))
  (b* ((name (symbol-fix name))
       (key-type (symbol-fix key-type))
       (val-type (symbol-fix val-type))
       (val-type-pkg (symbol-package-name val-type))
       (val-type-str (translate-type val-type int-to-rat nil))
       (maybe-val-str (concatenate 'string "maybe_" val-type-str))
       (maybe-val (intern$ maybe-val-str val-type-pkg))
       ;; translate-fty-option doesn't generate extra-fn
       ((mv maybe-val-type &)
        (translate-fty-option maybe-val val-type int-to-rat))
       (assoc-return `(,key-type "_" ,val-type))
       (assoc-return-type
        (translate-fty-alist-assoc-return key-type val-type assoc-return
                                          int-to-rat))
       (alist-fn
        (translate-fty-alist-type key-type val-type maybe-val int-to-rat))
       (acons-fn (translate-fty-alist-acons name))
       (assoc-fn
        (translate-fty-alist-assoc name maybe-val assoc-return))
       )
    (mv `(,maybe-val-type
          ,assoc-return-type)
        `(,acons-fn
          ,assoc-fn
          ,alist-fn))))


(define translate-one-fty-type ((name symbolp)
                                (body fty-type-p)
                                (int-to-rat booleanp))
  :returns (mv (translated paragraphp
                           :hints (("Goal"
                                    :in-theory (enable paragraphp wordp))))
               (extended-extra-fn paragraphp))
  (b* ((body (fty-type-fix body)))
    (cond ((equal (fty-type-kind body) :prod)
           (translate-fty-prod name (fty-type-prod->fields body) int-to-rat))
          ((equal (fty-type-kind body) :option)
           (translate-fty-option name (fty-type-option->some-type body)
                                 int-to-rat))
          ((equal (fty-type-kind body) :list)
           (translate-fty-list name (fty-type-list->elt-type body)
                               int-to-rat))
          ((equal (fty-type-kind body) :alist)
           (translate-fty-alist name (fty-type-alist->key-type body)
                                (fty-type-alist->val-type body) int-to-rat))
          (t (mv nil nil)))))

(define translate-fty-types-recur ((fty-types fty-types-p)
                                   (int-to-rat booleanp))
  :returns (mv (translated paragraphp)
               (extended-extra-fn paragraphp))
  :measure (len fty-types)
  :hints (("Goal" :in-theory (e/d (fty-types-fix)
                                  ())))
  (b* ((fty-types (fty-types-fix fty-types))
       ((unless (consp fty-types)) (mv nil nil))
       ((cons first rest) fty-types)
       ((cons name body) first)
       ((mv translated-first extra-fn-first)
        (translate-one-fty-type name body int-to-rat))
       ((mv translated-rest extra-fn-rest)
        (translate-fty-types-recur rest int-to-rat))
       (translated (cons translated-first translated-rest))
       (extra-fn (cons extra-fn-first extra-fn-rest)))
    (mv translated extra-fn)))

(define translate-fty-types ((fty-types fty-types-p)
                             (int-to-rat booleanp))
  :returns (translated paragraphp
                       :hints (("Goal"
                                :in-theory (enable paragraphp wordp))))
  (b* (((mv translated extra-fn)
        (translate-fty-types-recur fty-types int-to-rat))
       (symbol-lst (translate-symbol-lst (strip-cars fty-types)))
       (create-line
        (if (endp symbol-lst) nil
          `("[" ,@symbol-lst "] = CreateDatatypes(" ,@symbol-lst ")" #\Newline))))
    `(,translated ,create-line ,extra-fn)))

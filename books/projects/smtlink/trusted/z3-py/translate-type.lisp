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

(defsection SMT-translate-fty
  :parents (z3-py)
  :short "Translating FTY declarations"

  (local (in-theory (enable string-or-symbol-p)))

  (define translate-bool ((b booleanp) (nil-type symbolp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (enable paragraphp wordp))))
    (cond
     ;; Boolean: nil
     ((and (equal b nil)
           (equal nil-type nil))
      (list "False"))
     ;; A fty nil
     ((equal b nil)
      (list (str::downcase-string (concatenate 'string (lisp-to-python-names
                                                        nil-type) ".nil"))))
     ;; Boolean: t
     (t (list "True"))))

  (define translate-symbol ((sym symbolp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (enable paragraphp wordp))))
    (str::downcase-string (lisp-to-python-names sym)))

  (define translate-symbol-lst ((formals symbol-listp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (enable translate-symbol
                                                            paragraphp
                                                            wordp))))
    :measure (len formals)
    (b* ((formals (symbol-list-fix formals))
         ((unless (consp formals)) nil)
         ((unless (consp (cdr formals)))
          (list (translate-symbol (car formals))))
         ((cons first rest) formals)
         (translated-name (translate-symbol first)))
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
      (str::downcase-string (lisp-to-python-names type))))

  (define translate-fty-field-lst ((fields fty-field-alist-p)
                                   (int-to-rat booleanp))
    :returns (translated paragraphp
                         :hints (("Goal" :in-theory (enable translate-type
                                                            translate-symbol
                                                            paragraphp wordp))))
    :measure (len fields)
    :hints (("Goal" :in-theory (e/d (fty-field-alist-fix) ())))
    (b* ((fields (fty-field-alist-fix fields))
         ((unless (consp fields)) nil)
         ((cons first rest) fields)
         (name (translate-symbol (car first)))
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
         (name (translate-symbol name))
         (datatype-line `(,name "= z3.Datatype" #\( #\' ,name #\' #\) #\Newline))
         (translated-fields (translate-fty-field-lst fields int-to-rat))
         (fields-line `(,name ".declare('" ,name "'" ,@translated-fields ")"
                              #\Newline))
         (create-line `(,name " = " ,name ".create()" #\Newline)))
      `(,datatype-line
        ,fields-line
        ,create-line)))

  (define translate-fty-option ((name symbolp)
                                (some-type symbolp)
                                (int-to-rat booleanp))
    :returns (translated paragraphp
                         :hints (("Goal"
                                  :in-theory (enable paragraphp wordp))))
    (b* ((name (symbol-fix name))
         (name (translate-symbol name))
         (datatype-line
          `(,name "= z3.Datatype" #\( #\' ,name #\' #\) #\Newline))
         (translated-type (translate-type some-type int-to-rat nil))
         (declare-line1
          `(,name ".declare('some', ('val', " ,translated-type "))" #\Newline))
         (declare-line2
          `(,name ".declare('nil')" #\Newline))
         (create-line `(,name " = " ,name ".create()" #\Newline)))
      `(,datatype-line
        ,declare-line1
        ,declare-line2
        ,create-line)))

  (define translate-fty-list ((name symbolp)
                              (elt-type symbolp)
                              (int-to-rat booleanp))
    :returns (translated paragraphp
                         :hints (("Goal"
                                  :in-theory (enable paragraphp wordp))))
    (b* ((name (symbol-fix name))
         (name (translate-symbol name))
         (datatype-line
          `(,name "= z3.Datatype" #\( #\' ,name #\' #\) #\Newline))
         (translated-elt-type (translate-type elt-type int-to-rat nil))
         (declare-line1
          `(,name ".declare('cons', ('car', " ,translated-elt-type "), "
                  "('cdr', " ,name "))" #\Newline))
         (declare-line2
          `(,name ".declare('nil')" #\Newline))
         (consp-fn `("def " ,name "_consp(l): return Not(l == " ,name ".nil)"
                     #\Newline))
         (create-line `(,name " = " ,name ".create()" #\Newline)))
      `(,datatype-line
        ,declare-line1
        ,declare-line2
        ,create-line
        ,consp-fn)))

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
         (datatype-line `(,assoc-return "= z3.Datatype('" ,assoc-return "')"
                                        #\Newline))
         (declare-line1 `(,assoc-return ".declare('cons', ('car', " ,key-type
                                        "), ('cdr', " ,val-type "))" #\Newline))
         (declare-line2 `(,assoc-return ".declare('nil')" #\Newline))
         (consp-fn `("def " ,assoc-return "_consp(l): return Not(l == "
                     ,assoc-return ".nil)" #\Newline))
         (create-line `(,assoc-return " = " ,assoc-return ".create()" #\Newline))
         )
      `(,@datatype-line
        ,@declare-line1
        ,@declare-line2
        ,create-line
        ,@consp-fn)))

  (define translate-fty-alist-acons ((name symbolp)
                                     (maybe-val symbolp))
    :returns (translated paragraphp
                         :hints (("Goal"
                                  :in-theory (enable paragraphp wordp))))
    (b* ((name (symbol-fix name))
         (maybe-val (symbol-fix maybe-val))
         (maybe-val (translate-symbol maybe-val))
         (name (translate-symbol name))
         (fn-name `(,name "_acons")))
      `("def " ,fn-name "(key, value, alist): return Store(alist, key, "
        ,maybe-val ".some(value))"
        #\Newline)))

  (define translate-fty-alist-assoc ((name symbolp)
                                     (maybe-val symbolp)
                                     (assoc-return paragraphp))
    :returns (translated paragraphp
                         :hints (("Goal"
                                  :in-theory (enable paragraphp wordp))))
    :guard-debug t
    (b* ((name (symbol-fix name))
         (name (translate-symbol name))
         (maybe-val (symbol-fix maybe-val))
         (maybe-val (translate-symbol maybe-val))
         (assoc-return (paragraph-fix assoc-return))
         (fn-name
          `(,name "_" ,(translate-symbol 'ASSOC-EQUAL))))
      `("def " ,fn-name "(key, alist): return If(Select(alist, key) == "
        ,maybe-val ".nil, " ,assoc-return ".nil, "
        ,assoc-return ".cons(key, " ,maybe-val
        ".val(Select(alist, key))))" #\Newline)))

  (define make-pair-type ((key-type symbolp)
                          (val-type symbolp))
    :returns (pair-type stringp)
    (b* ((key-type (symbol-fix key-type))
         (val-type (symbol-fix val-type))
         (key-type-str (symbol-name key-type))
         (val-type-str (symbol-name val-type))
         (pair-type
          (concatenate 'string key-type-str "_" val-type-str))
         )
      (str::downcase-string (lisp-to-python-names pair-type))))

  (define translate-fty-alist-type ((name symbolp)
                                    (key-type symbolp)
                                    (maybe-val symbolp)
                                    (int-to-rat booleanp))
    :returns (translated paragraphp
                         :hints (("Goal"
                                  :in-theory (enable paragraphp wordp))))
    (b* ((name (symbol-fix name))
         (name (translate-symbol name))
         (key-type (symbol-fix key-type))
         (key-type (translate-type key-type int-to-rat nil))
         (maybe-val (symbol-fix maybe-val))
         (maybe-val (translate-type maybe-val int-to-rat nil))
         )
      `(,name " = ArraySort(" ,key-type ", " ,maybe-val ")" #\Newline)))

  (define translate-fty-alist ((name symbolp)
                               (key-type symbolp)
                               (val-type symbolp)
                               (int-to-rat booleanp))
    :returns (translated paragraphp
                         :hints (("Goal"
                                  :in-theory (enable paragraphp wordp))))
    :guard-hints (("Goal" :in-theory (e/d (paragraphp wordp) ())))
    (b* ((name (symbol-fix name))
         (key-type (symbol-fix key-type))
         (val-type (symbol-fix val-type))
         (val-type-pkg (symbol-package-name val-type))
         (val-type-str (translate-type val-type int-to-rat nil))
         (maybe-val-str (concatenate 'string "maybe_" val-type-str))
         (maybe-val (intern$ maybe-val-str val-type-pkg))
         (maybe-val-type
          (translate-fty-option maybe-val val-type int-to-rat))
         (assoc-return (make-pair-type key-type val-type))
         (assoc-return-type
          (translate-fty-alist-assoc-return key-type val-type assoc-return
                                            int-to-rat))
         (alist-equality
          (translate-fty-alist-type name key-type maybe-val int-to-rat))
         (acons-fn (translate-fty-alist-acons name maybe-val))
         (assoc-fn
          (translate-fty-alist-assoc name maybe-val assoc-return))
         )
      (append `(,maybe-val-type
                ,alist-equality
                ,assoc-return-type)
              `(,acons-fn
                ,assoc-fn))))


  (define translate-one-fty-type ((name symbolp)
                                  (body fty-type-p)
                                  (int-to-rat booleanp))
    :returns (translated paragraphp
                         :hints (("Goal"
                                  :in-theory (enable paragraphp wordp))))
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
            (t nil))))

  (define translate-fty-types-recur ((fty-types fty-types-p)
                                     (int-to-rat booleanp))
    :returns (translated paragraphp)
    :measure (len fty-types)
    :hints (("Goal" :in-theory (e/d (fty-types-fix)
                                    ())))
    (b* ((fty-types (fty-types-fix fty-types))
         ((unless (consp fty-types)) nil)
         ((cons first rest) fty-types)
         ((cons name body) first)
         (translated-first
          (translate-one-fty-type name body int-to-rat))
         (translated-rest
          (translate-fty-types-recur rest int-to-rat))
         (translated (cons translated-first translated-rest)))
      translated))

  (define translate-fty-types ((fty-types fty-types-p)
                               (int-to-rat booleanp))
    :returns (translated paragraphp)
    (translate-fty-types-recur fty-types int-to-rat))
  )

(defsection SMT-translate-abstract-sort
  :parents (z3-py)
  :short "Translating abstract sorts."

  (define translate-abstract-types ((abs symbol-listp))
    :returns (translated paragraphp)
    :measure (len (symbol-list-fix abs))
    (b* ((abs (symbol-list-fix abs))
         ((unless (consp abs)) nil)
         ((cons abs-hd abs-tl) abs)
         (name (translate-symbol abs-hd))
         (first-abs
          `(,name " = z3.DeclareSort('", name "')" #\Newline)))
      `(,first-abs ,@(translate-abstract-types abs-tl))))
  )

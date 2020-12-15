;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (Canada Day, 2019)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)

(include-book "translate-constant")
(include-book "fixtype-precond-template")

(local (in-theory (enable int-to-rat-p
                          string-or-symbol-p
                          word-p)))

;; -------------------------------------------------------
;; translate a type name
(define translate-type ((type symbolp)
                        (sym symbolp)
                        (int-to-rat int-to-rat-p)
                        (fixinfo smt-fixtype-info-p))
  :returns (translated word-p)
  (b* ((type (symbol-fix type))
       (name (name-of-recognizer type fixinfo))
       (itr (int-to-rat-fix int-to-rat))
       (kind (int-to-rat-kind itr))
       (item (cond ((and (equal name 'integer)
                         (or (and (equal kind :switch)
                                  (equal (int-to-rat-switch->okp itr) 't))
                             (and (equal kind :symbol-list)
                                  (member-equal sym
                                                (int-to-rat-symbol-list->lst
                                                 itr)))))
                    (assoc-equal 'rational *SMT-types*))
                   (t (assoc-equal name *SMT-types*))))
       ((unless (endp item)) (cdr item)))
    (str::downcase-string (lisp-to-python-names name))))

;; -------------------------------------------------------
;; translate a type declaration
(define translate-declaration ((name symbolp) (type symbolp)
                               (int-to-rat int-to-rat-p)
                               (fixinfo smt-fixtype-info-p))
  :returns (translated paragraph-p)
  (b* ((name (symbol-fix name))
       (type (symbol-fix type))
       (translated-name (translate-symbol name))
       (translated-type
        (translate-type type name int-to-rat fixinfo)))
    `(,translated-name = "z3.Const" #\( #\' ,translated-name #\' #\, #\Space
                       ,translated-type #\) #\Newline)))

(define translate-type-decl-list ((type-decl-lst decl-list-p)
                                  (fixinfo smt-fixtype-info-p)
                                  (int-to-rat int-to-rat-p))
  :returns (translated paragraph-p)
  :measure (len type-decl-lst)
  (b* ((type-decl-lst (decl-list-fix type-decl-lst))
       ((unless (consp type-decl-lst)) nil)
       ((cons first rest) type-decl-lst)
       ((decl d) first)
       ((hint-pair h) d.type)
       ((unless (type-decl-p h.thm fixinfo))
        (er hard? 'translate-type=>translate-type-decl-list
            "Type theorem is not a type-decl-p: ~q0"
            h.thm))
       (translated-type-decl
        (translate-declaration d.name (car h.thm) int-to-rat fixinfo)))
    (cons translated-type-decl
          (translate-type-decl-list rest fixinfo int-to-rat))))

;; -------------------------------------------------------
;; translate symbol type
(local
 (defthm paragraph-p-of-car-of-string-list-fix
   (paragraph-p (car (str::string-list-fix symbols)))
   :hints (("Goal" :in-theory (e/d (paragraph-p word-p str::string-list-fix)
                                   ()))))
 )

(define translate-symbol-declare ((symbols string-listp))
  :returns (translated paragraph-p)
  :measure (len symbols)
  (b* ((symbols (str::string-list-fix symbols))
       ((unless (consp symbols)) nil)
       ((cons first rest) symbols))
    (cons `(,first " = Symbol_z3.intern('" ,first "')" #\Newline)
          (translate-symbol-declare rest))))

(define translate-symbol-enumeration ((symbols string-listp))
  :returns (translated paragraph-p)
  (b* ((datatype-line '("Symbol_z3 = _SMT_.Symbol()" #\Newline))
       (declarations (translate-symbol-declare symbols)))
    `(,datatype-line
      ,@declarations)))

;; -------------------------------------------------------
;; translate fixtype definition
;; translation template
(define translate-abstract-template ((name paragraph-p))
  :returns (translated paragraph-p)
  (b* ((name (paragraph-fix name)))
    `(,name " = DeclareSort('" ,name "')" #\Newline)))

(define translate-array-template ((name paragraph-p)
                                  (key-type paragraph-p)
                                  (val-type paragraph-p))
  :returns (translated paragraph-p)
  (b* ((name (paragraph-fix name))
       (key-type (paragraph-fix key-type))
       (val-type (paragraph-fix val-type)))
    `(,name " = ArraySort(" ,key-type ", " ,val-type ")" #\Newline)))

(define translate-destructor-template ((destructor paragraph-p)
                                       (return-type paragraph-p))
  :returns (translated paragraph-p)
  (b* ((destructor (paragraph-fix destructor))
       (return-type (paragraph-fix return-type)))
    `("('" ,destructor "', " ,return-type ")")))

(define translate-prod-template ((name paragraph-p)
                                 (constructor paragraph-p)
                                 (destructor-list paragraph-p))
  :returns (translated paragraph-p)
  (b* ((name (paragraph-fix name))
       (constructor (paragraph-fix constructor))
       (destructor-list (paragraph-fix destructor-list)))
    `(,name ".declare('" ,constructor "'" ,destructor-list ")" #\Newline)))

(define translate-sum-template ((name paragraph-p)
                                (declare-lines paragraph-p))
  :returns (translated paragraph-p)
  (b* ((name (paragraph-fix name))
       (declare-lines (paragraph-fix declare-lines))
       (datatype-line
        `(,name "= z3.Datatype" #\( #\' ,name #\' #\) #\Newline))
       (create-line
        `(,name " = " ,name ".create()" #\Newline)))
    `(,datatype-line
      ,declare-lines
      ,create-line)))

(define translate-sum-declare ((name paragraph-p)
                               (kind-fn paragraph-p)
                               (name-val paragraph-p)
                               (symbol-type paragraph-p))
  :returns (translated paragraph-p)
  (b* ((name (paragraph-fix name))
       (kind-fn (paragraph-fix kind-fn))
       (name-val (paragraph-fix name-val))
       (symbol-type (paragraph-fix symbol-type))
       (declare-line `(,name ".declare('make', ('" ,kind-fn "', "
                             ,symbol-type "), ('value', " ,name-val "))"
                             #\Newline)))
    declare-line))

(define translate-sum-top-template ((val-type paragraph-p)
                                    (type paragraph-p)
                                    (declare-lines paragraph-p))
  :returns (translated paragraph-p)
  (b* ((val-type (paragraph-fix val-type))
       (type (paragraph-fix type))
       (declare-lines (paragraph-fix declare-lines))
       (datatype-line1
        `(,val-type "= z3.Datatype" #\( #\' ,val-type #\' #\) #\Newline))
       (datatype-line2
        `(,type "= z3.Datatype" #\( #\' ,type #\' #\) #\Newline))
       (create-line `(,val-type ", " ,type " = CreateDatatypes("
                                ,val-type ", " ,type ")" #\Newline)))
    `(,datatype-line1
      ,datatype-line2
      ,declare-lines
      ,create-line)))

(define translate-enum-template ((name paragraph-p)
                                 (enum-lines paragraph-p))
  :returns (translated paragraph-p)
  (b* ((name (paragraph-fix name))
       (enum-lines (paragraph-fix enum-lines))
       (declare-line
        `(,name "= z3.Datatype" #\( #\' ,name #\' #\) #\Newline))
       (create-line `(,name " = " ,name ".create()" #\Newline)))
    `(,declare-line
      ,enum-lines
      ,create-line)))

(define translate-array ((name symbolp)
                         (rec symbolp)
                         (smt-type smt-type-p)
                         (int-to-rat int-to-rat-p)
                         (precond pseudo-term-list-listp)
                         (fixinfo smt-fixtype-info-p))
  :returns (mv (translated-fixtypes paragraph-p)
               (fixtype-precond pseudo-term-list-listp))
  :guard (equal (smt-type-kind smt-type) :array)
  (b* ((name (symbol-fix name))
       (smt-type (smt-type-fix smt-type))
       ((smt-type-array a) smt-type)
       (name-str (translate-symbol name))
       (key-type (translate-type a.key-type name int-to-rat fixinfo))
       (val-type (translate-type a.val-type name int-to-rat fixinfo))
       (translated (translate-array-template name-str key-type val-type))
       (precond (precond-array rec smt-type precond)))
    (mv translated precond)))

(define translate-constructor ((constructor type-function-p))
  :returns (translated paragraph-p)
  (b* ((constructor (type-function-fix constructor))
       ((type-function f) constructor))
    (translate-symbol f.name)))

(define translate-destructor-list ((name symbolp)
                                   (name-origin symbolp)
                                   (destructors type-function-list-p)
                                   (fixinfo smt-fixtype-info-p)
                                   (int-to-rat int-to-rat-p))
  :returns (translated paragraph-p)
  :measure (len destructors)
  (b* ((name (symbol-fix name))
       (destructors (type-function-list-fix destructors))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       (int-to-rat (int-to-rat-fix int-to-rat))
       ((unless (consp destructors)) nil)
       ((cons first rest) destructors)
       (destructor (translate-symbol (type-function->name first)))
       (return-type-sym (type-function->return-type first))
       (return-type (translate-type return-type-sym name int-to-rat
                                    fixinfo))
       (translated-destructor
        (translate-destructor-template destructor return-type))
       (translated-destructor-list
        (translate-destructor-list name name-origin rest fixinfo int-to-rat)))
    `(", " ,translated-destructor ,translated-destructor-list)))

(define translate-prod ((name symbolp)
                        (name-origin symbolp)
                        (prod prod-p)
                        (fixinfo smt-fixtype-info-p)
                        (symbols symbol-string-alistp)
                        (index natp)
                        (avoid symbol-listp)
                        (int-to-rat int-to-rat-p)
                        (precond pseudo-term-list-listp)
                        state)
  :returns (mv (translated-fixtypes paragraph-p)
               (fixtype-precond pseudo-term-list-listp)
               (new-symbols symbol-string-alistp)
               (index natp))
  (b* ((name (symbol-fix name))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       (prod (prod-fix prod))
       ((prod p) prod)
       ;; generate a symbol for kind
       ((mv & new-index new-symbols)
        (translate-constant `(quote ,p.kind) index symbols avoid))
       (name-str (translate-symbol name))
       (constructor (translate-constructor p.constructor))
       (destructor-list
        (translate-destructor-list name name-origin p.destructors fixinfo
                                   int-to-rat))
       (translated (translate-prod-template name-str constructor destructor-list))
       (new-precond (precond-prod prod precond state)))
    (mv translated new-precond new-symbols new-index)))

(define translate-prod-list ((name symbolp)
                             (name-origin symbolp)
                             (prod-list prod-list-p)
                             (fixinfo smt-fixtype-info-p)
                             (symbols symbol-string-alistp)
                             (index natp)
                             (avoid symbol-listp)
                             (int-to-rat int-to-rat-p)
                             (precond pseudo-term-list-listp)
                             state)
  :returns (mv (translated-fixtypes paragraph-p)
               (fixtype-precond pseudo-term-list-listp)
               (new-symbols symbol-string-alistp)
               (index natp))
  :measure (len prod-list)
  (b* ((name (symbol-fix name))
       (prod-list (prod-list-fix prod-list))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       (precond (pseudo-term-list-list-fix precond))
       (symbols (symbol-string-alist-fix symbols))
       (index (nfix index))
       ((unless (consp prod-list)) (mv nil precond symbols index))
       ((cons first rest) prod-list)
       ((mv first-translated first-precond first-symbols first-index)
        (translate-prod name name-origin first fixinfo symbols index avoid
                        int-to-rat precond state))
       ((mv rest-translated rest-precond rest-symbols rest-index)
        (translate-prod-list name name-origin rest fixinfo
                             first-symbols first-index avoid int-to-rat
                             first-precond state)))
    (mv (cons first-translated rest-translated)
        rest-precond rest-symbols rest-index)))

(define translate-sum-val ((name symbolp)
                           (name-origin symbolp)
                           (smt-type smt-type-p)
                           (fixinfo smt-fixtype-info-p)
                           (symbols symbol-string-alistp)
                           (index natp)
                           (avoid symbol-listp)
                           (int-to-rat int-to-rat-p)
                           (precond pseudo-term-list-listp)
                           state)
  :returns (mv (translated-fixtypes paragraph-p)
               (fixtype-precond pseudo-term-list-listp)
               (new-symbols symbol-string-alistp)
               (index natp))
  :guard (equal (smt-type-kind smt-type) :sum)
  (b* ((name (symbol-fix name))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       (smt-type (smt-type-fix smt-type))
       ((smt-type-sum s) smt-type)
       (name-str (translate-symbol name))
       ((mv prod-list-line precond-prods new-symbols new-index)
        (translate-prod-list name name-origin s.prods fixinfo
                             symbols index avoid int-to-rat precond state))
       ;; (kind-name (symbol-append name-origin '-kind))
       ;; (kind-name-str (translate-symbol kind-name))
       (kind-fn-str (translate-symbol (smt-type-kind-fn smt-type)))
       (name-origin-str (translate-symbol name-origin))
       (translated-sum
        (translate-sum-declare name-origin-str kind-fn-str name-str
                               (translate-type
                                'symbolp nil (make-int-to-rat-switch)
                                fixinfo))))
    (mv `(,prod-list-line ,translated-sum) precond-prods
        new-symbols new-index)))

(define get-kinds ((prods prod-list-p))
  :returns (kinds symbol-listp)
  :measure (len prods)
  (b* ((prods (prod-list-fix prods))
       ((unless (consp prods)) nil)
       ((cons first rest) prods)
       ((prod p) first))
    (cons p.kind (get-kinds rest))))

(define translate-enum-list ((name symbolp)
                             (kinds symbol-listp))
  :returns (translated paragraph-p)
  :measure (len kinds)
  (b* ((name (symbol-fix name))
       (name-str (translate-symbol name))
       (kinds (symbol-list-fix kinds))
       ((unless (consp kinds)) nil)
       ((cons first rest) kinds))
    (cons (translate-prod-template name-str (translate-symbol first) nil)
          (translate-enum-list name rest))))

(define translate-enum ((name symbolp)
                        (kinds symbol-listp))
  :returns (translated paragraph-p)
  (b* ((name (symbol-fix name))
       (kinds (symbol-list-fix kinds))
       (name-str (translate-symbol name))
       (enum-list-line (translate-enum-list name kinds))
       (translated (translate-sum-template name-str enum-list-line)))
    translated))

(define translate-sum ((name symbolp)
                       (smt-type smt-type-p)
                       (fixinfo smt-fixtype-info-p)
                       (symbols symbol-string-alistp)
                       (index natp)
                       (avoid symbol-listp)
                       (int-to-rat int-to-rat-p)
                       (precond pseudo-term-list-listp)
                       state)
  :returns (mv (translated-fixtypes paragraph-p)
               (fixtype-precond pseudo-term-list-listp)
               (symbols symbol-string-alistp)
               (index natp))
  :guard (equal (smt-type-kind smt-type) :sum)
  (b* ((name (symbol-fix name))
       (name-str (translate-symbol name))
       (name-val-sym (symbol-append name '-val))
       (name-val (translate-symbol name-val-sym))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       (smt-type (smt-type-fix smt-type))
       ((mv translated-sum-val precond-sum-val new-symbols new-index)
        (translate-sum-val name-val-sym name smt-type fixinfo symbols index
                           avoid int-to-rat precond state))
       (translated-sum-top
        (translate-sum-top-template name-str name-val translated-sum-val)))
    (mv translated-sum-top precond-sum-val new-symbols new-index)))

(define translate-fixtype ((fixtype smt-fixtype-p)
                           (fixinfo smt-fixtype-info-p)
                           (symbols symbol-string-alistp)
                           (index natp)
                           (avoid symbol-listp)
                           (int-to-rat int-to-rat-p)
                           (precond-acc pseudo-term-list-listp)
                           state)
  :returns (mv (translated-fixtypes paragraph-p)
               (fixtype-precond pseudo-term-list-listp)
               (new-symbols symbol-string-alistp)
               (new-index natp))
  (b* ((fixtype (smt-fixtype-fix fixtype))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       (int-to-rat (int-to-rat-fix int-to-rat))
       (symbols (symbol-string-alist-fix symbols))
       (index (nfix index))
       (precond-acc (pseudo-term-list-list-fix precond-acc))
       ((smt-fixtype f) fixtype)
       (kind (smt-type-kind f.kind)))
    (case kind
      (:abstract (mv (translate-abstract-template (translate-symbol f.name))
                     precond-acc symbols index))
      (:array (b* (((mv translated new-precond)
                    (translate-array f.name f.recognizer f.kind int-to-rat
                                     precond-acc fixinfo)))
                (mv translated new-precond symbols index)))
      (:sum (translate-sum f.name f.kind fixinfo
                           symbols index avoid int-to-rat precond-acc state))
      (t (mv nil precond-acc symbols index)))))

(define translate-fixtype-list ((fixtypes smt-fixtype-list-p)
                                (fixinfo smt-fixtype-info-p)
                                (symbols symbol-string-alistp)
                                (index natp)
                                (avoid symbol-listp)
                                (int-to-rat int-to-rat-p)
                                (precond-acc pseudo-term-list-listp)
                                (seen symbol-listp)
                                state)
  :returns (mv (translated-fixtypes paragraph-p)
               (fixtype-precond pseudo-term-list-listp)
               (new-symbols symbol-string-alistp)
               (new-index natp))
  :measure (len fixtypes)
  (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
       (fixinfo (smt-fixtype-info-fix fixinfo))
       (symbols (symbol-string-alist-fix symbols))
       (index (nfix index))
       (avoid (symbol-list-fix avoid))
       (precond-acc (pseudo-term-list-list-fix precond-acc))
       ((unless (consp fixtypes)) (mv nil precond-acc symbols index))
       ((cons first rest) fixtypes)
       ((smt-fixtype f) first)
       ((if (member-equal f.name seen))
        (translate-fixtype-list rest fixinfo symbols index avoid int-to-rat
                                precond-acc seen state))
       ((if (equal f.basicp t))
        (translate-fixtype-list rest fixinfo symbols index avoid int-to-rat
                                precond-acc seen state))
       ((mv first-translated first-precond first-symbols first-index)
        (translate-fixtype first fixinfo symbols index avoid int-to-rat
                           precond-acc state))
       ((mv rest-translated rest-precond rest-symbols rest-index)
        (translate-fixtype-list rest fixinfo first-symbols first-index avoid
                                int-to-rat first-precond (cons f.name seen)
                                state)))
    (mv (cons first-translated rest-translated) rest-precond
        rest-symbols rest-index)))

(defsection SMT-translate-abstract-sort
  :parents (z3-py)
  :short "Translating abstract sorts."

  (define translate-abstract-types ((fixtypes smt-fixtype-list-p))
    :returns (translated paragraph-p)
    :measure (len (smt-fixtype-list-fix fixtypes))
    (b* ((fixtypes (smt-fixtype-list-fix fixtypes))
         ((unless (consp fixtypes)) nil)
         ((cons ftype-hd ftype-tl) fixtypes)
         ((smt-fixtype ftype) ftype-hd)
         ((if (not (equal (smt-type-kind ftype.kind) :abstract)))
          (translate-abstract-types ftype-tl))
         (name (translate-symbol ftype.name))
         (first-abs
          `(,name " = z3.DeclareSort('", name "')" #\Newline)))
      `(,first-abs ,@(translate-abstract-types ftype-tl))))
  )

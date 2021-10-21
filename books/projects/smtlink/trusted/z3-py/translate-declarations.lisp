;; Copyright (C) 2015, University of British Columbia
;; Written (originally) by Yan Peng (11th October, 2021)
;;
;; License: A 3-clause BSD license.
;; See the LICENSE file distributed with ACL2

(in-package "SMT")
(include-book "centaur/fty/top" :dir :system)
(include-book "xdoc/top" :dir :system)
(include-book "std/util/define" :dir :system)
(include-book "std/strings/top" :dir :system)

(include-book "../../utils/pseudo-term")
(include-book "../../verified/judgements")
(include-book "../../verified/basics")
(include-book "translate-variable")
(include-book "translate-quote")

(local (in-theory (enable paragraph-p word-p pseudo-term-fix)))
(set-induction-depth-limit 1)

(define conjunction-to-list ((decl-term pseudo-termp)
                             (acc pseudo-term-listp))
  :returns (decl-list pseudo-term-listp)
  :measure (acl2-count (pseudo-term-fix decl-term))
  :verify-guards nil
  (b* ((decl-term (pseudo-term-fix decl-term))
       (acc (pseudo-term-list-fix acc))
       ((if (equal decl-term ''t)) acc)
       ((unless (is-conjunct? decl-term))
        (cons decl-term acc))
       ((list* & decl-hd decl-tl &) decl-term)
       (acc-hd (conjunction-to-list decl-hd acc)))
    (conjunction-to-list decl-tl acc-hd)))

(verify-guards conjunction-to-list)

#|
(conjunction-to-list '(if (integerp x) (rationalp y) 'nil)
                     nil)
|#

(define is-translatable-decl? ((decl pseudo-termp))
  :returns (okp booleanp)
  (b* ((decl (pseudo-term-fix decl)))
    (and (consp decl)
         (consp (cdr decl))
         (symbolp (car decl))
         (not (equal (car decl) 'quote))
         (symbolp (cadr decl))))
  ///
  (more-returns
   (okp (implies okp
                 (and (consp decl)
                      (consp (cdr decl))
                      (symbolp (car decl))
                      (symbolp (cadr decl))))
        :name implies-of-is-translatable-decl?)))

(define translate-type ((type symbolp))
  :returns (translated stringp)
  (b* ((type (symbol-fix type))
       (item (assoc-equal type *SMT-types*))
       ((unless item)
        (prog2$ (er hard? 'translate-declarations=>translate-type
                    "Not a basic type, not supported. ~q0" type)
                "")))
    (cdr item))
  ///
  (more-returns
   (translated (paragraph-p translated)
               :name paragraph-of-translate-type)))

(define translate-one-decl ((decl pseudo-termp))
  :returns (translated paragraph-p)
  (b* (((unless (is-translatable-decl? decl))
        (er hard? 'translate-declarations=>translate-one-decl
            "Declaration is not translatable: ~q0" decl))
       ((list type var) decl)
       (translated-var (translate-variable var))
       (translated-type (translate-type type)))
    `(,translated-var = "z3.Const" #\( #\' ,translated-var #\' #\, #\Space
                      ,translated-type #\) #\Newline)))

(define translate-declaration-list ((decl-list pseudo-term-listp))
  :returns (translated paragraph-p)
  :measure (len decl-list)
  (b* ((decl-list (pseudo-term-list-fix decl-list))
       ((unless (consp decl-list)) nil)
       ((cons decl-hd decl-tl) decl-list))
    (cons (translate-one-decl decl-hd)
          (translate-declaration-list decl-tl))))

#|
(translate-declaration-list '((rationalp y) (integerp x)))
|#

(local
 (defthm paragraph-of-car-of-string-list-fix
   (paragraph-p (car (str::string-list-fix syms)))
   :hints (("Goal" :in-theory (enable str::string-list-fix))))
 )

(define translate-symbol-declare ((syms string-listp))
  :returns (translated paragraph-p)
  :measure (len (str::string-list-fix syms))
  (b* ((syms (str::string-list-fix syms))
       ((unless (consp syms)) nil)
       ((cons first rest) syms))
    (cons `(,first " = Symbol_z3.intern('" ,first "')" #\Newline)
          (translate-symbol-declare rest))))

;; (translate-symbol-declare '("sym1" "sym2"))

(define translate-symbol-enumeration ((symbols string-listp))
  :returns (translated paragraph-p)
  (b* ((datatype-line '("Symbol_z3 = _SMT_.Symbol()" #\Newline))
       (declarations (translate-symbol-declare symbols)))
    `(,datatype-line
      ,@declarations)))

(local 
 (defthm pseudo-term-list-of-reverse
   (implies (pseudo-term-listp x)
            (pseudo-term-listp (reverse x)))
   :hints (("Goal"
            :in-theory (enable pseudo-term-listp acl2::rev))))
 )

(define translate-declarations ((decl-term pseudo-termp)
                                (syms string-listp))
  :returns (translated paragraph-p)
  :guard-debug t
  (b* ((decl-term (pseudo-term-fix decl-term))
       (syms (str::string-list-fix syms))
       (decl-list (conjunction-to-list decl-term nil))
       (translated-declaration-list
        (translate-declaration-list (reverse decl-list)))
       (translated-syms (translate-symbol-enumeration syms)))
    `(,@translated-syms
      ,@translated-declaration-list)))

#|
(translate-declarations '(if (integerp x) (rationalp y) 'nil))
|#

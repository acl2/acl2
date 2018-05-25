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
  :returns (translated paragraphp)
  (b* ((type (symbol-fix type))
       (item (cond ((equal flag 'uninterpreted)
                    (assoc-equal type *SMT-uninterpreted-types*))
                   ((and (equal type 'integerp) int-to-rat)
                    (assoc-equal 'rationalp *SMT-types*))
                   (t (assoc-equal type *SMT-types*))))
       ((unless (endp item)) (cdr item)))
    (lisp-to-python-names (fty-info->name (cdr fty-item)))))

(define translate-fty-field-lst ((fields fty-field-alist-p)
                                 (int-to-rat booleanp))
  :returns (translated paragraphp)
  (b* ((fields (fty-field-alist-fix fields))
       ((unless (consp fields)) nil)
       ((cons first rest) fields)
       (name (translate-symbol (car first) nil))
       (type (translate-type (cadr first) int-to-rat nil))
       (translated-field `(", ('" ,name "', " ,type ")")))
    (cons translated-field
          (translate-fty-field-lst rest))))

(define translate-fty-prod ((name symbolp)
                            (fields fty-field-alist-p)
                            (int-to-rat booleanp))
  :returns (translated paragraphp)
  (b* ((name (symbol-fix name))
       (datatype-line `(,name "= Datatype('" ,name "')" #\Newline))
       (translated-fields (translate-fty-field-lst fields int-to-rat))
       (fields-line `(,name ".declare('" ,name "'" ,@translated-fields ")"
                            #\Newline)))
    `(,datatype-line
      ,fields-line)))

(define translate-fty-prod-lst ((prod-lst fty-prod-alist-p)
                                (int-to-rat booleanp))
  :returns (translated paragraphp)
  (b* ((prod-lst (fty-prod-alist-fix prod-lst))
       ((unless (consp prod-lst)) nil)
       ((cons first rest) prod-lst))
    (cons (translate-fty-prod (car first) (cadr first) int-to-rat)
          (translate-fty-prod-lst rest int-to-rat))))

(define translate-fty-option ((name symbolp)
                              (some-type symbolp)
                              (int-to-rat booleanp))
  :returns (translated paragraphp)
  (b* (()
       ())
    ()))

(define translate-fty-option-lst ((option-lst fty-option-alist-p)
                                  (int-to-rat booleanp))
  :returns (translated paragraphp)
  (b* ((option-lst (fty-option-alist-fix option-lst))
       ((unless (consp option-lst)) nil)
       ((cons first rest) option-lst))
    (cons (translate-fty-option (car first) (cadr first) int-to-rat)
          (translate-fty-option-lst rest int-to-rat))))

(define translate-fty-list ((name symbolp)
                            (elt-type symbolp)
                            (int-to-rat booleanp))
  :returns ()
  ())

(define translate-fty-list-lst ((list-lst fty-list-alist-p)
                                (int-to-rat booleanp))
  :returns (translated paragraphp)
  (b* ((list-lst (fty-list-alist-fix list-lst))
       ((unless (consp list-lst)) nil)
       ((cons first rest) list-lst))
    (cons (translate-fty-option (car first) (cadr first) int-to-rat)
          (translate-fty-list-lst rest int-to-rat))))

(define translate-fty-alist ((name symbolp)
                             (alist-pair fty-alist-p)
                             (int-to-rat booleanp))
  :returns ()
  ())

(define translate-fty-alist-lst ((alist-lst fty-alist-alist-p)
                                 (int-to-rat booleanp))
  :returns (translated paragraphp)
  (b* ((alist-lst (fty-alist-alist-fix alist-lst))
       ((unless (consp alist-lst)) nil)
       ((cons first rest) alist-lst))
    (cons (translate-fty-option (car first) (cadr first) int-to-rat)
          (translate-fty-alist-lst rest int-to-rat))))

(define translate-fty-types ((fty-types fty-types-p)
                             (int-to-rat booleanp)
                             (acc paragraphp))
  :returns (translated paragraphp)
  (b* ((fty-types (fty-types-fix fty-types))
       (acc (paragraph-fix acc))
       ((fty-types f) fty-types)
       ((mv prod prod-names) (translate-fty-prod-lst f.prod int-to-rat))
       ((mv option option-names) (translate-fty-option-lst f.option int-to-rat))
       ((mv list list-names) (translate-fty-list-lst f.list int-to-rat))
       ((mv alist alist-names) (translate-fty-alist-lst f.alist int-to-rat))
       (symbol-lst `(,@prod-names ,@option-names ,@list-names ,@alist-names))
       (translated-symbol-lst (translate-symbol-list symbol-lst))
       (create `(,@translated-symbol-lst "= CreateDatatypes"
                                         #\( ,@translated-symbol-lst #\)
                                         #\Newline)))
    `(,@prod ,@option ,@list ,@alist ,@create)))

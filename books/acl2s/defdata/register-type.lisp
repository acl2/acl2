#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
API to register a type
author: harshrc
file name: register-type.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "defdata-attach")

;TODO
; Q: howto to generate an enumerator or fixer from a predicate def
; 11 June 2014 - 2am

; A: We will take the inverse of P defined in defdata paper i.e. we
; will map each predicate expression to a core defdata
; expression. Once we have it, we will use E defined in defdata paper
; to generate the enumerator expression. To furthur generate a fixer,
; we can take the acl2-count or size of the argument (a value in the
; domain of the fixer) and pass it through the enumerator definition
; to obtain the result of the fixer function. But we will probably use
; a separate F interpretation to directly generate a fixer from the
; core defdata expression. Like P, we will store P^-1 in the builtin
; combinator table.

(def-const *register-type-keywords*
  '(:predicate :enumerator ;mandatory names
               :enum/acc
               :domain-size
               :clique :def :normalized-def :prettyified-def ;defdata
               :verbose :hints
               :theory-name
               :min-rec-depth :max-rec-depth
               :recp ;is recursive or not
               :satisfies :satisfies-fixer
               :default-base-value
               ;; the following are not implemented yet
               :equiv :equiv-fixer
               :fixer :fixer-domain
               :lub :glb
               :sampling
               ))

; [2015-07-01 Wed] enumerator and enum/acc are attachable functions

(defun type-of-pred-aux (pred tbl)
  (declare (xargs :guard (and (symbolp pred) (sym-aalist1p tbl))))
  (cond ((endp tbl) nil)
        ((equal pred (get-alist :predicate (cdar tbl)))
         (caar tbl))
        (t (type-of-pred-aux pred (cdr tbl)))))

#|
(defun type-of-pred (pred tbl)
  (cond ((equal pred 'intp) 'integer)
        ((equal pred 'boolp) 'boolean)
        ((equal pred 'tlp) 'true-list)
        (t (type-of-pred-aux pred tbl))))
|#

(defun type-of-pred (pred tbl ptbl)
  (declare (xargs :guard (and (symbolp pred) (sym-aalist1p tbl) (sym-aalist1p ptbl))))
  (let ((apred (assoc-equal :type (get-alist pred ptbl))))
    (if apred
        (cdr apred)
    (type-of-pred-aux pred tbl))))

#|
(type-of-pred 'boolp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'boolp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'bool
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'tlp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'intp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred 'integerp
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
(type-of-pred nil
              (type-metadata-table (w state))
              (pred-alias-table (w state)))
|#

(defun enum-of-type (type tbl)
  (declare (xargs :guard (and (symbolp type) (sym-aalist1p tbl))))
  (get-alist :enumerator (get-alist type tbl)))

; (enum-of-type 'integer (type-metadata-table (w state)))

(defun trans1-cmp (form wrld)
  (declare (xargs :mode :program))
  (declare (xargs :guard (plist-worldp wrld)))
  (acl2::translate1-cmp
   form nil nil nil 'ctx wrld (default-state-vars nil)))

(defun base-val-of-type (type tbl wrld)
  (declare (xargs :mode :program))
  (declare (xargs :guard (and (symbolp type) (sym-aalist1p tbl) (plist-worldp wrld))))
  (b* ((base-val (get-alist :default-base-value (get-alist type tbl)))
       ((mv - trans-base-val -)
        (if (and (symbolp base-val)
                 (acl2::legal-variable-or-constant-namep base-val)
                 (acl2::legal-constantp1 base-val))
            (trans1-cmp base-val wrld)
          (mv nil `',base-val nil))))
    trans-base-val))

; (defconst *x* 'x)
; (defdata x *x*)
; (defdata non-empty-true-list (cons all true-list))
; (base-val-of-type 'x (type-metadata-table (w state)) (w state)) = 'x
; (base-val-of-type 'integer (type-metadata-table (w state)) (w state)) = '0
; (base-val-of-type 'non-empty-true-list (type-metadata-table (w state)) (w state)) = '(nil)
; (base-val-of-type 'symbol (type-metadata-table (w state)) (w state)) = 'a


#|

(defun type-of-type (type tbl atbl ctx)
  (let ((atype (assoc-equal :type (get-alist type atbl))))
    (if atype
        (cdr atype)
      (let ((res (get-alist type tbl)))
        (if res
            type
          (er soft ctx
 "~%**Unknown type **: ~x0 is not a known type name.~%" type ))))))

(defun pred-of-type (type tbl atbl ctx)
  (let ((atype (assoc-equal :predicate (get-alist type atbl))))
    (if atype
        (cdr atype)
      (let ((res (get-alist :predicate (get-alist type tbl))))
        (or res
            (er hard ctx
 "~%**Unknown type **: ~x0 is not a known type name.~%" type ))))))

|#

; Decided to take care of error printing on my own, but kept previous
; versions above.

(defun type-of-type (type tbl atbl)
  (declare (xargs :guard (and (symbolp type) (sym-aalist1p tbl)
                              (sym-aalist1p atbl))))
  (let ((atype (assoc-equal :type (get-alist type atbl))))
    (if atype
        (cdr atype)
      (let ((res (get-alist type tbl)))
        (if res
            type
          nil)))))

(defun pred-of-type (type tbl atbl)
  (declare (xargs :guard (and (symbolp type) (sym-aalist1p tbl)
                              (sym-aalist1p atbl))))
  (let ((atype (assoc-equal :predicate (get-alist type atbl))))
    (if atype
        (cdr atype)
      (let ((res (get-alist :predicate (get-alist type tbl))))
        res))))

; A function to determine the domain size of a type.
; Note that we return 'infinite instead of t if the domain
; size is determined to be infinite.

#|

Removed error checking which was causing problems for
mutually recursive definitions.

(defun defdata-domain-size-fn (type wrld)
  (declare (xargs :guard (and (symbolp type) (plist-worldp wrld))
                  :verify-guards nil))
  (b* ((tbl (table-alist 'type-metadata-table wrld))
       (atbl (table-alist 'type-alias-table wrld))
       (ttype (type-of-type type tbl atbl))
       ((unless ttype)
        (er hard 'domain-size
            "~%The given type, ~x0, is not a known type or alias type." type))
       (type-info (assoc ttype tbl))
       (domain (cdr (assoc :domain-size (cdr type-info)))))
    (if (natp domain)
        domain
      'infinite)))
|#

; If we have a mutually recursive definition and can't figure out the
; size, just assume infinite.
(defun defdata-domain-size-fn (type wrld)
  (declare (xargs :guard (and (symbolp type) (plist-worldp wrld))
                  :verify-guards nil))
  (b* ((tbl (table-alist 'type-metadata-table wrld))
       (atbl (table-alist 'type-alias-table wrld))
       (ttype (type-of-type type tbl atbl))
       (type-info (assoc ttype tbl))
       (domain (cdr (assoc :domain-size (cdr type-info)))))
    (if (natp domain)
        domain
      'infinite)))

(defmacro defdata-domain-size (type)
  `(defdata-domain-size-fn ',type (w state)))

(defun defdata-base-val-of-type-fn (type wrld)
  (declare (xargs :mode :program
                  :guard (and (symbolp type) (plist-worldp wrld))
                  :verify-guards nil))
  (b* ((tbl (type-metadata-table wrld))
       (atbl (table-alist 'type-alias-table wrld))
       (ttype (type-of-type type tbl atbl)))
    (base-val-of-type ttype tbl wrld)))

(defmacro defdata-base-val-of-type (type)
  `(defdata-base-val-of-type-fn ',type (w state)))

(defun get-or-size-acc (or-def acc wrld)
  (declare (xargs :mode :program))
  (if (endp or-def)
      acc
    (b* ((type (car or-def))
         (size-type (if (legal-variablep type) ; otherwise treat as a constant
                        (defdata-domain-size-fn (car or-def) wrld)
                      1)))
      (if (natp size-type)
          (get-or-size-acc (cdr or-def) (+ size-type acc) wrld)
        t))))

(defun get-or-size (or-def wrld)
  (declare (xargs :mode :program))
  (get-or-size-acc or-def 0 wrld))

#|

 The determination of the size of the domain is incomplete.

 It should be the case that the following returns 3, but it returns
 infinite, because we don't handle records.

 (defdata foo (enum '(1 2 3)))
 (defdata r2 (record (f . foo)))
 (defdata-domain-size r2)

 Also, make sure maps are correctly handled, as well as lists of given
 lengths, etc.

|#

(defun register-type-fn (name args ctx pkg wrld)
  (declare (xargs :mode :program))
  (b* (((mv kwd-alist rest)
        (extract-keywords ctx *register-type-keywords* args nil nil))
       ((when rest) (er hard? ctx "~| Extra args: ~x0~%" rest))
       ((unless (proper-symbolp name))
        (er hard? ctx "~| ~x0 should be a proper symbol.~%" name))

       ((unless (well-formed-type-metadata-p kwd-alist wrld))
        (er hard? ctx "~| ~s0~%" (ill-formed-type-metadata-msg kwd-alist wrld)))

       (?pred-name (get1 :predicate kwd-alist))
       (enum (get1 :enumerator kwd-alist))
       (enum/acc (get1 :enum/acc kwd-alist))
       (enum-formals (acl2::formals enum wrld))
       (enum-guard (acl2::guard enum nil wrld))
       (enum/acc-formals (or (and enum/acc (acl2::formals enum/acc wrld))
                             '(M SEED)))
       (enum/acc-guard (or (and enum/acc (acl2::guard enum/acc nil wrld))
                           '(AND (NATP M) (UNSIGNED-BYTE-P 31 SEED))))

       ;; these two names are constant, but attachable names. TODO: Revisit this decision!
       (enum-name (make-enumerator-symbol name pkg))
       (enum/acc-name (make-uniform-enumerator-symbol name pkg))
       (def (get1 :def kwd-alist))
       (enum-type? (and (consp def) (equal (car def) 'enum)))
       (normalized-def (get1 :normalized-def kwd-alist))
       (or-type? (and (consp def) (equal (car def) 'or)))
       (or-size (if or-type? (get-or-size (cdr normalized-def) wrld) 0))
       (domain-size (or (get1 :domain-size kwd-alist)
                        (and enum-type? (nfix (1- (len normalized-def))))
                        (and or-type? or-size)
                        (and (quotep def) 1)
                        (and (atom def) 1) ; alias caught above
                        t))

       ((when (eq enum enum-name))
        (er hard? ctx "~| Please rename the enumerator ~x0 to be different from ~x1, to which it will be attached.~%" enum enum-name))
       ((when (eq enum/acc enum/acc-name))
        (er hard? ctx "~| Please rename the enumerator ~x0 to be different from ~x1, to which it will be attached.~%" enum/acc enum/acc-name))

       (enum/acc-default (s+ enum/acc-name '|-BUILTIN| :pkg pkg))
       (kwd-alist (put-assoc-eq :enumerator enum-name kwd-alist))
       (kwd-alist (put-assoc-eq :enum/acc enum/acc-name kwd-alist))

       (kwd-alist (put-assoc-eq :domain-size domain-size kwd-alist))
       (kwd-alist (put-assoc-eq
                   :theory-name (or (get1 :theory-name kwd-alist)
                                    (s+ name '-theory :pkg pkg))
                   kwd-alist))

       (existing-entry (assoc-eq name (table-alist 'type-metadata-table wrld)))
       ((when existing-entry)
        (if (not (equal kwd-alist (cdr existing-entry)))
            (er hard? ctx "~| ~x0 is already a registered defdata type.~%" name)
          '())) ;redundant event

       (default-val (or (get1 :default-base-value kwd-alist) (funcall-w enum (list 0) ctx wrld)))
       (kwd-alist (put-assoc-eq :default-base-value default-val kwd-alist))

       (kwd-alist (put-assoc-eq :min-rec-depth (or (get1 :min-rec-depth kwd-alist) 0) kwd-alist))
       (kwd-alist (put-assoc-eq :max-rec-depth (or (get1 :max-rec-depth kwd-alist) 30) kwd-alist))

       ;(- (cw "** default value of ~x0 is ~x1" enum default-val))

       )

    `(ENCAPSULATE
      nil
      (LOGIC)
      (WITH-OUTPUT
       :SUMMARY-OFF (:OTHER-THAN ACL2::FORM) :ON (ERROR)
       (PROGN
        ,@(AND (table-alist 'ACL2::ACL2S-DEFAULTS-TABLE wrld)
               '((LOCAL (ACL2::ACL2S-DEFAULTS :SET :TESTING-ENABLED :NAIVE))))
        ;;(defstub ,enum-name (*) => *)
        (encapsulate
         (((,enum-name *) => * :formals ,enum-formals :guard ,enum-guard))
         (local (defun ,enum-name ,enum-formals
                  (declare (xargs :guard ,enum-guard))
                  (declare (ignorable . ,enum-formals))
                  ',default-val))
         ;; (defthm ,(s+ enum-name "-IS-OF-TYPE-" pred-name)
         ;;   (,pred-name (,enum-name . ,enum-formals)))
         )

        ;;(defstub ,enum/acc-name (* *) => (mv * *))
        ,@(and (not enum/acc) (make-enum-uniform-defun-ev enum/acc-default enum-name))
        (encapsulate
         (((,enum/acc-name * *) => (mv * *) :formals ,enum/acc-formals :guard ,enum/acc-guard))
         (local (defun ,enum/acc-name ,enum/acc-formals
                  (declare (xargs :guard ,enum/acc-guard))
                  (declare (ignorable . ,enum/acc-formals))
                  (mv ',default-val 0))))

        (DEFTTAG :defdata-attach)
        (DEFATTACH (,enum-name ,enum) :skip-checks t)
        (DEFATTACH (,enum/acc-name ,(or enum/acc enum/acc-default)) :skip-checks t)
        (DEFTTAG nil)
        (TABLE TYPE-METADATA-TABLE ',name ',kwd-alist)
        (VALUE-TRIPLE :REGISTERED)
        )))
     ))

(defmacro register-type (name &rest keys)
  (b* ((verbosep (let ((lst (member :verbose keys)))
                   (and lst (cadr lst))))
       (ctx 'register-type)
       ((unless (and (member :predicate keys) (member :enumerator keys)))
        (er hard ctx "~| Keyword args predicate, enumerator are mandatory.~%")))
    `(encapsulate
      nil
      (with-output
       ,@(if verbosep '(:on :all) '(:on error)) :stack :push
       (make-event
        (register-type-fn ',name ',keys ',ctx (current-package state) (w state)))))))

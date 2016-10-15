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


(defconst *register-type-keywords*
  '(:predicate :enumerator ;mandatory names
               :enum/acc
               :equiv :equiv-fixer
               :fixer :fixer-domain
               :lub :glb
               :sampling
               :size
               :verbose :hints
               :theory-name
               :clique :def :normalized-def :prettyified-def ;defdata
               ))

; [2015-07-01 Wed] enumerator and enum/acc are attachable functions

(defun register-type-fn (name args ctx pkg wrld)
  (declare (xargs :mode :program))
  (b* (((mv kwd-alist rest) (extract-keywords ctx *register-type-keywords* args nil))
       ((when rest) (er hard? ctx "~| Extra args: ~x0~%" rest))
       ((unless (proper-symbolp name)) (er hard? ctx "~| ~x0 should be a proper symbol.~%" name))
       
       
       ((unless (well-formed-type-metadata-p kwd-alist wrld))
        (er hard? ctx "~| ~s0~%" (ill-formed-type-metadata-msg kwd-alist wrld)))
       
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

       ((when (eq enum enum-name))
        (er hard? ctx "~| Please rename the enumerator ~x0 to be different from ~x1, to which it will be attached.~%" enum enum-name))
       ((when (eq enum/acc enum/acc-name))
        (er hard? ctx "~| Please rename the enumerator ~x0 to be different from ~x1, to which it will be attached.~%" enum/acc enum/acc-name))
       
       (enum/acc-default (s+ enum/acc-name '|-BUILTIN|))
       (kwd-alist (put-assoc-eq :enumerator enum-name kwd-alist))
       (kwd-alist (put-assoc-eq :enum/acc enum/acc-name kwd-alist))
       
       (kwd-alist (put-assoc-eq :size (or (get1 :size kwd-alist) 't) kwd-alist))
       (kwd-alist (put-assoc-eq :theory-name (or (get1 :theory-name kwd-alist) (s+ name 'theory)) kwd-alist))

       (existing-entry (assoc-eq name (table-alist 'type-metadata-table wrld)))
       ((when existing-entry)
        (if (not (equal kwd-alist (cdr existing-entry)))
            (er hard? ctx "~| ~x0 is already a registered defdata type.~%" name)
          '())) ;redundant event

       (default-val (funcall-w enum (list 0) ctx wrld))
       (- (cw "** default value of ~x0 is ~x1" enum default-val))

       )
    
    `(ENCAPSULATE
      nil
      (LOGIC)
      (WITH-OUTPUT
       :SUMMARY (ACL2::FORM) :ON (ERROR)
       (PROGN
        ;;(defstub ,enum-name (*) => *)
        (encapsulate 
         (((,enum-name *) => * :formals ,enum-formals :guard ,enum-guard))
         (local (defun ,enum-name ,enum-formals
                  (declare (xargs :guard ,enum-guard))
                  (declare (ignorable . ,enum-formals))
                  ',default-val)))
        
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
    `(with-output ,@(if verbosep '(:on :all) '(:on error)) :stack :push
       (make-event
        (register-type-fn ',name ',keys ',ctx (current-package state) (w state))))))





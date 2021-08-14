#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
API to register a user-defined combinator
author: harshrc
file name: register-combinator.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "defdata-util")


; USER COMBINATOR TABLE
(defun get-defconst-val (x wrld)
  (cadr (acl2-getprop x 'acl2::const wrld)))

(def-const *register-user-combinator-keywords*
'(:arity :aliases :expansion :verbose
         :syntax-restriction-fn :syntax-restriction-msg 
        ; :local-theory-template :theory-template
         :polymorphic-type-form :polymorphic-events
         :pre-pred-hook-fns :in-pred-hook-fns :post-pred-hook-fns 
         :post-hook-fns
         ))

(defun register-user-combinator-fn (name args ctx wrld)
  (declare (ignorable wrld))
  (b* (((mv kwd-alist rest)
        (extract-keywords ctx *register-user-combinator-keywords* args nil nil))
       ((when rest) (er hard? ctx "~| Extra args: ~x0~%" rest))
       ((unless (proper-symbolp name)) (er hard? ctx "~| ~x0 should be a proper symbol.~%" name))
       ;; ((unless (well-formed-type-metadata-p kwd-alist wrld))
       ;;  (er hard? ctx "~| ~s0~%" (ill-formed-type-metadata-entry-msg kwd-alist wrld)))
       
       (aliases (union-eq (list name) (get1 :aliases kwd-alist)))
       (theory-name (get1 :theory-name  kwd-alist (symbol-fns::suffix name '-theory)))
       (kwd-alist (put-assoc-eq :aliases aliases kwd-alist))
       (kwd-alist (put-assoc-eq :theory-name theory-name kwd-alist))
       
       ;; (le (get1 :local-theory-template  kwd-alist))
       ;; (local-theory-template (if (legal-constantp le)
       ;;                   (get-defconst-val le wrld)
       ;;                 le))
       ;; (ex-dt (get1 :theory-template  kwd-alist))
       ;; (theory-template (if (legal-constantp ex-dt)
       ;;                     (get-defconst-val ex-dt wrld)
       ;;                   ex-dt))
       ;; (kwd-alist (put-assoc-eq :theory-template theory-template kwd-alist))
       ;; (kwd-alist (put-assoc-eq :local-theory-template local-theory-template kwd-alist))
       )
       
       
                       
  `((table user-combinator-table ',name ',kwd-alist)
    (add-pre-post-hook defdata-defaults-table :pre-pred-hook-fns ',(get1 :pre-pred-hook-fns kwd-alist) )
    (add-pre-post-hook defdata-defaults-table :in-pred-hook-fns ',(get1 :in-pred-hook-fns kwd-alist))
    (add-pre-post-hook defdata-defaults-table :post-pred-hook-fns ',(get1 :post-pred-hook-fns kwd-alist))
    (add-pre-post-hook defdata-defaults-table :post-hook-fns ',(get1 :post-hook-fns kwd-alist))
    )))

(logic)
(defmacro register-user-combinator (name &rest keys) 
  (b* ((verbosep (let ((lst (member :verbose keys)))
                   (and lst (cadr lst))))
       (ctx 'register-user-combinator)
       ((unless (and (member :arity keys) (member :expansion keys)))
        (er hard? ctx "~| Keyword args arity, expansion are mandatory.~%")))
    `(with-output ,@(and (not verbosep) '(:off :all :on comment)) :stack :push
       (make-event
        (cons 'PROGN 
              (register-user-combinator-fn ',name ',keys ',ctx (w state)))))))


  

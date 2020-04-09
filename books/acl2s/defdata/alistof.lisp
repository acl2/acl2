#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
alist support in core defdata language
author: harshrc
file name: alistof.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "data-structures/utilities" :dir :system)
(include-book "coi/symbol-fns/symbol-fns" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "register-combinator")


(defconst *alistof-export-defthms*
  '((defthm _pred_-IMPLIES-ALISTP
      (implies (_PRED_ x)
               (alistp x))
      :hints (("Goal" :in-theory (enable _PRED_ alistp)))
      :rule-classes ((:forward-chaining)
                     ;(:rewrite :backchain-limit-lst 1)
                     ))

    (defthm _PRED_-IMPLIES-TLP
      (implies (_PRED_ x)
               (true-listp x))
      :hints (("Goal" :in-theory (disable _PRED_ true-listp)))
      :rule-classes ((:forward-chaining)
                     (:compound-recognizer)
                     ;(:rewrite :backchain-limit-lst 1)
                     ))

;Rather do this using polymorphic sig infrastructure TODO
    ;; (:@ :symbol-alist-subtype-p
    ;;     (defthm _PRED_-SUBTYPE-OF-SYMBOL-ALIST
    ;;       (implies (_PRED_ x)
    ;;                (acl2::symbol-alistp x))
    ;;       :rule-classes :tau-system)
    ;;     )
    ))

(program)

(defun alistof-theory-events (name keybody valbody new-types kwd-alist wrld)
  (declare (ignorable valbody))
  (declare (xargs :mode :program))
;assumption: key/val body are core defdata exps (holds because user-combinators occur only at top-level)
  (b* ((M (append new-types (table-alist 'type-metadata-table wrld)))
       (A (table-alist 'type-alias-table wrld))
       (pred (predicate-name name A M))
       ((when (not (proper-symbolp pred)))
        (er hard? 'alistof-theory-events
            "~| Couldnt find predicate name for ~x0.~%" name))
       ((mv symbol-alist-subtypep ?keypred) 
        (if (and (proper-symbolp keybody) (assoc-eq keybody M))
            (mv (subtype-p (predicate-name keybody A M)
                           'acl2::symbolp
                           wrld)
                (predicate-name keybody A M))
          (mv nil :undef)))
       (disabled (get1 :disabled  kwd-alist))
       (curr-pkg (get1 :current-package kwd-alist))
       (pkg-sym (pkg-witness curr-pkg))
       (local-events-template nil)
       (export-defthms-template *alistof-export-defthms*)
       (features (and symbol-alist-subtypep '(:symbol-alist-subtype-p)))
       (splice-alist `((_disabled-runes_ . ,disabled)))
       (atom-alist `((_PRED_ . ,pred) (_KEYPRED_ . ,keypred)))
       (str-alist `(("_PRED_" . ,(symbol-name pred)) ("_KEYPRED_" . ,(symbol-name keypred))))
       (local-events (template-subst local-events-template
                                     :features features
                                     :splice-alist splice-alist
                                     :atom-alist atom-alist
                                     :str-alist str-alist
                                     :pkg-sym pkg-sym))
       (export-defthms (template-subst export-defthms-template
                                     :features features
                                     :splice-alist splice-alist
                                     :atom-alist atom-alist
                                     :str-alist str-alist
                                     :pkg-sym pkg-sym))
       (all-defthm-names (get-event-names export-defthms))
       (theory-name (get1 :theory-name  kwd-alist))

       )
    `(,@(and local-events `((local (progn . ,local-events))))
      ,@export-defthms ;definitely not empty
      (acl2::def-ruleset! ,theory-name ',all-defthm-names)
      )))

(defun alistof-theory-ev (p top-kwd-alist wrld)
  (b* (((cons name A) p)
       ((acl2::assocs pdef new-types kwd-alist) A) ;ignore odef
       (kwd-alist (append kwd-alist top-kwd-alist)))
       
    (case-match pdef
      (('ALISTOF key-body val-body) (alistof-theory-events name key-body val-body new-types kwd-alist wrld))
      (& '()))))

(defloop user-alistof-theory-events1 (ps kwd-alist wrld)
  (for ((p in ps)) (append (alistof-theory-ev p kwd-alist wrld))))

(defun user-alistof-theory-events (ps kwd-alist wrld)
  (b* ((events (user-alistof-theory-events1 ps kwd-alist wrld)))
    (and (consp events)
         (append
          `((commentary ,(get1 :print-commentary kwd-alist) "~| Alistof theory events...~%")
            (value-triple
             (progn$
              (time-tracker :alistof-theory-events :end)
              (time-tracker :alistof-theory-events :init
                            :times '(2 7)
                            :interval 5
                            :msg "Elapsed runtime in theory events for alistof is ~st secs;~|~%")
              :invisible)))
          
          events))))

(logic)
(deflabel alistof)
(register-user-combinator alistof 
 :arity 2 :verbose t
 :aliases (acl2::alistof)
 :expansion (lambda (_name _args) `(OR nil (acons ,(car _args) ,(cadr _args) ,_name)))
 :syntax-restriction-fn proper-symbol-listp
 :syntax-restriction-msg "alistof syntax restriction: ~x0 should be type names."
 :polymorphic-type-form (alistof :a :b)
 :post-pred-hook-fns (user-alistof-theory-events))

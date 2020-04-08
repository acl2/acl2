#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
list support in core defdata language
author: harshrc
file name: listof.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "tools/templates" :dir :system)
(include-book "register-combinator")


(defconst *listof-export-defthms*
  '((defthm _PRED_-IMPLIES-TLP
      (implies (_PRED_ x)
               (true-listp x))
;ASK Pete: true-listp is disabled in the std/lists theory, earlier we used coi/lists/basic, where it was enabled! Which to use?
      :hints (("Goal" :in-theory (enable true-listp)))
      :rule-classes ((:forward-chaining)
                     (:compound-recognizer)
                     (:rewrite :backchain-limit-lst 1)))
    (:@ :atom-list-subtype-p
        (defthm _PRED_-SUBTYPE-OF-ATOM-LIST
          (implies (_PRED_ x)
                   (atom-listp x))
          :rule-classes :tau-system)
          )))

(program)

(defun listof-theory-events (name cbody new-types kwd-alist wrld)
  (declare (xargs :mode :program))
;assumption: cbody is a core defdata exp (holds because user-combinators occur only at top-level)
  (b* ((M (append new-types (table-alist 'type-metadata-table wrld)))
       (A (table-alist 'type-alias-table wrld))
       (pred (predicate-name name A M))
       ((when (not (proper-symbolp pred)))
        (er hard? 'listof-theory-events
            "~| Couldnt find predicate name for ~x0.~%" name))
       ((mv atom-list-subtypep ?cpred) 
        (if (and (proper-symbolp cbody) (assoc-eq cbody M))
            (mv (subtype-p (predicate-name cbody A M)
                           'acl2::atom wrld)
                (predicate-name cbody A M))
          (mv nil :undef)))
       (disabled (get1 :disabled  kwd-alist))
       (curr-pkg (get1 :current-package kwd-alist))
       (pkg-sym (pkg-witness curr-pkg))
       (local-events-template nil)
       (export-defthms-template *listof-export-defthms*)

       (features (and atom-list-subtypep '(:atom-list-subtype-p)))
       (splice-alist `((_disabled-runes_ . ,disabled)))
       (atom-alist `((_PRED_ . ,pred) (_CPRED_ . ,cpred)))
       (str-alist `(("_PRED_" . ,(symbol-name pred)) ("_CPRED_" . ,(symbol-name cpred))))
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
      ,@export-defthms ;shouldnt be empty
      (acl2::def-ruleset! ,theory-name ',all-defthm-names)
      )))

(defun listof-theory-ev (p top-kwd-alist wrld)
  (b* (((cons name A) p)
       ((acl2::assocs pdef new-types kwd-alist) A) ;replace odef with pdef
       (kwd-alist (append kwd-alist top-kwd-alist)))
    (case-match pdef
      (('LISTOF cbody) (listof-theory-events name cbody new-types kwd-alist wrld))
      (& '()))))

(defloop user-listof-theory-events1 (ps kwd-alist wrld)
  (for ((p in ps)) (append (listof-theory-ev p kwd-alist wrld))))

(defun user-listof-theory-events (ps kwd-alist wrld)
  (b* ((events (user-listof-theory-events1 ps kwd-alist wrld)))
    (and (consp events)
         (append
          `((commentary ,(get1 :print-commentary kwd-alist) "~| Listof theory events...~%")
            (value-triple
             (progn$
              (time-tracker :listof-theory-events :end)
              (time-tracker :listof-theory-events :init
                            :times '(2 7)
                            :interval 5
                            :msg "Elapsed runtime in theory events for listof is ~st secs;~|~%")
              :invisible)))
          events))))

(logic)
(deflabel listof)
(register-user-combinator listof 
                          :arity 1 :verbose t
                          :aliases (subset acl2::subset acl2::listof)
                          :expansion (lambda (_name _args) `(OR nil (cons ,(car _args) ,_name)))
                          :polymorphic-type-form (listof :a)
                          :post-pred-hook-fns (user-listof-theory-events))

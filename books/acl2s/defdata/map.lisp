#|$ACL2s-Preamble$;
(include-book ;; Newline to fool ACL2/cert.pl dependency scanner
 "../portcullis")
(acl2::begin-book t);$ACL2s-Preamble$|#

#|
maps support in core defdata language
author: harshrc
file name: map.lisp
date created: [2014-08-06 Sun]
data last modified: [2014-08-06]
|#

(in-package "DEFDATA")

(include-book "data-structures/utilities" :dir :system)
(include-book "coi/symbol-fns/symbol-fns" :dir :system)
(include-book "tools/templates" :dir :system)
(include-book "register-combinator")

(defconst *map-local-events* '())



(defconst *map-export-defthms*
  '((defthm _pred_-IMPLIES-GOOD-MAP
      (implies (_pred_ x)
               (acl2::good-map x))
      :hints (("goal" :in-theory (e/d (_pred_))))
      :rule-classes ((:rewrite :backchain-limit-lst 1) 
                     (:forward-chaining)))
    
    (defthm _pred_-EXCLUDES-ATOM-LIST
      (implies (and (_pred_ x)
                    (consp x))
               (not (atom-listp x)))
      :hints (("goal" :in-theory (e/d (_pred_) )))
      :rule-classes (:tau-system))
    
    (defthm _pred_-MAP-IDENTITY2-GENERALIZE
      (implies (_pred_ x)
               (_pred_ (acl2::map-identity2 a x)))
      :rule-classes (:generalize))

    (:@ :key-is-typename
        (defthm DISJOINT-_pred_-_keypred_
          (implies (_pred_ x)
                   (not (_keypred_ x)))
          :rule-classes :tau-system
          :hints (("Goal" :in-theory (e/d (_pred_ _keypred_)))))

        (defthm _keypred_-IS-WELL-FORMED
          (implies (_keypred_ x)
                   (acl2::wf-keyp x))
          :rule-classes ((:rewrite :backchain-limit-lst 1)
                         (:forward-chaining)))
        
        (defthm _pred_-DOMAIN-LEMMA
          (implies (and (_pred_ x)
                        (mget a x))
                   (_keypred_ a))
          :hints (("Goal" :in-theory (e/d 
                                      (_pred_ mget acl2::extensible-records)
                                      (_keypred_))))
          :rule-classes (;(:rewrite :backchain-limit-lst 1)
                         :forward-chaining :generalize))

        ;; added on jmitesh's request.
        (defthm DELETING-AN-ENTRY-IN-_pred_
          (implies (and (_pred_ x)
                        (_keypred_ a))
                   (_pred_ (mset a nil x)))
          :hints (("Goal" :in-theory (e/d (acl2::extensible-records)))))


        )

    (:@ (ACL2::AND :key-is-typename :val-is-typename)

        (defthm _pred_-SELECTOR
          (implies (and (_pred_ x)
                        (mget acl2::a x))
                   (_valpred_ (mget acl2::a x)))
          :hints (("Goal" :in-theory (e/d 
                                      (_pred_ mget acl2::extensible-records)
                                      (_keypred_ _valpred_)))))


        (defthm _pred_-SELECTOR-generalize
          (implies (and (_pred_ x)
;(mget acl2::a x) shifted below
                        )
                   (or (_valpred_ (mget acl2::a x))
                       (equal (mget acl2::a x) nil)))
          :hints (("Goal" :in-theory (e/d 
                                      (_pred_ mget acl2::extensible-records)
                                      (_keypred_ _valpred_))))
          :rule-classes :generalize)

        ;; (local
        ;;  (defthm _pred_MODIFIER-SUPPORT
        ;;    (implies (and (_pred_ x)
        ;;                  (_keypred_ acl2::a)
        ;;                  (_valpred_ v))
        ;;             (_pred_ (acl2::mset-wf acl2::a v x)))
        ;;    :hints (("Goal" :induct (acl2::good-map x)
        ;;             :in-theory (e/d (_pred_ acl2::good-map acl2::mset-wf)
        ;;                             (_keypred_ _valpred_ acl2::wf-keyp))))))
        (defthm _pred_-MODIFIER
          (implies (and (_pred_ x)
                        (_keypred_ acl2::a)
                        (_valpred_ v))
                   (_pred_ (mset acl2::a v x)))
          :hints (("Goal" :in-theory 
                   (e/d (_pred_ mset acl2::extensible-records)
                        (_keypred_ _valpred_ acl2::wf-keyp))))
          :rule-classes (:rewrite :generalize)))
    

    
    
    ))

(defun map-attach-constraint-rules-ev (p wrld)
  (b* (((cons name A) p)
       ((acl2::assocs pdef new-types) A)) ;what about pdef?
       
    (case-match pdef
      (('MAP keybody valbody)
       (b* ((M (append new-types (type-metadata-table wrld)))
            (A (type-alias-table wrld))
            (pred (predicate-name name A M))
            (?keypred (and (proper-symbolp keybody)
                           (assoc-eq keybody M)
                           (predicate-name keybody A M)))
            (?valpred (and (proper-symbolp keybody)
                           (assoc-eq keybody M)
                           (predicate-name valbody A M))))
         `((defdata-attach ,name
             :constraint (mget a x) ;x is the variable of this type
             :constraint-variable x
             :rule (implies (and (,keypred a)
                                 (,valpred x.a)
                                 (,pred x1))
                            (equal x (mset a x.a x1)))
             :meta-precondition (or (acl2::variablep a)
                                    (fquotep a)) ;not completely sound, since (mget a x) might be nil
             :match-type :subterm-match))))

      (& '()))))
             

(defloop map-attach-constraint-rules-events (ps kwd-alist wrld)
  (declare (ignorable kwd-alist))
  (for ((p in ps)) (append (map-attach-constraint-rules-ev p wrld))))


(program)

(defun map-theory-events (name keybody valbody new-types kwd-alist wrld)
 ; (declare (xargs :mode :program))
;assumption: key/val body are core defdata exps (holds because user-combinators occur only at top-level)
  (b* ((M (append new-types (type-metadata-table wrld)))
       (A (type-alias-table wrld))
       (pred (predicate-name name A M))
       ((when (not (proper-symbolp pred)))
        (er hard? 'map-theory-events
            "~| Couldnt find predicate name for ~x0.~%" name))
       ((mv ?symbol-alist-subtypep ?keypred) 
        (if (and (proper-symbolp keybody) (assoc-eq keybody M))
            (mv (subtype-p (predicate-name keybody A M)
                           'acl2::symbolp wrld)
                (predicate-name keybody A M))
          (mv nil nil))) ;inconsistent with earlier use of :undef
       (?valpred (and (proper-symbolp keybody)
                      (assoc-eq keybody M)
                      (predicate-name valbody A M)))

       (disabled (get1 :disabled kwd-alist))
       (curr-pkg (get1 :current-package kwd-alist))
       (pkg-sym (pkg-witness curr-pkg))
       (disabled (cons 'acl2::mset-diff-mset disabled))
       (local-events-template *map-local-events*)
       (export-defthms-template *map-export-defthms*)
       (features (append (and keypred '(:key-is-typename)) (and valpred '(:val-is-typename))))
       (splice-alist `((_disabled-runes_ . ,disabled)))
       (atom-alist `((_PRED_ . ,pred) (_TYPENAME_ . ,name) (_KEYPRED_ . ,keypred) (_VALPRED_ . ,valpred)))
       (str-alist `(("_PRED_" . ,(symbol-name pred)) ("_KEYPRED_" . ,(symbol-name keypred)) ("_VALPRED_" . ,(symbol-name valpred))))
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
       (theory-name (get1 :theory-name kwd-alist))

       )
    `(,@(and local-events `((local (progn . ,local-events))))
      ,@export-defthms ;definitely not empty
      (acl2::def-ruleset! ,theory-name ',all-defthm-names)
      )))

(defun map-theory-ev (p top-kwd-alist wrld)
  (b* (((cons name A) p)
       ((acl2::assocs pdef new-types kwd-alist) A) ;what about pdef?
       (kwd-alist (append kwd-alist top-kwd-alist)))
       
    (case-match pdef
      (('MAP key-body val-body) (map-theory-events name key-body val-body new-types kwd-alist wrld))
      (& '()))))
             

(defloop user-map-theory-events1 (ps kwd-alist wrld)
  (for ((p in ps)) (append (map-theory-ev p kwd-alist wrld))))

(defun user-map-theory-events (ps kwd-alist wrld)
  (b* ((events (user-map-theory-events1 ps kwd-alist wrld)))
    (and (consp events)
         (append
          `((commentary ,(get1 :print-commentary kwd-alist) "~| Map theory events...~%")
            (value-triple
             (progn$
              (time-tracker :map-theory-events :end)
              (time-tracker :map-theory-events :init
                            :times '(2 7)
                            :interval 5
                            :msg "Elapsed runtime in theory events for maps is ~st secs;~|~%")
              :invisible)))
          events))))
      

(logic)
(deflabel map)
(register-user-combinator map
                          :arity 2 :verbose t
                          :aliases (acl2::map)
                          :expansion (lambda (_name _args) `(OR nil (mset ,(car _args) ,(cadr _args) ,_name)))
                          :syntax-restriction-fn proper-symbol-listp
                          :syntax-restriction-msg "map syntax restriction: ~x0 should be type names."
                          :polymorphic-type-form (alistof :a :b)
                          ;; :local-events *map-local-events*
                          ;; :export-defthms *map-export-defthms*
                          :post-pred-hook-fns (user-map-theory-events)
                          :post-hook-fns (map-attach-constraint-rules-events))


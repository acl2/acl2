;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "TYPES")

(include-book "type-fty")
(include-book "type-fix")
(include-book "kwargs")

(defun field-access (field str)
  (safe-packn-pos (list str '-> field) str))

(defun structure-field-access-functions (str body)
  (if (not (consp body)) nil
    (let ((entry (car body)))
      (cons (field-access (car entry) str)
            (structure-field-access-functions str (cdr body))))))

(defun equal-structure-fields (str body x y)
  (if (not (consp body)) nil
    (let ((entry (car body)))
      (cons `(equal (,(field-access (car entry) str) ,x)
                    (,(field-access (car entry) str) ,y))
            (equal-structure-fields str (cdr body) x y)))))

(defun add-rule-classes (str instance body)
  (if (not (consp body)) nil
    (let ((entry (car body)))
      (let ((access (field-access (car entry) str)))
        (cons `(,@entry :rule-classes (:rewrite (:forward-chaining :trigger-terms ((,access ,instance)))))
              (add-rule-classes str instance (cdr body)))))))

;; (defun fix-constant-rewrite (field)
;;   (let ((access ()))
;;     `(:rewrite ,(safe access '-of- fix '-instance-normalize-const 

;; (defun fix-constant-rewrites (body)
;;   (if (not (consp body)) nil
;;     (let ((entry (car body)))
;;       (cons (fix-constant-rewrite (car entry))
;;             (fix-constant-rewrites (cdr body))))))

(defmacro def::type-str (name body &rest args)
  (b* ((name-p      (safe-packn-pos (list name '-p)      name))
       (name-fix    (safe-packn-pos (list name '-fix)    name))
       (name-fix!   (safe-packn-pos (list name '-fix!)   name))
       (name-equiv  (safe-packn-pos (list name '-equiv)  name))
       (name-instance (safe-packn-pos (list name '-instance) name))
       (equal-name-fix-to-name-equiv-rewrite
        (safe-packn-pos (list 'equal- name-fix '-to- name-equiv '-rewrite) name))
       (equal-name-fix-to-name-equiv-forward
        (safe-packn-pos (list 'equal- name-fix '-to- name-equiv '-forward) name))
       (name-extensionality
        (safe-packn-pos (list name '-extensionality) name))
       (name-extensionality-rewrite
        (safe-packn-pos (list name-extensionality '-rewrite) name))
       (name-equiv-reduction
        (safe-packn-pos (list name-equiv '-reduction) name))
       ;;((mv non-executable args) (extract-keyword-value :non-executable nil args))
       ((mv reduce-equiv args) (extract-keyword-value :reduce-equiv nil args))
       ((mv equal-fix-rule-class args) (extract-keyword-value :equal-fix-rule-class nil args))
       )
    `(progn
       
       (fty::defprod ,name
         ,(add-rule-classes name name-instance body)
         ,@args
         :inline nil
         :xvar ,name-instance
         )

       ;;,@(and non-executable `((in-theory (disable ,@(fix-constant-rewrites body)))))
       
       (defthmd ,name-equiv-reduction
         (implies
          (and
           (syntaxp (and (not (equal (car x) ',name-fix))
                         (not (equal (car y) ',name-fix))))
           (and (,name-p x) (,name-p y)))
          (iff (,name-equiv x y)
               (equal x y)))
         :rule-classes ((:rewrite :backchain-limit-lst 0)))
       
       (defthmd ,equal-name-fix-to-name-equiv-forward
         (implies
          (equal (,name-fix x) y)
          (,name-equiv x y))
         :rule-classes (:forward-chaining
                        (:forward-chaining
                         :corollary (implies
                                     (equal y (,name-fix x))
                                     (,name-equiv y x)))))
       
       (defthm ,equal-name-fix-to-name-equiv-rewrite
         (and (equal (equal (,name-fix x) y)
                     (and (,name-p y)
                          (,name-equiv x y)))
              (equal (equal y (,name-fix x))
                     (and (,name-p y)
                          (,name-equiv x y)))))

       (defthmd ,name-extensionality
         (equal (,name-equiv x y)
                (and ,@(equal-structure-fields name body 'x 'y)))
         :hints (("Goal" :in-theory (enable ,name-fix
                                            ,@(structure-field-access-functions name body)
                                            ))))
       
       (defthm ,name-extensionality-rewrite
         (implies
          (acl2::in-conclusion-check (,name-equiv x y) :top :negated)
          (equal (,name-equiv x y)
                 (and ,@(equal-structure-fields name body 'x 'y))))
         :hints (("Goal" :in-theory (enable ,name-extensionality))))

       (in-theory (disable ,equal-name-fix-to-name-equiv-rewrite ,name-equiv))
       
       ;;
       ;; This wasn't working because there is no (:definition ,name-equiv) .. argh!
       ;;
       (theory-invariant
        (incompatible
         (:rewrite ,equal-name-fix-to-name-equiv-rewrite)
         (:definition ,name-equiv)))
       (theory-invariant
        (incompatible
         (:rewrite ,equal-name-fix-to-name-equiv-rewrite)
         (:definition ,(safe-packn-pos (list name-equiv '$inline) name))))

       (in-theory (enable
                   ,@(and reduce-equiv  `(,name-equiv-reduction))
                   ,@(and (member equal-fix-rule-class '(:all :rewrite))
                          `(,equal-name-fix-to-name-equiv-rewrite))
                   ,@(and (member equal-fix-rule-class '(:all :forward-chaining))
                          `(,equal-name-fix-to-name-equiv-forward))
                   ))
       
       (def::un ,name-fix! (x)
         (declare (xargs :signature ((t) ,name-p)))
         (with-guard-checking :none (ec-call (,name-fix x))))
       
       (fty::add-fix! ,name :fix! ,name-fix!)
       
       )))

(defun field-bindings (name fields args)
  (if (not (consp fields)) nil
    (let ((field (car fields)))
      (cons `(,field (,(field-access field name) ,@args))
            (field-bindings name (cdr fields) args)))))

(defun field-name-list (fields)
  (if (not (consp fields)) nil
    (let* ((entry (car fields))
           (field (car entry)))
      (cons field (field-name-list (cdr fields))))))

(defun field-predicates (fields fty-alist)
  (if (not (consp fields)) nil
    (let* ((entry (car fields))
           (field (car entry))
           (type  (cadr entry)))
      (let* ((entry  (fty::get-entry type fty-alist))
             (type-p (fty::get-key  'fty::pred entry)))
        (cons `(,type-p ,field)
              (field-predicates (cdr fields) fty-alist))))))

(defun body-body (body)
  (if (not body) nil
    (case-match body
      (('and . args)  args)
      (('or . &)      (assert! nil ("def::type-str-refinement does not support disjunctions")))
      (&              (list body)))))

(defun def-type-str-refinement-predicate (type-name type-p args guard non-executable refines root fields bind body in-theory disable fty-alist)
  (let* ((type-p  (default-name type-p     type-name '-p     type-name))
         (body    (body-body body))
         (entry   (fty::get-entry refines fty-alist))
         (rtype-p (fty::get-key  'fty::pred entry))
         (decls    `(declare (type t ,@args) (xargs ,@(and guard `(:guard ,guard)) ,@(and non-executable `(:non-executable t)))))
         (field-preds    (field-predicates fields fty-alist))
         (fields         (append (field-name-list fields) bind))
         (field-bindings (field-bindings root fields args))
         )
    (let ((body `(and (,rtype-p ,@args)
                      (let (,@field-bindings)
                        (declare (ignorable ,@fields))
                        (and ,@field-preds
                             ,@body)))))
      `(encapsulate
           ()

         ;;(local (in-theory (theory 'acl2::minimal-theory)))
         ,@(and in-theory `((local (in-theory ,in-theory))))
         
         (defun ,type-p ,args
           ,decls
           ,body)
         
         (defthm ,(safe-packn-pos (list type-name '-implies) type-name)
           (implies
            (,type-p ,@args)
            ,body)
           :rule-classes (:rewrite :forward-chaining))
       
         (defthm ,(safe-packn-pos (list 'implies- type-name) type-name)
           (implies
            ,body
            (,type-p ,@args)))
         
         ,@(and disable `((in-theory (disable ,type-p))))
         ,@(and non-executable `((in-theory (disable (,type-p)))))
         
         ))))

(set-state-ok t)

(defun def-type-str-refinement-predicate-wrapper (type-name type-p args guard non-executable refines root fields bind body in-theory disable state)
  (declare (xargs :stobjs state :mode :program))
  (let ((fty-alist (fty::get-fixtypes-alist (w state))))
    (let ((root (or root refines)))
      (def-type-str-refinement-predicate type-name type-p args guard non-executable refines root fields bind body in-theory disable fty-alist))))
  
(defmacro def::type-str-refinement-predicate (type-name
                                              args 
                                              &key
                                              (type-p 'nil)
                                              (guard 'nil) (non-executable 'nil) (refines 'nil) (root 'nil) (fields 'nil) (bind 'nil) (body 'nil) (in-theory 'nil) (disable 'nil))
  `(make-event (def-type-str-refinement-predicate-wrapper ',type-name ',type-p ',args ',guard ',non-executable ',refines ',root ',fields ',bind ',body ',in-theory ',disable state)))

(defun fix-fields (root var fields fty-alist)
  (if (not (consp fields)) nil
    (let* ((entry (car fields))
           (field (car entry))
           (type  (cadr entry))
           (entry (fty::get-entry type fty-alist))
           (fix   (fty::get-key 'fty::fix! entry))
           (key   (safe-packn-pos (list field) :key)))
      (list* key
             `(,fix (,(field-access field root) ,var))
             (fix-fields root var (cdr fields) fty-alist)))))

(defun def-type-str-refinement-fix (type-name
                                    type-p
                                    fields
                                    refines
                                    root   
                                    fix
                                    fix!
                                    open-default
                                    disable
                                    non-executable
                                    in-theory
                                    fty-alist)
  (let* ((type-p  (default-name type-p type-name '-p    type-name))
         (fix!    (default-name fix!   type-name '-fix! type-name))
         (fix     (type-fix     fix    type-name fix!   type-name))
         (entry          (fty::get-entry refines fty-alist))
         (rtype-fix!     (fty::get-key 'fty::fix! entry))
         (field-updates  (fix-fields root 'x fields fty-alist))
         (change-root    (safe-packn-pos (list 'change- root) root)))
    `(encapsulate
         ()
       
       (def::un ,fix! (x)
         (declare (xargs :signature ((t) ,type-p)
                         ,@(and  non-executable `(:non-executable t))))
         (let ((x (,rtype-fix! x)))
           (,change-root x ,@field-updates)))

       ,@(and non-executable `((in-theory (disable (,fix)))))
       
       ,@(standard-fixing-rules fix! type-p nil)

       (def::type-fix ,type-name
         :type-p ,type-p
         :fix   ,fix
         :fix!  ,fix!
         :open-fix-default ,open-default
         :prefer-guarded nil
         :non-executable ,non-executable
         :fix-in-theory ,in-theory
         :fix-signature nil
         :disable-fix ,disable
         )
       
       )))

(defun def-type-str-refinement-fix-wrapper (type-name
                                            type-p
                                            fields
                                            refines
                                            root   
                                            fix
                                            fix!
                                            open-default
                                            disable
                                            non-executable
                                            in-theory
                                            state)
  (declare (xargs :stobjs state :mode :program))
  (let ((fty-alist (fty::get-fixtypes-alist (w state))))
    (let ((root (or root refines)))
      (def-type-str-refinement-fix type-name
        type-p
        fields
        refines
        root   
        fix
        fix!
        open-default
        disable
        non-executable
        in-theory
        fty-alist))))

(defmacro def::type-str-refinement-fix (type-name &rest kvlist)
  (b* ((kwargs (kwargs (def-type-str-refinement-keywords) kvlist))
       ((&key type-p fields refines root fix fix! open-fix-default disable-fix non-executable fix-in-theory) kwargs)
       (in-theory fix-in-theory)
       (disable   disable-fix)
       (open-default open-fix-default))
    `(make-event
      (def-type-str-refinement-fix-wrapper
        ',type-name
        ',type-p
        ',fields
        ',refines
        ',root
        ',fix
        ',fix!
        ',open-default
        ',disable
        ',non-executable
        ',in-theory
        state))))

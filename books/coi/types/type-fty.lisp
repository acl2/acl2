;;  
;; Copyright (C) 2021, Collins Aerospace
;; All rights reserved.
;; 
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "TYPES")
(include-book "centaur/fty/deftypes" :dir :system)
(include-book "centaur/fty/basetypes" :dir :system)
(include-book "coi/util/defun" :dir :system)
(include-book "std/util/bstar" :dir :system)
(include-book "coi/util/in-conclusion" :dir :system)

(defmacro b* (&rest args)
  `(acl2::b* ,@args))

(defmacro then (&rest args)
  `(progn$ ,@args))

(defmacro else (&rest args)
  `(progn$ ,@args))

(defun pairlist-meta (qlist vlist)
  (if (and (consp qlist) (consp vlist))
      `(cons (cons ,(car qlist) ,(car vlist))
             ,(pairlist-meta (cdr qlist) (cdr vlist)))
    acl2::*nil*))

(defmacro doc-string (str &rest args)
  `(mv-let (c s) (fmt1-to-string ,str (acl2::PAIRLIS2 acl2::*base-10-chars* (list ,@args)) 0)
     (declare (ignore c))
     s))

(defmacro assert! (test msg &key (context ''assert!) (value 'nil))
  (let ((msg  (car msg))
        (vars (cdr msg)))
    `(let ((hard-error-value (if (not ,test) (hard-error ,context ,msg ,(pairlist-meta acl2::*base-10-chars* vars)) nil)))
       (declare (ignore hard-error-value))
       ,value)))

(defmacro undefined-fn (fn)
  `(let ((fn ,fn))
     (or (not fn)
         (and (eq (getpropc fn 'acl2::formals t) t)
              (eq (getpropc fn 'acl2::macro-args t) t)))))

(def::und safe-package-witness (x)
  (declare (xargs :fty ((symbol) symbol)))
  (if (equal (symbol-package-name x) "COMMON-LISP")
      'acl2::defthm
    x))

(defun good-atomp (x)
  (declare (type t x))
  (or (acl2-numberp x)
      (symbolp x)
      (characterp x)
      (stringp x)))
  
(def::und safe-packn-pos (lst witness)
  (declare (xargs :signature ((good-atom-listp symbolp) symbolp)))
  (acl2::packn-pos lst (safe-package-witness witness)))

(def::und default-name (name base suffix witness)
  (declare (xargs :signature ((symbolp symbolp good-atomp symbolp) symbolp)))
  (or name (safe-packn-pos (list base suffix) witness)))

(def::und type-fix! (type-fix! type-fix type-name witness)
  (declare (xargs :signature ((symbolp symbolp symbolp symbolp) symbolp)))
  (let ((suffix! (if (and (not type-fix!) (not type-fix)) '-fix '-fix!)))
    (default-name type-fix! type-name suffix! witness)))

(def::und type-fix (type-fix type-name type-fix! witness)
  (declare (xargs :signature ((symbolp symbolp symbolp symbolp) symbolp)))
  (or type-fix
      (let ((res (safe-packn-pos (list type-name '-fix) witness)))
        (if (not (equal res type-fix!)) res
          (safe-packn-pos (list type-name '-fix-fast) witness)))))

(def::un replace-assoc (key val alist)
  (declare (xargs :signature ((t t alistp) alistp)))
  (if (not (consp alist)) (cons (cons key val) nil)
    (let ((entry (car alist)))
      (if (equal (car entry) key) (cons (cons key val) (cdr alist))
        (cons entry (replace-assoc key val (cdr alist)))))))

(def::und get-key-keylist (key body)
  (declare (xargs :signature ((symbolp true-listp) t)))
  (if (endp body) nil
    (if (endp (cdr body)) nil
      (if (equal (car body) key) (car (cdr body))
        (get-key-keylist key (cddr body))))))

(set-state-ok t)

(defun fty-add-fix! (name fix! state)
  (declare (xargs :mode :program))
  (let ((fty-alist (fty::get-fixtypes-alist (w state))))
    (let ((hit (assoc name fty-alist)))
      (let ((name-alist (cdr hit)))
        (let ((name-alist (acons 'fty::fix! fix! name-alist)))
          (let ((fty-alist (replace-assoc name name-alist fty-alist)))
            `(table fty::fixtypes 'fty::fixtype-alist ',fty-alist)))))))

(defmacro fty::add-fix! (name &key (fix! 'nil))
  `(make-event (fty-add-fix! ',name ',fix! state)))

(defun def-fty-type-fn (type-name type-p type-fix type-fix! type-equiv fix-constants)
  (let* ((type-p      (default-name type-p     type-name '-p     type-name))
         (type-equiv  (default-name type-equiv type-name '-equiv type-p))
         (type-fix!   (type-fix! type-fix! type-fix type-name type-p))
         (type-fix    (type-fix type-fix type-name type-fix! type-p)))
    `(encapsulate
         ()

       (fty::deffixtype
        ,type-name
        :pred   ,type-p
        :fix    ,type-fix
        :equiv  ,type-equiv
        :executablep ,fix-constants
        :define nil
        )
       
       (fty::add-fix! ,type-name :fix! ,type-fix!)
       
       )))

(defmacro def::type-fty (name &key (type-p 'nil) (fix 'nil) (fix! 'nil) (equiv 'nil) (fix-constants 't))
  (def-fty-type-fn name type-p fix fix! equiv fix-constants))

#+joe
(def::type-fty type-name
  :pred  type-p 
  :fix   type-fix
  :fix!  type-fix!
  :equiv type-equiv
  :fix-constants t
  )

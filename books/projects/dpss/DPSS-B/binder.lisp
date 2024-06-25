;;
;; Copyright (C) 2023, Collins Aerospace
;; All rights reserved.
;;
;; This software may be modified and distributed under the terms
;; of the 3-clause BSD license.  See the LICENSE file for details.
;;
(in-package "ACL2")

;;
;; So this is what the type refinement macro should look like ..
;; the existing macro should probably be "def::type-refinement-properties"
;;
;; (def::type-refinement hyp-1
;;   :refines Escort
;;   :body (and (< (Escort->PL esc) (Escort->PR esc)) (<= 1 (Escort->E esc)))
;;   :type-witness (Escort! :PL 0 :L 0 :E 1 :R 0 :PR 1)
;;   )

#|
(defun field-accessor (name field)
  (packn-pos (list name "->" field) name))

(defun optional-binding (name field)
  ``(,,field (or ,,field (,',(field-accessor name field) ,,name))))

(defun optional-bindings (name fields)
  (if (not (consp fields)) nil
    (cons (optional-binding name (car fields))
          (optional-bindings name (cdr fields)))))

(defun keyword-exists-p (field)
  (packn-pos (list field "-p") field))

(defun keyword-initial-value (field exists?)
  (if exists? `(,field 'nil ,(keyword-exists-p field))
    `(,field 'nil)))

(defun keyword-exists-listp (fields)
  (if (not (consp fields)) nil
    (cons (keyword-exists-p (car fields))
          (keyword-exists-listp (cdr fields)))))

(defun keyword-initial-values (fields exists?)
  (if (not (consp fields)) nil
    (cons (keyword-initial-value (car fields) exists?)
          (keyword-initial-values (cdr fields) exists?))))

(defun field-accessor-list (fields name)
  (if (not (consp fields)) nil
    (cons (field-accessor name (car fields))
          (field-accessor-list (cdr fields) name))))

(defun zip-dot-lists (x y)
  (if (and (consp x) (consp y))
      (cons (cons (car x) (car y))
            (zip-dot-lists (cdr x) (cdr y)))
    nil))

(defun body-fields (body)
  (if (not (consp body)) nil
    (let ((entry (car body)))
      (cons (car entry)
            (body-fields (cdr body))))))

(defun name*-macro-body (name fields)
  `(let ,(optional-bindings name fields)
     (,name ,@fields)))

(defmacro type-str* (name body)
  (let ((name* (packn-pos (list name "*") name))
        (fields (body-fields body)))
    `(
      (type-str ,name
        ,body)
   
      (defmacro ,name* (,name &key ,@(keyword-initial-values fields nil))
        ,(name*-macro-body name fields))
   
      (defmacro Escort! (&key ,@(keyword-initial-values fields t))
        (declare (xargs :guard (and ,@(keyword-exists-listp fields)))
                 (ignorable ,@(keyword-exists-listp fields)))
        `(,name* nil ,',@fields))
   
      (def-b*-binder ,name*
        :body (patbind-fn args '(,@(zip-dot-lists fields (field-accessor-list fields name)))
                          forms rest-expr))
   
      )))
|#

(include-book "coi/types/types" :dir :system)

#+joe
(defmacro assert? (pred expr str)
  `(let ((pred ,pred)
         (expr ,expr)
         (str  ,str))
     (prog2$
      (assert$ pred str)
      expr)))

(include-book "std/testing/assert-qmark" :dir :system)

(defun bind-keys (keys map arg)
  (if (not (consp keys)) nil
    (b* (((list* key var keys) keys))
      (let ((hit (assoc-equal (symbol-name key) map)))
        (let ((fn (assert? (consp hit) (cdr hit) "bind-keys" (msg "key ~x0 not found in ~x1" key map))))
          (let ((fn (assert$ (symbolp fn) fn)))
            (cons `(,var (,fn ,arg))
                  (bind-keys keys map arg))))))))

(defun symbol-keys-to-string-keys (alist)
  (if (not (consp alist)) nil
    (b* (((cons (list* key pat) alist) alist))
      (cons (list* (symbol-name key) pat)
            (symbol-keys-to-string-keys alist)))))
 
(defun patbind-fn (keys map forms rest-expr)
  (let ((map (symbol-keys-to-string-keys map)))
    (let ((form (assert$ (equal (len forms) 1) (car forms))))
      `(let ,(bind-keys keys map form)
         ,rest-expr))))


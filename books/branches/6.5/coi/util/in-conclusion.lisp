#|-*-Lisp-*-=================================================================|#
#|                                                                           |#
#| coi: Computational Object Inference                                       |#
#|                                                                           |#
#|===========================================================================|#

#|
;; Support for detecting when a term is (or is not) in the current
;; conclusion.

;; (syntaxp (in-conclusion))
;; (syntaxp (in-conclusion-check term))
;;   (syntaxp (in-conclusion-check term :top :negated))
;;   (syntaxp (in-conclusion-check term :top :any))
;;   (syntaxp (in-conclusion-check term :top t))
;; (syntaxp (backchaining-check))
;; (syntaxp (not-in-conclusion))
|#

(in-package "ACL2")

(set-state-ok t)

(defun appears-in-clause (fn args fapp clause)
  (declare (type t fn args clause))
  (if (consp clause)
      (if fapp
          (or (and (equal fn (car clause))
                   (equal args (cdr clause)))
              (appears-in-clause fn args nil (cdr clause)))
        (or (appears-in-clause fn args t (car clause))
            (appears-in-clause fn args nil (cdr clause))))
    nil))

(defun in-conclusion-fn (term mfc state)
  (declare (ignore state)
           (type t term))
  (if (not (acl2::mfc-ancestors mfc))
      (and (if (consp term) (appears-in-clause (car term) (cdr term) nil (acl2::mfc-clause mfc)) t)
           (list (cons 'in-conclusion-free-variable `(quote t))))
    nil))

(defmacro in-conclusion ()
  `(bind-free (in-conclusion-fn nil acl2::mfc acl2::state) 
              (in-conclusion-free-variable)))

(defun check-term (negated expr term)
  (declare (type t term))
  (cond
   ((equal negated :negated) 
    (equal expr term))
   ((equal negated :any)
    (or (equal expr term)
        (and (consp term)
             (equal (car term) 'not)
             (consp (cdr term))
             (equal expr (cadr term)))))
   (t 
    (and (consp term)
         (equal (car term) 'not)
         (consp (cdr term))
         (equal expr (cadr term))))))
      
(defun member-of-clause (negated expr clause)
  (declare (type t clause))
  (if (consp clause)
      (let ((term (car clause)))
        (or (check-term negated expr term)
            (member-of-clause negated expr (cdr clause))))
    nil))

(defun quote-list (list)
  (declare (type t list))
  (if (consp list)
      (cons `(quote ,(car list))
            (quote-list (cdr list)))
    nil))

(defun equal_len (n list)
  (declare (type (integer 0 *) n))
  (if (consp list)
      (if (zp n) nil
        (equal_len (1- n) (cdr list)))
    (and (null list) (= n 0))))

;; ==================================

;; This stuff should probably move to (or come from) syntax:: .. 

(defun syn__consp (term)
  (declare (type t term))
  (and 
   (equal_len 3 term)
   (equal (car term) 'cons)))

(defun syn__cdr (term)
  (declare (type (satisfies syn__consp) term))
  (caddr term))

(defun syn__car (term)
  (declare (type (satisfies syn__consp) term))
  (cadr term))

(defun syn__quotep (term)
  (declare (type t term))
  (and (equal_len 2 term)
             (equal (car term) 'quote)))

(defun syn__dequote (term)
  (declare (type (satisfies syn__quotep) term))
  (cadr term))

(defun delist (args)
  (declare (type t args))
  (cond
   ((syn__consp args)
    (cons (syn__car args)
          (delist (syn__cdr args))))
   ((syn__quotep args)
    (quote-list (syn__dequote args)))
   (t
    nil)))

;; ==================================

(defun in-conclusion-check-fn (top fn args mfc state)
  (declare (ignore state)
           (type t args))
  (if (not (acl2::mfc-ancestors mfc))
      (let ((args (delist args)))
        (let ((clause (mfc-clause mfc)))
          (and (if (not top) (appears-in-clause fn args nil clause)
                 (if (and (equal fn 'not)
                          (consp args))
                     (member-of-clause :negated (car args) clause)
                   (member-of-clause top (cons fn args) clause)))
               (list (cons 'in-conclusion-free-variable `(quote t))))))
    nil))

(defmacro in-conclusion-check (term &key (top 'nil))
  (declare (xargs :guard (consp term)))
  `(and
    (equal in-conclusion-check-term (list ,@(cdr term)))
    (bind-free (in-conclusion-check-fn ,top ',(car term) in-conclusion-check-term acl2::mfc acl2::state) 
               (in-conclusion-free-variable))))

(defun backchaining-check-fn (mfc state)
  (declare (ignore state))
  (if (not (acl2::mfc-ancestors mfc)) nil
    (list (cons 'backchaining-free-variable `(quote t)))))

(defmacro backchaining-check ()
  `(bind-free (backchaining-check-fn acl2::mfc acl2::state) (backchaining-free-variable)))

(defun not-in-conclusion-fn (mfc state)
  (declare (ignore state))
  (and (acl2::mfc-ancestors mfc)
       (list (cons 'in-conclusion-free-variable `(quote t)))))

(defmacro not-in-conclusion ()
  `(bind-free (not-in-conclusion-fn acl2::mfc acl2::state) 
              (in-conclusion-free-variable)))



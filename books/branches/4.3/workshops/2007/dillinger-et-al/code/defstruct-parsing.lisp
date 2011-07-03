#|$ACL2s-Preamble$;
(ld "hacker-pkg.lsp")

(begin-book);$ACL2s-Preamble$|#


(in-package "ACL2-HACKER")

(program)
(set-state-ok t)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; defstruct parsing
;

(defun defstruct-conc-name (name options)
  (cond ((endp options)
         (string-append (symbol-name name) "-"))
        ((eq ':conc-name (car options))
         "")
        ((and (consp (car options))
              (eq ':conc-name (caar options)))
         (let ((arglst (cdar options)))
           (if (and (consp arglst)
                    (symbolp (car arglst))
                    (car arglst))
             (symbol-name (car arglst))
             "")))
        (t
         (defstruct-conc-name name (cdr options)))))


(defun defstruct-constructor-name-lst1 (name options sofar nilseen)
  (cond ((endp options)
         (cond (sofar
                sofar)
               (nilseen
                nil)
               (t
                (list (intern-in-package-of-symbol
                       (string-append "MAKE-" (symbol-name name))
                       name)))))
        ((and (consp (car options))
              (eq ':constructor (caar options))
              (consp (cdar options)))
         (cond ((null (cadar options))
                (defstruct-constructor-name-lst1 name
                                                 (cdr options)
                                                 sofar
                                                 t))
               ((symbolp (cadar options))
                (defstruct-constructor-name-lst1 name
                                                 (cdr options)
                                                 (cons (cadar options) sofar)
                                                 nilseen))
               (t ; bad
                (defstruct-constructor-name-lst1 name
                                                 (cdr options)
                                                 sofar
                                                 nilseen))))
        (t
         (defstruct-constructor-name-lst1 name (cdr options) sofar nilseen))))

(defun defstruct-constructor-name-lst (name options)
  (defstruct-constructor-name-lst1 name options nil nil))


(defun defstruct-copier-name-lst1 (name options sofar nilseen)
  (cond ((endp options)
         (cond (sofar
                sofar)
               (nilseen
                nil)
               (t
                (list (intern-in-package-of-symbol
                       (string-append "COPY-" (symbol-name name))
                       name)))))
        ((and (consp (car options))
              (eq ':copier (caar options))
              (consp (cdar options)))
         (cond ((null (cadar options))
                (defstruct-copier-name-lst1 name
                                               (cdr options)
                                               sofar
                                               t))
               ((symbolp (cadar options))
                (defstruct-copier-name-lst1 name
                                               (cdr options)
                                               (cons (cadar options) sofar)
                                               nilseen))
               (t ; bad
                (defstruct-copier-name-lst1 name
                                               (cdr options)
                                               sofar
                                               nilseen))))
        (t
         (defstruct-copier-name-lst1 name (cdr options) sofar nilseen))))

(defun defstruct-copier-name-lst (name options)
  (defstruct-copier-name-lst1 name options nil nil))


; :include ignored!
; :initial-offset unimportant
; :named unimportant


(defun defstruct-predicate-name-lst1 (name options sofar nilseen)
  (cond ((endp options)
         (cond (sofar
                sofar)
               (nilseen
                nil)
               (t
                (list (intern-in-package-of-symbol
                       (string-append (symbol-name name) "-P")
                       name)))))
        ((and (consp (car options))
              (eq ':predicate (caar options))
              (consp (cdar options)))
         (cond ((null (cadar options))
                (defstruct-predicate-name-lst1 name
                                               (cdr options)
                                               sofar
                                               t))
               ((symbolp (cadar options))
                (defstruct-predicate-name-lst1 name
                                               (cdr options)
                                               (cons (cadar options) sofar)
                                               nilseen))
               (t ; bad
                (defstruct-predicate-name-lst1 name
                                               (cdr options)
                                               sofar
                                               nilseen))))
        (t
         (defstruct-predicate-name-lst1 name (cdr options) sofar nilseen))))

(defun defstruct-predicate-name-lst (name options)
  (defstruct-predicate-name-lst1 name options nil nil))


; :print-function, :print-object unimportant
; :type assumed unimportant


(defun defstruct-accessors (conc-name descs package-of-symbol)
  (if (endp descs)
    nil
    (let* ((desc (car descs))
           (name (if (consp desc) (car desc) desc)))
      (if (symbolp name)
        (cons (if (equal conc-name "")
                name
                (intern-in-package-of-symbol
                 (string-append conc-name (symbol-name name))
                 package-of-symbol))
              (defstruct-accessors conc-name (cdr descs) package-of-symbol))
        ;; bad:
        (defstruct-accessors conc-name (cdr descs) package-of-symbol)))))


(defun defstruct-name-and-fns (form)
  (if (not (and (consp form)
                (eq (car form) 'defstruct)
                (consp (cdr form))
                (or (symbolp (cadr form))
                    (and (consp (cadr form))
                         (symbolp (caadr form))))))
    nil
    (let* ((name-and-options (cadr form))
           (name (if (consp name-and-options)
                   (car name-and-options)
                   name-and-options))
           (options (if (consp name-and-options)
                      (cdr name-and-options)
                      nil))
           (slot-descs (if (and (consp (cddr form))
                                (stringp (caddr form)))
                         (cdddr form)
                         (cddr form)))
           (conc-name (defstruct-conc-name name options))
           (top-fns (append (defstruct-constructor-name-lst name options)
                            (defstruct-copier-name-lst name options)
                            (defstruct-predicate-name-lst name options)))
           (accessors (defstruct-accessors conc-name slot-descs name)))
      (cons name (append top-fns accessors)))))


;
; end of defstruct parsing
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


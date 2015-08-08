(in-package "ACL2")

; Modification by Matt K. after v4-3: Removed :load-compiled-file :comp, which
; was part of the include-book forms just below, in support of provisional
; certification.  Presumably the indicated books have already been compiled by
; now, anyhow.
(include-book "defstruct-parsing"); was in portcullis

;Needed to use, but not needed for certification:
;(include-book "defcode" :load-compiled-file :comp :ttags ((defcode)))

(program)
(set-state-ok t)


; a helper macro for building other stuff
(defmacro make-raw-definitions (code &key compile fresh
                                save-fns save-macros save-vars)
  (declare (xargs :guard (and (true-listp code)
                              (or (booleanp compile)
                                  (true-listp compile))
                              (or (booleanp fresh)
                                  (symbol-listp fresh))
                              (symbol-listp save-fns)
                              (symbol-listp save-macros)
                              (symbol-listp save-vars))))
  (let* ((all-saves (append save-fns save-macros save-vars))
         (fresh-lst (if (eq fresh 't) all-saves fresh)))
    `(with-output
      :off summary
      (progn
       ,@ (and fresh-lst
               `((assert-unbound . ,fresh-lst)
                 (deflabels . ,fresh-lst)))
       ,@ (and save-fns
               `((ensure-special-raw-definition-flag . ,save-fns)))
       (defcode
         :extend
         (in-raw-mode ,@ (and save-fns
                              `((dolist (f ',save-fns)
                                        (maybe-push-undo-stack 'defun f))))
                      ,@ (and save-macros
                              `((dolist (m ',save-macros)
                                        (maybe-push-undo-stack 'defmacro m))))
                      ,@ (and save-vars
                              `((dolist (v ',save-vars)
                                        (maybe-push-undo-stack 'defconst v))))
                      ,@ code)
         :retract
         ,(and all-saves
               `(in-raw-mode (dolist (s ',all-saves)
                                     (maybe-pop-undo-stack s))))
         :compile
         (progn . ,(if (eq compile 't) code compile)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; some low-level pieces for building high-level abstractions
;
;

(defmacro defun-raw (name ll &rest rst)
  `(make-raw-definitions
    ((defun ,name ,ll . ,rst))
    :compile t
    :fresh t
    :save-fns (,name)))


(defmacro defmacro-raw (name ll &rest rst)
  `(make-raw-definitions
    ((defmacro ,name ,ll . ,rst))
    :compile t
    :fresh t
    :save-macros (,name)))


(defmacro copy-raw-defun (src dst)
  `(make-raw-definitions
    ((setf (symbol-function ',dst)
           (symbol-function ',src)))
    :compile nil
    :fresh t
    :save-fns (,dst)))


(defmacro copy-raw-defmacro (src dst)
  `(make-raw-definitions
    ((setf (macro-function ',dst)
           (macro-function ',src)))
    :compile nil
    :fresh t
    :save-macros (,dst)))


(defmacro defvar-raw (&whole form name &optional initial-val doc)
  (declare (ignore initial-val doc)
           (xargs :guard (symbolp name)))
  `(make-raw-definitions
    ((defvar . ,(cdr form)))
    :compile nil
    :fresh t
    :save-vars (,name)))


(defmacro defparameter-raw (&whole form name initial-val &optional doc)
  (declare (ignore initial-val doc)
           (xargs :guard (symbolp name)))
  `(make-raw-definitions
    ((defparameter . ,(cdr form)))
    :compile nil
    :fresh t
    :save-vars (,name)))


(defmacro defconstant-raw (&whole form name initial-val &optional doc)
  (declare (ignore initial-val doc)
           (xargs :guard (symbolp name)))
  `(make-raw-definitions
    ((defconstant . ,(cdr form)))
    :compile nil
    :fresh t
    :save-vars (,name)))



(defmacro defstruct-raw (&rest args)
  (declare (xargs :guard args))
  (let* ((form (cons 'defstruct args))
         (name-and-fns (acl2-hacker::defstruct-name-and-fns form)))
    (if (consp name-and-fns)
      `(make-raw-definitions
        (,form)
        :compile nil
        :fresh ,name-and-fns
        :save-fns ,(cdr name-and-fns))
      `(er hard 'defstruct-raw
           "Unrecognized defstruct definition form:~%~x0~%"
           ',form))))

#| ; killed because of OpenMCL issues
(defun raw-only-definitions1 (revremforms all-forms compile fresh
                              save-fns save-macros save-vars)
  (if (endp revremforms)
    (let* ((fresh-no-dups (remove-duplicates-eql fresh))
           (main `(make-raw-definitions
                   ,all-forms
                   :compile ,compile
                   :fresh ,fresh-no-dups
                   :save-fns ,save-fns
                   :save-macros ,save-macros
                   :save-vars ,save-vars)))
      (if (equal fresh-no-dups fresh)
        main
        (let ((dups (duplicates fresh)))
          `(progn (value-triple (cw "Warning: Some names are being defined more than once in raw lisp:~%~x0~%" ',dups))
                  ,main))))
    (let ((form (car revremforms))
          (rst (cdr revremforms)))
      (cond ((and (consp form)
                  (eq 'defun (car form))
                  (>= (len form) 4)
                  (symbolp (cadr form)))
             (raw-only-definitions1
              rst
              all-forms
              (cons form compile)
              (cons (cadr form) fresh)
              (cons (cadr form) save-fns)
              save-macros
              save-vars))
            ((and (consp form)
                  (eq 'defmacro (car form))
                  (>= (len form) 4)
                  (symbolp (cadr form)))
             (raw-only-definitions1
              rst
              all-forms
              (cons form compile)
              (cons (cadr form) fresh)
              save-fns
              (cons (cadr form) save-macros)
              save-vars))
            ((and (consp form)
                  (or (eq 'defvar (car form))
                      (eq 'defparameter (car form)))
                  (>= (len form) 2)
                  (symbolp (cadr form)))
             (raw-only-definitions1
              rst
              all-forms
              compile ; don't compile
              (cons (cadr form) fresh)
              save-fns
              save-macros
              (cons (cadr form) save-vars)))
            ((and (consp form)
                  (eq 'defstruct (car form))
                  (>= (len form) 2))
             (let ((name-and-fns (acl2-hacker::defstruct-name-and-fns form)))
               (if (consp name-and-fns)
                 (raw-only-definitions1
                  rst
                  all-forms
                  compile ; don't compile
                  (append name-and-fns fresh)
                  (append (cdr name-and-fns) save-fns)
                  save-macros
                  save-vars)
                 `(progn! (er soft
                          'raw-only-definitions
                          "Unrecognized defstruct definition form:~%~x0~%"
                          ',form)))))
            (t
             `(progn! (er soft
                          'raw-only-definitions
                          "Unrecognized raw definition form:~%~x0~%"
                          ',form)))))))

(defmacro raw-only-definitions (&rest forms)
  (raw-only-definitions1 (reverse forms) forms nil nil nil nil nil))
|#


(defmacro modify-raw-defun
  (name name-for-old ll &rest decls-and-body)
  (declare (xargs :guard (and (symbolp name)
                              (symbolp name-for-old)
                              (symbol-listp ll)
                              (consp decls-and-body))))
  `(progn (copy-raw-defun ,name ,name-for-old)
          (make-raw-definitions
           ((defun ,name ,ll
              ,@ (and ll `((declare (ignorable . ,ll))))
              . ,decls-and-body))
           :compile t
           :fresh nil
           :save-fns (,name))))

; tests & stuff:
#|
(include-book
 "defcode" :ttags :all)

(defttag t)

(defstruct-raw foo bar)

(modify-raw-defun foo-bar old-foo-bar (s)
                  (progn (format t "Foobar!~%")
                         (old-foo-bar s)))

(set-raw-mode t)

(foo-bar (make-foo :bar 42))

|#

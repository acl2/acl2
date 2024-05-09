(in-package :cl-user)
(defpackage fast-http.util
  (:use :cl)
  (:import-from :fast-http.error
                :strict-error)
  (:import-from :alexandria
                :once-only
                :ensure-list)
  (:import-from :cl-utilities
                :with-collectors)
  (:export :defun-insane
           :defun-speedy
           :defun-careful
           :casev
           :casev=
           :case-byte
           :tagcase
           :tagcasev
           :tagcasev=
           :make-collector
           :number-string-p))
(in-package :fast-http.util)

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defvar *insane-declaration* '(declare (optimize (speed 3) (safety 0) (space 0) (compilation-speed 0))))
  (defvar *speedy-declaration* '(declare (optimize (speed 3) (safety 0) (space 0) (compilation-speed 0))))
  (defvar *careful-declaration* '(declare (optimize (speed 3) (safety 2)))))

(defmacro defun-insane (name lambda-list &body body)
  `(progn
     (declaim (inline ,name))
     (defun ,name ,lambda-list
       ,*insane-declaration*
       ,@body)))

(defmacro defun-speedy (name lambda-list &body body)
  `(progn
     (declaim (notinline ,name))
     (defun ,name ,lambda-list
       ,*speedy-declaration*
       ,@body)))

(defmacro defun-careful (name lambda-list &body body)
  `(progn
     (declaim (notinline ,name))
     (defun ,name ,lambda-list
       ,*careful-declaration*
       ,@body)))

(defmacro casev (keyform &body clauses)
  (once-only (keyform)
    (flet ((get-val (val)
             (cond
               ((eq val 'otherwise) val)
               ((symbolp val) (symbol-value val))
               ((constantp val) val)
               (T (error "CASEV can be used only with variables or constants")))))
      `(case ,keyform
         ,@(loop for (val . clause) in clauses
                 if (eq val 'otherwise)
                   collect `(otherwise ,@clause)
                 else if (listp val)
                   collect `((,@(mapcar #'get-val val)) ,@clause)
                 else
                   collect `(,(get-val val) ,@clause))))))

(defmacro casev= (keyform &body clauses)
  (once-only (keyform)
    (flet ((get-val (val)
             (cond
               ((eq val 'otherwise) val)
               ((symbolp val) (symbol-value val))
               ((constantp val) val)
               (T (error "CASEV can be used only with variables or constants")))))
      `(cond
         ,@(loop for (val . clause) in clauses
                 if (eq val 'otherwise)
                   collect `(T ,@clause)
                 else if (listp val)
                        collect `((or ,@(mapcar (lambda (val)
                                                  `(= ,keyform ,(get-val val)))
                                                val))
                                  ,@clause)
                 else
                   collect `((= ,keyform ,(get-val val)) ,@clause))))))

(defmacro case-byte (byte &body cases)
  `(casev= ,byte
     ,@(loop for (val . form) in cases
             if (eq val 'otherwise)
               collect `(,val ,@form)
             else if (listp val)
               collect `(,(mapcar #'char-code val) ,@form)
             else
               collect `(,(char-code val) ,@form))))

(defmacro tagcase (keyform &body blocks)
  (let ((end (gensym "END")))
    `(tagbody
        (case ,keyform
          ,@(loop for (tag . body) in blocks
                  if (eq tag 'otherwise)
                    collect `(otherwise ,@body (go ,end))
                  else
                    collect `(,tag (go ,(if (listp tag) (car tag) tag)))))
        (go ,end)
        ,@(loop for (tag . body) in blocks
                if (listp tag)
                  append tag
                else
                  collect tag
                collect `(progn ,@body
                                (go ,end)))
      ,end)))

(defmacro tagcasev (keyform &body blocks)
  (let ((end (gensym "END")))
    `(tagbody
        (casev ,keyform
          ,@(loop for (tag . body) in blocks
                  if (eq tag 'otherwise)
                    collect `(otherwise ,@body (go ,end))
                  else
                    collect `(,tag (go ,(if (listp tag) (car tag) tag)))))
        (go ,end)
        ,@(loop for (tag . body) in blocks
                if (listp tag)
                  append tag
                else if (not (eq tag 'otherwise))
                       collect tag
                collect `(progn ,@body
                                (go ,end)))
      ,end)))

(defmacro tagcasev= (keyform &body blocks)
  (let ((end (gensym "END")))
    `(tagbody
        (casev= ,keyform
          ,@(loop for (tag . body) in blocks
                  if (eq tag 'otherwise)
                    collect `(otherwise ,@body (go ,end))
                  else
                    collect `(,tag (go ,(if (listp tag) (car tag) tag)))))
        (go ,end)
        ,@(loop for (tag . body) in blocks
                if (listp tag)
                  append tag
                else if (not (eq tag 'otherwise))
                       collect tag
                collect `(progn ,@body
                                (go ,end)))
      ,end)))

(defun make-collector ()
  (let ((none '#:none))
    (declare (dynamic-extent none))
    (with-collectors (buffer)
      (return-from make-collector
        (lambda (&optional (data none))
          (unless (eq data none)
            (buffer data))
          buffer)))))

(declaim (inline %whitespacep))
(defun %whitespacep (char)
  (declare (type character char)
           (optimize (speed 3) (safety 0)))
  (or (char= char #\Space)
      (char= char #\Tab)))

(declaim (inline position-not-whitespace))
(defun position-not-whitespace (string &key from-end)
  (declare (type #+ecl string #-ecl simple-string string)
           (optimize (speed 3) (safety 0)))
  (let* ((len (length string))
         (start (if from-end (1- len) 0))
         (end (if from-end 0 (1- len)))
         (step-fn (if from-end #'1- #'1+)))
    (declare (type integer len start end))
    (do ((i start (funcall step-fn i)))
        ((= i end) i)
      (declare (type integer i))
      (unless (%whitespacep (aref string i))
        (return-from position-not-whitespace i)))))

(declaim (inline number-string-p))
(defun number-string-p (string)
  (declare (type #+ecl string #-ecl simple-string string)
           (optimize (speed 3) (safety 2)))
  ;; empty string
  (when (zerop (length string))
    (return-from number-string-p nil))
  (let ((end (position-not-whitespace string :from-end t))
        (dot-read-p nil))
    ;; spaces string
    (when (null end)
      (return-from number-string-p nil))
    (locally (declare (type integer end)
                      (optimize (safety 0)))
      (incf end)
      (do ((i (the integer (or (position-not-whitespace string) 0)) (1+ i)))
          ((= i end) T)
        (declare (type integer i))
        (let ((char (aref string i)))
          (declare (type character char))
          (cond
            ((alpha-char-p char)
             (return-from number-string-p nil))
            ((digit-char-p char))
            ((char= char #\.)
             (when dot-read-p
               (return-from number-string-p nil))
             (setq dot-read-p t))
            (T (return-from number-string-p nil))))))))

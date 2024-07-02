(in-package :cl-user)
(defpackage quri.util
  (:use :cl)
  (:import-from :alexandria
                :with-gensyms)
  (:export :simple-byte-vector
           :standard-alpha-char-p
           :standard-alpha-byte-p
           :standard-alphanumeric-p
           :standard-alphanumeric-byte-p
           :with-array-parsing
           :with-string-parsing
           :with-byte-array-parsing
           :redo
           :gonext
           :goto))
(in-package :quri.util)

(deftype simple-byte-vector (&optional (len '*)) `(simple-array (unsigned-byte 8) (,len)))

(defun standard-alpha-char-p (char)
  (declare (type character char)
           (optimize (speed 3) (safety 0)))
  (standard-alpha-byte-p (char-code char)))

(defun standard-alpha-byte-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (or (<= #.(char-code #\A) byte #.(char-code #\Z))
      (<= #.(char-code #\a) byte #.(char-code #\z))))

(defun standard-alphanumeric-p (char)
  (declare (type character char)
           (optimize (speed 3) (safety 0)))
  (or (digit-char-p char)
      (standard-alpha-char-p char)))

(defun standard-alphanumeric-byte-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (or (<= #.(char-code #\0) byte #.(char-code #\9))
      (standard-alpha-byte-p byte)))

(define-condition parsing-end-unexpectedly (simple-error)
  ((state :initarg :state
          :initform nil))
  (:report (lambda (condition stream)
             (format stream "Parsing ended unexpectedly~:[~;~:* at ~A~]"
                     (slot-value condition 'state)))))

(define-condition no-next-state (simple-error) ())

(defmacro with-string-parsing ((elem p seq &optional (start 0) end key) &body body)
  `(let ((,elem #\Nul))
     (declare (type character ,elem))
     (%with-array-parsing (,elem ,p ,seq ,start ,end ,key) ,@body)))

(defmacro with-byte-array-parsing ((elem p seq &optional (start 0) end key) &body body)
  `(let ((,elem 0))
     (declare (type (unsigned-byte 8) ,elem))
     (%with-array-parsing (,elem ,p ,seq ,start ,end ,key) ,@body)))

(defmacro with-array-parsing ((elem p seq &optional (start 0) end key) &body body)
  `(let (,elem)
     (%with-array-parsing (,elem ,p ,seq ,start ,end ,key) ,@body)))

(defmacro %with-array-parsing ((elem p seq &optional (start 0) end key) &body body)
  (with-gensyms (g-end no-next-state last key-fn)
    (let ((eof-exists nil))
      `(let (,@(and key `((,key-fn ,key)))
             (,p ,start)
             (,g-end (locally (declare #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
                       (or ,end (length ,seq)))))
         (declare (ignorable ,p ,g-end))
         ,@(loop for (exp . rest) on body
                 while (and (listp exp) (eq (car exp) 'declare))
                 collect exp
                 do (setq body rest))
         (macrolet ((goto (tag &optional (amount 1))
                      `(locally (declare (optimize (speed 3) (safety 0)))
                         (incf ,',p ,amount)
                         ,@(if (eql amount 0)
                               ()
                               `((when (= ,',p ,',g-end)
                                   (go :eof))
                                 (setq ,',elem
                                       ,',(if key
                                              `(if ,key-fn
                                                   (funcall ,key-fn (aref ,seq ,p))
                                                   (aref ,seq ,p))
                                              `(aref ,seq ,p)))))
                         (go ,tag))))
           (tagbody
              (when (= ,p ,g-end)
                (go :eof))
              (locally (declare (optimize (speed 3) (safety 0)))
                (setq ,elem ,@(if key
                                  `((if ,key-fn
                                        (funcall ,key-fn (aref ,seq ,p))
                                        (aref ,seq ,p)))
                                  `((aref ,seq ,p)))))
              ,@(loop for (tagpart . rest) on body
                      for (tag . part) = tagpart
                      if (eq tag :eof)
                        append (progn
                                 (setf eof-exists t)
                                 `(,@tagpart
                                   (go ,last)))
                      else
                        append
                        (list tag
                              `(macrolet ((redo (&optional (amount 1))
                                            `(goto ,',tag ,amount))
                                          (gonext (&optional (amount 1))
                                            `(goto ,',(or (caar rest) no-next-state)
                                                   ,amount)))
                                 ,@part
                                 (error 'parsing-end-unexpectedly :state ',tag))))

              ,no-next-state
              (error 'no-next-state)

              ,@(if eof-exists
                    ()
                    '(:eof))

              ,last))))))

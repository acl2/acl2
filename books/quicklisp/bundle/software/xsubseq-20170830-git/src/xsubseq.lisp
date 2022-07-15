(in-package :cl-user)
(defpackage xsubseq
  (:use :cl)
  #+(or sbcl openmcl cmu allegro)
  (:import-from #+sbcl :sb-cltl2
                #+openmcl :ccl
                #+cmu :ext
                #+allegro :sys
                :variable-information)
  (:export :xsubseq
           :octets-xsubseq
           :string-xsubseq
           :concatenated-xsubseqs
           :null-concatenated-xsubseqs
           :octets-concatenated-xsubseqs
           :string-concatenated-xsubseqs
           :make-concatenated-xsubseqs
           :xlength
           :xnconc
           :xnconcf
           :coerce-to-sequence
           :coerce-to-string
           :with-xsubseqs))
(in-package :xsubseq)

(deftype octets (&optional (len '*))
  `(simple-array (unsigned-byte 8) (,len)))

(defstruct (xsubseq (:constructor make-xsubseq (data start &optional (end (length data))
                                                &aux (len (- end start)))))
  (data nil)
  (start 0 :type integer)
  (end 0 :type integer)
  (len 0 :type integer))

(defstruct (octets-xsubseq (:include xsubseq)
                           (:constructor make-octets-xsubseq (data start &optional (end (length data))
                                                              &aux (len (- end start))))))

(defstruct (string-xsubseq (:include xsubseq)
                           (:constructor make-string-xsubseq (data start &optional (end (length data))
                                                              &aux (len (- end start))))))

(defstruct (concatenated-xsubseqs (:constructor %make-concatenated-xsubseqs))
  (len 0 :type integer)
  (last nil :type list)
  (children nil :type list))

(defun make-concatenated-xsubseqs (&rest children)
  (if (null children)
      (make-null-concatenated-xsubseqs)
      (%make-concatenated-xsubseqs :children children
                                   :last (last children)
                                   :len (reduce #'+
                                                children
                                                :key #'xsubseq-len
                                                :initial-value 0))))

(defstruct (null-concatenated-xsubseqs (:include concatenated-xsubseqs)))

(defstruct (octets-concatenated-xsubseqs (:include concatenated-xsubseqs)))

(defstruct (string-concatenated-xsubseqs (:include concatenated-xsubseqs)))

(defun xsubseq (data start &optional (end (length data)))
  (typecase data
    (octets (make-octets-xsubseq data start end))
    (string (make-string-xsubseq data start end))
    (t (make-xsubseq data start end))))

#+(or sbcl openmcl cmu allegro)
(define-compiler-macro xsubseq (&whole form &environment env data start &optional end)
  (let ((type (cond
                ((constantp data) (type-of data))
                ((and (symbolp data)
                      (assoc 'type (nth-value 2 (variable-information data env)))))
                ((and (listp data)
                      (eq (car data) 'make-string))
                 'string)
                ((and (listp data)
                      (eq (car data) 'the)
                      (cadr data)))
                ((and (listp data)
                      (eq (car data) 'make-array)
                      (null (cadr (member :adjustable data)))
                      (null (cadr (member :fill-pointer data)))
                      (cadr (member :element-type data))))))
        (g-data (gensym "DATA")))
    (if (null type)
        form
        (cond
          ((subtypep type 'octets) `(let ((,g-data ,data))
                                      (make-octets-xsubseq ,g-data ,start ,(or end `(length ,g-data)))))
          ((subtypep type 'string) `(let ((,g-data ,data))
                                      (make-string-xsubseq ,g-data ,start ,(or end `(length ,g-data)))))
          (t form)))))

(defun %xnconc2 (seq1 seq2)
  (flet ((seq-values (seq)
           (if (concatenated-xsubseqs-p seq)
               (values (concatenated-xsubseqs-children seq)
                       (concatenated-xsubseqs-last seq)
                       (concatenated-xsubseqs-len seq))
               (let ((children (list seq)))
                 (values children children
                         (xsubseq-len seq))))))
    (macrolet ((make-concatenated (type seq1 seq2)
                  `(multiple-value-bind (children last len)
                       (seq-values ,seq2)
                     (,(cond
                         ((eq type 'octets) 'make-octets-concatenated-xsubseqs)
                         ((eq type 'string) 'make-string-concatenated-xsubseqs)
                         (t '%make-concatenated-xsubseqs))
                      :len (+ (xsubseq-len ,seq1) len)
                      :children (cons ,seq1 children)
                      :last last))))
      (etypecase seq1
        (null-concatenated-xsubseqs seq2)
        (concatenated-xsubseqs
         (multiple-value-bind (children last len)
             (seq-values seq2)
           (if (concatenated-xsubseqs-last seq1)
               (progn
                 (rplacd (concatenated-xsubseqs-last seq1)
                         children)
                 (setf (concatenated-xsubseqs-last seq1) last)
                 (incf (concatenated-xsubseqs-len seq1) len))
               ;; empty concatenated-xsubseqs
               (progn
                 (setf (concatenated-xsubseqs-children seq1) children
                       (concatenated-xsubseqs-len seq1) len
                       (concatenated-xsubseqs-last seq1) last)))
           seq1))
        (octets-xsubseq
         (make-concatenated octets seq1 seq2))
        (string-xsubseq
         (make-concatenated string seq1 seq2))
        (xsubseq (make-concatenated t seq1 seq2))))))

(defun xnconc (subseq &rest more-subseqs)
  (reduce #'%xnconc2 more-subseqs :initial-value subseq))

(define-modify-macro xnconcf (subseq &rest more-subseqs) xnconc)

(defun xlength (seq)
  (etypecase seq
    (xsubseq (xsubseq-len seq))
    (concatenated-xsubseqs (concatenated-xsubseqs-len seq))))

(defun coerce-to-sequence (seq)
  (etypecase seq
    (octets-concatenated-xsubseqs (octets-concatenated-xsubseqs-to-sequence seq))
    (string-concatenated-xsubseqs (string-concatenated-xsubseqs-to-sequence seq))
    (concatenated-xsubseqs (concatenated-xsubseqs-to-sequence seq))
    (xsubseq (xsubseq-to-sequence seq))))

#+(or sbcl openmcl cmu allegro)
(define-compiler-macro coerce-to-sequence (&whole form &environment env seq)
  (let ((type (cond
                ((constantp seq) (type-of seq))
                ((and (symbolp seq)
                      (assoc 'type (nth-value 2 (variable-information seq env)))))
                ((and (listp seq)
                      (eq (car seq) 'the)
                      (cadr seq))))))
    (if (null type)
        form
        (cond
          ((subtypep type 'octets-concatenated-xsubseqs) `(octets-concatenated-xsubseqs-to-sequence ,seq))
          ((subtypep type 'string-concatenated-xsubseqs) `(string-concatenated-xsubseqs-to-sequence ,seq))
          ((subtypep type 'concatenated-xsubseqs) `(concatenated-xsubseqs-to-sequence ,seq))
          ((subtypep type 'xsubseq) `(xsubseq-to-sequence ,seq))
          (t form)))))

(defun coerce-to-string (seq)
  (etypecase seq
    (null-concatenated-xsubseqs "")
    (octets-concatenated-xsubseqs (octets-concatenated-xsubseqs-to-string seq))
    (string-concatenated-xsubseqs (string-concatenated-xsubseqs-to-sequence seq))
    (octets-xsubseq (octets-xsubseq-to-string seq))
    (string-xsubseq (xsubseq-to-sequence seq))))

#+(or sbcl openmcl cmu allegro)
(define-compiler-macro coerce-to-string (&whole form &environment env seq)
  (let ((type (cond
                ((constantp seq) (type-of seq))
                ((and (symbolp seq)
                      (assoc 'type (nth-value 2 (variable-information seq env)))))
                ((and (listp seq)
                      (eq (car seq) 'the)
                      (cadr seq))))))
    (if (null type)
        form
        (cond
          ((subtypep type 'octets-concatenated-xsubseqs) `(octets-concatenated-xsubseqs-to-string ,seq))
          ((subtypep type 'string-concatenated-xsubseqs) `(string-concatenated-xsubseqs-to-sequence ,seq))
          ((subtypep type 'octets-xsubseq) `(octets-xsubseq-to-string ,seq))
          ((subtypep type 'string-xsubseq) `(xsubseq-to-sequence ,seq))
          (t form)))))

(defun xsubseq-to-sequence (seq)
  (let ((result (make-array (xsubseq-len seq)
                            :element-type
                            (array-element-type (xsubseq-data seq)))))
    (replace result (xsubseq-data seq)
             :start2 (xsubseq-start seq)
             :end2 (xsubseq-end seq))
    result))

(defun octets-xsubseq-to-string (seq)
  (let ((result (make-array (xsubseq-len seq)
                            :element-type 'character)))
    (declare (type simple-string result))
    (let ((data (xsubseq-data seq))
          (end (xsubseq-end seq)))
      (do ((i (xsubseq-start seq) (1+ i))
           (j 0 (1+ j)))
          ((= i end) result)
        (setf (aref result j)
              (code-char
               (the (unsigned-byte 8)
                    (aref (the octets data) i))))))))

(defun concatenated-xsubseqs-to-sequence (seq)
  (let ((result (make-array (concatenated-xsubseqs-len seq)
                            :element-type
                            (array-element-type (xsubseq-data (car (concatenated-xsubseqs-children seq)))))))
    (loop with current-pos = 0
          for seq in (concatenated-xsubseqs-children seq)
          do (replace result (xsubseq-data seq)
                      :start1 current-pos
                      :start2 (xsubseq-start seq)
                      :end2 (xsubseq-end seq))
             (incf current-pos
                   (xsubseq-len seq)))
    result))

(defun octets-concatenated-xsubseqs-to-sequence (seq)
  (let ((result (make-array (concatenated-xsubseqs-len seq)
                            :element-type '(unsigned-byte 8))))
    (declare (type octets result))
    (loop with current-pos of-type integer = 0
          for seq in (concatenated-xsubseqs-children seq)
          do (replace result (the octets (xsubseq-data seq))
                      :start1 current-pos
                      :start2 (xsubseq-start seq)
                      :end2 (xsubseq-end seq))
             (incf current-pos
                   (xsubseq-len seq)))
    result))

(defun octets-concatenated-xsubseqs-to-string (seq)
  (let ((result (make-array (concatenated-xsubseqs-len seq)
                            :element-type 'character)))
    (declare (type simple-string result))
    (loop with current-pos = 0
          for seq in (concatenated-xsubseqs-children seq)
          do (do ((i (xsubseq-start seq) (1+ i))
                  (j current-pos (1+ j)))
                 ((= i (xsubseq-end seq))
                  (setf current-pos j))
               (setf (aref result j)
                     (code-char
                      (the (unsigned-byte 8)
                           (aref (the octets (xsubseq-data seq)) i))))))
    result))

(defun string-concatenated-xsubseqs-to-sequence (seq)
  (let ((result (make-string (concatenated-xsubseqs-len seq))))
    (declare (type simple-string result))
    (loop with current-pos of-type integer = 0
          for seq in (concatenated-xsubseqs-children seq)
          do (replace result (the simple-string (xsubseq-data seq))
                      :start1 current-pos
                      :start2 (xsubseq-start seq)
                      :end2 (xsubseq-end seq))
             (incf current-pos
                   (xsubseq-len seq)))
    result))

(defmacro with-xsubseqs ((xsubseqs &key initial-value) &body body)
  `(let ((,xsubseqs ,(or initial-value
                         `(make-null-concatenated-xsubseqs))))
     ,@body

     (typecase ,xsubseqs
       (null-concatenated-xsubseqs nil)
       (xsubseq (xsubseq-to-sequence ,xsubseqs))
       (t (concatenated-xsubseqs-to-sequence ,xsubseqs)))))

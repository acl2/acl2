#|
 This file is a part of Colleen
 (c) 2016 Shirakumo http://tymoon.eu (shinmera@tymoon.eu)
 Author: Nicolas Hafner <shinmera@tymoon.eu>
|#

(in-package #:org.shirakumo.pathname-utils)

(defvar *wild-component* #+cormanlisp "*" #-cormanlisp :wild)
(defvar *wild-inferiors-component* #+cormanlisp "**" #-cormanlisp :wild-inferiors)
(defvar *wild-file* (make-pathname :directory NIL
                                   :name *wild-component*
                                   :type *wild-component*
                                   :version (or #-(or allegro abcl xcl) *wild-component*)))
(defvar *wild-directory* (make-pathname :directory `(:relative ,*wild-component*)
                                        :name NIL :type NIL :version NIL))
(defvar *wild-inferiors* (make-pathname :directory `(:relative ,*wild-inferiors-component*)
                                        :name NIL :type NIL :version NIL))
(defvar *wild-path* (merge-pathnames *wild-file* *wild-directory*))

(defun clean-directory-spec (dir)
  (when dir
    (let ((parts ()))
      (loop with back = 0
            for el in (reverse dir)
            until (find el '(:absolute :relative :home))
            do (cond 
                 ((unspecific-p el))
                 ((equal el "."))
                 ((eql el :back) (incf back))
                 ((< 0 back) (decf back))
                 (T (push el parts)))
            finally (case el
                      (:home (loop repeat back do (push :up parts)) (push :home parts))
                      (:relative (loop repeat back do (push :up parts)))))
      (list* (car dir) parts))))

(defun normalize-directory-spec (dir)
  (clean-directory-spec
   (etypecase dir
     (string `(:absolute ,dir))
     ((member :wild :wild-inferiors) `(:relative ,dir))
     (cons
      (if (member (first dir) '(:absolute :relative))
          dir
          #+gcl `(:relative ,dir)
          #-gcl (error "Invalid directory component ~s" dir)))
     (T (unless (unspecific-p dir)
          dir)))))

(defun normalize-pathname (pathname)
  (let ((pathname (pathname pathname)))
    (flet ((maybe-component (component)
             (let ((value (funcall component pathname)))
               (if (unspecific-p value) NIL value))))
      (make-pathname
       :host (maybe-component #'pathname-host)
       :device (maybe-component #'pathname-device)
       :name (maybe-component #'pathname-name)
       :type (maybe-component #'pathname-type)
       :version (maybe-component #'pathname-version)
       :directory (normalize-directory-spec (pathname-directory pathname))
       :defaults pathname))))

(defun pathname* (pathname)
  (typecase pathname
    (pathname pathname)
    (T (normalize-pathname pathname))))

(defun unspecific-p (component)
  (or (eq component NIL)
      (eq component :unspecific)
      (and (stringp component)
           (= 0 (length component)))))

(defun relative-p (pathname)
  (let ((pathname (pathname* pathname)))
    (when (or (eql :relative (car (pathname-directory pathname)))
              (unspecific-p (pathname-directory pathname)))
      pathname)))

(defun absolute-p (pathname)
  (let ((pathname (pathname* pathname)))
    (when (eql :absolute (car (pathname-directory pathname)))
      pathname)))

(defun logical-p (pathname)
  (let ((pathname (pathname* pathname)))
    (when (typep (pathname* pathname) 'logical-pathname)
      pathname)))

(defun physical-p (pathname)
  (let ((pathname (pathname* pathname)))
    (when (typep (pathname* pathname) '(and pathname (not logical-pathname)))
      pathname)))

(defun root-p (pathname)
  (let ((pathname (pathname* pathname)))
    (when (and (directory-p pathname)
               (equal '(:absolute) (normalize-directory-spec (pathname-directory pathname))))
      pathname)))

(defun directory-p (pathname)
  (let ((pathname (pathname* pathname)))
    (when (and (unspecific-p (pathname-name pathname))
               (unspecific-p (pathname-type pathname)))
      pathname)))

(defun file-p (pathname)
  (let ((pathname (pathname* pathname)))
    (unless (directory-p pathname)
      pathname)))

(defun subpath-p (subpath base &optional (root base))
  (when (relative-p root)
    (error "Cannot compare subpathness for a relative pathname root."))
  (let* ((subpath (normalize-pathname subpath))
         (base (normalize-pathname base))
         (subspec (cdr (pathname-directory (merge-pathnames subpath root))))
         (basespec (cdr (pathname-directory (merge-pathnames base root)))))
    (when (and (equal (pathname-host subpath) (pathname-host base))
               (equal (pathname-device subpath) (pathname-device base))
               (or (null (pathname-name base))
                   (equal (pathname-name subpath) (pathname-name base)))
               (or (null (pathname-type base))
                   (equal (pathname-type subpath) (pathname-type base)))
               (loop for (s . nil) on subspec
                     for (b . br) on basespec
                     do (unless (equal s b) (return))
                     finally (return (null br))))
      subpath)))

(defun pathname= (a b &key (ignore-version T))
  (let ((a (normalize-pathname a))
        (b (normalize-pathname b)))
    (labels ((normalize (part)
               (if (unspecific-p part) NIL part))
             (part= (part)
               (equal (normalize (funcall part a))
                      (normalize (funcall part b)))))
      (and (part= #'pathname-name)
           (part= #'pathname-type)
           (part= #'pathname-host)
           (part= #'pathname-device)
           (or ignore-version
               (part= #'pathname-version))
           (equal (normalize-directory-spec (pathname-directory a))
                  (normalize-directory-spec (pathname-directory b)))))))

(defun pathname-equal (a b)
  (pathname= (truename a) (truename b)))

(defun to-root (pathname)
  (make-pathname :name NIL :type NIL :version NIL :directory '(:absolute) :defaults (pathname pathname)))

(defun to-physical (pathname)
  (let ((pathname (pathname* pathname)))
    (if (logical-p pathname)
        (translate-logical-pathname pathname)
        pathname)))

(defun to-directory (pathname)
  (case pathname
    ((:up :back) (make-pathname :name NIL :type NIL :version NIL :directory `(:relative ,pathname) :defaults #p""))
    ((:home) (make-pathname :name NIL :type NIL :version NIL :defaults (user-homedir-pathname)))
    (T (make-pathname :name NIL :type NIL :version NIL :defaults (pathname* pathname)))))

(defun to-file (pathname)
  (make-pathname :directory NIL :device NIL :host NIL
                 :defaults (pathname* pathname)))

(defun subdirectory (pathname &rest subdirs)
  (let* ((base (to-directory pathname))
         (basedir (or (pathname-directory base) '(:relative)))
         (subdir (loop for sub in subdirs
                       for subpath = (etypecase sub
                                       ((or pathname keyword stream) (to-directory sub))
                                       (string (to-directory (concatenate 'string sub "/"))))
                       append (cdr (pathname-directory subpath)))))
    (make-pathname
     :directory (append basedir subdir)
     :defaults base)))

(defun pop-directory (pathname)
  (let* ((pathname (pathname* pathname))
         (directory (pathname-directory pathname)))
    (make-pathname :directory (when directory
                                (list* (car directory) (butlast (cdr directory))))
                   :defaults pathname)))

(defun parent (pathname)
  (let ((pathname (pathname* pathname)))
    (cond ((directory-p pathname)
           (let ((dir (pathname-directory pathname)))
             (if (root-p pathname)
                 pathname
                 (let ((dir (typecase (car (last (cdr dir)))
                              (null (list :relative :up))
                              (string (list* (car dir) (butlast (cdr dir))))
                              (T (append dir '(:up))))))
                   (make-pathname
                    :directory (unless (equal '(:relative) dir)
                                 dir)
                    :defaults pathname)))))
          (T
           (to-directory pathname)))))

(defun upwards (pathname)
  (cond ((directory-p pathname)
         (if (null (cdr (normalize-directory-spec (pathname-directory pathname))))
             (parent pathname)
             (subdirectory (parent (parent pathname))
                           (directory-name pathname))))
        (T
         (make-pathname :directory (pathname-directory
                                    (parent (to-directory pathname)))
                        :defaults pathname))))

(defun downwards (pathname subdir)
  (cond ((directory-p pathname)
         (if (null (cdr (normalize-directory-spec (pathname-directory pathname))))
             (subdirectory pathname
                           subdir)
             (subdirectory (parent pathname)
                           subdir
                           (directory-name pathname))))
        (T
         (make-pathname :directory (pathname-directory (subdirectory pathname subdir))
                        :defaults pathname))))

(defun enough-pathname (subpath base)
  (pathname* (enough-namestring subpath base)))

(defun relative-pathname (from to)
  (let ((from (normalize-pathname (merge-pathnames (to-directory from))))
        (to (normalize-pathname (merge-pathnames to))))
    (unless (equal (pathname-host from) (pathname-host to))
      (error "Cannot relativise pathnames across hosts."))
    (unless (equal (pathname-device from) (pathname-device to))
      (error "Cannot relativise pathnames across devices."))
    (let ((from-dir (copy-list (pathname-directory from)))
          (to-dir (copy-list (pathname-directory to)))
          (final-dir (list :relative)))
      (loop for a = (car from-dir)
            for b = (car to-dir)
            while (and from-dir to-dir (equal a b))
            do (pop from-dir) (pop to-dir))
      (loop repeat (length from-dir)
            do (push :up final-dir))
      (loop for to in to-dir
            do (push to final-dir))
      (make-pathname :directory (unless (equal '(:relative) final-dir)
                                  (nreverse final-dir))
                     :device NIL
                     :defaults to))))

(defun file-in (directory file)
  (make-pathname :name (pathname-name file)
                 :type (pathname-type file)
                 :defaults directory))

(defun file-type (pathname)
  (let ((pathname (pathname pathname)))
    (let ((type (pathname-type pathname))
          (name (pathname-name pathname)))
      (cond ((unspecific-p type)
             (let ((pos (position #\. name :from-end T)))
               (if pos (subseq name (1+ pos)) NIL)))
            (T
             (let ((pos (position #\. type :from-end T)))
               (if pos (subseq type (1+ pos)) type)))))))

(defun file-name (pathname)
  (let ((pathname (pathname pathname)))
    (if (directory-p pathname)
        NIL
        (format NIL "~a~@[.~a~]" (pathname-name pathname) (pathname-type pathname)))))

(defun directory-name (pathname)
  (let ((pathname (to-directory pathname)))
    (car (last (rest (pathname-directory pathname))))))

(defun directory-separator (&optional (pathname *default-pathname-defaults*))
  (let ((name (namestring (make-pathname :directory '(:absolute "nowhere") :defaults pathname))))
    (subseq name (+ (search "nowhere" name) (length "nowhere")))))

(defun components (pathname)
  (let ((pathname (pathname* pathname)))
    (list
     :namestring (namestring pathname)
     :truename (ignore-errors (truename pathname))
     :host (pathname-host pathname)
     :device (pathname-device pathname)
     :name (pathname-name pathname)
     :type (pathname-type pathname)
     :version (pathname-version pathname)
     :directory (pathname-directory pathname))))

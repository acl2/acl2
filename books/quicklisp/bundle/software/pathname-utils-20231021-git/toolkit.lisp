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

(declaim (inline unspecific-p))
(defun unspecific-p (component)
  (or (eq component NIL)
      (eq component :unspecific)
      (and (stringp component)
           (= 0 (length component)))))

(defun clean-directory-spec (dir &key resolve-home)
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
                      (:home (loop repeat back do (push :up parts))
                       (if resolve-home
                           (loop for dir in (reverse (rest (pathname-directory (user-homedir-pathname))))
                                 do (push dir parts))
                           (push :home parts)))
                      (:relative (loop repeat back do (push :up parts)))))
      (list* (car dir) parts))))

(defun normalize-directory-spec (dir &key resolve-home)
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
          dir)))
   :resolve-home resolve-home))

(defun normalize-pathname (pathname &key resolve-home)
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
       :directory (normalize-directory-spec (pathname-directory pathname) :resolve-home resolve-home)
       :defaults pathname))))

(defun pathname* (pathname)
  (typecase pathname
    (pathname pathname)
    (T (normalize-pathname pathname))))

(defun relative-p (pathname)
  (let ((pathname (pathname* pathname)))
    (if (or (eql :relative (car (pathname-directory pathname)))
              (unspecific-p (pathname-directory pathname)))
        (values pathname pathname)
        (values NIL pathname))))

(defun absolute-p (pathname)
  (let ((pathname (pathname* pathname)))
    (if (eql :absolute (car (pathname-directory pathname)))
        (values pathname pathname)
        (values NIL pathname))))

(defun logical-p (pathname)
  (let ((pathname (pathname* pathname)))
    (if (typep (pathname* pathname) 'logical-pathname)
        (values pathname pathname)
        (values NIL pathname))))

(defun physical-p (pathname)
  (let ((pathname (pathname* pathname)))
    (if (typep (pathname* pathname) '(and pathname (not logical-pathname)))
        (values pathname pathname)
        (values NIL pathname))))

(defun root-p (pathname)
  (let ((pathname (pathname* pathname)))
    (if (and (directory-p pathname)
             (equal '(:absolute) (normalize-directory-spec (pathname-directory pathname))))
        (values pathname pathname)
        (values NIL pathname))))

(defun directory-p (pathname)
  (let ((pathname (pathname* pathname)))
    (if (and (unspecific-p (pathname-name pathname))
             (unspecific-p (pathname-type pathname)))
        (values pathname pathname)
        (values NIL pathname))))

(defun file-p (pathname)
  (let ((pathname (pathname* pathname)))
    (if (directory-p pathname)
        (values NIL pathname)
        (values pathname pathname))))

(defun subpath-p (subpath base &optional (root base))
  (when (relative-p root)
    (error "Cannot compare subpathness for a relative pathname root."))
  (let* ((subpath (normalize-pathname subpath))
         (base (normalize-pathname base))
         (subspec (cdr (pathname-directory (merge-pathnames subpath root))))
         (basespec (cdr (pathname-directory (merge-pathnames base root)))))
    (if (and (equal (pathname-host subpath) (pathname-host base))
             (equal (pathname-device subpath) (pathname-device base))
             (or (null (pathname-name base))
                 (equal (pathname-name subpath) (pathname-name base)))
             (or (null (pathname-type base))
                 (equal (pathname-type subpath) (pathname-type base)))
             (loop for (s . nil) on subspec
                   for (b . br) on basespec
                   do (unless (equal s b) (return))
                   finally (return (null br))))
        (values subpath subpath)
        (values NIL subpath))))

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

(defun to-relative (pathname)
  (let ((pathname (pathname* pathname)))
    (make-pathname :directory (when (rest (pathname-directory pathname))
                                (list* :relative (rest (pathname-directory pathname))))
                   :defaults pathname)))

(defun to-absolute (pathname)
  (let ((pathname (pathname* pathname)))
    (make-pathname :directory (list* :absolute (rest (pathname-directory pathname)))
                   :defaults pathname)))

(defun force-directory (pathname)
  (let ((pathname (pathname* pathname)))
    (make-pathname :directory (append (or (normalize-directory-spec (pathname-directory pathname))
                                          (list :relative))
                                      (list (file-namestring pathname)))
                   :name NIL :type NIL :version NIL :defaults pathname)))

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
  (let ((from (normalize-pathname (merge-pathnames (to-directory from)) :resolve-home T))
        (to (normalize-pathname (merge-pathnames to) :resolve-home T)))
    (unless (equal (pathname-host from) (pathname-host to))
      (error "Cannot relativise pathnames across hosts."))
    (unless (equal (pathname-device from) (pathname-device to))
      (error "Cannot relativise pathnames across devices."))
    (let ((from-dir (pathname-directory from))
          (to-dir (pathname-directory to))
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
    (when (wild-pathname-p (make-pathname :name (pathname-name pathname) :type (pathname-type pathname)))
      (error "Cannot produce a concrete file-type for a wild pathname:~%  ~s" pathname))
    (let ((type (pathname-type pathname))
          (name (pathname-name pathname)))
      (cond ((unspecific-p type)
             (let ((pos (position #\. name :from-end T)))
               (if pos (subseq name (1+ pos)) NIL)))
            (T
             (let ((pos (position #\. type :from-end T)))
               (if (and pos (< 0 pos)) (subseq type (1+ pos)) type)))))))

(defun file-name (pathname)
  (let ((pathname (pathname pathname)))
    (when (wild-pathname-p (make-pathname :name (pathname-name pathname) :type (pathname-type pathname)))
      (error "Cannot produce a concrete file-name for a wild pathname:~%  ~s" pathname))
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

(defun parse-native-namestring (namestring &key (as :file) junk-allowed)
  #+windows (parse-dos-namestring namestring :as as :junk-allowed junk-allowed)
  #+unix (parse-unix-namestring namestring :as as :junk-allowed junk-allowed)
  #-(or windows unix)
  (let ((path (parse-namestring namestring NIL *default-pathname-defaults* :junk-allowed junk-allowed)))
    (if (and (eql :directory as)
             (or (pathname-name path) (pathname-type path)))
        (make-pathname :directory (append (pathname-directory path) (list (format NIL "~a~@[.~a~]" (pathname-name path) (pathname-type path)))))
        path)))

(defun parse-unix-namestring (namestring &key (as :file) junk-allowed)
  (if (string= "" namestring)
      #p""
      (let ((base (case (char namestring 0)
                    (#\~ '(:home :absolute))
                    (#\/ '(:absolute))
                    (T '(:relative))))
            (buf (make-string-output-stream))
            (name NIL)
            (type NIL))
        (flet ((push-file ()
                 (let* ((leftover (get-output-stream-string buf))
                        (dot (position #\. leftover :from-end T)))
                   (when (string/= "" leftover)
                     (case dot
                       ((0 NIL) (setf name leftover))
                       (T (setf name (subseq leftover 0 dot)
                                type (subseq leftover (1+ dot))))))))
               (push-dir ()
                 (let* ((dirname (get-output-stream-string buf)))
                   (cond ((string= "" dirname))
                         ((string= "." dirname))
                         ((string= ".." dirname) (push :back base))
                         (T (push dirname base))))))
          (loop for i from (if (eql :relative (first base)) 0 1) below (length namestring)
                for char = (char namestring i)
                do (case char
                     (#\/ (push-dir))
                     (#\Nul (unless junk-allowed
                              (cerror "Ignore the character" "Illegal character ~c in namestring:~%  ~a"
                                      char namestring)))
                     (T (write-char char buf)))
                finally (ecase as
                          (:file (push-file))
                          (:directory (push-dir)))))
        (make-pathname :name name :type type :directory (unless (equal base '(:relative)) (reverse base))))))

(defun getenv (x)
  (declare (ignorable x))
  #+(or abcl clasp clisp ecl xcl) (ext:getenv x)
  #+allegro (sys:getenv x)
  #+clozure (ccl:getenv x)
  #+cmucl (unix:unix-getenv x)
  #+scl (cdr (assoc x ext:*environment-list* :test #'string=))
  #+cormanlisp
  (let* ((buffer (ct:malloc 1))
         (cname (ct:lisp-string-to-c-string x))
         (needed-size (win:getenvironmentvariable cname buffer 0))
         (buffer1 (ct:malloc (1+ needed-size))))
    (prog1 (if (zerop (win:getenvironmentvariable cname buffer1 needed-size))
               nil
               (ct:c-string-to-lisp-string buffer1))
      (ct:free buffer)
      (ct:free buffer1)))
  #+gcl (system:getenv x)
  #+genera nil
  #+lispworks (lispworks:environment-variable x)
  #+mcl (ccl:with-cstrs ((name x))
          (let ((value (_getenv name)))
            (unless (ccl:%null-ptr-p value)
              (ccl:%get-cstring value))))
  #+mkcl (#.(or (find-symbol 'getenv :si) (find-symbol 'getenv :mk-ext) '((lambda (x) nil))) x)
  #+sbcl (sb-ext:posix-getenv x)
  #-(or abcl allegro clasp clisp clozure cmucl cormanlisp ecl gcl genera lispworks mcl mkcl sbcl scl xcl)
  NIL)

(defun parse-dos-namestring (namestring &key (as :file) junk-allowed)
  (if (string= "" namestring)
      #p""
      (let ((directory '(:relative))
            (buf (make-string-output-stream))
            (device NIL)
            (name NIL)
            (type NIL)
            (base #p"")
            (start 0))
        (let ((colon (position #\: namestring)))
          (when (and colon (< 0 colon)
                     (loop for i from 0 below colon always (alpha-char-p (char namestring i))))
            (setf device (subseq namestring 0 colon))
            (setf start (1+ colon))))
        (case (char namestring start)
          ((#\\ #\/)
           (setf directory '(:absolute))
           (incf start)))
        (flet ((push-file ()
                 (let* ((leftover (get-output-stream-string buf))
                        (dot (position #\. leftover :from-end T)))
                   (when (string/= "" leftover)
                     (case dot
                       ((0 NIL) (setf name leftover))
                       (T (setf name (subseq leftover 0 dot)
                                type (subseq leftover (1+ dot))))))))
               (push-dir ()
                 (let* ((dirname (get-output-stream-string buf)))
                   (cond ((string= "" dirname))
                         ((string= "." dirname))
                         ((string= ".." dirname)
                          (push :back directory))
                         ((and (char= #\% (char dirname 0))
                               (char= #\% (char dirname (1- (length dirname))))
                               (< 2 (length dirname))
                               (equal '(:relative) directory))
                          ;; Resolve the envvar
                          (let ((var (or (getenv (subseq dirname 1 (1- (length dirname)))) "")))
                            (setf base (parse-dos-namestring var :as :directory :junk-allowed junk-allowed))))
                         (T (push dirname directory))))))
          (loop for i from start below (length namestring)
                for char = (char namestring i)
                do (case char
                     ((#\\ #\/) (push-dir))
                     ((#\< #\> #\: #\" #\| #\? #\* #\Nul)
                      (unless junk-allowed
                        (cerror "Ignore the character" "Illegal character ~c in namestring:~%  ~a"
                                char namestring)))
                     (T (write-char char buf)))
                finally (ecase as
                          (:file (push-file))
                          (:directory (push-dir)))))
        (merge-pathnames (make-pathname :name name :type type :device device :directory (unless (equal directory '(:relative)) (reverse directory)))
                         base))))

(defun native-namestring (pathname &key stream junk-allowed)
  #+windows (dos-namestring pathname :stream stream :junk-allowed junk-allowed)
  #+unix (unix-namestring pathname :stream stream :junk-allowed junk-allowed)
  #-(or windows unix) (write-string (namestring pathname) stream))

(defun unix-namestring (pathname &key (stream) junk-allowed)
  (etypecase stream
    (null
     (with-output-to-string (stream)
       (unix-namestring pathname :stream stream :junk-allowed junk-allowed)))
    (stream
     (flet ((write-part (part)
              (loop for char across part
                    do (case char
                         ((#\/ #\Nul)
                          (unless junk-allowed
                            (cerror "Don't print the character." "Illegal character ~c in pathname:~%  ~a"
                                    char pathname)))
                         (T
                          (write-char char stream))))))
       (let ((dir (pathname-directory pathname)))
         (cond ((and (eql :absolute (first dir))
                     (eql :home (second dir)))
                (unix-namestring (user-homedir-pathname) :stream stream)
                (setf dir (cdr dir)))
               ((eql :absolute (first dir))
                (write-char #\/ stream)))
         (loop for component in (rest dir)
               do (cond ((find component '(:back :up))
                         (write-part ".."))
                        ((find component '(".." ".") :test #'string=)
                         (unless junk-allowed
                           (cerror "Print the component anyway" "Illegal directory ~s in pathname:~%  ~a"
                                   component pathname))
                         (write-part component))
                        (T (write-part component)))
                  (write-char #\/ stream)))
       (when (pathname-name pathname)
         (write-part (pathname-name pathname)))
       (when (pathname-type pathname)
         (write-char #\. stream)
         (write-part (pathname-type pathname))))
     stream)))

(defun dos-namestring (pathname &key (stream) junk-allowed)
  (etypecase stream
    (null
     (with-output-to-string (stream)
       (dos-namestring pathname :stream stream :junk-allowed junk-allowed)))
    (stream
     (flet ((write-part (part)
              (loop for char across part
                    do (case char
                         ((#\< #\> #\: #\" #\| #\? #\* #\\ #\/ #\Nul)
                          (unless junk-allowed
                            (cerror "Don't print the character." "Illegal character ~c in pathname:~%  ~a"
                                    char pathname)))
                         (T
                          (write-char char stream))))))
       (let ((dir (pathname-directory pathname)))
         (cond ((and (eql :absolute (first dir))
                     (eql :home (second dir)))
                (dos-namestring (user-homedir-pathname) :stream stream)
                (setf dir (cdr dir)))
               ((eql :absolute (first dir))
                (typecase (pathname-device pathname)
                  (null (write-string "\\" stream))
                  (string (format stream "~a:\\" (pathname-device pathname)))
                  (T (write-string (namestring (make-pathname :device (pathname-device pathname))) stream)))))
         (loop for component in (rest dir)
               do (cond ((find component '(:back :up))
                         (write-string ".." stream))
                        ((find component '(".." ".") :test #'string=)
                         (unless junk-allowed
                           (cerror "Print the component anyway" "Illegal directory ~s in pathname:~%  ~a"
                                   component pathname))
                         (write-part component))
                        (T (write-part component)))
                  (write-char #\\ stream))
         (when (pathname-name pathname)
           (write-part (pathname-name pathname)))
         (when (pathname-type pathname)
           (write-char #\. stream)
           (write-part (pathname-type pathname)))
         stream)))))

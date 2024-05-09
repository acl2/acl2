(in-package :cl-user)
(defpackage quri.parser
  (:use :cl
        :quri.error
        :quri.port
        :quri.util)
  #+(or sbcl openmcl cmu allegro)
  (:import-from #+sbcl :sb-cltl2
                #+openmcl :ccl
                #+cmu :ext
                #+allegro :sys
                :variable-information)
  (:import-from :alexandria
                :with-gensyms
                :define-constant)
  (:export :parse-uri
           :parse-scheme
           :parse-authority
           :parse-path
           :parse-query
           :parse-fragment))
(in-package :quri.parser)

(declaim (type (simple-array fixnum (128)) +uri-char+))
(define-constant +uri-char+
    (let ((uri-char (make-array 128 :element-type 'fixnum :initial-element 0)))
      (dotimes (i 128 uri-char)
        (let ((char (code-char i)))
          (when (or (alphanumericp char)
                    (char= char #\%)
                    (char= char #\:)
                    (char= char #\@)
                    (char= char #\-)
                    (char= char #\.)
                    (char= char #\_)
                    (char= char #\~)
                    (char= char #\!)
                    (char= char #\$)
                    (char= char #\&)
                    (char= char #\')
                    (char= char #\()
                    (char= char #\))
                    (char= char #\*)
                    (char= char #\+)
                    (char= char #\,)
                    (char= char #\;)
                    (char= char #\=))
            (setf (aref uri-char i) 1)))))
  :test 'equalp)

#+(or sbcl openmcl cmu allegro)
(define-compiler-macro parse-uri (&whole form &environment env data &key start end)
  (declare (ignore start end))
  (let ((type (cond
                ((constantp data) (type-of data))
                ((symbolp data) (cdr (assoc 'type (nth-value 2 (variable-information data env))))))))
    (cond
      ((null type) form)
      ((subtypep type 'simple-string) `(parse-uri-string ,@(cdr form)))
      ((subtypep type 'simple-byte-vector) `(parse-uri-byte-vector ,@(cdr form)))
      (t form))))

(defun parse-uri (data &key (start 0) end)
  "Parse a URI string or a URI byte vector and return 7 URI components:
- scheme,
- userinfo,
- host name,
- port,
- path,
- query,
- fragment."
  (etypecase data
    (simple-string (parse-uri-string data :start start :end end))
    (simple-byte-vector (parse-uri-byte-vector data :start start :end end))
    (string (parse-uri (coerce data 'simple-string) :start start :end end))))

(defun parse-uri-string (data &key (start 0) end)
  (declare (type simple-string data)
           (optimize (speed 3) (safety 2)))
  (let (scheme userinfo host port path query fragment
        (parse-start start)
        (parse-end (or end (length data))))
    (declare (type fixnum parse-start parse-end))
    (block nil
      (flet ((parse-from-path (data start)
               (declare (type simple-string data)
                        (type fixnum start))
               (multiple-value-bind (data start end)
                   (parse-path-string data :start start :end parse-end)
                 (declare (type simple-string data)
                          (type fixnum start end))
                 (unless (= start end)
                   (setq path (subseq data start end)))
                 ;; Pitfall: There may be no query but a fragment that has a '?', e.g.
                 ;; https://example.org/#/?b
                 (let ((maybe-query-start (or (nth-value 1 (parse-query-string data :start end :end parse-end))
                                              (1+ parse-end)))
                       (maybe-fragment-start (or (nth-value 1 (parse-fragment-string data :start end :end parse-end))
                                                 (1+ parse-end))))
                   (flet ((parse-fragment (path-end)
                            (multiple-value-bind (data start end)
                                (parse-fragment-string data :start (or path-end end) :end parse-end)
                              (when data
                                (setq fragment (subseq (the string data) (the fixnum start) (the fixnum end)))))))
                     (if (< (the fixnum maybe-query-start) (the fixnum maybe-fragment-start))
                         (multiple-value-bind (parsed-data path-start path-end)
                             (parse-query-string data :start end :end parse-end)
                           (when parsed-data
                             (setq query (subseq (the string parsed-data) (the fixnum path-start) (the fixnum path-end))))
                           (parse-fragment path-end))
                         (parse-fragment end)))))))
        (multiple-value-bind (parsed-data start end got-scheme)
            (parse-scheme-string data :start parse-start :end parse-end)
          (if parsed-data
              (locally (declare (type fixnum start end))
                (setq scheme
                      (or got-scheme
                          (string-downcase (subseq data start end))))
                (incf end))             ;eat the trailing #\:
              (setq scheme nil
                    end parse-start))
          (locally (declare (type fixnum end))
            (unless (= end parse-end)
              (multiple-value-bind (parsed-data userinfo-start userinfo-end
                                    host-start host-end port-start port-end)
                  (parse-authority-string data :start end :end parse-end)
                (when parsed-data
                  (locally (declare (type fixnum host-start host-end))
                    (when userinfo-start
                      (setq userinfo (subseq (the string data) (the fixnum userinfo-start) (the fixnum userinfo-end))))
                    (unless (= host-start host-end)
                      (setq host (subseq data host-start host-end)))
                    (cond
                      (port-start
                       (locally (declare (type fixnum port-start port-end))
                         (unless (= port-start port-end)
                           (handler-case
                               (setq port
                                     (parse-integer data :start (the fixnum port-start) :end (the fixnum port-end)))
                             (error ()
                               (error 'uri-invalid-port
                                      :data data :position port-start))))))
                      (scheme
                       (setq port (scheme-default-port scheme))))))
                (locally (declare (optimize (safety 0)))
                  (parse-from-path data (or port-end host-end end)))))))))
    (values scheme userinfo host port path query fragment)))

(defun parse-uri-byte-vector (data &key (start 0) end)
  (declare (type simple-byte-vector data)
           (optimize (speed 3) (safety 2)))
  (let (scheme userinfo host port path query fragment
        (parse-start start)
        (parse-end (or end (length data))))
    (declare (type fixnum parse-start parse-end))
    (flet ((subseq* (data &optional (start 0) end)
             (declare (type simple-byte-vector data))
             (values (babel:octets-to-string data :start start :end end)))
           (parse-integer-from-bv (data &key (start 0) end)
             (declare (type fixnum start end)
                      (optimize (speed 3) (safety 2)))
             (when (= start end)
               (return-from parse-integer-from-bv nil))
             (do ((i start (1+ i))
                  (res 0))
                 ((= i end) res)
               (declare (type fixnum i res))
               (let ((code (aref data i)))
                 (declare (type fixnum code)
                          #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
                 (unless (<= #.(char-code #\0) code #.(char-code #\9))
                   (error 'uri-invalid-port
                          :data data :position i))

                 (setq res (+ (* res 10)
                              (- code #.(char-code #\0))))))))
      (block nil
        (flet ((parse-from-path (data start)
                 (declare (type simple-byte-vector data)
                          (type fixnum start))
                 (multiple-value-bind (data start end)
                     (parse-path-byte-vector data :start start :end parse-end)
                   (declare (type fixnum start end))
                   (unless (= start end)
                     (setq path (subseq* data start end)))
                   (multiple-value-bind (parsed-data path-start path-end)
                       (parse-query-byte-vector data :start end :end parse-end)
                     (when parsed-data
                       (setq query (subseq* parsed-data (the fixnum path-start) (the fixnum path-end))))
                     (multiple-value-bind (data start end)
                         (parse-fragment-byte-vector data :start (or path-end end) :end parse-end)
                       (when data
                         (setq fragment (subseq* data (the fixnum start) (the fixnum end)))))))))
          (multiple-value-bind (parsed-data start end got-scheme)
              (parse-scheme-byte-vector data :start parse-start :end parse-end)
            (if parsed-data
                (locally (declare (type fixnum start end))
                  (setq scheme
                    (or got-scheme
                        (let ((data-str (make-string (- end start))))
                          (do ((i start (1+ i))
                               (j 0 (1+ j)))
                              ((= i end) data-str)
                            (let ((code (aref data i)))
                              (setf (aref data-str j)
                                    (code-char
                                     (if (<= #.(char-code #\A) code #.(char-code #\Z))
                                         (+ code 32)
                                         code))))))))
                  (incf end))           ;eat the trailing #\:
                (setq scheme nil
                      end parse-start))
            (locally (declare (type fixnum end))
              (unless (= end parse-end)
                (multiple-value-bind (parsed-data userinfo-start userinfo-end
                                      host-start host-end port-start port-end)
                    (parse-authority-byte-vector data :start end :end parse-end)
                  (when parsed-data
                    (locally (declare (type simple-byte-vector data)
                                      (type fixnum host-start host-end))
                      (when userinfo-start
                        (setq userinfo (subseq* data (the fixnum userinfo-start) (the fixnum userinfo-end))))
                      (unless (= host-start host-end)
                        (setq host (subseq* data host-start host-end)))
                      (cond
                        (port-start
                         (setq port
                               (parse-integer-from-bv data :start port-start :end port-end)))
                        (scheme
                         (setq port (scheme-default-port scheme))))))
                  (locally (declare (optimize (safety 0)))
                    (parse-from-path data (or port-end host-end (1+ end)))))))))))
    (values scheme userinfo host port path query fragment)))

(defmacro defun-with-array-parsing (name (char p data start end &rest other-args) &body body)
  (with-gensyms (args type form env)
    (flet ((intern-proper-case (a b)
             (intern (format nil "~:@(~a-~a~)" a b))))
      (let ((fn-for-string (intern-proper-case name :string))
            (fn-for-byte-vector (intern-proper-case name :byte-vector)))
        `(progn
           (defun ,name (,data &rest ,args &key ,start ,end)
             (declare (ignore ,start ,end))
             (etypecase ,data
                 (simple-string (apply ',(intern-proper-case name :string) data ,args))
                 (simple-byte-vector (apply ',(intern-proper-case name :byte-vector) data ,args))))

           #+(or sbcl openmcl cmu allegro)
           (define-compiler-macro ,name (&whole ,form &environment ,env ,data &rest ,args)
             (declare (ignore ,args))
             (let ((,type (cond
                            ((constantp ,data) (type-of ,data))
                            ((symbolp ,data) (cdr (assoc 'type (nth-value 2 (variable-information ,data ,env))))))))
               (cond
                 ((null ,type) ,form)
                 ((subtypep ,type 'simple-string) `(,',fn-for-string ,@(cdr ,form)))
                 ((subtypep ,type 'simple-byte-vector) `(,',fn-for-byte-vector ,@(cdr ,form)))
                 (t ,form))))

           (defun ,fn-for-string (,data &key (,start 0) (,end (length ,data)) ,@other-args)
             (declare (type simple-string ,data)
                      (type fixnum ,start ,end)
                      (optimize (speed 3) (safety 2)))
             (macrolet ((char=* (char1 char2)
                          `(char= ,char1 ,char2))
                        (char-code* (char)
                          `(char-code ,char))
                        (scheme-char-p* (char)
                          `(scheme-char-p ,char))
                        (standard-alpha-char-p* (char)
                          `(standard-alpha-char-p ,char)))
               (block ,name
                 (with-string-parsing (,char ,p ,data ,start ,end)
                   (declare (type fixnum ,p))
                   ,@body))))

           (defun ,fn-for-byte-vector (,data &key (,start 0) (,end (length ,data)) ,@other-args)
             (declare (type simple-byte-vector ,data)
                      (type fixnum ,start ,end)
                      (optimize (speed 3) (safety 2)))
             (macrolet ((char=* (byte char)
                          `(= ,byte ,(char-code char)))
                        (char-code* (byte)
                          byte)
                        (scheme-char-p* (byte)
                          `(scheme-byte-p ,byte))
                        (standard-alpha-char-p* (byte)
                          `(standard-alpha-byte-p ,byte)))
               (block ,name
                 (with-byte-array-parsing (,char ,p ,data ,start ,end)
                   (declare (type fixnum ,p))
                     ,@body)))))))))

(defun scheme-char-p (char)
  (declare (type character char)
           (optimize (speed 3) (safety 0)))
  (or (standard-alphanumeric-p char)
      (char= char #\+)
      (char= char #\-)
      (char= char #\.)))

(defun scheme-byte-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (or (standard-alphanumeric-byte-p byte)
      (= byte (char-code #\+))
      (= byte (char-code #\-))
      (= byte (char-code #\.))))

(defun-with-array-parsing parse-scheme (char p data start end)
  (parsing-scheme-start
   (when (or (char=* char #\h)
             (char=* char #\H))
     (goto parsing-H))
   (unless (standard-alpha-char-p* char)
     (return-from parse-scheme nil))
   (gonext))

  (parsing-scheme
   (cond
     ((char=* char #\:)
      (return-from parse-scheme
        (values data start p)))
     ((scheme-char-p* char)
      (redo))
     (t
      (return-from parse-scheme nil))))

  (parsing-H
   (if (or (char=* char #\t)
           (char=* char #\T))
       (goto parsing-HT)
       (goto parsing-scheme 0)))

  (parsing-HT
   (if (or (char=* char #\t)
           (char=* char #\T))
       (goto parsing-HTT)
       (goto parsing-scheme 0)))

  (parsing-HTT
   (if (or (char=* char #\p)
           (char=* char #\P))
       (goto parsing-HTTP)
       (goto parsing-scheme 0)))

  (parsing-HTTP
   (cond
     ((char=* char #\:)
      (return-from parse-scheme
        (values data start p "http")))
     ((or (char=* char #\s)
          (char=* char #\S))
      (goto parsing-HTTPS))
     (t (goto parsing-scheme 0))))

  (parsing-HTTPS
   (if (char=* char #\:)
       (return-from parse-scheme
         (values data start p "https"))
       (goto parsing-scheme 0)))

  (:eof (return-from parse-scheme nil)))

(defun-with-array-parsing parse-authority (char p data start end
                                                &aux
                                                (authority-mark nil)
                                                (colon-mark nil)
                                                userinfo-start
                                                userinfo-end
                                                host-start
                                                host-end
                                                port-start
                                                port-end)
  (parsing-first
   (cond
     ((char=* char #\/)
      (gonext))
     (t
      (return-from parse-authority
        (values data nil nil start start nil nil)))))

  (parsing-authority-starting
   (unless (char=* char #\/)
     (return-from parse-authority
        (values data nil nil start start nil nil)))
   (setq authority-mark (1+ p))
   (gonext))

  (parsing-authority-start
   (if (char=* char #\[)
       (goto parsing-ipliteral)
       (gonext 0)))

  ;; parsing host or userinfo
  (parsing-authority
   (cond
     ((char=* char #\:)
      (setq colon-mark p)
      (redo))
     ((char=* char #\@)
      (when userinfo-start
        (error 'uri-malformed-string :data data :position p))
      (setq userinfo-start authority-mark
            userinfo-end p)
      (setq authority-mark (1+ p)
            colon-mark nil)
      (redo))
     ((or (char=* char #\/)
          (char=* char #\?)
          (char=* char #\#))
      (go :eof))
     ((let ((code (char-code* char)))
        (or (<= 128 code)
            (= (aref +uri-char+ code) 1)))
      (redo))
     (t (error 'uri-malformed-string
               :data data :position p))))

  (parsing-ipliteral
   (if (char=* char #\])
       (goto parsing-authority)
       (redo)))

  (:eof
   (unless authority-mark
     (return-from parse-authority
       (values data
               nil nil
               start start
               nil nil)))
   (if colon-mark
       (setq host-start authority-mark
             host-end colon-mark
             port-start (1+ colon-mark)
             port-end p)
       (setq host-start authority-mark
             host-end p))
   (return-from parse-authority
     (values data
             userinfo-start userinfo-end
             host-start host-end
             port-start port-end))))

(defun path-char-p (char)
  (declare (type character char)
           (optimize (speed 3) (safety 0)))
  (let ((byte (char-code char)))
    (and (< byte 128)
         (or (= (aref +uri-char+ byte) 1)
             (= byte #.(char-code #\/))))))

(defun path-byte-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (or (= (aref +uri-char+ byte) 1)
      (= byte (char-code #\/))))

(defun query-char-p (char)
  (declare (type character char)
           (optimize (speed 3) (safety 0)))
  (or (path-char-p char)
      (char= char #\?)))

(defun query-byte-p (byte)
  (declare (type (unsigned-byte 8) byte)
           (optimize (speed 3) (safety 0)))
  (or (path-byte-p byte)
      (= byte (char-code #\?))))

(defmacro parse-until-string (delimiters data &key start end test)
  (with-gensyms (p char)
    `(block nil
       (progn
         (do ((,p ,start (1+ ,p)))
             ((= ,p ,end)
              (values ,data ,start ,end))
           (declare (type fixnum ,p))
           (let ((,char (aref ,data ,p)))
             (declare (type character ,char))
             (when (or ,@(loop for delim in delimiters
                               collect `(char= ,delim ,char)))
               (return (values ,data ,start ,p)))
             ,@(when test
                 `((unless (funcall ,test ,char)
                      (error 'uri-malformed-string
                             :data ,data :position ,p))))))))))

(defmacro parse-until-byte-vector (delimiters data &key start end test)
  (with-gensyms (p byte)
    `(block nil
       (progn
         (do ((,p ,start (1+ ,p)))
             ((= ,p ,end)
              (values ,data ,start ,end))
           (declare (type fixnum ,p))
           (let ((,byte (aref ,data ,p)))
             (declare (type (unsigned-byte 8) ,byte))
             (when (or ,@(loop for delim in delimiters
                               collect `(= ,(char-code delim) ,byte)))
               (return (values ,data ,start ,p)))
             ,@(when test
                 `((unless (funcall ,test ,byte)
                     (error 'uri-malformed-string
                            :data ,data :position ,p))))))))))

(defun parse-path (data &key (start 0) (end (length data)))
  (etypecase data
    (simple-string
     (parse-path-string data :start start :end end))
    (simple-byte-vector
     (parse-path-byte-vector data :start start :end end))))

(defun parse-path-string (data &key (start 0) (end (length data)))
  (declare (type simple-string data)
           (optimize (speed 3) (safety 2))
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (parse-until-string (#\? #\#) data :start start :end end))

(defun parse-path-byte-vector (data &key (start 0) (end (length data)))
  (declare (type simple-byte-vector data)
           (optimize (speed 3) (safety 2))
           #+sbcl (sb-ext:muffle-conditions sb-ext:compiler-note))
  (parse-until-byte-vector (#\? #\#) data :start start :end end))

(defun parse-query (data &key (start 0) (end (length data)))
  (etypecase data
    (string
     (parse-query-string data :start start :end end))
    (simple-byte-vector
     (parse-query-byte-vector data :start start :end end))))

#+(or sbcl openmcl cmu allegro)
(define-compiler-macro parse-query (&whole form &environment env data &key start end)
  (declare (ignore start end))
  (let ((type (cond
                ((constantp data) (type-of data))
                ((symbolp data) (cdr (assoc 'type (nth-value 2 (variable-information data env))))))))
    (cond
      ((null type) form)
      ((subtypep type 'simple-string) `(parse-query-string ,@(cdr form)))
      ((subtypep type 'simple-byte-vector) `(parse-query-byte-vector ,@(cdr form)))
      (t form))))

(defun parse-query-string (data &key (start 0) (end (length data)))
  (declare (type simple-string data)
           (type fixnum start end)
           (optimize (speed 3) (safety 2)))
  (let ((?-pos (position #\? data :start start :end end)))
    (when ?-pos
      (parse-until-string (#\#) data :start (1+ (the fixnum ?-pos)) :end end))))

(defun parse-query-byte-vector (data &key (start 0) (end (length data)))
  (declare (type simple-byte-vector data)
           (type fixnum start end)
           (optimize (speed 3) (safety 2)))
  (let ((?-pos (position #.(char-code #\?) data :start start :end end)))
    (when ?-pos
      (parse-until-byte-vector (#\#) data :start (1+ (the fixnum ?-pos)) :end end))))

(defun parse-fragment (data &key (start 0) (end (length data)))
  (etypecase data
    (string (parse-fragment-string data :start start :end end))
    (simple-byte-vector (parse-fragment-byte-vector data :start start :end end))))

#+(or sbcl openmcl cmu allegro)
(define-compiler-macro parse-fragment (&whole form &environment env data &key start end)
  (declare (ignore start end))
  (let ((type (cond
                ((constantp data) (type-of data))
                ((symbolp data) (cdr (assoc 'type (nth-value 2 (variable-information data env))))))))
    (cond
      ((null type) form)
      ((subtypep type 'simple-string) `(parse-fragment-string ,@(cdr form)))
      ((subtypep type 'simple-byte-vector) `(parse-fragment-byte-vector ,@(cdr form)))
      (t form))))

(defun parse-fragment-string (data &key (start 0) (end (length data)))
  (declare (type simple-string data)
           (type fixnum start end)
           (optimize (speed 3) (safety 2)))
  (let ((|#-pos| (position #\# data
                           :start start
                           :end end)))
    (when |#-pos|
      (values data (1+ (the fixnum |#-pos|)) end))))

(defun parse-fragment-byte-vector (data &key (start 0) (end (length data)))
  (declare (type simple-byte-vector data)
           (type fixnum start end)
           (optimize (speed 3) (safety 2)))
  (let ((|#-pos| (position #\# data
                           :start start
                           :end end
                           :key #'code-char)))
    (when |#-pos|
      (values data (1+ (the fixnum |#-pos|)) end))))

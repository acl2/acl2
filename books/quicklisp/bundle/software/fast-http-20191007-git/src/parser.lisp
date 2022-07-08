(in-package :cl-user)
(defpackage fast-http.parser
  (:use :cl
        :fast-http.http
        :fast-http.error
        :proc-parse)
  (:import-from :fast-http.byte-vector
                :+space+
                :+tab+
                :+cr+
                :+lf+
                :simple-byte-vector
                :digit-byte-char-p
                :digit-byte-char-to-integer)
  (:import-from :fast-http.util
                :defun-insane
                :defun-speedy)
  (:import-from :alexandria
                :format-symbol
                :with-gensyms
                :define-constant
                :when-let)
  (:export :callbacks

           :make-callbacks

           :parse-request
           :parse-response

           ;; Conditions
           :eof

           ;; Types
           :pointer))
(in-package :fast-http.parser)

;;
;; Variables

(declaim (type fixnum +max-header-line+))
(defconstant +max-header-line+ 1024
  "Maximum number of header lines allowed.

This restriction is for protecting users' application
against denial-of-service attacks where the attacker feeds
us a never-ending header that the application keeps buffering.")


;;
;; Types

(deftype pointer () 'integer)


;;
;; Callbacks

(defstruct callbacks
  (message-begin nil :type (or null function))     ;; 1 arg
  (url nil :type (or null function))
  (first-line nil :type (or null function))
  (status nil :type (or null function))
  (header-field nil :type (or null function))
  (header-value nil :type (or null function))
  (headers-complete nil :type (or null function))  ;; 1 arg
  (body nil :type (or null function))
  (message-complete nil :type (or null function)))

(defmacro callback-data (name http callbacks data start end)
  (with-gensyms (callback e)
    `(when-let (,callback (,(format-symbol t "~A-~A" :callbacks name) ,callbacks))
       (handler-bind ((error
                        (lambda (,e)
                          (unless (typep ,e 'fast-http-error)
                            (error ',(format-symbol t "~A-~A" :cb name)
                                   :error ,e)
                            (abort ,e)))))
         (funcall ,callback ,http ,data ,start ,end)))))

(defmacro callback-notify (name http callbacks)
  (with-gensyms (callback e)
    `(when-let (,callback (,(format-symbol t "~A-~A" :callbacks name) ,callbacks))
       (handler-bind ((error
                        (lambda (,e)
                          (unless (typep ,e 'fast-http-error)
                            (error ',(format-symbol t "~A-~A" :cb name)
                                   :error ,e)
                            (abort ,e)))))
         (funcall ,callback ,http)))))


;;
;; Parser utilities

(define-condition eof () ())

(define-condition expect-failed (parsing-error)
  ((fast-http.error::description :initform "expect failed")))


;;
;; Tokens

(declaim (type (simple-array character (128)) +tokens+))
(define-constant +tokens+
    (make-array 128
                :element-type 'character
                :initial-contents
                '( #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul
                   #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul
                   #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul
                   #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul
                   #\Nul   #\!   #\Nul   #\#    #\$    #\%    #\&    #\'
                   #\Nul  #\Nul   #\*    #\+   #\Nul    #\-   #\.   #\Nul
                   #\0    #\1    #\2    #\3    #\4    #\5    #\6    #\7
                   #\8    #\9   #\Nul  #\Nul  #\Nul  #\Nul  #\Nul  #\Nul
                   #\Nul   #\a    #\b    #\c    #\d    #\e    #\f    #\g
                   #\h    #\i    #\j    #\k    #\l    #\m    #\n    #\o
                   #\p    #\q    #\r    #\s    #\t    #\u    #\v    #\w
                   #\x    #\y    #\z   #\Nul  #\Nul  #\Nul   #\^    #\_
                   #\`    #\a    #\b    #\c    #\d    #\e    #\f    #\g
                   #\h    #\i    #\j    #\k    #\l    #\m    #\n    #\o
                   #\p    #\q    #\r    #\s    #\t    #\u    #\v    #\w
                   #\x    #\y    #\z   #\Nul   #\|   #\Nul   #\~   #\Nul ))
    :test 'equalp)

(declaim (type (simple-array fixnum (128)) +unhex+))
(define-constant +unhex+
    (make-array 128 :element-type 'fixnum :initial-contents
                '(-1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1
                  -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1
                  -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1
                  0  1  2  3  4  5  6  7  8  9 -1 -1 -1 -1 -1 -1
                  -1 10 11 12 13 14 15 -1 -1 -1 -1 -1 -1 -1 -1 -1
                  -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1
                  -1 10 11 12 13 14 15 -1 -1 -1 -1 -1 -1 -1 -1 -1
                  -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1 -1))
    :test 'equalp)

(defun-insane unhex-byte (byte)
  (aref +unhex+ byte))

;;
;; Main

(defun-insane parse-method (data start end)
  (declare (type simple-byte-vector data)
           (type pointer start end))
  (with-octets-parsing (data :start start :end end)
    (return-from parse-method
      (values
       (prog1
           (match-case
            ("CONNECT"     :CONNECT)
            ("COPY"        :COPY)
            ("CHECKOUT"    :CHECKOUT)
            ("DELETE"      :DELETE)
            ("GET"         :GET)
            ("HEAD"        :HEAD)
            ("LOCK"        :LOCK)
            ("MKCOL"       :MKCOL)
            ("MKCALENDAR"  :MKCALENDAR)
            ("MKACTIVITY"  :MKACTIVITY)
            ("MOVE"        :MOVE)
            ("MERGE"       :MERGE)
            ("M-SEARCH"    :M-SEARCH)
            ("NOTIFY"      :NOTIFY)
            ("OPTIONS"     :OPTIONS)
            ("POST"        :POST)
            ("PROPFIND"    :PROPFIND)
            ("PROPPATCH"   :PROPPATCH)
            ("PUT"         :PUT)
            ("PURGE"       :PURGE)
            ("PATCH"       :PATCH)
            ("REPORT"      :REPORT)
            ("SEARCH"      :SEARCH)
            ("SUBSCRIBE"   :SUBSCRIBE)
            ("TRACE"       :TRACE)
            ("UNLOCK"      :UNLOCK)
            ("UNSUBSCRIBE" :UNSUBSCRIBE)
            (otherwise (error 'invalid-method)))
         (unless (= (current) +space+)
           (error 'invalid-method)))
       (pos))))
  (error 'eof))

(defun-insane parse-url (data start end)
  (declare (type simple-byte-vector data)
           (type pointer start end))
  (flet ((url-char-byte-p (byte)
           (or (<= (char-code #\!) byte (char-code #\~))
               (<= 128 byte))))
    (with-octets-parsing (data :start start :end end)
      (skip-while url-char-byte-p)
      (return-from parse-url (pos)))
    (error 'eof)))

(defun-insane parse-http-version (data start end)
  (declare (type simple-byte-vector data)
           (type pointer start end))
  (let (major minor)
    (with-octets-parsing (data :start start :end end)
      (or (match? "HTTP/")
          (return-from parse-http-version (values nil nil (pos))))
      (if (digit-byte-char-p (current))
          (setq major (digit-byte-char-to-integer (current)))
          (return-from parse-http-version (values nil nil (pos))))
      (advance)
      (or (skip? #\.) (return-from parse-http-version (values nil nil (pos))))
      (if (digit-byte-char-p (current))
          (setq minor (digit-byte-char-to-integer (current)))
          (return-from parse-http-version (values nil nil (pos))))
      (advance)
      (return-from parse-http-version
        (values major minor (pos))))
    (error 'eof)))

(defun-insane parse-status-code (http callbacks data start end)
  (declare (type simple-byte-vector data)
           (type pointer start end))
  (or (with-octets-parsing (data :start start :end end)
        (if (digit-byte-char-p (current))
            (setf (http-status http) (digit-byte-char-to-integer (current)))
            (error 'invalid-status))
        (loop
          (advance)
          (cond
            ((digit-byte-char-p (current))
             (setf (http-status http)
                   (+ (the fixnum (* 10 (http-status http)))
                      (digit-byte-char-to-integer (current))))
             (when (< 999 (http-status http))
               (error 'invalid-status :status-code (http-status http))))
            ((= (current) +space+)
             ;; Reading the status text
             (advance)
             (let ((status-text-start (pos)))
               (skip* (not #\Return))
               (advance)
               (skip #\Newline)
               (callback-data :status http callbacks data status-text-start (- (pos) 1)))
             (return))
            ((= (current) +cr+)
             ;; No status text
             (advance)
             (skip #\Newline)
             (return))
            (T (error 'invalid-status))))
        (pos))
      (error 'eof)))

(defun-speedy parse-header-field-and-value (http callbacks data start end)
  (declare (type simple-byte-vector data)
           (type pointer start end))
  (or
   (with-octets-parsing (data :start start :end end)
     (let ((field-start (pos))
           field-end)
       (macrolet ((skip-until-value-start-and (&body body)
                    `(progn
                       ;; skip #\: and leading spaces
                       (skip #\:)
                       (skip* #\Space #\Tab)
                       (cond
                         ((= (current) +cr+)
                          ;; continue to the next line
                          (advance)
                          (skip #\Newline)
                          (cond
                            ((or (= (current) +space+)
                                 (= (current) +tab+))
                             (skip* #\Space #\Tab)
                             (if (= (current) +cr+)
                                 ;; empty body
                                 (progn
                                   (advance)
                                   (skip #\Newline)
                                   (callback-data :header-field http callbacks data field-start field-end)
                                   (callback-data :header-value http callbacks data (pos) (pos)))
                                 (progn ,@body)))
                            ;; empty body
                            (t
                             (callback-data :header-field http callbacks data field-start field-end)
                             (callback-data :header-value http callbacks data (pos) (pos)))))
                         (t ,@body))))
                  (handle-otherwise ()
                    `(progn
                       ;; skip until field end
                       (do ((char (aref +tokens+ (current))
                                  (aref +tokens+ (current))))
                           ((= (current) (char-code #\:)))
                         (declare (type character char))
                         (when (char= char #\Nul)
                           (error 'invalid-header-token))
                         (advance))

                       (setq field-end (pos))
                       (skip-until-value-start-and
                        (advance-to*
                         (parse-header-value http callbacks data (pos) end field-start field-end)))))
                  (expect-field-end (&body body)
                    `(if (= (current) #.(char-code #\:))
                         (progn
                           (setq field-end (pos))
                           ,@body)
                         (handle-otherwise))))
         (match-i-case
          ("content-length"
           (expect-field-end
            (skip-until-value-start-and
             (multiple-value-bind (value-start value-end next content-length)
                 (parse-header-value-content-length data (pos) end)
               (declare (type pointer next))
               (setf (http-content-length http) content-length)
               (advance-to* next)
               (callback-data :header-field http callbacks data field-start field-end)
               (callback-data :header-value http callbacks data value-start value-end)))))
          ("transfer-encoding"
           (expect-field-end
            (skip-until-value-start-and
             (multiple-value-bind (value-start value-end next chunkedp)
                 (parse-header-value-transfer-encoding data (pos) end)
               (declare (type pointer next))
               (setf (http-chunked-p http) chunkedp)
               (advance-to* next)
               (callback-data :header-field http callbacks data field-start field-end)
               (callback-data :header-value http callbacks data value-start value-end)))))
          ("upgrade"
           (expect-field-end
            (skip-until-value-start-and
             (setf (http-upgrade-p http) T)
             (let ((value-start (pos)))
               (skip* (not #\Return))
               (advance)
               (skip #\Newline)
               (callback-data :header-field http callbacks data field-start field-end)
               (callback-data :header-value http callbacks data value-start (- (pos) 2))))))
          (otherwise (handle-otherwise)))))
     (pos))
   (error 'eof)))

(defun-speedy parse-header-value (http callbacks data start end &optional field-start field-end)
  (or (with-octets-parsing (data :start start :end end)
        (skip* (not #\Return))
        (advance)
        (skip #\Newline)
        (when field-start
          (callback-data :header-field http callbacks data field-start field-end))
        (callback-data :header-value http callbacks data start (- (pos) 2))
        (pos))
      (error 'eof)))

(defun-speedy parse-header-value-transfer-encoding (data start end)
  (declare (type simple-byte-vector data)
           (type pointer start end))
  (with-octets-parsing (data :start start :end end)
    (match-i-case
     ("chunked"
      (if (= (current) +cr+)
          (progn
            (advance)
            (skip #\Newline)
            (return-from parse-header-value-transfer-encoding
              (values start (- (pos) 2) (pos) t)))
          (progn
            (skip+ (not #\Return))
            (advance)
            (skip #\Newline)
            (return-from parse-header-value-transfer-encoding
              (values start (- (pos) 2) (pos) nil)))))
     (otherwise
      (skip* (not #\Return))
      (advance)
      (skip #\Newline)
      (return-from parse-header-value-transfer-encoding
        (values start (- (pos) 2) (pos) nil)))))
  (error 'eof))

(defun-speedy parse-header-value-content-length (data start end)
  (declare (type simple-byte-vector data)
           (type pointer start end))
  (let ((content-length 0))
    (declare (type integer content-length))
    (with-octets-parsing (data :start start :end end)
      (if (digit-byte-char-p (current))
          (setq content-length (digit-byte-char-to-integer (current)))
          (error 'invalid-content-length))
      (loop
        (advance)
        (cond
          ((digit-byte-char-p (current))
           (setq content-length
                 (+ (* 10 content-length)
                    (digit-byte-char-to-integer (current)))))
          ((= (current) +cr+)
           (advance)
           (skip #\Newline)
           (return-from parse-header-value-content-length
             (values start (- (pos) 2) (pos) content-length)))
          ((= (current) +space+)
           ;; Discard spaces
           )
          (t (error 'invalid-content-length)))))
    (error 'eof)))

(defun-speedy parse-header-line (http callbacks data start end)
  (declare (type simple-byte-vector data)
           (type pointer start end))
  (when (<= end start)
    (error 'eof))
  (let ((current (aref data start)))
    (declare (type (unsigned-byte 8) current))
    (cond
      ((or (= current +tab+)
           (= current +space+))
       (parse-header-value http callbacks data start end))
      ((/= current +cr+)
       (parse-header-field-and-value http callbacks data start end))
      (t
       (incf start)
       (when (= start end)
         (error 'eof))
       (setq current (aref data start))
       (unless (= current +lf+)
         (error 'expect-failed))
       (values (1+ start) t)))))

(defun-speedy parse-headers (http callbacks data start end)
  (declare (type http http)
           (type simple-byte-vector data)
           (type pointer start end))
  (or (with-octets-parsing (data :start start :end end)
        ;; empty headers
        (when (= (current) +cr+)
          (advance)
          (if (= (current) +lf+)
              (return-from parse-headers (1+ (pos)))
              (error 'expect-failed)))

        (advance-to* (parse-header-field-and-value http callbacks data start end))

        (setf (http-mark http) (pos))
        (loop
          (when (= +max-header-line+ (the fixnum (incf (http-header-read http))))
            (error 'header-overflow))
          (multiple-value-bind (next endp)
              (parse-header-line http callbacks data (pos) end)
            (advance-to* next)
            (when endp
              (return)))
          (setf (http-mark http) (pos)))
        (setf (http-mark http) (pos))
        (setf (http-state http) +state-body+)

        (pos))
      (error 'eof)))

(defun-speedy read-body-data (http callbacks data start end)
  (declare (type http http)
           (type simple-byte-vector data)
           (type pointer start end))
  (let ((readable-count (the pointer (- end start))))
    (declare (dynamic-extent readable-count)
             (type pointer readable-count))
    (if (<= (http-content-length http) readable-count)
        (let ((body-end (+ start (http-content-length http))))
          (declare (dynamic-extent body-end))
          (setf (http-content-length http) 0)
          (callback-data :body http callbacks data start body-end)
          (setf (http-mark http) body-end)
          (values body-end t))
        ;; still needs to read
        (progn
          (decf (http-content-length http) readable-count)
          (callback-data :body http callbacks data start end)
          (setf (http-mark http) end)
          (values end nil)))))

(defun-speedy http-message-needs-eof-p (http)
  (let ((status-code (http-status http)))
    (declare (type status-code status-code))
    (when (= status-code 0) ;; probably request
      (return-from http-message-needs-eof-p nil))

    (when (or (< 99 status-code 200) ;; 1xx e.g. Continue
              (= status-code 204)    ;; No Content
              (= status-code 304))   ;; Not Modified
      (return-from http-message-needs-eof-p nil))

    (when (or (http-chunked-p http)
              (http-content-length http))
      (return-from http-message-needs-eof-p nil))
    T))

(defun-speedy parse-body (http callbacks data start end requestp)
  (declare (type http http)
           (type simple-byte-vector data)
           (type pointer start end))
  (macrolet ((message-complete ()
               `(progn
                  (callback-notify :message-complete http callbacks)
                  (setf (http-state http) +state-first-line+))))
    (case (http-content-length http)
      (0
       ;; Content-Length header given but zero: Content-Length: 0\r\n
       (message-complete)
       start)
      ('nil
       (if (or requestp
               (not (http-message-needs-eof-p http)))
           ;; Assume content-length 0 - read the next
           (progn
             (message-complete)
             end)
           ;; read until EOF
           (progn
             (callback-data :body http callbacks data start end)
             (setf (http-mark http) end)
             end)))
      (otherwise
       ;; Content-Length header given and non-zero
       (multiple-value-bind (next completedp)
           (read-body-data http callbacks data start end)
         (when completedp
           (message-complete))
         next)))))

(defun-speedy parse-chunked-body (http callbacks data start end)
  (declare (type http http)
           (type simple-byte-vector data)
           (type pointer start end))

  (when (= start end)
    (return-from parse-chunked-body start))

  (or (with-octets-parsing (data :start start :end end)
        (tagbody
           (cond
             ((= (http-state http) +state-chunk-size+)
              (go chunk-size))
             ((= (http-state http) +state-body+)
              (go body))
             ((= (http-state http) +state-chunk-body-end-crlf+)
              (go body-end-crlf))
             ((= (http-state http) +state-trailing-headers+)
              (go trailing-headers))
             (T (error 'invalid-internal-state :code (http-state http))))

         chunk-size
           (let ((unhex-val (unhex-byte (current))))
             (declare (type fixnum unhex-val)
                      (dynamic-extent unhex-val))
             (when (= unhex-val -1)
               (error 'invalid-chunk-size))
             (setf (http-content-length http) unhex-val)

             (loop
               (advance)
               (if (= (current) +cr+)
                   (progn
                     (advance)
                     (tagbody
                        (skip #\Newline)
                      :eof
                        (return)))
                   (progn
                     (setq unhex-val (unhex-byte (current)))
                     (cond
                       ((= unhex-val -1)
                        (cond
                          ((or (= (current) (char-code #\;))
                               (= (current) (char-code #\Space)))
                           (skip* (not #\Return))
                           (advance)
                           (tagbody
                              (skip #\Newline)
                            :eof
                              (return)))
                          (t (error 'invalid-chunk-size))))
                       (t (setf (http-content-length http)
                                (+ (* 16 (http-content-length http)) unhex-val)))))))
             (setf (http-state http) +state-body+) 
             (if (eofp)
                 (return-from parse-chunked-body (pos))
                 (setf (http-mark http) (pos))))

         body
           (cond
             ((zerop (http-content-length http))
              ;; trailing headers
              (setf (http-state http) +state-trailing-headers+)
              (go trailing-headers))
             (T
              (multiple-value-bind (next completedp)
                  (read-body-data http callbacks data (pos) end)
                (declare (type pointer next))
                (unless completedp
                  (return-from parse-chunked-body (pos)))
                (setf (http-state http) +state-chunk-body-end-crlf+)
                (advance-to next))))

         body-end-crlf
           (skip #\Return)
           (tagbody
              (skip #\Newline)
            :eof
              (setf (http-state http) +state-chunk-size+)
              (when (eofp)
                (return-from parse-chunked-body (pos))))
           (setf (http-mark http) (pos))
           (go chunk-size)

         trailing-headers
           (return-from parse-chunked-body
             (prog1 (parse-headers http callbacks data (pos) end)
               (callback-notify :message-complete http callbacks)))))
      (error 'eof)))

(defun-speedy parse-request (http callbacks data &key (start 0) end)
  (declare (type http http)
           (type simple-byte-vector data))
  (let ((end (or end (length data))))
    (declare (type pointer start end))
    (handler-bind ((match-failed
                     (lambda (c)
                       (declare (ignore c))
                       (error 'expect-failed))))
      (with-octets-parsing (data :start start :end end)
        (setf (http-mark http) start)

        (tagbody
           (let ((state (http-state http)))
             (declare (type fixnum state))
             (cond
               ((= +state-first-line+ state)
                (go first-line))
               ((= +state-headers+ state)
                (go headers))
               ((<= +state-chunk-size+ state +state-trailing-headers+)
                (go body))
               (T (error 'invalid-internal-state :code state))))

         first-line
           ;; skip first empty line (some clients add CRLF after POST content)
           (when (= (current) +cr+)
             (advance)
             (tagbody
                (skip #\Newline)
              :eof
                (when (eofp)
                  (return-from parse-request (pos)))))

           (setf (http-mark http) (pos))
           (callback-notify :message-begin http callbacks)

           (multiple-value-bind (method next)
               (parse-method data (pos) end)
             (declare (type pointer next))
             (setf (http-method http) method)
             (advance-to* next))
           (skip* #\Space)
           (let ((url-start-mark (pos))
                 (url-end-mark (parse-url data (pos) end)))
             (declare (type pointer url-start-mark url-end-mark))
             (tagbody retry-url-parse
                (advance-to* url-end-mark)

                (skip* #\Space)

                (cond
                  ;; No HTTP version
                  ((= (current) +cr+)
                   (callback-data :url http callbacks data url-start-mark url-end-mark)
                   (advance)
                   (skip #\Newline))
                  (T (multiple-value-bind (major minor next)
                         (parse-http-version data (pos) end)
                       (declare (type pointer next))
                       (unless major
                         ;; Invalid HTTP version.
                         ;; Assuming it's also a part of URI.
                         (setq url-end-mark (parse-url data next end))
                         (go retry-url-parse))
                       (callback-data :url http callbacks data url-start-mark url-end-mark)
                       (setf (http-major-version http) major
                             (http-minor-version http) minor)
                       (advance-to* next))
                     (skip #\Return)
                     (skip #\Newline)))))

           (setf (http-mark http) (pos))
           (setf (http-state http) +state-headers+)
           (callback-notify :first-line http callbacks)

         headers
           (advance-to* (parse-headers http callbacks data (pos) end))

           (callback-notify :headers-complete http callbacks)
           (setf (http-header-read http) 0)

           ;; Exit, the rest of the connect is in a different protocol.
           (when (http-upgrade-p http)
             (setf (http-state http) +state-first-line+)
             (callback-notify :message-complete http callbacks)
             (return-from parse-request (pos)))

           (setf (http-state http)
                 (if (http-chunked-p http)
                     +state-chunk-size+
                     +state-body+))

         body
           (if (http-chunked-p http)
               (advance-to* (parse-chunked-body http callbacks data (pos) end))
               (progn
                 (and (advance-to* (parse-body http callbacks data (pos) end t))
                      (go first-line))))
           (return-from parse-request (pos)))))
    (error 'eof)))

(defun-speedy parse-response (http callbacks data &key (start 0) end)
  (declare (type http http)
           (type simple-byte-vector data))
  (let ((end (or end
                 (length data))))
    (declare (type pointer start end))
    (handler-bind ((match-failed
                     (lambda (c)
                       (declare (ignore c))
                       (error 'expect-failed))))
      (with-octets-parsing (data :start start :end end)
        (setf (http-mark http) start)

        (tagbody
           (let ((state (http-state http)))
             (declare (type fixnum state))
             (cond
               ((= +state-first-line+ state)
                (go first-line))
               ((= +state-headers+ state)
                (go headers))
               ((<= +state-chunk-size+ state +state-trailing-headers+)
                (go body))
               (T (error 'invalid-internal-state :code state))))

         first-line
           (setf (http-mark http) (pos))
           (callback-notify :message-begin http callbacks)

           (multiple-value-bind (major minor next)
               (parse-http-version data (pos) end)
             (declare (type pointer next))
             (setf (http-major-version http) major
                   (http-minor-version http) minor)
             (advance-to* next))

           (cond
             ((= (current) +space+)
              (advance)
              (advance-to (parse-status-code http callbacks data (pos) end)))
             ((= (current) +cr+)
              (skip #\Newline))
             (T (error 'invalid-version)))

           (setf (http-mark http) (pos))
           (setf (http-state http) +state-headers+)
           (callback-notify :first-line http callbacks)

         headers
           (advance-to* (parse-headers http callbacks data (pos) end))

           (callback-notify :headers-complete http callbacks)
           (setf (http-header-read http) 0)
           (setf (http-state http)
                 (if (http-chunked-p http)
                     +state-chunk-size+
                     +state-body+))

         body
           (if (http-chunked-p http)
               (advance-to* (parse-chunked-body http callbacks data (pos) end))
               (progn
                 (advance-to* (parse-body http callbacks data (pos) end nil))
                 (unless (eofp)
                   (go first-line))))
           (return-from parse-response (pos)))))
    (error 'eof)))

(defun parse-header-value-parameters (data &key
                                             header-value-callback
                                             header-parameter-key-callback
                                             header-parameter-value-callback)
  (declare (type simple-string data)
           (optimize (speed 3) (safety 2)))

  (let* ((header-name-mark 0)
         parameter-key-mark
         parameter-value-mark
         parsing-quoted-string-p
         (p 0)
         (end (length data))
         (char (aref data p)))
    (declare (type character char))

    (when (= end 0)
      (return-from parse-header-value-parameters 0))

    (macrolet ((go-state (state &optional (advance 1))
                   `(locally (declare (optimize (speed 3) (safety 0)))
                      (incf p ,advance)
                      (when (= p end)
                        (go eof))
                      (setq char (aref data p))
                      (go ,state))))
      (flet ((tokenp (char)
               (declare (optimize (speed 3) (safety 0)))
               (let ((byte (char-code char)))
                 (and (< byte 128)
                      (not (char= (the character (aref +tokens+ byte)) #\Nul))))))
        (tagbody
         parsing-header-value-start
           (case char
             ((#\Space #\Tab)
              (go-state parsing-header-value))
             (otherwise
              (unless (tokenp char)
                (error 'invalid-header-value))
              (setq header-name-mark p)
              (go-state parsing-header-value 0)))

         parsing-header-value
           (case char
             (#\;
              (when header-value-callback
                (funcall (the function header-value-callback)
                         data header-name-mark p))
              (setq header-name-mark nil)
              (go-state looking-for-parameter-key))
             (otherwise (go-state parsing-header-value)))

         looking-for-parameter-key
           (case char
             ((#\Space #\Tab #\; #\Newline #\Return)
              (go-state looking-for-parameter-key))
             (otherwise
              (unless (tokenp char)
                (error 'invalid-parameter-key))
              (setq parameter-key-mark p)
              (go-state parsing-parameter-key)))

         parsing-parameter-key
           (case char
             (#\=
              (assert parameter-key-mark)
              (when header-parameter-key-callback
                (funcall (the function header-parameter-key-callback)
                         data parameter-key-mark p))
              (setq parameter-key-mark nil)
              (go-state parsing-parameter-value-start))
             (otherwise
              (unless (tokenp char)
                (error 'invalid-parameter-key))
              (go-state parsing-parameter-key)))

         parsing-parameter-value-start
           (case char
             (#\"
              ;; quoted-string
              (setq parameter-value-mark (1+ p))
              (setq parsing-quoted-string-p t)
              (go-state parsing-parameter-quoted-value))
             ((#.+space+ #.+tab+)
              (go-state parsing-parameter-value-start))
             (otherwise
              (setq parameter-value-mark p)
              (go-state parsing-parameter-value 0)))

         parsing-parameter-quoted-value
           (if (char= char #\")
               (progn
                 (assert parameter-value-mark)
                 (setq parsing-quoted-string-p nil)
                 (when header-parameter-value-callback
                   (funcall (the function header-parameter-value-callback)
                            data parameter-value-mark p))
                 (setq parameter-value-mark nil)
                 (go-state looking-for-parameter-key))
               (go-state parsing-parameter-quoted-value))

         parsing-parameter-value
           (case char
             (#\;
              (assert parameter-value-mark)
              (when header-parameter-value-callback
                (funcall (the function header-parameter-value-callback)
                         data parameter-value-mark p))
              (setq parameter-value-mark nil)
              (go-state looking-for-parameter-key))
             (otherwise
              (go-state parsing-parameter-value)))

         eof
           (when header-name-mark
             (when header-value-callback
               (funcall (the function header-value-callback)
                        data header-name-mark p)))
           (when parameter-key-mark
             (error 'invalid-eof-state))
           (when parameter-value-mark
             (when parsing-quoted-string-p
               (error 'invalid-eof-state))
             (when header-parameter-value-callback
               (funcall (the function header-parameter-value-callback)
                        data parameter-value-mark p))))))
    p))

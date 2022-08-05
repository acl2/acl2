(defpackage #:dexador.backend.winhttp
  (:nicknames :dex.winhttp)
  (:use #:cl
        #:dexador.util
        #:winhttp)
  (:import-from #:dexador.body
                #:decode-body
                #:write-multipart-content
                #:decompress-body)
  (:import-from #:dexador.error
                #:http-request-failed)
  (:import-from #:winhttp
                #:set-ignore-certificates
                #:set-timeouts)
  (:import-from #:fast-io
                #:fast-output-stream
                #:with-fast-output
                #:fast-write-sequence
                #:finish-output-stream)
  (:import-from #:babel)
  (:import-from #:flexi-streams)
  (:import-from #:cl-cookie
                #:cookie-jar-host-cookies
                #:write-cookie-header
                #:parse-set-cookie-header
                #:merge-cookies)
  (:import-from #:alexandria
                #:read-file-into-byte-vector
                #:ensure-list
                #:when-let)
  (:import-from #:split-sequence
                #:split-sequence)
  (:export :request

           ;; Restarts
           :retry-request
           :ignore-and-continue))
(in-package #:dexador.backend.winhttp)

(defconstant +WINHTTP_OPTION_DISABLE_FEATURE+ 63)
(defconstant +WINHTTP_DISABLE_COOKIES+    #x00000001)
(defconstant +WINHTTP_DISABLE_REDIRECTS+  #x00000002)
(defconstant +WINHTTP_DISABLE_KEEP_ALIVE+ #x00000008)

(defun set-option (req var value &optional (type :uint32))
  (cffi:with-foreign-object (buf type)
    (setf (cffi:mem-aref buf type) value)
    (let ((ret (winhttp::%set-option req
                                     var
                                     buf
                                     (cffi:foreign-type-size type))))
      (unless ret
        (winhttp::get-last-error)))))

(defun query-headers* (req)
  (loop with hash = (make-hash-table :test 'equal)
        for (name-camelcased value) in (query-headers req)
        for name = (string-downcase name-camelcased)
        if (gethash name hash)
          do (setf (gethash name hash)
                   (format nil "~A, ~A" (gethash name hash) value))
        else
          do (setf (gethash name hash) value)
        finally (return hash)))

(defun convert-content (content multipart-p form-urlencoded-p)
  (etypecase content
    (cons
     (cond (multipart-p
            (let ((boundary (make-random-string 12)))
              (values
               (let ((stream (make-instance 'fast-output-stream)))
                 (write-multipart-content content boundary stream)
                 (finish-output-stream stream))
               (format nil "multipart/form-data; boundary=~A" boundary))))
           (form-urlencoded-p
            (values
             (babel:string-to-octets (quri:url-encode-params content))
             "application/x-www-form-urlencoded"))))
    (string (values (babel:string-to-octets content)
                    "text/plain"))
    (pathname (values (read-file-into-byte-vector content)
                      (mimes:mime content)))
    ((array (unsigned-byte 8) (*)) content)
    (null (make-array 0 :element-type '(unsigned-byte 8)))))

;; TODO: Try asynchronous
(defun request (uri &rest args
                            &key (method :get) (version 1.1)
                            content headers
                            basic-auth
                            cookie-jar
                            (connect-timeout *default-connect-timeout*) (read-timeout *default-read-timeout*)
                            (keep-alive t) (use-connection-pool t)
                            (max-redirects 5)
                            ssl-key-file ssl-cert-file ssl-key-password
                            stream (verbose *verbose*)
                            force-binary force-string
                            want-stream
                            proxy
                            (insecure *not-verify-ssl*)
                            ca-path)
  (declare (ignore version use-connection-pool
                   ssl-key-file ssl-cert-file ssl-key-password
                   stream verbose
                   proxy
                   ca-path))
  (let* ((uri (quri:uri uri))
         (content-type
           (find :content-type headers :key #'car :test #'string-equal))
         (multipart-p (or (string= (cdr content-type) "multipart/form-data")
                          (and (null (cdr content-type))
                               (consp content)
                               (find-if #'pathnamep content :key #'cdr))))
         (form-urlencoded-p (or (string= (cdr content-type) "application/x-www-form-urlencoded")
                                (and (null (cdr content-type))
                                     (consp content)
                                     (not multipart-p))))
         (user-agent
           (cdr (find :user-agent headers :key #'car :test #'string-equal))))
    (multiple-value-bind (content detected-content-type)
        (convert-content content multipart-p form-urlencoded-p)
      (when detected-content-type
        (if content-type
            (setf (cdr (assoc :content-type headers :test #'string-equal)) detected-content-type)
            (setf headers (append `(("Content-Type" . ,detected-content-type)) headers))))

      (when cookie-jar
        (let ((cookies
                (cookie-jar-host-cookies cookie-jar (quri:uri-host uri) (or (quri:uri-path uri) "/")
                                         :securep (string= (quri:uri-scheme uri) "https"))))
          (when cookies
            (setf headers
                  (append headers
                          `(("Cookie" . ,(write-cookie-header cookies))))))))
      (with-http (session (or user-agent *default-user-agent*))
        (with-connect (conn session (quri:uri-host uri) (quri:uri-port uri))
          (with-request (req conn :verb method
                                  :url (format nil "~@[~A~]~@[?~A~]"
                                               (quri:uri-path uri)
                                               (quri:uri-query uri))
                                  :https-p (equalp (quri:uri-scheme uri) "https"))
            (cond
              ((quri:uri-userinfo uri)
               (destructuring-bind (user pass) (split-sequence #\: (quri:uri-userinfo uri))
                 (set-credentials req user pass)))
              (basic-auth
               (set-credentials req (car basic-auth) (cdr basic-auth))))

            ;; TODO: SSL arguments
            ;; TODO: proxy support
            (set-option req
                        +WINHTTP_OPTION_DISABLE_FEATURE+
                        (logior +WINHTTP_DISABLE_COOKIES+
                                +WINHTTP_DISABLE_REDIRECTS+
                                (if keep-alive 0 +WINHTTP_DISABLE_KEEP_ALIVE+)))

            (dolist (header headers)
              (add-request-headers req
                                   (format nil "~:(~A~): ~A" (car header) (cdr header))))

            (when (and (equalp (quri:uri-scheme uri) "https")
                       insecure)
              (set-ignore-certificates req))

            (when connect-timeout
              (set-timeouts req
                            :connect (* 1000 connect-timeout)
                            :recv (* 1000 read-timeout)))

            (send-request req content)

            (receive-response req)

            (let ((status (query-status-code req))
                  (response-headers (query-headers* req)))
              (when cookie-jar
                (when-let (set-cookies (append (ensure-list (gethash "set-cookie" response-headers))
                                               (ensure-list (gethash "set-cookie2" response-headers))))
                  (merge-cookies cookie-jar
                                 (remove nil (mapcar (lambda (cookie)
                                                       (declare (type string cookie))
                                                       (unless (= (length cookie) 0)
                                                         (parse-set-cookie-header cookie
                                                                                  (quri:uri-host uri)
                                                                                  (quri:uri-path uri))))
                                                     set-cookies)))))

              ;; Redirect
              (when (and (member status '(301 302 303 307))
                         (gethash "location" response-headers)
                         (/= max-redirects 0))
                (let ((location-uri (quri:uri (gethash "location" response-headers))))
                  (let ((method
                          (if (and (or (null (quri:uri-host location-uri))
                                       (and (string= (quri:uri-scheme location-uri)
                                                     (quri:uri-scheme uri))
                                            (string= (quri:uri-host location-uri)
                                                     (quri:uri-host uri))
                                            (eql (quri:uri-port location-uri)
                                                 (quri:uri-port uri))))
                                   (or (= status 307)
                                       (member method '(:get :head) :test #'eq)))
                              method
                              :get)))
                    ;; TODO: slurp the body
                    (return-from request
                                 (apply #'request (quri:merge-uris location-uri uri)
                                        :max-redirects (1- max-redirects)
                                        :method method
                                        args)))))

              (let ((body (with-fast-output (body :vector)
                            (loop with buffer = (make-array 1024 :element-type '(unsigned-byte 8))
                                  for bytes = (read-data req buffer)
                                  until (zerop bytes)
                                  do (fast-write-sequence buffer body 0 bytes)))))
                (when (gethash "content-encoding" response-headers)
                  (setf body
                        (decompress-body
                          (gethash "content-encoding" response-headers)
                          body)))

                (let ((body (if force-binary
                                body
                                (decode-body (gethash "content-type" response-headers) body
                                             :default-charset (if force-string
                                                                  babel:*default-character-encoding*
                                                                  nil)))))
                  ;; Raise an error when the HTTP response status is 4xx or 5xx.
                  (when (<= 400 status)
                    (restart-case
                        (http-request-failed status
                                             :body body
                                             :headers response-headers
                                             :uri uri
                                             :method method)
                      (retry-request ()
                        :report "Retry the same request."
                        (apply #'request uri args))
                      (ignore-and-continue ()
                        :report "Ignore the error and continue.")))

                  ;; TODO: This obviously isn't streaming.
                  ;;   Wrapping 'req' object by gray streams would be better,
                  ;;   but freeing it could be a problem for the next.
                  (when want-stream
                    (setf body
                          (etypecase body
                            (string (make-string-input-stream body))
                            (vector (flex:make-in-memory-input-stream body)))))

                  (values body
                          status
                          response-headers
                          uri))))))))))

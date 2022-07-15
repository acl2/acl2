(in-package :cl-user)
(defpackage quri
  (:use :cl
        :quri.uri
        :quri.uri.ftp
        :quri.uri.http
        :quri.uri.ldap
        :quri.uri.file
        :quri.error)
  (:import-from :quri.domain
                :uri-tld
                :uri-domain
                :ipv4-addr-p
                :ipv6-addr-p
                :ip-addr-p
                :ip-addr=
                :cookie-domain-p)
  (:import-from :quri.parser
                :parse-uri
                :parse-scheme
                :parse-authority
                :parse-path
                :parse-query
                :parse-fragment)
  (:import-from :quri.port
                :scheme-default-port)
  (:import-from :quri.decode
                :url-decode
                :url-decode-params)
  (:import-from :quri.encode
                :url-encode
                :url-encode-params)
  (:import-from :split-sequence :split-sequence)
  (:import-from :alexandria
                :delete-from-plist
                :when-let*)
  (:export :parse-uri
           :parse-scheme
           :parse-authority
           :parse-path
           :parse-query
           :parse-fragment

           :make-uri
           :uri
           :uri=
           :uri-equal
           :uri-p
           :uri-scheme
           :uri-userinfo
           :uri-host
           :uri-port
           :uri-path
           :uri-query
           :uri-fragment
           :uri-authority

           :uri-tld
           :uri-domain
           :ipv4-addr-p
           :ipv6-addr-p
           :ip-addr-p
           :ip-addr=
           :cookie-domain-p

           :urn
           :urn-p
           :urn-nid
           :urn-nss

           :make-uri-ftp
           :uri-ftp
           :uri-ftp-p
           :uri-ftp-typecode

           :make-uri-http
           :make-uri-https
           :uri-http
           :uri-http-p
           :uri-https
           :uri-https-p
           :uri-query-params

           :make-uri-ldap
           :make-uri-ldaps
           :uri-ldap
           :uri-ldap-p
           :uri-ldap-dn
           :uri-ldap-attributes
           :uri-ldap-scope
           :uri-ldap-filter
           :uri-ldap-extensions

           :make-uri-file
           :uri-file
           :uri-file-p
           :uri-file-pathname

           :copy-uri
           :render-uri
           :merge-uris

           :url-decode
           :url-decode-params
           :url-encode
           :url-encode-params

           :uri-error
           :uri-malformed-string
           :uri-invalid-port
           :url-decoding-error
           :uri-malformed-urlencoded-string))
(in-package :quri)

(defun scheme-constructor (scheme)
  "Get a constructor function appropriate for the scheme."
  (cond
    ((string= scheme "http")  #'make-uri-http)
    ((string= scheme "https") #'make-uri-https)
    ((string= scheme "ldap")  #'make-uri-ldap)
    ((string= scheme "ldaps") #'make-uri-ldaps)
    ((string= scheme "ftp")   #'make-uri-ftp)
    ((string= scheme "file")  #'make-uri-file)
    ((string= scheme "urn")   #'make-urn)
    (t                        #'make-basic-uri)))

(defun uri (data &key (start 0) end)
  (if (uri-p data)
      data
      (multiple-value-bind (scheme userinfo host port path query fragment)
          (parse-uri data :start start :end end)
        (apply (scheme-constructor scheme)
               :scheme scheme
               :userinfo userinfo
               :host host
               :path path
               :query query
               :fragment fragment
               (and port
                    `(:port ,port))))))

(defun copy-uri (uri &key (scheme (uri-scheme uri))
                          (userinfo (uri-userinfo uri))
                          (host (uri-host uri))
                          (port (uri-port uri))
                          (path (uri-path uri))
                          (query (uri-query uri))
                          (fragment (uri-fragment uri)))
  (make-uri :scheme scheme
            :userinfo userinfo
            :host host
            :port port
            :path path
            :query query
            :fragment fragment))

(defun make-uri (&rest initargs &key scheme userinfo host port path query fragment defaults)
  (declare (ignore userinfo host port path fragment))
  (setf initargs (delete-from-plist initargs :defaults))
  (if defaults
      (apply #'copy-uri (uri defaults) initargs)
      (progn
        (when (consp query)
          (setf (getf initargs :query) (url-encode-params query)))
        (apply (scheme-constructor scheme) initargs))))

(defun render-uri (uri &optional stream)
  (flet ((maybe-slash (authority path)
           (if (and (not (uiop:emptyp authority)) (not (uiop:emptyp path))
                    (char/= (uiop:last-char authority) #\/)
                    (char/= (uiop:first-char path) #\/))
               "/"
               "")))
    (cond
      ((uri-ftp-p uri)
       (format stream
               "~@[~(~A~):~]~@[//~A~]~a~@[~A~]~@[;type=~A~]~@[?~A~]~@[#~A~]"
               (uri-scheme uri)
               (uri-authority uri)
               (maybe-slash (uri-authority uri) (uri-path uri))
               (uri-path uri)
               (uri-ftp-typecode uri)
               (uri-query uri)
               (uri-fragment uri)))
      ((uri-file-p uri)
       (format stream
               "~@[~(~A~)://~]~@[~A~]~@[?~A~]~@[#~A~]"
               (uri-scheme uri)
               (uri-path uri)
               (uri-query uri)
               (uri-fragment uri)))
      (t
       (format stream
               "~@[~(~A~):~]~@[//~A~]~a~@[~A~]~@[?~A~]~@[#~A~]"
               (uri-scheme uri)
               (uri-authority uri)
               (maybe-slash (uri-authority uri) (uri-path uri))
               (uri-path uri)
               (uri-query uri)
               (uri-fragment uri))))))

(defun %uri= (uri1 uri2 &key normalize-path-p)
  (check-type uri1 uri)
  (check-type uri2 uri)
  (flet ((%path (path)
           "Define path equivalence relations."
           (cond (normalize-path-p
                  (if (or (null path) (equal path ""))
                      "/"
                      path))
                 (t
                  (or path "")))))
    (and (eq (type-of uri1) (type-of uri2))
         (equal (%path (uri-path uri1)) (%path (uri-path uri2)))
         (equal (uri-query uri1) (uri-query uri2))
         (equal (uri-fragment uri1) (uri-fragment uri2))
         (equalp (uri-authority uri1) (uri-authority uri2))
         (or (not (uri-ftp-p uri1))
             (eql (uri-ftp-typecode uri1) (uri-ftp-typecode uri2))))))

(defun uri= (uri1 uri2)
  "Whether URI1 refers to the same URI as URI2.
Paths are not normalized. See `uri-equal'."
  (%uri= uri1 uri2))

(defun uri-equal (uri1 uri2)
  "Whether URI1 refers to the same URI as URI2.
Empty paths are normalized to '/' as per RFC 3986
(https://tools.ietf.org/html/rfc3986#section-6.2.3).
See `uri='."
  (%uri= uri1 uri2  :normalize-path-p t))

(defmethod print-object ((uri uri) stream)
  (if (and (null *print-readably*) (null *print-escape*))
      (render-uri uri stream)
      (format stream "#<~S ~A>"
              (type-of uri)
              (render-uri uri))))

(defun merge-uri-paths (ref-path base-path)
  (declare (type (or string null) ref-path base-path))
  (let* ((path-list (and base-path (nreverse (split-sequence #\/ base-path))))
         (ref-components (and ref-path (split-sequence #\/ ref-path)))
         ending-slash-p)
    ;; remove last component of base
    (pop path-list)
    (dolist (component ref-components)
      (cond ((string= ".." component)
             (pop path-list)
             (setf ending-slash-p t))
            ((string= "." component)
             (setf ending-slash-p t))
            (t
             (push component path-list)
             (setf ending-slash-p nil))))
    (setf path-list (nreverse path-list))
    (with-output-to-string (s)
      (loop for (component . more) on path-list
         do (progn
              (write-string component s)
              (when (or more ending-slash-p)
                (write-char #\/ s)))))))

(defun merge-uris (reference base)
  "Merge a reference URI into the base URI as described in RFC 2396 Section 5.2.
The returned URI is always a new instance. Neither REFERENCE nor BASE is
mutated."
  (declare (uri reference base))
  ;; Steps described at
  ;; https://datatracker.ietf.org/doc/html/rfc2396#section-5.2
  ;; Step 1 is absent since it's implicit
  (let ((merged-uri (copy-uri reference)))
    (flet ((return-merged-uri () (return-from merge-uris (uri merged-uri)))
           (merge-paths () (setf (uri-path merged-uri)
                                 (merge-uri-paths (uri-path merged-uri) nil))))
      ;; Step 2
      (when (uri-equal reference base)
        (return-merged-uri))
      ;; Step 3
      (when (uri-scheme merged-uri)
          (merge-paths)
          (return-merged-uri))
      (setf merged-uri (copy-uri merged-uri :scheme (uri-scheme base)))
      ;; Step 4
      (when (null (uri-port merged-uri))
        (setf (uri-port merged-uri) (scheme-default-port (uri-scheme merged-uri))))
      (when (uri-host merged-uri)
        (merge-paths)
        (return-merged-uri))
      (setf (uri-userinfo merged-uri) (uri-userinfo base))
      (setf (uri-host merged-uri) (uri-host base))
      (setf (uri-port merged-uri) (uri-port base))
      ;; Step 5
      (when (null (uri-path merged-uri))
        (setf (uri-path merged-uri) (uri-path base))
        (return-merged-uri))
      ;; Step 6
      (alexandria:when-let* ((p (uri-path merged-uri))
                             (first-char (and (> (length p) 0) (char p 0)))
                             (_ (char= #\/ first-char)))
        (merge-paths)
        (return-merged-uri))
      ;; Step 7
      (setf (uri-path merged-uri)
            (merge-uri-paths (uri-path merged-uri) (uri-path base)))
      (return-merged-uri))))

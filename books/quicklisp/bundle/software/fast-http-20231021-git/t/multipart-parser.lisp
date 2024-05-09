(in-package :cl-user)
(defpackage fast-http-test.multipart-parser
  (:use :cl
        :fast-http
        :fast-http.multipart-parser
        :fast-http.parser
        :fast-http-test.test-utils
        :xsubseq
        :prove)
  (:import-from :cl-utilities
                :collecting
                :collect))
(in-package :fast-http-test.multipart-parser)

(syntax:use-syntax :interpol)

(plan nil)

(defun test-ll-parser (boundary body expected &optional description)
  (let ((parser (make-ll-multipart-parser :boundary boundary))
        results
        headers)
    (http-multipart-parse parser
                          (make-callbacks
                           :header-field (lambda (parser data start end)
                                           (declare (ignore parser))
                                           (push (cons (babel:octets-to-string data :start start :end end)
                                                       nil)
                                                 headers))
                           :header-value (lambda (parser data start end)
                                           (declare (ignore parser))
                                           (setf (cdr (car headers))
                                                 (append (cdr (car headers))
                                                         (list (babel:octets-to-string data :start start :end end)))))
                           :body (lambda (parser data start end)
                                   (declare (ignore parser))
                                   (push
                                    (list :headers
                                          (loop for (key . values) in (nreverse headers)
                                                append (list key (apply #'concatenate 'string values)))
                                          :body
                                          (babel:octets-to-string data :start start :end end))
                                    results)
                                   (setf headers nil)))
                          body)
    (is (nreverse results) expected description)))

(test-ll-parser "AaB03x"
                (bv (str #?"--AaB03x\r\n"
                         #?"Content-Disposition: form-data; name=\"field1\"\r\n"
                         #?"\r\n"
                         #?"Joe Blow\r\nalmost tricked you!\r\n"
                         #?"--AaB03x\r\n"
                         #?"Content-Disposition: form-data; name=\"pics\"; filename=\"file1.txt\"\r\n"
                         #?"Content-Type: text/plain\r\n"
                         #?"\r\n"
                         #?"... contents of file1.txt ...\r\r\n"
                         #?"--AaB03x--\r\n"))
                '((:headers ("Content-Disposition" "form-data; name=\"field1\"")
                   :body #?"Joe Blow\r\nalmost tricked you!")
                  (:headers ("Content-Disposition" "form-data; name=\"pics\"; filename=\"file1.txt\""
                             "Content-Type" "text/plain")
                   :body #?"... contents of file1.txt ...\r"))
                "rfc1867")

(let ((big-content (make-string (* 1024 3) :initial-element #\a)))
  (test-ll-parser "---------------------------186454651713519341951581030105"
                  (bv (str #?"-----------------------------186454651713519341951581030105\r\n"
                           #?"Content-Disposition: form-data; name=\"file1\"; filename=\"random.png\"\r\n"
                           #?"Content-Type: image/png\r\n"
                           #?"\r\n"
                           big-content #?"\r\n"
                           #?"-----------------------------186454651713519341951581030105\r\n"
                           #?"Content-Disposition: form-data; name=\"file2\"; filename=\"random.png\"\r\n"
                           #?"Content-Type: image/png\r\n"
                           #?"\r\n"
                           big-content big-content #?"\r\n"
                           #?"-----------------------------186454651713519341951581030105--\r\n"))
                  `((:headers ("Content-Disposition" "form-data; name=\"file1\"; filename=\"random.png\""
                                                     "Content-Type" "image/png")
                     :body ,big-content)
                    (:headers ("Content-Disposition" "form-data; name=\"file2\"; filename=\"random.png\""
                                                     "Content-Type" "image/png")
                     :body ,(concatenate 'string big-content big-content)))
                  "big file"))

(test-ll-parser "---------------------------186454651713519341951581030105"
                (bv (str #?"-----------------------------186454651713519341951581030105\r\n"
                         #?"Content-Disposition: form-data; name=\"name\"\r\n"
                         #?"Content-Type: text/plain\r\n"
                         #?"\r\n"
                         #?"深町英太郎\r\n"
                         #?"-----------------------------186454651713519341951581030105\r\n"
                         #?"Content-Disposition: form-data; name=\"introduce\"\r\n"
                         #?"Content-Type: text/plain\r\n"
                         #?"\r\n"
                         #?"Common Lispが好きです。好きな関数はconsです。\r\n"
                         #?"-----------------------------186454651713519341951581030105--\r\n"))
                '((:headers ("Content-Disposition" "form-data; name=\"name\""
                             "Content-Type" "text/plain")
                   :body "深町英太郎")
                  (:headers ("Content-Disposition" "form-data; name=\"introduce\""
                             "Content-Type" "text/plain")
                   :body "Common Lispが好きです。好きな関数はconsです。"))
                "UTF-8")

(test-ll-parser "---------------------------186454651713519341951581030105"
                (bv (str #?"-----------------------------186454651713519341951581030105\r\n"
                         #?"Content-Disposition: form-data;\r\n"
                         #?"\tname=\"file1\"; filename=\"random.png\"\r\n"
                         #?"Content-Type: image/png\r\n"
                         #?"\r\n"
                         #?"abc\r\n"
                         #?"-----------------------------186454651713519341951581030105\r\n"
                         #?"Content-Disposition: form-data;\r\n"
                         #?" name=\"text\"\r\n"
                         #?"\r\n"
                         #?"Test text\n with\r\n ümläuts!\r\n"
                         #?"-----------------------------186454651713519341951581030105--\r\n"))
                '((:headers ("Content-Disposition" #?"form-data;\tname=\"file1\"; filename=\"random.png\""
                             "Content-Type" "image/png")
                   :body "abc")
                  (:headers ("Content-Disposition" "form-data; name=\"text\"")
                   :body #?"Test text\n with\r\n ümläuts!"))
                "multiline header value")

(let ((parser (make-ll-multipart-parser :boundary "AaB03x"))
      (callbacks (make-callbacks
                  :body (lambda (parser data start end)
                          (declare (ignore parser))
                          (princ (babel:octets-to-string data :start start :end end))))))
  (flet ((parse (body)
           (http-multipart-parse parser callbacks body)))
    (is-print (parse (bv (str #?"--AaB03x\r\n"
                              #?"Content-Disposition: form-data; name=\"field1\"\r\n"
                              #?"\r\n"
                              #?"Joe Blow\r\nalmost tricked you!\r\n")))
              #?"Joe Blow\r\nalmost tricked you!")
    (is-print (parse (bv #?"--AaB03x\r\n")) "")))

(let ((parser (make-ll-multipart-parser :boundary "AaB03x"))
      (callbacks (make-callbacks
                  :body (lambda (parser data start end)
                          (declare (ignore parser))
                          (princ (babel:octets-to-string data :start start :end end))))))
  (flet ((parse (body)
           (http-multipart-parse parser callbacks body)))
    (is-print (parse (bv (str #?"--AaB03x\r\n"
                              #?"Content-Disposition: form-data; name=\"field1\"\r\n"
                              #?"\r\n"
                              #?"Joe Blow\r\nalmost tricked you!\r\n")))
              #?"Joe Blow\r\nalmost tricked you!")
    (is-print (parse (bv #?"--Aa")) "")
    (is-print (parse (bv #?"B03x\r\n"))
              #?"")))

(let ((parser (make-ll-multipart-parser :boundary "AaB03x"))
      (callbacks (make-callbacks
                  :body (lambda (parser data start end)
                          (declare (ignore parser))
                          (princ (babel:octets-to-string data :start start :end end))))))
  (flet ((parse (body)
           (http-multipart-parse parser callbacks body)))
    (is-print (parse (bv (str #?"--AaB03x\r\n"
                              #?"Content-Disposition: form-data; name=\"field1\"\r\n"
                              #?"\r\n"
                              #?"Joe Blow\r\nalmost tricked you!\r\n")))
              #?"Joe Blow\r\nalmost tricked you!")
    (is-print (parse (bv #?"--Aa")) "")
    (is-print (parse (bv #?"BbCc\r\n"))
              #?"\r\n--AaBbCc")))

(let ((parser (make-ll-multipart-parser :boundary "AaB03x"))
      (callbacks (make-callbacks
                  :body (lambda (parser data start end)
                          (declare (ignore parser))
                          (princ (babel:octets-to-string data :start start :end end))))))
  (flet ((parse (body)
           (http-multipart-parse parser callbacks body)))
    (is-print (parse (bv (str #?"--AaB03x\r\n"
                              #?"Content-Disposition: form-data; name=\"field1\"\r\n"
                              #?"\r\n"
                              #?"Joe Blow\r\nalmost tricked you!\r\n")))
              #?"Joe Blow\r\nalmost tricked you!")
    (is-print (parse (bv "--Aa")) "")
    (is-print (parse (bv "B03x")) "")
    (is-print (parse (bv "C")) #?"\r\n--AaB03xC")))


(defun slurp-stream (stream)
  (with-xsubseqs (xsub)
    (let ((buffer (make-array 1024 :element-type '(unsigned-byte 8))))
      (loop for bytes-read = (read-sequence buffer stream)
            do (xnconcf xsub (xsubseq buffer 0 bytes-read))
            while (= bytes-read 1024)))))

(defun test-parser (content-type data expected &optional description)
  (let ((got (collecting
               (let ((parser
                       (make-multipart-parser content-type
                                              (lambda (field-name headers field-meta body)
                                                (setf body (slurp-stream body))
                                                (collect (list field-name
                                                               headers
                                                               field-meta
                                                               (babel:octets-to-string body)))))))
                 (funcall parser data)))))
    (flet ((hash-table-equal (hash plist desc)
             (subtest desc
               (maphash (lambda (k v)
                          (is v (getf plist (intern (string-upcase k) :keyword)) k))
                        hash))))
      (subtest (or description "")
        (loop for got in got
              for expected in expected
              do (is (first got) (first expected) "field-name")
                 (hash-table-equal (second got) (second expected) "headers")
                 (hash-table-equal (third got) (third expected) "field-meta")
                 (is (fourth got) (fourth expected) "body"))))))

(test-parser "multipart/form-data; boundary=AaB03x"
             (bv (str #?"--AaB03x\r\n"
                      #?"Content-Disposition: form-data; name=\"field1\"\r\n"
                      #?"\r\n"
                      #?"Joe Blow\r\nalmost tricked you!\r\n"
                      #?"--AaB03x\r\n"
                      #?"Content-Disposition: form-data; name=\"pics\"; filename=\"file1.txt\"\r\n"
                      #?"Content-Type: text/plain\r\n"
                      #?"\r\n"
                      #?"... contents of file1.txt ...\r\r\n"
                      #?"--AaB03x--\r\n"))
             '(("field1"
                (:content-disposition "form-data; name=\"field1\"")
                (:name "field1")
                #?"Joe Blow\r\nalmost tricked you!")
               ("pics"
                (:content-disposition "form-data; name=\"pics\"; filename=\"file1.txt\""
                 :content-type "text/plain")
                (:name "pics"
                 :filename "file1.txt")
                #?"... contents of file1.txt ...\r"))
             "rfc1867")

(let ((big-content (make-string (* 1024 3) :initial-element #\a)))
  (test-parser "multipart/form-data; boundary=\"---------------------------186454651713519341951581030105\""
               (bv (str #?"-----------------------------186454651713519341951581030105\r\n"
                        #?"Content-Disposition: form-data; name=\"file1\"; filename=\"random.png\"\r\n"
                        #?"Content-Type: image/png\r\n"
                        #?"\r\n"
                        big-content #?"\r\n"
                        #?"-----------------------------186454651713519341951581030105\r\n"
                        #?"Content-Disposition: form-data; name=\"file2\"; filename=\"random.png\"\r\n"
                        #?"Content-Type: image/png\r\n"
                        #?"\r\n"
                        big-content big-content #?"\r\n"
                        #?"-----------------------------186454651713519341951581030105--\r\n"))
               `(("file1"
                  (:content-disposition "form-data; name=\"file1\"; filename=\"random.png\""
                   :content-type "image/png")
                  (:name "file1" :filename "random.png")
                  ,big-content)
                 ("file2"
                  (:content-disposition "form-data; name=\"file2\"; filename=\"random.png\""
                   :content-type "image/png")
                  (:name "file2" :filename "random.png")
                  ,(concatenate 'string big-content big-content)))
               "big file"))

(test-parser "multipart/form-data; boundary=\"---------------------------186454651713519341951581030105\""
             (bv (str #?"-----------------------------186454651713519341951581030105\r\n"
                      #?"Content-Disposition: form-data; name=\"name\"\r\n"
                      #?"Content-Type: text/plain\r\n"
                      #?"\r\n"
                      #?"深町英太郎\r\n"
                      #?"-----------------------------186454651713519341951581030105\r\n"
                      #?"Content-Disposition: form-data; name=\"introduce\"\r\n"
                      #?"Content-Type: text/plain\r\n"
                      #?"\r\n"
                      #?"Common Lispが好きです。好きな関数はconsです。\r\n"
                      #?"-----------------------------186454651713519341951581030105--\r\n"))
             '(("name"
                (:content-disposition "form-data; name=\"name\""
                 :content-type "text/plain")
                (:name "name")
                "深町英太郎")
               ("introduce"
                (:content-disposition "form-data; name=\"introduce\""
                 :content-type "text/plain")
                (:name "introduce")
                "Common Lispが好きです。好きな関数はconsです。"))
             "UTF-8")

(test-parser "multipart/form-data; boundary=\"---------------------------186454651713519341951581030105\""
             (bv (str #?"-----------------------------186454651713519341951581030105\r\n"
                      #?"Content-Disposition: form-data;\r\n"
                      #?"\tname=\"file1\"; filename=\"random.png\"\r\n"
                      #?"Content-Type: image/png\r\n"
                      #?"\r\n"
                      #?"abc\r\n"
                      #?"-----------------------------186454651713519341951581030105\r\n"
                      #?"Content-Disposition: form-data;\r\n"
                      #?" name=\"text\"\r\n"
                      #?"\r\n"
                      #?"Test text\n with\r\n ümläuts!\r\n"
                      #?"-----------------------------186454651713519341951581030105--\r\n"))
             '(("file1"
                (:content-disposition #?"form-data;\tname=\"file1\"; filename=\"random.png\""
                 :content-type "image/png")
                (:name "file1" :filename "random.png")
                "abc")
               ("text"
                (:content-disposition "form-data; name=\"text\"")
                (:name "text")
                #?"Test text\n with\r\n ümläuts!"))
             "multiline header value")


;;
;; Continuous calling

(let* ((got-body nil)
       (parser (make-multipart-parser
                "multipart/form-data; boundary=\"---------------------------186454651713519341951581030105\""
                (lambda (field-name headers field-meta body)
                  (declare (ignore field-name headers field-meta))
                  (setf got-body (slurp-stream body))))))
  (is (funcall parser
               (bv (str #?"-----------------------------186454651713519341951581030105\r\n"
                        #?"Content-Disposition: form-data;\r\n"
                        #?"\tname=\"file1\"; filename=\"random.png\"\r\n"
                        #?"Content-Type: image/png\r\n"
                        #?"\r\n"
                        #?"abc\r\n")))
      nil)
  (is got-body nil)
  (is (funcall parser
               (bv #?"-----------------------------186454651713519341951581030105\r\n"))
      nil)
  (is got-body (bv "abc") :test #'equalp))

(let* ((got-body nil)
       (parser (make-multipart-parser
                "multipart/form-data; boundary=\"---------------------------186454651713519341951581030105\""
                (lambda (field-name headers field-meta body)
                  (declare (ignore field-name headers field-meta))
                  (setf got-body (slurp-stream body))))))
  (is (funcall parser
               (bv (str #?"-----------------------------186454651713519341951581030105\r\n"
                        #?"Content-Disposition: form-data;\r\n"
                        #?"\tname=\"file1\"; filename=\"random.png\"\r\n"
                        #?"Content-Type: image/png\r\n"
                        #?"\r\n"
                        #?"abc\r\n")))
      nil)
  (is got-body nil)
  (is (funcall parser
               (bv #?"-----------------------------186454651713519341951581030105abc\r\n"))
      nil)
  (is got-body nil)
  (is (funcall parser
               (bv #?"-----------------------------186454651713519341951581030105--"))
      t)
  (is got-body (bv (str #?"abc\r\n"
                        #?"-----------------------------186454651713519341951581030105abc"))
      :test #'equalp))

(let* ((got-body nil)
       (got-headers nil)
       (got-field-meta nil)
       (parser (make-multipart-parser
                "multipart/form-data; boundary=\"---------------------------186454651713519341951581030105\""
                (lambda (field-name headers field-meta body)
                  (declare (ignore field-name))
                  (setf got-headers headers)
                  (setf got-field-meta field-meta)
                  (setf got-body (slurp-stream body))))))
  (is (funcall parser
               (bv (str #?"-----------------------------186454651713519341951581030105\r\n"
                        #?"Content-Disposition: form-data; name=\"file\"; filename=\"黑客与画家(中文版).pdf\"\r\n"
                        #?"Content-Type: application/octet-stream\r\n"
                        #?"\r\n"
                        #?"abc\r\n")))
      nil)
  (is got-headers nil)
  (is got-field-meta nil)
  (is got-body nil)
  (is (funcall parser
               (bv #?"-----------------------------186454651713519341951581030105\r\n"))
      nil)
  (is (gethash "content-disposition" got-headers)
      "form-data; name=\"file\"; filename=\"黑客与画家(中文版).pdf\"")
  (is (gethash "filename" got-field-meta)
      "黑客与画家(中文版).pdf")
  (is got-body (bv "abc") :test #'equalp))

(finalize)

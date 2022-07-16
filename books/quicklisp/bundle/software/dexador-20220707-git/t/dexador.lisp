(in-package :cl-user)
(defpackage dexador-test
  (:use :cl
        :rove)
  (:import-from :clack.test
                :*clack-test-port*
                :*clack-test-access-port*
                :port-available-p
                :localhost))
(in-package :dexador-test)

(defun random-port ()
  "Return a port number not in use from 50000 to 60000."
  (loop for port from (+ 50000 (random 1000)) upto 60000
        if (clack.test::port-available-p port)
          return port))

(defmacro testing-app (desc app &body body)
  `(let ((*clack-test-port* (random-port)))
     (clack.test:testing-app ,desc ,app
       (dex:clear-connection-pool)
       ,@body)))

(deftest normal-case-tests
  (testing-app "normal case"
      (lambda (env)
        `(200 (:content-length ,(length (getf env :request-uri))) (,(getf env :request-uri))))
    (testing "GET"
      (multiple-value-bind (body code headers)
          (dex:get (localhost "/foo")
                   :headers '((:x-foo . "ppp")))
        (ok (eql code 200))
        (ok (equal body "/foo"))
        (ok (equal (gethash "content-length" headers) "4"))))
    (testing "HEAD"
      (multiple-value-bind (body code)
          (dex:head (localhost "/foo"))
        (ok (eql code 200))
        (ok (equal body ""))))
    (testing "PUT"
      (multiple-value-bind (body code)
          (dex:put (localhost "/foo"))
        (ok (eql code 200))
        (ok (equal body "/foo"))))
    (testing "DELETE"
      (multiple-value-bind (body code)
          (dex:delete (localhost "/foo"))
        (ok (eql code 200))
        (ok (equal body "/foo"))))))

(deftest proxy-http-tests
  #+windows
  (skip "Skipped proxy tests on Windows")
  #-windows
  (testing-app "proxy (http) case"
      ; proxy behavior is same as direct connection if http
      (lambda (env)
        (let ((body (format nil "~A~%~A"
                            (gethash "host" (getf env :headers))
                            (getf env :request-uri))))
          `(200 (:content-length ,(length body)) (,body))))
    (testing "GET"
      (multiple-value-bind (body code)
          (dex:get "http://lisp.org/foo"
                   :headers '((:x-foo . "ppp"))
                   :proxy (localhost))
        (ok (eql code 200))
        (ok (equal body (format nil "lisp.org~%/foo")))))
    (testing "HEAD"
      (multiple-value-bind (body code)
          (dex:head "http://lisp.org/foo"
                    :proxy (localhost))
        (ok (eql code 200))
        (ok (equal body ""))))
    (testing "PUT"
      (multiple-value-bind (body code)
          (dex:put "http://lisp.org/foo"
                   :proxy (localhost))
        (ok (eql code 200))
        (ok (equal body (format nil "lisp.org~%/foo")))))
    (testing "DELETE"
      (multiple-value-bind (body code)
          (dex:delete "http://lisp.org/foo"
                      :proxy (localhost))
        (ok (eql code 200))
        (ok (equal body (format nil "lisp.org~%/foo")))))))

(deftest proxy-socks5-tests
  #+windows
  (skip "SOCKS5 proxy tests are skipped")
  #-windows
  (testing-app "proxy (socks5) case"
      (flet ((check (uri in out)
               (flexi-streams:with-input-from-sequence (in in)
                 (equalp
                  (flexi-streams:with-output-to-sequence (out :element-type '(unsigned-byte 8))
                    (dexador.backend.usocket::ensure-socks5-connected in out (quri:uri uri) :get))
                  out))))
        (ok (check "http://example.com/"
               #(5 0
                 5 0 0  1  0 0 0 0  0 0)
               #(5 1 0
                 5 1 0  3 11 101 120 97 109 112 108 101 46 99 111 109  0 80)))
        (ok (check "https://example.com/"
               #(5 0
                 5 0 0  1  0 0 0 0  0 0)
               #(5 1 0
                 5 1 0  3 11 101 120 97 109 112 108 101 46 99 111 109  1 187)))
        (ok (check "http://example.com:8080/"
               #(5 0
                 5 0 0  1  0 0 0 0  0 0)
               #(5 1 0
                 5 1 0  3 11 101 120 97 109 112 108 101 46 99 111 109  31 144)))
        (ok (check "https://example.com:8080/"
               #(5 0
                 5 0 0  1  0 0 0 0  0 0)
               #(5 1 0
                 5 1 0  3 11 101 120 97 109 112 108 101 46 99 111 109  31 144)))
        (ok (check "http://example.com/"
                   #(5 0
                     5 0 0  4  0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0  0 0)
                   #(5 1 0
                     5 1 0  3 11 101 120 97 109 112 108 101 46 99 111 109  0 80)))
        (ok (check "http://example.com/"
                   #(5 0
                     5 0 0  3  1 0  0 0)
                   #(5 1 0
                     5 1 0  3 11 101 120 97 109 112 108 101 46 99 111 109  0 80)))
        (handler-case
            (check "http://example.com/"
                   #(4)
                   #())
          (dex:socks5-proxy-request-failed ()
            (ok t)))
        (handler-case
            (check "http://example.com/"
                   #(5 255)
                   #())
          (dex:socks5-proxy-request-failed ()
            (ok t))))

      #+needs-Tor-running-on-localhost
      (let ((proxy "socks5://127.0.0.1:9150"))
        (testing "SOCKS5 GET"
          (multiple-value-bind (body code)
              (dex:get "http://duskgytldkxiuqc6.onion/" :proxy proxy)
            (declare (ignore body))
            (ok (eql code 200))))
        (testing "SOCKS5 GET with SSL"
          (multiple-value-bind (body code)
              (dex:get "https://www.facebookcorewwwi.onion/" :proxy proxy)
            (declare (ignore body))
            (ok (eql code 200)))))))

(deftest redirection-tests
  (testing-app "redirection"
      (lambda (env)
        (let ((id (parse-integer (subseq (getf env :path-info) 1))))
          (cond
            ((= id 3)
             '(200 (:content-length 2) ("OK")))
            ((<= 300 id 399)
             `(,id (:location "/200") ()))
            ((= id 200)
             (let ((method (princ-to-string (getf env :request-method))))
               `(200 (:content-length ,(length method))
                     (,method))))
            (t
             `(302 (:location ,(format nil "/~D" (1+ id))) ())))))
    (testing "redirect"
      (multiple-value-bind (body code headers)
          (dex:get (localhost "/1"))
        (ok (eql code 200))
        (ok (equal body "OK"))
        (ok (equal (gethash "content-length" headers)
                   (princ-to-string 2)))))
    (testing "not enough redirect"
      (multiple-value-bind (body code headers)
          (dex:get (localhost "/1") :max-redirects 0)
        (declare (ignore body))
        (ok (eql code 302))
        (ok (equal (gethash "location" headers) "/2"))))
    (testing "exceed max redirect"
      (multiple-value-bind (body code headers)
          (dex:get (localhost "/4") :max-redirects 7)
        (declare (ignore body))
        (ok (eql code 302))
        (ok (equal (gethash "location" headers) "/12"))))
    (testing "POST redirects as GET"
      (multiple-value-bind (body code headers uri)
          (dex:post (localhost "/301"))
        (declare (ignore headers))
        (ok (eql code 200))
        (ok (equal body "GET"))
        (ok (equal (quri:uri-path uri) "/200"))))
    (testing "POST redirects as POST for 307"
      (multiple-value-bind (body code headers uri)
          (dex:post (localhost "/307"))
        (declare (ignore headers))
        (ok (eql code 200))
        (ok (equal body "POST"))
        (ok (equal (quri:uri-path uri) "/200"))))))

(deftest content-disposition-tests
  #+windows
  (skip "Content-Disposition tests are skipped")
  #-windows
  (testing "content-disposition"
    (ok (equal (dexador.backend.usocket::content-disposition "upload" #P"data/plain-file.txt")
               (format nil "Content-Disposition: form-data; name=\"upload\"; filename=\"plain-file.txt\"~C~C"
                       #\Return #\Newline))
        "ASCII file name")
    (ok (equal (dexador.backend.usocket::content-disposition "upload" #P"data/plain file.txt")
               (format nil "Content-Disposition: form-data; name=\"upload\"; filename=\"plain file.txt\"~C~C"
                       #\Return #\Newline))
        "ASCII file name with space")
    #+ecl
    (skip "Skipped because UTF-8 pathname is not allowed on ECL")
    #-ecl
    (ok (equal (dexador.backend.usocket::content-disposition "upload" #P"data/foo-あいうえお.txt")
               (format nil "Content-Disposition: form-data; name=\"upload\"; filename*=UTF-8''foo-%E3%81%82%E3%81%84%E3%81%86%E3%81%88%E3%81%8A.txt~C~C"
                       #\Return #\Newline))
        "UTF-8 file name")
    (ok (equal (dexador.backend.usocket::content-disposition "title" "ignore")
               (format nil "Content-Disposition: form-data; name=\"title\"~C~C"
                       #\Return #\Newline))
        "string value")))

;; SBCL replaces LF with CRLF when reading from a stream on Windows
(defun replace-crlf-to-lf (string)
  (ppcre:regex-replace-all (format nil "~C~C" #\Return #\Newline)
                           string
                           (format nil "~C" #\Newline)))

(deftest post-request-tests
  (testing-app "POST request"
      (lambda (env)
        (cond
          ((string= (getf env :path-info) "/upload")
           (let ((buf (make-array (getf env :content-length)
                                  :element-type '(unsigned-byte 8))))
             (read-sequence buf (getf env :raw-body))
             `(200 ()
                   (,(replace-crlf-to-lf (babel:octets-to-string buf))))))
          (t
           (let ((req (lack.request:make-request env)))
             `(200 ()
                   (,(with-output-to-string (s)
                       (loop for (k . v) in (lack.request:request-body-parameters req)
                             do (format s "~&~A: ~A~%"
                                        k
                                        (cond
                                          ((and (consp v)
                                                (streamp (car v)))
                                           (let* ((buf (make-array 1024 :element-type '(unsigned-byte 8)))
                                                  (n (read-sequence buf (car v))))
                                             (replace-crlf-to-lf (babel:octets-to-string (subseq buf 0 n)))))
                                          ((consp v)
                                           (car v))
                                          (t v)))))))))))
    (testing "content in alist"
      (multiple-value-bind (body code headers)
          (dex:post (localhost)
                    :content '(("name" . "Eitaro")
                               ("email" . "e.arrows@gmail.com")))
        (declare (ignore headers))
        (ok (eql code 200))
        (ok (equal body (format nil "name: Eitaro~%email: e.arrows@gmail.com~%")))))
    (testing "string content"
      (multiple-value-bind (body code headers)
          (dex:post (localhost "/upload")
                    :content "this is string data")
        (declare (ignore headers))
        (ok (eql code 200))
        (ok (equal body "this is string data"))))
    (testing "octets content"
      (multiple-value-bind (body code headers)
          (dex:post (localhost "/upload")
                    :content (babel:string-to-octets "this is octet data"))
        (declare (ignore headers))
        (ok (eql code 200))
        (ok (equal body "this is octet data"))))
    (testing "multipart"
      (multiple-value-bind (body code)
          (dex:post (localhost)
                    :content `(("title" . "Road to Lisp")
                               ("body" . ,(asdf:system-relative-pathname :dexador #P"t/data/quote.txt"))))
        (ok (eql code 200))
        (ok (equal body
                   (format nil "title: Road to Lisp~%body: \"Within a couple weeks of learning Lisp I found programming in any other language unbearably constraining.\" -- Paul Graham, Road to Lisp~2%")))))
    (testing "upload"
      (multiple-value-bind (body code)
          (dex:post (localhost "/upload")
                    :content (asdf:system-relative-pathname :dexador #P"t/data/quote.txt"))
        (ok (eql code 200))
        (ok (equal body
                   (format nil "\"Within a couple weeks of learning Lisp I found programming in any other language unbearably constraining.\" -- Paul Graham, Road to Lisp~%")))))))

(deftest http-request-failed-tests
  (testing-app "HTTP request failed"
      (lambda (env)
        (if (string= (getf env :path-info) "/404")
            '(404 (:x-foo 0) ("Not Found"))
            '(500 (:x-bar 1) ("Internal Server Error"))))
    (handler-case
        (progn
          (dex:get (localhost))
          (fail "Must raise an error DEX:HTTP-REQUEST-FAILED"))
      (dex:http-request-failed (e)
        (pass "Raise DEX:HTTP-REQUEST-FAILED error")
        (ok (eql (dex:response-status e) 500)
            "response status is 500")
        (ok (equal (dex:response-body e) "Internal Server Error")
            "response body is \"Internal Server Error\"")
        (ok (equal (gethash "x-bar" (dex:response-headers e))
                   "1"))))
    (handler-case
        (progn
          (dex:get (localhost "/404"))
          (fail "Must raise an error DEX:HTTP-REQUEST-NOT-FOUND"))
      (dex:http-request-not-found (e)
        (pass "Raise DEX:HTTP-REQUEST-FAILED error")
        (ok (eql (dex:response-status e) 404)
            "response status is 404")
        (ok (equal (dex:response-body e) "Not Found")
            "response body is \"Not Found\"")
        (ok (equal (gethash "x-foo" (dex:response-headers e))
                   "0"))))))

(deftest using-cookies-tests
  (testing-app "Using cookies"
      (lambda (env)
        (list (if (string= (getf env :path-info) "/302")
                  302
                  200)
              ;; mixi.jp
              '(:set-cookie "_auid=a8acafbaef245a806f6a308506dc95c8; domain=localhost; path=/; expires=Mon, 10-Jul-2017 12:32:47 GMT"
                ;; sourceforge
                :set-cookie2 "VISITOR=55a11217d3179d198af1d003; expires=\"Tue, 08-Jul-2025 12:54:47 GMT\"; httponly; Max-Age=315360000; Path=/")
              '("ok")))
    (let ((cookie-jar (cl-cookie:make-cookie-jar)))
      (ok (eql (length (cl-cookie:cookie-jar-cookies cookie-jar)) 0) "0 cookies")
      (dex:head (localhost) :cookie-jar cookie-jar)
      (ok (eql (length (cl-cookie:cookie-jar-cookies cookie-jar)) 2) "2 cookies")
      (dex:head (localhost) :cookie-jar cookie-jar))

    ;; 302
    (let ((cookie-jar (cl-cookie:make-cookie-jar)))
      (ok (eql (length (cl-cookie:cookie-jar-cookies cookie-jar)) 0) "0 cookies")
      (dex:head (localhost "/302") :cookie-jar cookie-jar)
      (ok (eql (length (cl-cookie:cookie-jar-cookies cookie-jar)) 2) "2 cookies")
      (dex:head (localhost "/302") :cookie-jar cookie-jar))))

(deftest verbose-tests
  (testing-app "verbose"
      (lambda (env)
        (declare (ignore env))
        '(200 () ("ok")))
    (ok (dex:get (localhost) :verbose t))))

(deftest want-stream-tests
  (testing-app "want-stream"
      (lambda (env)
        (declare (ignore env))
        '(200 (:content-type "text/plain") ("hi")))
    ;; decoding stream
    (let ((body (dex:get (localhost) :want-stream t :keep-alive nil)))
      #+windows
      (ok (typep body 'stream))
      #-windows
      (ok (typep body 'dexador.decoding-stream:decoding-stream)
          "body is a decoding stream")
      (ok (subtypep (stream-element-type body) 'babel:unicode-char)
          "body is a character stream")
      (let ((buf (make-string 2)))
        (read-sequence buf body)
        (ok (equal buf "hi"))))
    ;; binary stream
    (let ((body (dex:get (localhost) :want-stream t :force-binary t :keep-alive nil)))
      (ok (typep body 'stream) "body is a stream")
      (ok (open-stream-p body) "body is open")
      (ok (subtypep (stream-element-type body) '(unsigned-byte 8))
          "body is a octets stream")
      (let ((buf (make-array 2 :element-type '(unsigned-byte 8))))
        (read-sequence buf body)
        (ok (equal (babel:octets-to-string buf) "hi"))))))

(deftest big-body-with-want-stream-tests
  (testing-app "big body with want-stream"
      (lambda (env)
        (declare (ignore env))
        `(200 (:content-type "application/json; charset=utf-8"
               :content-length 748)
              ("[{\"name\":\"allow-statement-in-has-a\",\"commit\":{\"sha\":\"d58b3c96503786c64eb2dba22980ebb14010bdbf\",\"url\":\"https://api.github.com/repos/fukamachi/datafly/commits/d58b3c96503786c64eb2dba22980ebb14010bdbf\"}},{\"name\":\"fix-has-a\",\"commit\":{\"sha\":\"4bcea61e84402317ab49605918972983a1511e6a\",\"url\":\"https://api.github.com/repos/fukamachi/datafly/commits/4bcea61e84402317ab49605918972983a1511e6a\"}},{\"name\":\"jojo\",\"commit\":{\"sha\":\"d2b753e7fdd0dbeada9721380cf410186a85535b\",\"url\":\"https://api.github.com/repos/fukamachi/datafly/commits/d2b753e7fdd0dbeada9721380cf410186a85535b\"}},{\"name\":\"master\",\"commit\":{\"sha\":\"d2b753e7fdd0dbeada9721380cf410186a85535b\",\"url\":\"https://api.github.com/repos/fukamachi/datafly/commits/d2b753e7fdd0dbeada9721380cf410186a85535b\"}}]")))
    ;; decoding stream
    (let ((body (dex:get (localhost) :want-stream t)))
      #+windows
      (ok (typep body 'stream))
      #-windows
      (ok (typep body 'dexador.decoding-stream:decoding-stream)
          "body is a decoding stream")
      (ok (subtypep (stream-element-type body) 'babel:unicode-char)
          "body is a character stream")
      (let ((buf (make-string 1024)))
        (ok (eql (read-sequence buf body) 748))))))

(deftest redirection-for-want-stream-tests
  (testing-app "redirection for want-stream"
      (lambda (env)
        (if (string= (getf env :path-info) "/index.html")
            '(200 () ("ok"))
            '(307 (:location "/index.html"
                   :transfer-encoding "chunked") (""))))
    (let ((body (dex:get (localhost) :want-stream t)))
      (ok body))))

(deftest no-body-tests
  (testing-app "no body"
    (lambda (env)
      (let ((path (getf env :path-info)))
        (if (string= path "/204")
            '(204 () ())
            '(200 () ()))))
  ;; no Content-Length and no Transfer-Encoding
  (multiple-value-bind (body status headers)
      (dex:get (localhost))
    (ok (equal body ""))
    (ok (eql status 200))
    (ok (null (gethash "content-length" headers)))
    (ok (null (gethash "transfer-encoding" headers))))
  ;; 204 No Content
  (multiple-value-bind (body status headers)
      (dex:get (localhost "/204"))
    (ok (eql status 204))
    (ok (equal body ""))
    (ok (null (gethash "content-length" headers)))
    (ok (null (gethash "transfer-encoding" headers))))))

(defvar *json* "{\"name\":\"Eitaro Fukamachi\",\"name_ja\":\"深町英太郎\",\"login\":true}")
(deftest json-tests
  (testing-app "JSON"
      (lambda (env)
        (declare (ignore env))
        `(200 (:content-type "application/json") (,*json*)))
    (multiple-value-bind (body status)
        (dex:get (localhost))
      (ok (equal body *json*)
          "JSON is returned as a string")
      (ok (eql status 200)))
    (let ((babel:*default-character-encoding* :cp932))
      ;; Test if the JSON encoding
      (multiple-value-bind (body status)
          (dex:get (localhost))
        (ok (equal body *json*)
            "The default encoding is UTF-8 though babel:*default-character-encoding* is different")
        (ok (eql status 200))))))

(deftest keep-alive-tests
  (testing-app "keep-alive"
      (lambda (env)
        (declare (ignore env))
        '(200 () ("hi")))
    (let ((headers (nth-value 2 (dex:get (localhost)))))
      (ok (or (null (gethash "connection" headers))
              (string-equal (gethash "connection" headers) "keep-alive"))))
    (let ((headers (nth-value 2 (dex:get (localhost) :keep-alive nil))))
      (ok (equalp (gethash "connection" headers) "close")))
    (multiple-value-bind (b status response-headers uri opaque-socket-stream)
        (dex:get (localhost) :keep-alive t :use-connection-pool nil)
      (declare (ignorable b status response-headers uri opaque-socket-stream))
      #+windows
      (ok (null opaque-socket-stream) "no socket stream")
      #-windows
      (ok (open-stream-p opaque-socket-stream) "stream is kept alive")
      (ok (= status 200) "success")
      #-windows
      (multiple-value-bind (b2 status2 response-headers2 uri2 opaque-socket-stream2)
          (dex:get (localhost) :keep-alive t :use-connection-pool nil :stream opaque-socket-stream)
        (declare (ignorable b2 response-headers2 uri2))
        (ok (eql opaque-socket-stream opaque-socket-stream2) "stream is re-used")
        (ok (open-stream-p opaque-socket-stream2) "stream is kept alive")
        (ok (close opaque-socket-stream) "stream can be closed")
        (ok (= status2 200) "success")
        (multiple-value-bind (b3 status3 response-headers3 uri3 opaque-socket-stream3)
            (dex:get (localhost) :keep-alive t :use-connection-pool nil :stream opaque-socket-stream2)
          (declare (ignorable b3 uri3))
          (member (gethash "connection" response-headers3) '(nil "keep-alive") :test #'equalp)
          (ok (= status3 200) "success")
          (ok (not (eql opaque-socket-stream3 opaque-socket-stream2)) "passing in closed stream works"))))))

(deftest deflate-compression-tests
  (testing-app "deflate compression"
      (lambda (env)
        (declare (ignore env))
        `(200 (:content-encoding "deflate" :content-type "text/plain")
              ,(asdf:system-relative-pathname :dexador #p"t/data/test.zlib")))
    (let ((body (dex:get (localhost))))
      (ok (equal body "Deflate test string.")))))

(deftest gzip-compression-tests
  (testing-app "gzip compression"
      (lambda (env)
        (declare (ignore env))
        `(200 (:content-encoding "gzip" :content-type "text/plain")
              ,(asdf:system-relative-pathname :dexador #p"t/data/test.gz")))
    (let ((body (dex:get (localhost))))
      (ok (equal body "Gzip test string.")))))

(deftest unread-character-tests
  (ok (eql #\u2602
           (with-open-file (stream (asdf:system-relative-pathname
                                     :dexador #p"t/data/umb.bin")
                                   :element-type '(unsigned-byte 8))
             (let ((decoding-stream
                     (dexador.decoding-stream:make-decoding-stream stream)))
               (peek-char nil decoding-stream)
               (read-char decoding-stream))))))


(deftest connection-cache-test
  (let ((dexador.connection-cache:*connection-pool* (dexador.connection-cache:make-connection-pool 2)))
    ;; Make sure empty cache works
    (ok (null (dexador.connection-cache:steal-connection "some-host")))
    (dexador.connection-cache:clear-connection-pool)
    ;; Make sure push / steal works
    (dexador.connection-cache:push-connection "host1" "host1-socket")
    (ok (string= (dexador.connection-cache:steal-connection "host1") "host1-socket"))
    ;; Make sure steal actually removed the connection
    (ok (null (dexador.connection-cache:steal-connection "host1")))
    ;; Check to make sure multiple elements with the same key work
    (dexador.connection-cache:push-connection "host1" "host1-socket1")
    (dexador.connection-cache:push-connection "host1" "host1-socket2")
    (let ((result1 (dexador.connection-cache:steal-connection "host1"))
          (result2 (dexador.connection-cache:steal-connection "host1")))
      (ok (and (stringp result1) (stringp result2) (not (string= result1 result2)))))
    ;; make sure hash table stays clean
    (ok (zerop (hash-table-count (dexador.connection-cache::lru-pool-hash-table dexador.connection-cache::*connection-pool*))))
    ;; make sure maximum connections is obeyed and least recently used element is evicted
    (dexador.connection-cache:push-connection "host1" "host1-socket1")
    (dexador.connection-cache:push-connection "host2" "host2-socket")
    (dexador.connection-cache:push-connection "host2" "host2-socket")
    (ok (null (dexador.connection-cache:steal-connection "host1")))
    (ok (string= (dexador.connection-cache:steal-connection "host2") "host2-socket"))
    (ok (string= (dexador.connection-cache:steal-connection "host2") "host2-socket"))
    (ok (null (dexador.connection-cache:steal-connection "host2")))
    ;; Make sure clear-connection-pool works and callbacks are called
    (let ((called nil))
      (dexador.connection-cache:push-connection "host1" "host1-socket1" (lambda (s) (declare (ignore s)) (setf called t)))
      (dexador.connection-cache:clear-connection-pool)
      (ok called)
      (setf called nil)
      (dexador.connection-cache:push-connection "host1" "host1-socket" (lambda (s) (declare (ignore s))  (setf called "host1")))
      (dexador.connection-cache:push-connection "host2" "host2-socket" (lambda (s) (declare (ignore s)) (setf called "host2")))
      (dexador.connection-cache:push-connection "host3" "host3-socket" (lambda (s) (declare (ignore s)) (setf called "host3")))
      (ok (string= called "host1"))
      (dexador.connection-cache:push-connection "host4" "host4-socket" (lambda (s) (declare (ignore s)) (setf called "host4")))
      (ok (string= called "host2")))))

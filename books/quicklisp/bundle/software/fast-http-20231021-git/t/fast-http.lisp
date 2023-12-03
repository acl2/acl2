(in-package :cl-user)
(defpackage fast-http-test
  (:use :cl
        :fast-http
        :fast-http-test.test-utils
        :prove
        :babel
        :xsubseq)
  (:import-from :alexandria
                :ensure-list))
(in-package :fast-http-test)

(syntax:use-syntax :interpol)

(plan nil)

(defun is-request-or-response (type chunks headers body description)
  (let* (got-headers
         (got-body nil)
         finishedp
         headers-test-done-p body-test-done-p
         (chunks (ensure-list chunks))
         (length (length chunks))
         (parser (make-parser (ecase type
                                (:request (make-http-request))
                                (:response (make-http-response)))
                              :header-callback (lambda (h) (setf got-headers h))
                              :body-callback (lambda (b start end)
                                               (push (subseq b start end) got-body))
                              :finish-callback (lambda () (setf finishedp t)))))
    (subtest description
      (loop for i from 1
            for chunk in chunks
            do (multiple-value-bind (http header-complete-p completedp)
                   (funcall parser (babel:string-to-octets chunk))
                 (declare (ignore http))
                 (is completedp (= i length)
                     (format nil "is~:[ not~;~] completed: ~D / ~D" (= i length) i length))
                 (when (and header-complete-p
                            (not headers-test-done-p))
                   (subtest "headers"
                     (loop for (k v) on headers by #'cddr
                           do (is (gethash (string-downcase k) got-headers)
                                  v))
                     (is (hash-table-count got-headers) (/ (length headers) 2)))
                   (setf headers-test-done-p t))
                 (when (and completedp
                            (not body-test-done-p))
                   (is (and got-body
                            (apply #'concatenate '(simple-array (unsigned-byte 8) (*))
                                   (nreverse got-body))) body "body" :test #'equalp)
                   (setf body-test-done-p t)))))))

(defun is-request (chunks headers body description)
  (is-request-or-response :request chunks headers body description))

(defun is-response (chunks headers body description)
  (is-request-or-response :response chunks headers body description))


;;
;; Requests

(is-request (str #?"GET /test HTTP/1.1\r\n"
                 #?"User-Agent: curl/7.18.0 (i486-pc-linux-gnu) libcurl/7.18.0 OpenSSL/0.9.8g zlib/1.2.3.3 libidn/1.1\r\n"
                 #?"Host: 0.0.0.0=5000\r\n"
                 #?"Accept: */*\r\n"
                 #?"\r\n")
            '(:user-agent "curl/7.18.0 (i486-pc-linux-gnu) libcurl/7.18.0 OpenSSL/0.9.8g zlib/1.2.3.3 libidn/1.1"
              :host "0.0.0.0=5000"
              :accept "*/*")
            nil
            "curl GET")

(is-request (str #?"GET /favicon.ico HTTP/1.1\r\n"
                 #?"Host: 0.0.0.0=5000\r\n"
                 #?"User-Agent: Mozilla/5.0 (X11; U; Linux i686; en-US; rv:1.9) Gecko/2008061015 Firefox/3.0\r\n"
                 #?"Accept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\n"
                 #?"Accept-Language: en-us,en;q=0.5\r\n"
                 #?"Accept-Encoding: gzip,deflate\r\n"
                 #?"Accept-Charset: ISO-8859-1,utf-8;q=0.7,*;q=0.7\r\n"
                 #?"Keep-Alive: 300\r\n"
                 #?"Connection: keep-alive\r\n"
                 #?"\r\n")
            '(:host "0.0.0.0=5000"
              :user-agent "Mozilla/5.0 (X11; U; Linux i686; en-US; rv:1.9) Gecko/2008061015 Firefox/3.0"
              :accept "text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8"
              :accept-language "en-us,en;q=0.5"
              :accept-encoding "gzip,deflate"
              :accept-charset "ISO-8859-1,utf-8;q=0.7,*;q=0.7"
              :keep-alive "300"
              :connection "keep-alive")
            nil
            "Firefox GET")

(is-request (str #?"GET /dumbfuck HTTP/1.1\r\n"
                 #?"aaaaaaaaaaaaa:++++++++++\r\n"
                 #?"\r\n")
            '(:aaaaaaaaaaaaa "++++++++++")
            nil
            "dumbfuck")

(is-request (str #?"GET /forums/1/topics/2375?page=1#posts-17408 HTTP/1.1\r\n"
                 #?"\r\n")
            '()
            nil
            "fragment in URL")

(is-request (str #?"GET /get_no_headers_no_body/world HTTP/1.1\r\n"
                 #?"\r\n")
            '()
            nil
            "get no headers no body")

(is-request (str #?"GET /get_one_header_no_body HTTP/1.1\r\n"
                 #?"Accept: */*\r\n"
                 #?"\r\n")
            '(:accept "*/*")
            nil
            "get one headers no body")

(is-request (str #?"GET /get_funky_content_length_body_hello HTTP/1.0\r\n"
                 #?"conTENT-Length: 5\r\n"
                 #?"\r\n"
                 #?"HELLO")
            '(:content-length "5")
            (bv "HELLO")
            "get funky content length body HELLO")

(is-request (str #?"POST /post_identity_body_world?q=search#hey HTTP/1.1\r\n"
                 #?"Accept: */*\r\n"
                 #?"Transfer-Encoding: identity\r\n"
                 #?"Content-Length: 5\r\n"
                 #?"\r\n"
                 #?"World")
            '(:accept "*/*"
              :transfer-encoding "identity"
              :content-length "5")
            (bv "World")
            "post identity body world")

(is-request (str #?"POST /post_chunked_all_your_base HTTP/1.1\r\n"
                 #?"Transfer-Encoding: chunked\r\n"
                 #?"\r\n"
                 #?"1e\r\nall your base are belong to us\r\n"
                 #?"0\r\n"
                 #?"\r\n")
            '(:transfer-encoding "chunked")
            (bv "all your base are belong to us")
            "post - chunked body: all your base are belong to us")

(is-request (str #?"POST /two_chunks_mult_zero_end HTTP/1.1\r\n"
                 #?"Transfer-Encoding: chunked\r\n"
                 #?"\r\n"
                 #?"5\r\nhello\r\n"
                 #?"6\r\n world\r\n"
                 #?"000\r\n"
                 #?"\r\n")
            '(:transfer-encoding "chunked")
            (bv "hello world")
            "two chunks ; triple zero ending")

(is-request (str #?"POST /chunked_w_trailing_headers HTTP/1.1\r\n"
                 #?"Transfer-Encoding: chunked\r\n"
                 #?"\r\n"
                 #?"5\r\nhello\r\n"
                 #?"6\r\n world\r\n"
                 #?"0\r\n"
                 #?"Vary: *\r\n"
                 #?"Content-Type: text/plain\r\n"
                 #?"\r\n")
            '(:transfer-encoding "chunked"
              :vary "*"
              :content-type "text/plain")
            (bv "hello world")
            "chunked with trailing headers. blech.")

(is-request (str #?"POST /chunked_w_bullshit_after_length HTTP/1.1\r\n"
                 #?"Transfer-Encoding: chunked\r\n"
                 #?"\r\n"
                 #?"5; ihatew3;whatthefuck=aretheseparametersfor\r\nhello\r\n"
                 #?"6; blahblah; blah\r\n world\r\n"
                 #?"0\r\n"
                 #?"\r\n")
            '(:transfer-encoding "chunked")
            (bv "hello world")
            "with bullshit after the length")

(is-request #?"GET /with_\"stupid\"_quotes?foo=\"bar\" HTTP/1.1\r\n\r\n"
            '()
            nil
            "with quotes")

(is-request (str #?"GET /test HTTP/1.0\r\n"
                 #?"Host: 0.0.0.0:5000\r\n"
                 #?"User-Agent: ApacheBench/2.3\r\n"
                 #?"Accept: */*\r\n\r\n")
            '(:host "0.0.0.0:5000"
              :user-agent "ApacheBench/2.3"
              :accept "*/*")
            nil
            "ApacheBench GET")

(is-request #?"GET /test.cgi?foo=bar?baz HTTP/1.1\r\n\r\n"
            '()
            nil
            "Query URL with question mark")

(is-request #?"\r\nGET /test HTTP/1.1\r\n\r\n"
            '()
            nil
            "Newline prefix GET")

(is-request (str #?"GET /demo HTTP/1.1\r\n"
                 #?"Host: example.com\r\n"
                 #?"Connection: Upgrade\r\n"
                 #?"Sec-WebSocket-Key2: 12998 5 Y3 1  .P00\r\n"
                 #?"Sec-WebSocket-Protocol: sample\r\n"
                 #?"Upgrade: WebSocket\r\n"
                 #?"Sec-WebSocket-Key1: 4 @1  46546xW%0l 1 5\r\n"
                 #?"Origin: http://example.com\r\n"
                 #?"\r\n"
                 #?"Hot diggity dogg")
            '(:host "example.com"
              :connection "Upgrade"
              :sec-websocket-key2 "12998 5 Y3 1  .P00"
              :sec-websocket-protocol "sample"
              :upgrade "WebSocket"
              :sec-websocket-key1 "4 @1  46546xW%0l 1 5"
              :origin "http://example.com")
            nil
            "Upgrade request")

(is-request (str #?"CONNECT 0-home0.netscape.com:443 HTTP/1.0\r\n"
                 #?"User-agent: Mozilla/1.1N\r\n"
                 #?"Proxy-authorization: basic aGVsbG86d29ybGQ=\r\n"
                 #?"\r\n"
                 #?"some data\r\n"
                 #?"and yet even more data")
            '(:user-agent "Mozilla/1.1N"
              :proxy-authorization "basic aGVsbG86d29ybGQ=")
            nil
            "CONNECT request")

(is-request (str #?"REPORT /test HTTP/1.1\r\n"
                 #?"\r\n")
            '()
            nil
            "REPORT request")

(is-request (str #?"GET /\r\n"
                 #?"\r\n")
            '()
            nil
            "request with no HTTP version")

(is-request (str #?"M-SEARCH * HTTP/1.1\r\n"
                 #?"HOST: 239.255.255.250:1900\r\n"
                 #?"MAN: \"ssdp:discover\"\r\n"
                 #?"ST: \"ssdp:all\"\r\n"
                 #?"\r\n")
            '(:host "239.255.255.250:1900"
              :man "\"ssdp:discover\""
              :st "\"ssdp:all\"")
            nil
            "M-SEARCH request")

(is-request (str #?"GET / HTTP/1.1\r\n"
                 #?"Line1:   abc\r\n"
                 #?"\tdef\r\n"
                 #?" ghi\r\n"
                 #?"\t\tjkl\r\n"
                 #?"  mno \r\n"
                 #?"\t \tqrs\r\n"
                 #?"Line2: \t line2\t\r\n"
                 #?"Line3:\r\n"
                 #?" line3\r\n"
                 #?"Line4: \r\n"
                 #?" \r\n"
                 #?"Connection:\r\n"
                 #?" close\r\n"
                 #?"\r\n")
            '(:line1 #?"abc\tdef ghi\t\tjkl  mno \t \tqrs"
              :line2 #?"line2\t"
              :line3 "line3"
              :line4 ""
              :connection "close")
            nil
            "line folding in header value")

(is-request (str #?"GET http://hypnotoad.org?hail=all HTTP/1.1\r\n"
                 #?"\r\n")
            '()
            nil
            "host terminated by a query string")

(is-request (str #?"GET http://hypnotoad.org:1234?hail=all HTTP/1.1\r\n"
                 #?"\r\n")
            '()
            nil
            "host:port terminated by a query string")

(is-request (str #?"GET http://hypnotoad.org:1234 HTTP/1.1\r\n"
                 #?"\r\n")
            '()
            nil
            "host:port terminated by a space")

(is-request (str #?"PATCH /file.txt HTTP/1.1\r\n"
                 #?"Host: www.example.com\r\n"
                 #?"Content-Type: application/example\r\n"
                 #?"If-Match: \"e0023aa4e\"\r\n"
                 #?"Content-Length: 10\r\n"
                 #?"\r\n"
                 #?"cccccccccc")
            '(:host "www.example.com"
              :content-type "application/example"
              :if-match "\"e0023aa4e\""
              :content-length "10")
            (bv "cccccccccc")
            "PATCH request")

(is-request (str #?"CONNECT HOME0.NETSCAPE.COM:443 HTTP/1.0\r\n"
                 #?"User-agent: Mozilla/1.1N\r\n"
                 #?"Proxy-authorization: basic aGVsbG86d29ybGQ=\r\n"
                 #?"\r\n")
            '(:user-agent "Mozilla/1.1N"
              :proxy-authorization "basic aGVsbG86d29ybGQ=")
            nil
            "CONNECT caps request")

(is-request (str #?"GET /δ¶/δt/pope?q=1#narf HTTP/1.1\r\n"
                 #?"Host: github.com\r\n"
                 #?"\r\n")
            '(:host "github.com")
            nil
            "utf-8 path request")

(is-request (str #?"CONNECT home_0.netscape.com:443 HTTP/1.0\r\n"
                 #?"User-agent: Mozilla/1.1N\r\n"
                 #?"Proxy-authorization: basic aGVsbG86d29ybGQ=\r\n"
                 #?"\r\n")
            '(:user-agent "Mozilla/1.1N"
              :proxy-authorization "basic aGVsbG86d29ybGQ=")
            nil
            "underscore in hostname")

(is-request (str #?"POST / HTTP/1.1\r\n"
                 #?"Host: www.example.com\r\n"
                 #?"Content-Type: application/x-www-form-urlencoded\r\n"
                 #?"Content-Length: 4\r\n"
                 #?"\r\n"
                 #?"q=42\r\n")
            '(:host "www.example.com"
              :content-type "application/x-www-form-urlencoded"
              :content-length "4")
            (bv "q=42")
            "eat CRLF between requests, no \"Connection: close\" header")

(is-request (str #?"POST / HTTP/1.1\r\n"
                 #?"Host: www.example.com\r\n"
                 #?"Content-Type: application/x-www-form-urlencoded\r\n"
                 #?"Content-Length: 4\r\n"
                 #?"Connection: close\r\n"
                 #?"\r\n"
                 #?"q=42\r\n")
            '(:host "www.example.com"
              :content-type "application/x-www-form-urlencoded"
              :content-length "4"
              :connection "close")
            (bv "q=42")
            "eat CRLF between requests even if \"Connection: close\" is set")

(is-request (str #?"PURGE /file.txt HTTP/1.1\r\n"
                 #?"Host: www.example.com\r\n"
                 #?"\r\n")
            '(:host "www.example.com")
            nil
            "PURGE request")

(is-request (str #?"SEARCH / HTTP/1.1\r\n"
                 #?"Host: www.example.com\r\n"
                 #?"\r\n")
            '(:host "www.example.com")
            nil
            "SEARCH request")

(is-request (str #?"GET http://a%12:b!&*$@hypnotoad.org:1234/toto HTTP/1.1\r\n"
                 #?"\r\n")
            '()
            nil
            "host:port and basic_auth")

#+nil
(is-request (str #?"GET / HTTP/1.1\n"
                 #?"Line1:   abc\n"
                 #?"\tdef\n"
                 #?" ghi\n"
                 #?"\t\tjkl\n"
                 #?"  mno \n"
                 #?"\t \tqrs\n"
                 #?"Line2: \t line2\t\n"
                 #?"Line3:\n"
                 #?" line3\n"
                 #?"Line4: \n"
                 #?" \n"
                 #?"Connection:\n"
                 #?" close\n"
                 #?"\n")
            '(:line1 #?"abc\tdef ghi\t\tjkl  mno \t \tqrs"
              :line2 #?"line2\t"
              :line3 "line3"
              :line4 ""
              :connection "close")
            nil
            "line folding in header value")


;;
;; Responses

(is-response (str #?"HTTP/1.1 301 Moved Permanently\r\n"
                  #?"Location: http://www.google.com/\r\n"
                  #?"Content-Type: text/html; charset=UTF-8\r\n"
                  #?"Date: Sun, 26 Apr 2009 11:11:49 GMT\r\n"
                  #?"Expires: Tue, 26 May 2009 11:11:49 GMT\r\n"
                  #?"X-$PrototypeBI-Version: 1.6.0.3\r\n"
                  #?"Cache-Control: public, max-age=2592000\r\n"
                  #?"Server: gws\r\n"
                  #?"Content-Length:  219  \r\n"
                  #?"\r\n"
                  #?"<HTML><HEAD><meta http-equiv=\"content-type\" content=\"text/html;charset=utf-8\">\n"
                  #?"<TITLE>301 Moved</TITLE></HEAD><BODY>\n"
                  #?"<H1>301 Moved</H1>\n"
                  #?"The document has moved\n"
                  #?"<A HREF=\"http://www.google.com/\">here</A>.\r\n"
                  #?"</BODY></HTML>\r\n")
             '(:location "http://www.google.com/"
               :content-type "text/html; charset=UTF-8"
               :date "Sun, 26 Apr 2009 11:11:49 GMT"
               :expires "Tue, 26 May 2009 11:11:49 GMT"
               :x-$prototypebi-version "1.6.0.3"
               :cache-control "public, max-age=2592000"
               :server "gws"
               :content-length "219  ")
             (bv (str #?"<HTML><HEAD><meta http-equiv=\"content-type\" content=\"text/html;charset=utf-8\">\n"
                      #?"<TITLE>301 Moved</TITLE></HEAD><BODY>\n"
                      #?"<H1>301 Moved</H1>\n"
                      #?"The document has moved\n"
                      #?"<A HREF=\"http://www.google.com/\">here</A>.\r\n"
                      #?"</BODY></HTML>\r\n"))
             "Google 301")

(is-response (str #?"HTTP/1.1 200 OK\r\n"
                  #?"Date: Tue, 04 Aug 2009 07:59:32 GMT\r\n"
                  #?"Server: Apache\r\n"
                  #?"X-Powered-By: Servlet/2.5 JSP/2.1\r\n"
                  #?"Content-Type: text/xml; charset=utf-8\r\n"
                  #?"Connection: close\r\n"
                  #?"\r\n"
                  #?"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
                  #?"<SOAP-ENV:Envelope xmlns:SOAP-ENV=\"http://schemas.xmlsoap.org/soap/envelope/\">\n"
                  #?"  <SOAP-ENV:Body>\n"
                  #?"    <SOAP-ENV:Fault>\n"
                  #?"       <faultcode>SOAP-ENV:Client</faultcode>\n"
                  #?"       <faultstring>Client Error</faultstring>\n"
                  #?"    </SOAP-ENV:Fault>\n"
                  #?"  </SOAP-ENV:Body>\n"
                  #?"</SOAP-ENV:Envelope>")
             '(:date "Tue, 04 Aug 2009 07:59:32 GMT"
               :server "Apache"
               :x-powered-by "Servlet/2.5 JSP/2.1"
               :content-type "text/xml; charset=utf-8"
               :connection "close")
             (bv (str #?"<?xml version=\"1.0\" encoding=\"UTF-8\"?>\n"
                      #?"<SOAP-ENV:Envelope xmlns:SOAP-ENV=\"http://schemas.xmlsoap.org/soap/envelope/\">\n"
                      #?"  <SOAP-ENV:Body>\n"
                      #?"    <SOAP-ENV:Fault>\n"
                      #?"       <faultcode>SOAP-ENV:Client</faultcode>\n"
                      #?"       <faultstring>Client Error</faultstring>\n"
                      #?"    </SOAP-ENV:Fault>\n"
                      #?"  </SOAP-ENV:Body>\n"
                      #?"</SOAP-ENV:Envelope>"))
             "no Content-Length response")

(defparameter *response*
  #?"HTTP/1.1 200 OK\r
Server: Wookie (0.3.11)\r
Transfer-Encoding: chunked\r
\r
7\r
hello, \r
4\r
how \r
4\r
are \r
4\r
you?\r
0\r
\r
")

(subtest "chunk body"
  (let* ((http (fast-http:make-http-response))
         (parser (fast-http:make-parser http
                                        :body-callback
                                        (lambda (chunk start end)
                                          (format t "chunk: ~a~%" (babel:octets-to-string (subseq chunk start end))))
                                        :finish-callback
                                        (lambda ()
                                          (format t "finish.~%"))))
         (header-chunk1 (subseq *response* 0 1))     ; <headers>
         (header-chunk2 (subseq *response* 1 72))    ; <headers>
         (chunk1 (subseq *response* 72 84))   ; "hello, "
         (chunk2 (subseq *response* 84 102))  ; "how are "
         (chunk3 (subseq *response* 102))     ; "you?"
         (do-parse (lambda (chunk)
                     (funcall parser (babel:string-to-octets chunk)))))
    (funcall do-parse header-chunk1)
    (funcall do-parse header-chunk2)
    (is-print (funcall do-parse chunk1) #?"chunk: hello, \n" "chunk1")
    (is-print (funcall do-parse chunk2) #?"chunk: how \nchunk: are \n" "chunk2")
    (is-print (funcall do-parse chunk3) #?"chunk: you?\nfinish.\n" "chunk3 and finish")))

(subtest "chunk body"
  (let* ((http (fast-http:make-http-response))
         (parser (fast-http:make-parser http
                                        :body-callback
                                        (lambda (chunk start end)
                                          (format t "chunk: ~a~%" (babel:octets-to-string (subseq chunk start end))))
                                        :finish-callback
                                        (lambda ()
                                          (format t "finish.~%"))))
         (chunk01 (subseq *response* 0 17))
         (chunk02 (subseq *response* 17 72))
         (chunk03 (subseq *response* 72 73))
         (chunk04 (subseq *response* 73 84))
         (chunk05 (subseq *response* 84 85))
         (chunk06 (subseq *response* 85 87))
         (chunk07 (subseq *response* 87 91))
         (chunk08 (subseq *response* 91 93))
         (chunk09 (subseq *response* 93 101))
         (chunk10 (subseq *response* 101 103))
         (chunk11 (subseq *response* 103))
         (do-parse (lambda (chunk)
                     (funcall parser (babel:string-to-octets chunk)))))
    ;; first line
    (funcall do-parse chunk01)
    ;; headers
    (funcall do-parse chunk02)

    (is-print (funcall do-parse chunk03) "")
    (is-print (funcall do-parse chunk04) #?"chunk: hello, \n")
    (is-print (funcall do-parse chunk05) "")
    (is-print (funcall do-parse chunk06) "")
    (is-print (funcall do-parse chunk07) #?"chunk: how \n")
    (is-print (funcall do-parse chunk08) "")
    (is-print (funcall do-parse chunk09) #?"chunk: are \n")
    (is-print (funcall do-parse chunk10) "")
    (is-print (funcall do-parse chunk11) #?"chunk: you?\nfinish.\n")))

;; Take from http://www.sonosite.com/
;; https://github.com/fukamachi/fast-http/pull/15
(is-response (str #?"HTTP/1.1 200 OK\r\n"
                 #?"Set-Cookie: SESS99110bddbcd18a012d19509db399dc05=9hubdaihrslaka5ci69novcl55; expires=Fri, 30-Jan-2015 08:43:59 GMT; path=/; domain=.sonosite.com\r\n"
                 #?"Last-Modified: Fri, 30 Jan 2015 05:35:20 GMT\r\n"
                 #?"ETag: \"d7b7d261ac63a34d416e6cbefc5b6e3f\"\r\n"
                 #?"Expires: Sun, 19 Nov 1978 05:00:00 GMT\r\n"
                 #?"Content-Type: text/html; charset=utf-8\r\n"
                 #?"Server: Go Away\r\n"
                 #?"Age: 0\r\n"
                 #?"Cache-Control: must-revalidate\r\n"
                 #?"X-Yottaa-Optimizations: ob/0 si/1215743397 tts/1416857618979 ti/52d77c618b5f02370e0119d9 ai/50e5c1b84707e60c8000021f\r\n"
                 #?"Transfer-Encoding: chunked\r\n"
                 #?"Date: Fri, 30 Jan 2015 05:43:59 GMT\r\n"
                 #?"Age: 0\r\n"
                 #?"Connection: keep-alive\r\n"
                 #?"X-Yottaa-Metrics: 042136fb801b/[427,231,-] 041136fba428/[-,429.246]\r\n"
                 #?"\r\n"
                 #?"0\r\n\r\n")
             '(:set-cookie ("SESS99110bddbcd18a012d19509db399dc05=9hubdaihrslaka5ci69novcl55; expires=Fri, 30-Jan-2015 08:43:59 GMT; path=/; domain=.sonosite.com")
               :last-modified "Fri, 30 Jan 2015 05:35:20 GMT"
               :etag "\"d7b7d261ac63a34d416e6cbefc5b6e3f\""
               :expires "Sun, 19 Nov 1978 05:00:00 GMT"
               :content-type "text/html; charset=utf-8"
               :server "Go Away"
               :age "0, 0"
               :cache-control "must-revalidate"
               :x-yottaa-optimizations "ob/0 si/1215743397 tts/1416857618979 ti/52d77c618b5f02370e0119d9 ai/50e5c1b84707e60c8000021f"
               :transfer-encoding "chunked"
               :date "Fri, 30 Jan 2015 05:43:59 GMT"
               :connection "keep-alive"
               :x-yottaa-metrics "042136fb801b/[427,231,-] 041136fba428/[-,429.246]")
            nil
            "multiple number headers")

(finalize)

(in-package :cl-user)
(defpackage fast-http-test.benchmark
  (:use :cl
        :fast-http)
  (:export :run-ll-benchmark
           :run-benchmark
           :run-ll-profile
           :run-profile))
(in-package :fast-http-test.benchmark)

(syntax:use-syntax :interpol)

(defun run-ll-benchmark ()
  (let ((http (make-http-request))
        (callbacks (make-callbacks))
        (data (babel:string-to-octets #?"GET /cookies HTTP/1.1\r\nHost: 127.0.0.1:8090\r\nConnection: keep-alive\r\nCache-Control: max-age=0\r\nAccept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\nUser-Agent: Mozilla/5.0 (Windows NT 6.1; WOW64) AppleWebKit/537.17 (KHTML, like Gecko) Chrome/24.0.1312.56 Safari/537.17\r\nAccept-Encoding: gzip,deflate,sdch\r\nAccept-Language: en-US,en;q=0.8\r\nAccept-Charset: ISO-8859-1,utf-8;q=0.7,*;q=0.3\r\nCookie: name=wookie\r\n\r\n")))
    #+sbcl (sb-ext:gc :full t)
    (time
     (loop repeat 100000 do
       (parse-request http callbacks data)))))

(defun run-benchmark ()
  (let ((data (babel:string-to-octets #?"GET /cookies HTTP/1.1\r\nHost: 127.0.0.1:8090\r\nConnection: keep-alive\r\nCache-Control: max-age=0\r\nAccept: text/html,application/xhtml+xml,application/xml;q=0.9,*/*;q=0.8\r\nUser-Agent: Mozilla/5.0 (Windows NT 6.1; WOW64) AppleWebKit/537.17 (KHTML, like Gecko) Chrome/24.0.1312.56 Safari/537.17\r\nAccept-Encoding: gzip,deflate,sdch\r\nAccept-Language: en-US,en;q=0.8\r\nAccept-Charset: ISO-8859-1,utf-8;q=0.7,*;q=0.3\r\nCookie: name=wookie\r\n\r\n"))
        (http (make-http-request)))
    #+sbcl (sb-ext:gc :full t)
    (time
     (loop repeat 100000 do
       (let ((parser (make-parser http)))
         (funcall parser data))))))

(eval-when (:compile-toplevel :load-toplevel :execute)
  (defparameter *profile-packages*
    '("FAST-HTTP" "FAST-HTTP.PARSER" "FAST-HTTP.BYTE-VECTOR" "FAST-HTTP.ERROR" "FAST-HTTP.UTIL")))

#+sbcl
(defun run-ll-profile ()
  #.`(sb-profile:profile ,@*profile-packages*)
  (run-ll-benchmark)
  (sb-profile:report)
  #.`(sb-profile:unprofile ,@*profile-packages*))

#+sbcl
(defun run-profile ()
  #.`(sb-profile:profile ,@*profile-packages*)
  (run-benchmark)
  (sb-profile:report)
  #.`(sb-profile:unprofile ,@*profile-packages*))

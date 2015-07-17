
(pushnew "/home/anton/prj/cl+ssl/cl-plus-ssl/" asdf:*central-registry*)
(ql:quickload :cl+ssl)
(ql:quickload :usocket)

(let* ((socket (usocket:socket-connect "sni.velox.ch" 443
                                       :element-type '(unsigned-byte 8)))
       (ssl-stream (cl+ssl:make-ssl-client-stream (usocket:socket-stream socket)
                                                  :hostname "sni.velox.ch"))
       (char-stream (flexi-streams:make-flexi-stream ssl-stream
                                                     :external-format '(:utf-8 :eol-style :crlf)))
       (reply-buf (make-string 1000)))
  (unwind-protect
       (progn
         (format char-stream "GET / HTTP/1.1~%")
         (format char-stream "Host: sni.velox.ch~%~%")
         (finish-output char-stream)
         (read-sequence reply-buf char-stream)
         reply-buf)
    (usocket:socket-close socket)))

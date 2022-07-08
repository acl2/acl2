(in-package :cl+ssl.test)

(def-suite :cl+ssl.alpn :in :cl+ssl
  :description "ALPN tests")

(in-suite :cl+ssl.alpn)

(test alpn-client
  (when (cl+ssl::openssl-is-at-least 1 0 2)
    (flet ((test-alpn-result (target proposed expected)
             (usocket:with-client-socket (socket stream target 443
                                                 :element-type '(unsigned-byte 8))
               (is
                (equal expected
                       (cl+ssl:get-selected-alpn-protocol
                        (cl+ssl:make-ssl-client-stream stream :alpn-protocols proposed)))))))
      (test-alpn-result "example.com" nil nil)
      (test-alpn-result "example.com" '( "should-not-exist" "h2" "also-should-not-exist")
                        "h2"))))

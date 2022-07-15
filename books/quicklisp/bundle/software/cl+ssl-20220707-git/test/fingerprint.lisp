(in-package :cl+ssl.test)

(def-suite :cl+ssl.fingerprint :in :cl+ssl
  :description "Certificate fingerprint test")

(in-suite :cl+ssl.fingerprint)

(test fingerprint-google-cert
  (with-cert ("google.der" cert)
    (is (equalp (cl+ssl:certificate-fingerprint cert)
                #(#x7F #xD0 #x53 #xFA #x7F #x4E #x6E #x20 #xDA #xD4 #xC1 #x26
                  #x2A #x54 #x57 #x82 #xA2 #x22 #xA0 #xBC)))
    (is (equalp (cl+ssl:certificate-fingerprint cert :md5)
                #(#x67 #xAC #xDC #xE3 #x51 #x60 #x44 #x9A #xCB #x2A #x64 #x89
                  #xA9 #x10 #x52 #x39)))))

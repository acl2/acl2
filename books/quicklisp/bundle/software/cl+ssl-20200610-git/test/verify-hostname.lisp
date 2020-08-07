;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl+ssl.test)

(def-suite :cl+ssl.verify-hostname :in :cl+ssl
  :description "Hostname verification tests")

(in-suite :cl+ssl.verify-hostname)

(test veriy-hostname-success
  ;; presented identifier, reference identifier, validation and parsing result
  (let ((tests '(("www.example.com" "WWW.eXamPle.CoM" (nil)) ;; case insensitive match
                 ("www.example.com." "www.example.com" (nil)) ;; ignore trailing dots (prevenet *.com. matches)
                 ("www.example.com" "www.example.com." (nil))
                 ("*.example.com" "www.example.com" (t "" ".example.com" t))
                 ("b*z.example.com" "buzz.example.com" (t "b" "z.example.com" nil))
                 ("*baz.example.com" "foobaz.example.com" (t "" "baz.example.com" nil))
                 ("baz*.example.com" "baz1.example.com" (t "baz" ".example.com" nil)))))
    (loop for (i r v) in tests do
          (is (equalp (multiple-value-list (cl+ssl::validate-and-parse-wildcard-identifier i r)) v))
          (is (cl+ssl::try-match-hostname i r)))))

(test verify-hostname-fail
  (let ((tests '(("*.com" "eXamPle.CoM")
                 (".com." "example.com.")
                 ("*.www.example.com" "www.example.com.")
                 ("foo.*.example.com" "foo.bar.example.com.")
                 ("xn--*.example.com" "xn-foobar.example.com")
                 ("*fooxn--bar.example.com" "bazfooxn--bar.example.com")
                 ("*.akamaized.net" "tv.eurosport.com")
                 ("a*c.example.com" "abcd.example.com")
                 ("*baz.example.com" "foobuzz.example.com"))))
    (loop for (i r) in tests do
          (is-false (cl+ssl::try-match-hostname i r)))))

(defun full-cert-path (name)
  (merge-pathnames (concatenate 'string
                                "test/certs/"
                                name)
                   (asdf:component-pathname (asdf:find-system :cl+ssl.test))))

(defun load-cert(name)
  (let ((full-path (full-cert-path name)))
    (unless (probe-file full-path)
      (error "Unable to find certificate ~a~%Full path: ~a" name full-path))
    (cl+ssl:decode-certificate-from-file full-path)))

(defmacro with-cert ((name var) &body body)
  `(let* ((,var (load-cert ,name)))
     (when (cffi:null-pointer-p ,var)
       (error "Unable to load certificate: ~a" ,name))
     (unwind-protect
          (progn ,@body)
       (cl+ssl::x509-free ,var))))

(test verify-google-cert
  (with-cert ("google.der" cert)
      (is-true (cl+ssl:verify-hostname cert
                                       "qwe.fr.doubleclick.net"))))

(test verify-google-cert-dns-wildcard
  (with-cert ("google_wildcard.der" cert)
      (is-true (cl+ssl:verify-hostname cert
                                       "www.google.co.uk"))))

(test verify-google-cert-without-dns
  (with-cert ("google_nodns.der" cert)
      (is-true (cl+ssl:verify-hostname cert
                                       "www.google.co.uk"))))

(test verify-google-cert-printable-string
  (with-cert ("google_printable.der" cert)
      (is-true (cl+ssl:verify-hostname cert
                                       "www.google.co.uk"))))

(test verify-google-cert-teletex-string
  (with-cert ("google_teletex.der" cert)
      (is-true (cl+ssl:verify-hostname cert
                                       "www.google.co.uk"))))

(test verify-google-cert-bmp-string
  (with-cert ("google_bmp.der" cert)
      (is-true (cl+ssl:verify-hostname cert
                                       "google.co.uk"))))

(test verify-google-cert-universal-string
  (with-cert ("google_universal.der" cert)
      (is-true (cl+ssl:verify-hostname cert
                                       "google.co.uk"))))

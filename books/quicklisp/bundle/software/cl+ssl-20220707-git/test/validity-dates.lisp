;;;; -*- Mode: LISP; Syntax: COMMON-LISP; indent-tabs-mode: nil; coding: utf-8; show-trailing-whitespace: t -*-

(in-package :cl+ssl.test)

(def-suite :cl+ssl.validity-dates :in :cl+ssl
  :description "Validity date tests")

(in-suite :cl+ssl.validity-dates)

(test validity-dates-google-cert
  (when (and (cl+ssl::openssl-is-at-least 1 1 0)
             (not  (cl+ssl::libresslp)))
    (with-cert ("google.der" cert)
      (is (= (cl+ssl:certificate-not-after-time cert)
             3641760000))
      (is (= (cl+ssl:certificate-not-before-time cert)
             3634055286)))))

(test validity-dates-after-2050
  "Make sure we handle dates after 2050, which are encoded in ASN1 as a
GeneralizedTime, whereas dates before 2050 are encoded as UTCTime."
  (when (and (cl+ssl::openssl-is-at-least 1 1 0)
             (not  (cl+ssl::libresslp)))
    (with-cert ("mixed-time-formats.der" cert)
      (is (= (cl+ssl:certificate-not-before-time cert)
             (encode-universal-time 04 25 11 20 11 2021 0)))
      (is (= (cl+ssl:certificate-not-after-time cert)
             (encode-universal-time 04 25 11 20 11 2071 0))))))

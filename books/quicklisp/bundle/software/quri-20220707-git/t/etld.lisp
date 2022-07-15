(in-package :cl-user)
(defpackage quri-test.etld
  (:use :cl
        :quri.etld
        :prove))
(in-package :quri-test.etld)

(plan nil)

(subtest "parse-domain"
  (is (parse-domain "com") nil)
  (is (parse-domain "example.com") "example.com")
  (is (parse-domain "www.example.com") "example.com")
  (is (parse-domain "uk.com") nil)
  (is (parse-domain "example.uk.com") "example.uk.com")
  (is (parse-domain "b.example.uk.com") "example.uk.com")
  (is (parse-domain "a.b.example.uk.com") "example.uk.com")
  (is (parse-domain "test.ac") "test.ac")

  ;; TLD with only 1 (wildcard) rule
  (is (parse-domain "cy") nil)
  (is (parse-domain "c.cy") nil)
  (is (parse-domain "b.c.cy") "b.c.cy")
  (is (parse-domain "a.b.c.cy") "b.c.cy")

  ;; jp domain
  (is (parse-domain "jp") nil)
  (is (parse-domain "test.jp") "test.jp")
  (is (parse-domain "www.test.jp") "test.jp")
  (is (parse-domain "ac.jp") nil)
  (is (parse-domain "test.ac.jp") "test.ac.jp")
  (is (parse-domain "kyoto.jp") nil)
  (is (parse-domain "test.kyoto.jp") "test.kyoto.jp")
  (is (parse-domain "ide.kyoto.jp") nil)
  (is (parse-domain "b.ide.kyoto.jp") "b.ide.kyoto.jp")
  (is (parse-domain "a.b.ide.kyoto.jp") "b.ide.kyoto.jp")
  (is (parse-domain "c.kobe.jp") nil)
  (is (parse-domain "b.c.kobe.jp") "b.c.kobe.jp")
  (is (parse-domain "a.b.c.kobe.jp") "b.c.kobe.jp")
  (is (parse-domain "city.kobe.jp") "city.kobe.jp")
  (is (parse-domain "www.city.kobe.jp") "city.kobe.jp")

  ;; TLD with a wildcard rule and exceptions
  (is (parse-domain "ck") nil)
  (is (parse-domain "test.ck") nil)
  (is (parse-domain "b.test.ck") "b.test.ck")
  (is (parse-domain "a.b.test.ck") "b.test.ck")
  (is (parse-domain "www.ck") "www.ck")
  (is (parse-domain "www.www.ck") "www.ck")

  ;; US K12
  (is (parse-domain "us") nil)
  (is (parse-domain "test.us") "test.us")
  (is (parse-domain "www.test.us") "test.us")
  (is (parse-domain "ak.us") nil)
  (is (parse-domain "test.ak.us") "test.ak.us")
  (is (parse-domain "www.test.ak.us") "test.ak.us")
  (is (parse-domain "k12.ak.us") nil)
  (is (parse-domain "test.k12.ak.us") "test.k12.ak.us")
  (is (parse-domain "www.test.k12.ak.us") "test.k12.ak.us")

  ;; IDN labels.
  (is (parse-domain "公司.cn") nil)

  ;; Unlisted TLD
  (is (parse-domain "example") "example")
  (is (parse-domain "example.example") "example.example")
  (is (parse-domain "b.example.example") "example.example")
  (is (parse-domain "a.b.example.example") "example.example")

  ;; Listed TLD, but non-Internet TLD
  (is (parse-domain "local") "local")
  (is (parse-domain "example.local") "example.local")
  (is (parse-domain "b.example.local") "example.local")
  (is (parse-domain "a.b.example.local") "example.local"))

(finalize)

(in-package :cl-user)
(defpackage quri-test.domain
  (:use :cl
        :quri.domain
        :prove))
(in-package :quri-test.domain)

(plan nil)

(subtest "ipv4-addr-p"
  (ok (ipv4-addr-p "127.0.0.1")
      "127.0.0.1 is valid")
  (ok (ipv4-addr-p "255.255.255.255")
      "255.255.255.255 is valid")
  (ok (not (ipv4-addr-p "256.255.255.255"))
      "256.255.255.255 is not valid")
  (ok (not (ipv4-addr-p "345.23.1.0"))
      "345.23.1.0 is not valid")
  (ok (not (ipv4-addr-p "127.0"))
      "127.0 is not valid")
  (ok (not (ipv4-addr-p "127.0.0.0.1"))
      "127.0.0.0.1 is not valid")
  (ok (not (ipv4-addr-p "2ch.net"))
      "2ch.net is not valid")
  (ok (not (ipv4-addr-p "127..0.1"))
      "127..0.1 is not valid")
  (ok (not (ipv4-addr-p "..."))
      "... is not valid"))

(subtest "ipv6-addr-p"
  (ok (ipv6-addr-p "2001:0db8:bd05:01d2:288a:1fc0:0001:10ee"))
  (ok (ipv6-addr-p "2001:db8:20:3:1000:100:20:3"))
  (ok (ipv6-addr-p "2001:db8::1234:0:0:9abc"))
  (ok (ipv6-addr-p "2001:db8::9abc"))
  (ok (ipv6-addr-p "::1"))
  (ok (ipv6-addr-p "::"))
  (ok (ipv6-addr-p "1::"))
  (ok (not (ipv6-addr-p "1:1:1:1:1:1:1:1:1:1:1:1:1:1:1:1"))))

(subtest "ip-addr="
  (is (ip-addr= "127.0.0.1" "127.0.0.1") t)
  (is (ip-addr= "127.0.0.1" "127.0.0.2") nil)
  (is (ip-addr= "127.0.0.1" "localhost") nil)
  (is (ip-addr= "::1" "0:0:0:0:0:0:0:1") t)
  (is (ip-addr= "[::1]" "0:0:0:0:0:0:0:1") t)
  (is (ip-addr= "[::1]" "0:0:0:0:0:0:0:2") nil))

(subtest "cookie-domain-p"
  (is (cookie-domain-p "com" "com") nil)
  (is (cookie-domain-p "com" "example.com") nil)
  (is (cookie-domain-p "com" "foo.example.com") nil)
  (is (cookie-domain-p "com" "bar.foo.example.com") nil)

  (is (cookie-domain-p "example.com" "com") nil)
  (is (cookie-domain-p "example.com" "example.com") t)
  (is (cookie-domain-p "example.com" "foo.example.com") nil)
  (is (cookie-domain-p "example.com" "bar.foo.example.com") nil)

  (is (cookie-domain-p "foo.example.com" "com") nil)
  (is (cookie-domain-p "foo.example.com" "example.com") t)
  (is (cookie-domain-p "foo.example.com" "foo.example.com") t)
  (is (cookie-domain-p "foo.example.com" "bar.foo.example.com") nil)

  (is (cookie-domain-p "b.sapporo.jp" "jp") nil)
  (is (cookie-domain-p "b.sapporo.jp" "sapporo.jp") nil)
  (is (cookie-domain-p "b.sapporo.jp" "b.sapporo.jp") nil)
  (is (cookie-domain-p "b.sapporo.jp" "a.b.sapporo.jp") nil)

  (is (cookie-domain-p "b.c.sapporo.jp" "jp") nil)
  (is (cookie-domain-p "b.c.sapporo.jp" "sapporo.jp") nil)
  (is (cookie-domain-p "b.c.sapporo.jp" "c.sapporo.jp") nil)
  (is (cookie-domain-p "b.c.sapporo.jp" "b.c.sapporo.jp") t)
  (is (cookie-domain-p "b.c.sapporo.jp" "a.b.c.sapporo.jp") nil)

  (is (cookie-domain-p "b.c.d.sapporo.jp" "jp") nil)
  (is (cookie-domain-p "b.c.d.sapporo.jp" "sapporo.jp") nil)
  (is (cookie-domain-p "b.c.d.sapporo.jp" "d.sapporo.jp") nil)
  (is (cookie-domain-p "b.c.d.sapporo.jp" "c.d.sapporo.jp") t)
  (is (cookie-domain-p "b.c.d.sapporo.jp" "b.c.d.sapporo.jp") t)
  (is (cookie-domain-p "b.c.d.sapporo.jp" "a.b.c.d.sapporo.jp") nil)

  (is (cookie-domain-p "city.sapporo.jp" "jp") nil)
  (is (cookie-domain-p "city.sapporo.jp" "sapporo.jp") nil)
  (is (cookie-domain-p "city.sapporo.jp" "city.sapporo.jp") t)
  (is (cookie-domain-p "city.sapporo.jp" "a.city.sapporo.jp") nil)

  (is (cookie-domain-p "b.city.sapporo.jp" "jp") nil)
  (is (cookie-domain-p "b.city.sapporo.jp" "sapporo.jp") nil)
  (is (cookie-domain-p "b.city.sapporo.jp" "city.sapporo.jp") t)
  (is (cookie-domain-p "b.city.sapporo.jp" "b.city.sapporo.jp") t)
  (is (cookie-domain-p "b.city.sapporo.jp" "a.b.city.sapporo.jp") nil))

(finalize)

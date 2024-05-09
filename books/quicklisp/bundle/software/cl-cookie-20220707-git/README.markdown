# CL-Cookie

[![Build Status](https://travis-ci.org/fukamachi/cl-cookie.svg?branch=master)](https://travis-ci.org/fukamachi/cl-cookie)

HTTP cookie manager for Common Lisp.

## Usage

```common-lisp
(let ((cookie-jar (make-cookie-jar)))
  (merge-cookies cookie-jar
                 (list (parse-set-cookie-string "SID=31d4d96e407aad42; Path=/; Domain=example.com")))
  (cookie-jar-host-cookies cookie-jar "example.com"))
```

## See also

- [RFC 6265](http://tools.ietf.org/html/rfc6265)

## Author

* Eitaro Fukamachi (e.arrows@gmail.com)

## Copyright

Copyright (c) 2015 Eitaro Fukamachi (e.arrows@gmail.com)

## License

Licensed under the BSD 2-Clause License.

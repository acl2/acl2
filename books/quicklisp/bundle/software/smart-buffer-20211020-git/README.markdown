# smart-buffer

[![Build Status](https://travis-ci.org/fukamachi/smart-buffer.svg?branch=master)](https://travis-ci.org/fukamachi/smart-buffer)
[![Coverage Status](https://coveralls.io/repos/fukamachi/smart-buffer/badge.svg?branch=master)](https://coveralls.io/r/fukamachi/smart-buffer)

Smart-buffer provides an output buffer which changes the destination depending on content size.

* In-memory buffer for small data
* Temporary files on disk for big data

In-memory buffer is fast to read/write, however, it consumes much memory if the data can be large. On the other hand, files on disk are slower. Smart-buffer would be useful when the buffer must satisfy these two contradicting demands.

## Usage

`with-smart-buffer` returns an in-memory stream or a file stream.

```common-lisp
(with-smart-buffer (buffer)
  (write-to-buffer buffer (flex:string-to-octets "foobar")))
;=> #<FLEXI-STREAMS::VECTOR-INPUT-STREAM {100456A9A3}>

(with-smart-buffer (buffer :memory-limit 3)
  (write-to-buffer buffer (flex:string-to-octets "foobar")))
;=> #<SB-SYS:FD-STREAM for "file /private/var/folders/x3/8n07clk15tq3m4y6_yrmjy6c0000gn/T/tmpAR3FSGEY.tmp" {1005D06503}>
```

## Author

* Eitaro Fukamachi (e.arrows@gmail.com)

## Copyright

Copyright (c) 2015 Eitaro Fukamachi (e.arrows@gmail.com)

## License

Licensed under the BSD 3-Clause License.

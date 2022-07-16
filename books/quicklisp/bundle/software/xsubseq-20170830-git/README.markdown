# XSubseq

XSubseq provides functions to be able to handle "subseq"s more effieiently. As Common Lisp's `subseq` copies the data every time, "subseq" and "concatenate" code is very inefficient like the following code.

```common-lisp
(let ((result (make-array 0 :element-type '(unsigned-byte 8))))
  (lambda (data start end)
    (setf result (concatenate '(simple-array (unsigned-byte 8) (*))
                              result
                              (subseq data start end)))
    result))
```

XSubseq delays the copying until it is actually needed.

## Usage

```common-lisp
(defvar *data1* #(1 2 3))
(defvar *data2* #(4 5 6))

(xsubseq *data1* 0 1)
;=> #S(XSUBSEQ:XSUBSEQ :DATA #(1 2 3) :START 0 :END 1 :LEN 1)

(xnconc (xsubseq *data1* 0 1)
        (xsubseq *data2* 2))
;=> #S(XSUBSEQ:CONCATENATED-XSUBSEQS
;     :LEN 2
;     :LAST (#S(XSUBSEQ:XSUBSEQ :DATA #(4 5 6) :START 2 :END 3 :LEN 1))
;     :CHILDREN (#S(XSUBSEQ:XSUBSEQ :DATA #(1 2 3) :START 0 :END 1 :LEN 1)
;                #S(XSUBSEQ:XSUBSEQ :DATA #(4 5 6) :START 2 :END 3 :LEN 1)))

(coerce-to-sequence
 (xnconc (xsubseq *data1* 0 1)
         (xsubseq *data2* 2)))
;=> #(1 6)

(with-xsubseqs (result)
  (xnconcf result (xsubseq *data1* 0 1))
  (xnconcf result (xsubseq *data2* 2)))
;=> #(1 6)
```

## Installation

```common-lisp
(ql:quickload :xsubseq)
```

## Author

* Eitaro Fukamachi (e.arrows@gmail.com)

## Copyright

Copyright (c) 2014 Eitaro Fukamachi (e.arrows@gmail.com)

## License

Licensed under the BSD 2-Clause License.

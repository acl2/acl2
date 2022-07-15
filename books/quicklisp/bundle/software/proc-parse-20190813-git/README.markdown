# Proc-Parse

[![Build Status](https://travis-ci.org/fukamachi/proc-parse.svg?branch=master)](https://travis-ci.org/fukamachi/proc-parse)
[![Coverage Status](https://coveralls.io/repos/fukamachi/proc-parse/badge.svg?branch=master)](https://coveralls.io/r/fukamachi/proc-parse)

<blockquote>
Question: Are these parser macros for speed or just to make your application look cool?<br>
Answer: Both.
</blockquote>

This is a string/octets parser library for Common Lisp with speed and readability in mind. Unlike other libraries, the code is not a pattern-matching-like, but a char-by-char procedural parser.

Although the design is good for speed, the code could look ugly with `tagbody` and `go`. Proc-Parse wraps the code with sexy macros.

I believe we don't have to give up speed for the readability while we use Common Lisp.

## Usage

```common-lisp
(defun parse-url-scheme (data &key (start 0) end)
  "Return a URL scheme of DATA as a string."
  (declare (optimize (speed 3) (safety 0) (debug 0)))
  (block nil
    (with-vector-parsing (data :start start :end end)
      (match-i-case
       ("http:" (return "http"))
       ("https:" (return "https"))
       (otherwise (unless (standard-alpha-char-p (current))
                    (return nil))
                  (bind (scheme (skip* (not #\:)))
                    (return scheme)))))))
```

## API

### with-vector-parsing

- can parse both string and octets.

```Lisp
(with-vector-parsing ("It's Tuesday!" :start 5 :end 12)
  (bind (str (skip-until
              (lambda (c)
                (declare (ignore c))
                (eofp))))
    (print str))) ; "Tuesday"

(with-vector-parsing ((babel:string-to-octets "It's Tuesday!") :start 5 :end 12)
  (bind (str (skip-until
              (lambda (c)
                (declare (ignore c))
                (eofp))))
    (print str))) ; "Tuesday"
```

### with-string-parsing

- can parse string.

```Lisp
(with-string-parsing ("It's Tuesday!" :start 5 :end 12)
  (bind (str (skip-until
              (lambda (c)
                (declare (ignore c))
                (eofp))))
    (print str))) ; "Tuesday"
```

### with-octets-parsing

- can parse octets.

```Lisp
(with-octets-parsing ((babel:string-to-octets "It's Tuesday!") :start 5 :end 12)
  (bind (str (skip-until
              (lambda (c)
                (declare (ignore c))
                (eofp))))
    (print str))) ; "Tuesday"
```

### eofp

- can return EOF or not.

```Lisp
(with-vector-parsing ("hello")
  (print (eofp)) ; NIL
  (match "hello")
  (print (eofp))) ; T
```

### current

- can return the character of the current position.

```Lisp
(with-vector-parsing ("hello")
  (print (current)) ; #\h
  (skip #\h)
  (print (current))) ; #\e
```

### peek

- can peek next character from the current position

```Lisp
(with-vector-parsing ("hello")
  (print (current)) ; #\h
  (print (peek)) ; #\e
  (print (current))) ; #\h
```
  
- and you can specify the eof-value

```Lisp
(with-vector-parsing ("hello")
  (match "hell")
  (print (pos)) ; #\4
  (print (peek :eof-value 'yes))) ; YES
```

### pos

- can return the current position.

```Lisp
(with-vector-parsing ("hello")
  (print (pos)) ; 0
  (skip #\h)
  (print (pos))) ; 1
```

### advance

- can put the current postion forward.
- can cease parsing with EOF.

```Lisp
(with-vector-parsing ("hello")
  (print (current)) ; #\h
  (advance)
  (print (current)) ; #\e
  (match "ello")
  (print (current)) ; #\o
  (advance)
  (print "Hi")) ; "Hi" won't displayed.
```

### advance*

- can put the current postion forward.
- just returns NIL with EOF.

```Lisp
(with-vector-parsing ("hello")
  (print (current)) ; #\h
  (advance*)
  (print (current)) ; #\e
  (match "ello")
  (print (current)) ; #\o
  (advance*)
  (print (current)) ; #\o
  (print "Hi")) ; "Hi"
```

### skip

- can skip the specified character.
- can raise MATCH-FAILED error with unmatched characters.

```Lisp
(with-vector-parsing ("hello")
  (print (current)) ; #\h
  (skip #\h)
  (print (current)) ; #\e
  (skip (not #\h))
  (print (current)) ; #\l
  (skip #\f))
;; => Condition MATCH-FAILED was signalled.
```

### skip*

- can skip some straignt specified characters.
- just returns NIL with unmatched characters.

```Lisp
(with-vector-parsing ("hello")
  (skip* #\h)
  (print (current)) ; #\e
  (skip* (not #\l))
  (print (current)) ; #\l
  (skip* #\l)
  (print (current)) ; #\o
  (skip* #\f)) ; MATCH-FAILED won't be raised.
```

### skip+

- can skip some straignt specified characters.
- can raise MATCH-FAILED error with unmatched characters.

```Lisp
(with-vector-parsing ("hello")
  (skip+ #\h)
  (print (current)) ; #\e
  (skip* (not #\l))
  (print (current)) ; #\l
  (skip+ #\l)
  (print (current)) ; #\o
  (skip+ #\f))
;; => Condition MATCH-FAILED was signalled.
```

### skip?

- can skip the specified character.
- just returns NIL with unmatched characters.

```Lisp
(with-vector-parsing ("hello")
  (print (current)) ; #\h
  (skip? #\h)
  (print (current)) ; #\e
  (skip? (not #\h))
  (print (current)) ; #\l
  (skip? #\f)) ; MATCH-FAILED won't be raised.
```

### skip-until

- can skip until form returned T or parsing reached EOF.

```Lisp
(with-vector-parsing ("hello")
  (skip-until (lambda (char) (char= char #\o)))
  (print (current)) ; #\o
  (print (eofp)) ; NIL
  (skip-until (lambda (char) (char= char #\f)))
  (print (eofp))) ; T
```

### skip-while

- can skip while form returns T and parsing doesn't reach EOF.

```Lisp
(with-vector-parsing ("hello")
  (skip-while (lambda (char) (char/= char #\o)))
  (print (current)) ; #\o
  (print (eofp)) ; NIL
  (skip-while (lambda (char) (char/= char #\f)))
  (print (eofp))) ; T
```

### bind

- can bind subseqed string.

```Lisp
(with-vector-parsing ("hello")
  (bind (str1 (skip-until (lambda (c) (char= c #\l))))
    (print str1)) ; "he"
  (bind (str2 (skip* (not #\f)))
    (print str2))) ; "llo"
```

### match

- can skip matched one of the specified strings.
- can raise MATCH-FAILED error with unmatched characters.

```Lisp
(with-vector-parsing ("hello")
  (match "he")
  (print (current)) ; #\l
  (match "l" "ll")
  (print (current)) ; #\o
  (match "f"))
;; => Condition MATCH-FAILED was signalled.
```

### match-i

- can skip case-insensitively matched one of the specified strings.
- can raise MATCH-FAILED error with case-insensitively unmatched characters.

```Lisp
(with-vector-parsing ("hello")
  (match-i "He")
  (print (current)) ; #\l
  (match-i "L" "LL")
  (print (current)) ; #\o
  (match-i "F"))
;; => Condition MATCH-FAILED was signalled.
```

### match?

- can skip matched one of the specified strings.
- just returns NIL with unmatched characters.

```Lisp
(with-vector-parsing ("hello")
  (match? "he")
  (print (current)) ; #\l
  (match? "l" "ll")
  (print (current)) ; #\o
  (match? "f")) ; MATCH-FAILED won't be raised.
```

### match-case

- can dispatch to the matched case.
- aborts parsing when reaching EOF.

```Lisp
(with-vector-parsing ("hello")
  (match-case
   ("he" (print 0))
   ("ll" (print 1))
   (otherwise (print 2))) ; 0
  (print (current)) ; #\l
  (match-case
   ("he" (print 0))
   ("ll" (print 1))
   (otherwise (print 2))) ; 1
  (print (current)) ; #\o
  (match-case
   ("he" (print 0))
   ("ll" (print 1))
   (otherwise (print 2))) ; 2
  (print (current)) ; #\o
  (match-case
   ("he" (print 0))
   ("ll" (print 1))))
;; => Condition MATCH-FAILED was signalled.

(with-vector-parsing ("hello")
  (print
   (match-case
    ("hello" 0))) ;; Nothing will be printed.
  (print "It shold not be printed.")) ;; Nothing will be printed.
;; => NIL
```

### match-i-case

- can dispatch to the case-insensitively matched case.
- aborts parsing when reaching EOF.

```Lisp
(with-vector-parsing ("hello")
  (match-i-case
   ("He" (print 0))
   ("LL" (print 1))
   (otherwise (print 2))) ; 0
  (print (current)) ; #\l
  (match-i-case
   ("He" (print 0))
   ("LL" (print 1))
   (otherwise (print 2))) ; 1
  (print (current)) ; #\o
  (match-i-case
   ("He" (print 0))
   ("LL" (print 1))
   (otherwise (print 2))) ; 2
  (print (current)) ; #\o
  (match-i-case
   ("He" (print 0))
   ("LL" (print 1))))
;; => Condition MATCH-FAILED was signalled.

(with-vector-parsing ("hello")
  (print
   (match-i-case
    ("Hello" 0))) ;; Nothing will be printed.
  (print "It shold not be printed.")) ;; Nothing will be printed.
;; => NIL
```

### match-failed

- is the condition representing failure of matching.

```Lisp
(with-vector-parsing ("hello")
  (print (current)) ; #\h
  (skip #\f))
;; => Condition MATCH-FAILED was signalled.
```

## Author

* Eitaro Fukamachi
* Rudolph Miller

## Copyright

Copyright (c) 2015 Eitaro Fukamachi & Rudolph Miller

## License

Licensed under the BSD 2-Clause License.

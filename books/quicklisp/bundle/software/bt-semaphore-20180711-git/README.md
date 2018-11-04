# bt-semaphore

A simple semaphore class for bordeaux-threads inspired by SBCL's semaphore.
 
**Obsolete!** bordeaux-threads has its own built-in semaphores since version
0.8.6, so you should definitely use that instead of bt-semaphore.

## Installation

`bt-semaphore` is available via [Quicklisp](http://www.quicklisp.org/beta/). You
can also clone the Git repo if you're curious:

```
cd ~/quicklisp/local-projects
git clone https://github.com/rmoritz/bt-semaphore
```

## Usage

There are seven functions of interest at the moment:

 - `make-semaphore` creates a semaphore instance
 - `wait-on-semaphore` blocks until the semaphore can be decremented (ie. its
   count > 0) or the timeout has expired
 - `signal-semaphore` increments the semaphore & wakes n waiting threads
 - `try-semaphore` decrements the semaphore without blocking
 - `semaphore-count` returns the current count of the semaphore
 - `semaphore-waiters` returns the number of threads waiting on semaphore
 - `semaphore-name` is an accessor for the semaphore's name slot

To illustrate, here's a tiny example:

```common-lisp
(ql:quickload :bt-semaphore)

(defun semaphore-demo ()
  (defparameter sem (bt-sem:make-semaphore))
  (defparameter lock (bt:make-lock))
  (defparameter num 0)
  
  (format t "spawn 20 threads with 4s timeout~%")
  (loop
    repeat 20
    do (bt:make-thread
         (lambda ()
           (if (bt-sem:wait-on-semaphore sem :timeout 4)
             (bt:with-lock-held (lock)
               (incf num))))))
  (format t "num is ~d~%" num)
  (sleep 0.33)
  (format t "there are ~d waiting threads~%~%" (bt-sem:semaphore-waiters sem))

  (format t "signal 5 threads~%")
  (bt-sem:signal-semaphore sem 5)
  (sleep 0.33)
  (bt:with-lock-held (lock)
    (format t "num is ~d~%" num))
  (format t "there are ~d waiting threads~%~%" (bt-sem:semaphore-waiters sem))

  (format t "signal 10 threads~%")
  (bt-sem:signal-semaphore sem 10)
  (sleep 0.33)
  (bt:with-lock-held (lock)
    (format t "num is ~d~%" num))
  (format t "there are ~d waiting threads~%~%" (bt-sem:semaphore-waiters sem))

  (format t "4s sleep~%")
  (sleep 4)
  (bt:with-lock-held (lock)
    (format t "num is ~d~%" num))
  (format t "there are ~d waiting threads~%~%" (bt-sem:semaphore-waiters sem)))
```

Calling `SEMAPHORE-DEMO` at the REPL should produce the following output:

```
spawn 20 threads with 4s timeout
num is 0
there are 20 waiting threads

signal 5 threads
num is 5
there are 15 waiting threads

signal 10 threads
num is 15
there are 5 waiting threads

4s sleep
num is 15
there are 0 waiting threads
```

## Status

Working, but obsolete: bordeaux-threads has semaphore support since version 0.8.6.
You should definitely be using that instead of bt-semaphore.

You can run the test suites to verify that everything is working as it
should by invoking `(ql:quickload :bt-semaphore-test)` or `(asdf:test-system
:bt-semaphore)`.

## Bugs

Found one? Report it [here](https://github.com/rmoritz/bt-semaphore/issues), thanks.

## Author

* Ralph Moeritz (ralphmoritz@outlook.com)

## License

Copyright (c) Ralph Moeritz 2013.

Permission is hereby granted, free of charge, to any person obtaining a copy of
this software and associated documentation files (the "Software"), to deal in
the Software without restriction, including without limitation the rights to
use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies
of the Software, and to permit persons to whom the Software is furnished to do
so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

**THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
  IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
  FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
  AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
  LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
  OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
  SOFTWARE.**

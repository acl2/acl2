; Computational Object Inference
; Copyright (C) 2005-2014 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.

(in-package "ACL2")

;; This book, fast.lisp, contains fast versions of some super-ihs functions
;; that are fast to execute.  I'm letting this be demand driven, adding to it
;; as needed.

(include-book "super-ihs")

(defmacro the-usb (size x)
  `(the (unsigned-byte ,size) ,x))

(defmacro the-sb (size x)
  `(the (signed-byte ,size) ,x))

(defund loghead-30-exec (i)
  (declare (type (unsigned-byte 31) i))
  (the-usb 31 (logand 1073741823 i)))

(defthm loghead-30-exec-rewrite
  (equal (loghead-30-exec i)
         (loghead 30 i))
  :hints (("Goal" :in-theory (enable loghead-30-exec))))

(defund logbitp-30-exec (j)
  (declare (type (unsigned-byte 31) j))
  (not (equal 0 (logand 1073741824 j))))

(defthm logbitp-30-exec-rewrite
  (equal (logbitp-30-exec i)
         (logbitp 30 i))
  :hints (("Goal" :cases ((integerp i))
           :in-theory (enable logbitp-30-exec))))

;bzo I think this version doesn't do the chop that logapp does.  Make a
;version that does do the chop (and that won't need the (unsigned-byte-p 31 x)
;hyp to be equal to (logext 31 x)?
;
;bzo inline the function calls here?
(defund logext-31-exec (x)
  (declare (type (unsigned-byte 31) x))
  (the-sb 31 (if (not (equal 0 (logand 1073741824 x))) ;(logbitp-30-exec x)
                 (the-sb 31 (+ -1073741824 (the-usb 30 (logand 1073741823 x) ;(loghead-30-exec x)
                                                    ))) ;(logapp 30 x -1);
               x)))

(defthm logext-31-exec-rw
  (implies (unsigned-byte-p 31 x)
           (equal (logext-31-exec x)
                  (logext 31 x)))
  :hints (("Goal" :in-theory (enable LOGEXT logext-31-exec))))
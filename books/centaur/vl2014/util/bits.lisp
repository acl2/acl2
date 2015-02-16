; VL 2014 -- VL Verilog Toolkit, 2014 Edition
; Copyright (C) 2008-2015 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL2014")
(include-book "defs")
(include-book "centaur/fty/deftypes" :dir :system)
(local (std::add-default-post-define-hook :fix))

(defenum vl-bit-p
  (:vl-0val :vl-1val :vl-xval :vl-zval)
  :parents (vl-weirdint-p)
  :short "Representation of a single Verilog bit (0, 1, X, or Z)."

  :long "<p>Verilog has four register-transfer level values, @('0'), @('1'),
@('X'), and @('Z').  We represent these values using the keyword symbols
accepted by @('vl-bit-p'):</p>

<ul>
 <li>@(':vl-0val') means 0,</li>
 <li>@(':vl-1val') means 1,</li>
 <li>@(':vl-xval') means X, and</li>
 <li>@(':vl-zval') means Z.</li>
</ul>")

(fty::deflist vl-bitlist
  :elt-type vl-bit-p
  :elementp-of-nil nil
  :true-listp nil
  :parents (vl-weirdint-p))

(define vl-bit->char ((x vl-bit-p))
  :parents (vl-bit-p)
  :short "Get the character for a @(see vl-bit-p)."
  :returns (char characterp :rule-classes :type-prescription)
  :long "<p>@(call vl-bit->char) produces the ASCII character for a @(see vl-bit-p).
That is, it returns one of the characters: 0, 1, X, or Z.</p>"
  (let ((x (mbe :logic (vl-bit-fix x) :exec x)))
    (case x
      (:vl-0val #\0)
      (:vl-1val #\1)
      (:vl-xval #\X)
      (:vl-zval #\Z)
      (otherwise
       ;; hack for unconditional type prescription
       (progn$ (impossible)
               #\X)))))

(defprojection vl-bitlist->charlist ((x vl-bitlist-p))
  :returns (chars character-listp)
  :parents (vl-weirdint-p)
  :short "Get a character list for a @(see vl-bitlist-p)."
  (vl-bit->char x))

(define vl-bitlist->string ((x vl-bitlist-p))
  :parents (vl-weirdint-p)
  :short "Get the string corresponding to a @(see vl-bitlist-p)."
  :returns (str stringp :rule-classes :type-prescription)
  (implode (vl-bitlist->charlist x)))

(defenum vl-timeunit-p
  (:vl-s
   :vl-ms
   :vl-us
   :vl-ns
   :vl-ps
   :vl-fs)
  :parents (syntax)
  :short "Representation for SystemVerilog time units (s, ms, ps, ...)")

(define vl-timeunit->string ((x vl-timeunit-p))
  :parents (vl-timeunit-p)
  :short "Get the string corresponding to a @(see vl-timeunit-p)."
  :returns (str stringp :rule-classes :type-prescription)
  (let ((x (mbe :logic (vl-timeunit-fix x)
                :exec x)))
    (case x
      (:vl-s "s")
      (:vl-ms "ms")
      (:vl-us "us")
      (:vl-ns "ns")
      (:vl-ps "ps")
      (:vl-fs "fs")
      (otherwise (progn$ (impossible)
                         "s")))))


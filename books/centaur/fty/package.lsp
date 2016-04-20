; FTY type support library
; Copyright (C) 2014 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "std/portcullis" :dir :system)
(include-book "centaur/bitops/portcullis" :dir :system)

(defpkg "FTY"
  (append *std-pkg-symbols*
          *bitops-exports*
          '(std::def-primitive-aggregate
             std::extract-keywords
             std::getarg
             str::cat
             str::revappend-chars
             str::rchars-to-string
             enable*
             disable*
             e/d*
             std::prod-consp
             std::prod-cons
             std::prod-car
             std::prod-cdr
             std::prod-hons
             std::prod-cons-with-hint
             )
          #!ACL2
          '(a b c d e f g h i j k l m n o p q r s t u v w x y z

              ;; Minor things for better documentation
              fty
              fty-discipline
              natp
              nfix
              nat-equiv
              equivalence
              congruence
              hints
              )))


; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2019 Centaur Technology
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
; Original author: Mertcan Temel <mert@utexas.edu>

(in-package "SVL")

(include-book "centaur/sv/svex/4vec" :dir :system)
(include-book "std/util/defines" :dir :system)
(include-book "misc/untranslate-patterns" :dir :system)

(local
 (in-theory (enable sv::4vec-p)))

(define sbits
  ((start natp)
   (size natp)
   (new-val sv::4vec-p)
   (old-val sv::4vec-p))
  :returns (updated-val sv::4vec-p)

  (sv::4vec-part-install start
                         size
                         old-val
                         new-val))
  #|(b* ((head (sv::4vec-part-select 0 start old-val))
       (tail (sv::4vec-rsh start old-val))
       (tail-tail (sv::4vec-rsh size tail))
       (new-tail (sv::4vec-concat size new-val tail-tail)))
    (sv::4vec-concat start head new-tail))||#

(define bits
  ((val sv::4vec-p)
   (start natp)
   (size natp))
  :returns (result sv::4vec-p)
  :prepwork
  ((local
    (in-theory (enable sv::4vec-p))))
  (sv::4vec-part-select start
                        size val))


#|(defund 4vec-lsh$ (size val)
  (declare (ignorable size val))
  (sv::4vec-lsh (nfix size) val))||#

(define 4vec-concat$ ((size 4vec-p)
                      (x 4vec-p)
                      (y 4vec-p))
  :returns (res 4vec-p)
  (4vec-concat size x y))

(encapsulate
  nil

  ;; print (4vec-concat$ 1 val1 (4vec-concat$ 1 val2 ...)) as (4vec-list val1 val2 ...)

  (defmacro 4vec-cons (val1 val2)
    `(4vec-concat$ '1 ,val1 ,val2))

  (defmacro 4vec-list (&rest rp::rst)
    (cond ((null rp::rst) 0)
          ((null (cdr rp::rst))
           (list '4vec-cons (car rp::rst) 0))
          (t (xxxjoin '4vec-cons rp::rst))))

  (acl2::add-untranslate-pattern (svl::4vec-concat$ '1 ?x ?y)
                                 (svl::4vec-cons ?x ?y))

  (add-macro-fn 4vec-list 4vec-cons t)

  ;; print (bits val start 1) as (bit$ val start)
  #|(defmacro bit$ (val index)
    `(bits ,val ,index '1))

  (acl2::add-untranslate-pattern (svl::bits ?y ?x '1)
                                 (svl::bit$ ?y ?x))||#)

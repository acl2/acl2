; Use Rp-rewriter, then FGL as clause-processors (and some other things in between)
;
; Copyright (C) 2021 Centaur Technology
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
; Original author: Mertcan Temel <mert@centtech.com>


(in-package "RP")

(include-book "centaur/misc/memory-mgmt-logic" :dir :system)

(local
 (value-triple (acl2::set-max-mem (* 32 (expt 2 30)))))
(local
 (value-triple (hons-resize :addr-ht #u30_000_000)))

(include-book "make-sc-fgl-ready")
(value-triple (hons-clear t))
(include-book "projects/rp-rewriter/rp-then-fgl" :dir :system)
(value-triple (hons-clear t))
(include-book "svl-top")
(value-triple (hons-clear t))
(include-book "centaur/fgl/def-fgl-rewrite" :dir :system)


;;(attach-meta-fncs fgl-mult-rules)

(enable-meta-rules make-sc-fgl-ready-meta-main)
;;(enable-rules '((:META medw-compress-meta . equal)))
(disable-meta-rules medw-compress-meta)

(fgl::def-fgl-rewrite
 4vec-concat$-is-logapp
 (implies (and (natp a)
               (integerp x)
               (integerp y))
          (equal (svl::4vec-concat$ a x y)
                 (logapp a x y)))
 :hints (("Goal"
          :in-theory (e/d (SVL::LOGAPP-TO-4VEC-CONCAT
                           svl::4vec-concat$)
                          (logapp)))))


(defun and-list-for-fgl (lst)
  (if (atom lst)
      t
    (and (equal (car lst) 1)
         (and-list-for-fgl (cdr lst)))))


(fgl::def-fgl-rewrite
 and-list-to-and
 (equal (and-list hash lst) 
        (if (and-list-for-fgl lst)
            1
          0))          
 :hints (("Goal"
          :in-theory (e/d (and-list
                           BIT-FIX
                           and$
                           bitp)
                          (logapp)))))


(progn
  (fgl::def-fgl-rewrite mod-2-is-logcar
                        (implies (integerp x)
                                 (equal (mod x 2) (acl2::logcar x))))
  (fgl::def-fgl-rewrite floor-2-is-logcdr
                        (implies (integerp x)
                                 (equal (floor x 2) (acl2::logcdr x))))
  (fgl::def-fgl-rewrite
   bit-of-is-logbit
   (implies (integerp x)
            (equal (rp::bit-of x index) (logbit index x)))
   :hints (("Goal"                             ;
            :in-theory (e/d (rp::bit-of) ()))) ;
   ))

   

; SVL - Listener-based Hierachical Symbolic Vector Hardware Analysis Framework
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


(in-package "SVL")

(include-book "svexl-fasteval-correct")


(include-book "centaur/sv/svtv/process" :dir :system)

(set-ignore-ok t)

(define svtv-run-with-svexl
    ((sv::svtv acl2::svtv-p)
     (sv::inalist)
     &key
     ((sv::skip) 'nil)
     ((sv::include) 'nil)
     ((sv::boolvars) 't)
     ((simplify) 'nil)
     ((sv::quiet ) 'nil)
     ((sv::readable ) 't)
     ((sv::allvars) 'nil))
  (declare (ignorable sv::allvars sv::readable
                      sv::quiet sv::boolvars simplify))
  :prepwork ((local (in-theory (enable sv::svarlist-fix))))
  :returns
  (sv::res sv::svex-env-p)
  (b* (((sv::svtv sv::svtv) sv::svtv)
       (sv::inalist
        (ec-call (sv::svex-env-fix$inline sv::inalist)))
       ((acl2::with-fast sv::inalist))
       (sv::svtv.inmasks (make-fast-alist sv::svtv.inmasks))
       (sv::boolmasks
        (hons-copy (and sv::boolvars
                        (sv::svar-boolmasks-limit-to-bound-vars
                         (acl2::alist-keys sv::inalist)
                         sv::svtv.inmasks))))
       (sv::outs
        (b*
            (((unless (or sv::skip sv::include))
              sv::svtv.outexprs)
             (sv::outkeys
              (or sv::include
                  (set::difference
                   (set::mergesort
                    (sv::svex-alist-keys sv::svtv.outexprs))
                   (set::mergesort sv::skip)))))
          (acl2::fal-extract sv::outkeys sv::svtv.outexprs)))
       (sv::res
        (svl::svexl-alist-fasteval (svex-alist-to-svexl-alist sv::outs) sv::inalist)
        #|(mbe
        :logic ; ;
        (sv::svex-alist-eval-for-symbolic ; ;
        sv::outs sv::inalist ; ;
        (cons (cons ':vars ; ;
        (acl2::alist-keys sv::svtv.inmasks)) ; ;
        (cons (cons ':boolmasks sv::boolmasks) ; ;
        (cons (cons ':simplify simplify) ; ;
        (cons (cons ':allvars sv::allvars) ; ;
        'nil))))) ; ;
        :exec (svl::svexl-alist-fasteval (svex-alist-to-svexl-alist sv::outs) sv::inalist))||#))
    ;;(clear-memoize-table 'svex-eval)
    (and (not sv::quiet)
         (progn$ (cw "~%svtv inputs:~%")
                 (if sv::readable
                     (sv::svtv-print-alist-readable sv::inalist)
                     (sv::svtv-print-alist sv::inalist))
                 (cw "~%svtv outputs:~%")
                 (if sv::readable
                     (sv::svtv-print-alist-readable sv::res)
                     (sv::svtv-print-alist sv::res))
                 (cw "~%")))
    sv::res))


(memoize 'svex-alist-to-svexl-alist)

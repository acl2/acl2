; SV - Symbolic Vector Hardware Analysis Framework
; Copyright (C) 2014-2015 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

(in-package "SV")

(include-book "../svex/lists")
(include-book "std/strings/hexify" :dir :system)


(define svtv-print-alist ((al svex-env-p))
  (if (atom al)
      nil
    (prog2$
     (and (mbt (consp (car al)))
          (if (2vec-p (cdar al))
              (cw "  ~s0:~t1~s2~%" (caar al) 25 (str::hexify (2vec->val (cdar al))))
            (cw "  ~s0:~t1(4v) ~s2~%~t3~s4~%" (caar al) 20 (str::hexify (4vec->upper (cdar al)))
                25 (str::hexify (4vec->lower (cdar al))))))
     (svtv-print-alist (cdr al)))))

(define svtv-print-alist-readable-aux ((al svex-env-p) firstp)
  (if (atom al)
      nil
    (progn$
     (and (mbt (consp (car al)))
          (let ((front (if firstp " ((" "  ("))
                (back (if (consp (cdr al)) ")~%" "))~%")))
            (cond
             ((2vec-p (cdar al))
              (progn$
               (cw! front)
               (acl2::fmt-to-comment-window!
                "~x0 ~t1. ~s2"
                (pairlis2 '(#\0 #\1 #\2 #\3 #\4
                            #\5 #\6 #\7 #\8 #\9)
                          (list (caar al) 23
                                (str::hexify (2vec->val (cdar al)))))
                3 nil nil)
               (cw! back)))
             (t
              (let* ((upper (str::hexify (4vec->upper (cdar al))))
                     (lower (str::hexify (4vec->lower (cdar al))))
                     (mask  (str::hexify (logxor (4vec->upper (cdar al))
                                                 (4vec->lower (cdar al)))))
                     ;; padding for right-aligning the three values
                     (ul (length upper)) (ll (length lower)) (ml (length mask))
                     (maxl (max ml (max ul ll)))
                     (pad-u (- maxl ul))
                     (pad-l (- maxl ll))
                     (pad-m (- maxl ml)))
                (progn$
                 (cw! front)
                 (acl2::fmt-to-comment-window!
                  "~x0 ~t1  ~_2~s3~%"
                  (pairlis2 '(#\0 #\1 #\2 #\3 #\4
                              #\5 #\6 #\7 #\8 #\9)
                            (list (caar al) 23 pad-u upper))
                  3 nil nil)
                 (cw! "~t0. ~_1~s2" 23 pad-l lower)
                 (cw! back)
                 (cw! ";;;    non-Boolean mask: ~_0~s1~%" pad-m mask)))))))
     (svtv-print-alist-readable-aux (cdr al) nil))))

(define svtv-print-alist-readable ((al svex-env-p))
  (svtv-print-alist-readable-aux al t))

(define svtv-print-alists-readable ((als svex-envlist-p))
  (if (atom als)
      nil
    (prog2$ (svtv-print-alist-readable (car als))
            (svtv-print-alists-readable (cdr als)))))

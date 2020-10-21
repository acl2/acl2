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
(include-book "../mods/lhs")
(include-book "../svex/lists")
(include-book "centaur/fty/baselists" :dir :system)
(include-book "std/strings/hexify" :dir :system)

(defxdoc structure.lisp :parents (svex-stvs))
(local (xdoc::set-default-parents structure.lisp))

(local (std::add-default-post-define-hook :fix))

(define svtv-dontcare-p (x)
  (and (symbolp x)
       (consp (member-symbol-name (symbol-name x) '(_ - &)))))

(define svtv-baseentry-p (x)
  (or (4vec-p x)
      (eq x :ones)
      (and (symbolp x)
           (not (booleanp x))
           (not (keywordp x))
           (not (svtv-dontcare-p x))))
  ///

  (define svtv-baseentry-fix ((x svtv-baseentry-p))
    :returns (xx svtv-baseentry-p)
    :hooks nil
    (mbe :logic (if (svtv-baseentry-p x) x (4vec-x))
         :exec x)
    ///
    (defthm svtv-baseentry-fix-of-svtv-baseentry-p
      (implies (svtv-baseentry-p x)
               (equal (svtv-baseentry-fix x) x)))

    (deffixtype svtv-baseentry :pred svtv-baseentry-p :fix svtv-baseentry-fix
      :equiv svtv-baseentry-equiv :define t :forward t)))

(defprod svtv-condoverride
  ((value svtv-baseentry-p)
   (test  svtv-baseentry-p))
  :layout :list
  ///
  (defthm svtv-condoverride-implies-not-baseentry
    (implies (svtv-condoverride-p x)
             (not (svtv-baseentry-p x)))
    :hints(("Goal" :in-theory (enable svtv-baseentry-p 4vec-p svtv-condoverride-p)))))


(define svtv-entry-p (x)
  (or (svtv-dontcare-p x)
      (svtv-baseentry-p x)
      (svtv-condoverride-p x))
  ///

  (define svtv-entry-fix ((x svtv-entry-p))
    :returns (xx svtv-entry-p)
    :hooks nil
    (mbe :logic (if (svtv-entry-p x) x 'acl2::_)
         :exec x)
    ///
    (defthm svtv-entry-fix-of-svtv-entry-p
      (implies (svtv-entry-p x)
               (equal (svtv-entry-fix x) x)))

    (deffixtype svtv-entry :pred svtv-entry-p :fix svtv-entry-fix
      :equiv svtv-entry-equiv :define t :forward t)))



(deflist svtv-entrylist :elt-type svtv-entry :true-listp t)

(defprod svtv-line
  ((lhs lhs)
   (entries svtv-entrylist))
  :layout :tree)

(deflist svtv-lines :elt-type svtv-line :true-listp t)

(defprod svtv-overrideline
  ((lhs lhs)
   (test svar-p)
   (val svar-p)
   (entries svtv-entrylist))
  :layout :tree)

(deflist svtv-overridelines :elt-type svtv-overrideline :true-listp t)


(define svtv-outentry-p (x)
  (and (symbolp x)
       (not (booleanp x))
       (not (keywordp x)))
  ///

  ;; (defthm svtv-entry-p-when-outentry
  ;;   (implies (svtv-outentry-p x)
  ;;            (svtv-entry-p x))
  ;;   :hints(("Goal" :in-theory (enable svtv-entry-p))))

  (define svtv-outentry-fix ((x svtv-outentry-p))
    :returns (xx svtv-outentry-p)
    :hooks nil
    (mbe :logic (if (svtv-outentry-p x) x 'acl2::_)
         :exec x)
    ///
    (defthm svtv-outentry-fix-of-svtv-outentry-p
      (implies (svtv-outentry-p x)
               (equal (svtv-outentry-fix x) x)))

    (deffixtype svtv-outentry :pred svtv-outentry-p :fix svtv-outentry-fix
      :equiv svtv-outentry-equiv :define t :forward t)

    ;; (defrefinement svtv-entry-equiv svtv-outentry-equiv
    ;;   :hints(("Goal" :in-theory (enable svtv-entry-fix))))
    ))

(deflist svtv-outentrylist :elt-type svtv-outentry :true-listp t)

;; (defthm svtv-entrylist-when-outentrylist
;;   (implies (svtv-outentrylist-p x)
;;            (svtv-entrylist-p x))
;;   :hints(("Goal" :in-theory (enable svtv-outentrylist-p
;;                                     svtv-entrylist-p))))

;; (defthm svtv-entrylist-fix-of-outentrylist-fix
;;   (equal (svtv-outentrylist-fix (svtv-entrylist-fix x))
;;          (svtv-outentrylist-fix x))
;;   :hints(("Goal" :in-theory (enable svtv-outentrylist-fix svtv-entrylist-fix))))

;; (defrefinement svtv-entrylist-equiv svtv-outentrylist-equiv
;;   :hints (("goal" :use ((:instance svtv-entrylist-fix-of-outentrylist-fix)
;;                         (:instance svtv-entrylist-fix-of-outentrylist-fix (x y)))
;;            :in-theory (disable svtv-entrylist-fix-of-outentrylist-fix))))

(defprod svtv-outputline
  ((lhs lhs)
   (entries svtv-outentrylist))
  :layout :tree)

;; (defthm svtv-line-when-outputline
;;   (implies (svtv-outputline-p x)
;;            (svtv-line-p x))
;;   :hints(("Goal" :in-theory (enable svtv-outputline-p
;;                                     svtv-line-p))))

;; (defthm svtv-line-fix-of-outputline-fix
;;   (equal (svtv-outputline-fix (svtv-line-fix x))
;;          (svtv-outputline-fix x))
;;   :hints(("Goal" :in-theory (enable svtv-outputline-fix svtv-line-fix))))

;; (defrefinement svtv-line-equiv svtv-outputline-equiv
;;   :hints (("goal" :use ((:instance svtv-line-fix-of-outputline-fix)
;;                         (:instance svtv-line-fix-of-outputline-fix (x y)))
;;            :in-theory (disable svtv-line-fix-of-outputline-fix))))


(deflist svtv-outputs :elt-type svtv-outputline :true-listp t)

;; (defthm svtv-lines-when-outputs
;;   (implies (svtv-outputs-p x)
;;            (svtv-lines-p x))
;;   :hints(("Goal" :in-theory (enable svtv-outputs-p
;;                                     svtv-lines-p))))

;; (defthm svtv-lines-fix-of-outputs-fix
;;   (equal (svtv-outputs-fix (svtv-lines-fix x))
;;          (svtv-outputs-fix x))
;;   :hints(("Goal" :in-theory (enable svtv-outputs-fix svtv-lines-fix))))

;; (defrefinement svtv-lines-equiv svtv-outputs-equiv
;;   :hints (("goal" :use ((:instance svtv-lines-fix-of-outputs-fix)
;;                         (:instance svtv-lines-fix-of-outputs-fix (x y)))
;;            :in-theory (disable svtv-lines-fix-of-outputs-fix))))

(defprod svtv
  ((name           symbolp)
   (outexprs       svex-alist-p)
   (nextstate      svex-alist-p "NIL if not defined with :state-machine t or :keep-final-state t")
   (states         svex-alistlist-p "NIL if not defined with :keep-all-states t")
   (inmasks        svar-boolmasks-p)
   (outmasks       svar-boolmasks-p)
   (orig-ins       true-list-listp)
   (orig-overrides true-list-listp)
   (orig-outs      true-list-listp)
   (orig-internals true-list-listp)
   (expanded-ins         svtv-lines-p)
   (expanded-overrides   svtv-lines-p)
   (nphases        natp)))





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


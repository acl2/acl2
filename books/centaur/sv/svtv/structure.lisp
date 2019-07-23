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
   (nextstate      svex-alist-p "NIL if not defined with :state-machine t")
   (inmasks        svar-boolmasks-p)
   (outmasks       svar-boolmasks-p)
   (orig-ins       true-list-listp)
   (orig-overrides true-list-listp)
   (orig-outs      true-list-listp)
   (orig-internals true-list-listp)
   (expanded-ins         svtv-lines-p)
   (expanded-overrides   svtv-lines-p)
   (nphases        natp)))

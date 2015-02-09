; ESIM Symbolic Hardware Simulator
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


; vl2014/util/esim-lemmas.lisp -- lemmas for reasoning about E stuff (patterns,
; gpl, etc.)
;
; This book is only intended to be locally included!

(in-package "VL2014")
(include-book "centaur/vl2014/util/defs" :dir :system)
(include-book "centaur/esim/esim-sexpr-support" :dir :system)
(include-book "centaur/esim/esim-sexpr-support-thms" :dir :system)
(local (non-parallel-book))

(in-theory (disable good-esim-primitivep
                    good-esim-modulep
                    good-esim-occp
                    good-esim-occsp
                    bad-esim-modulep
                    bad-esim-occp
                    bad-esim-occsp))

(in-theory (disable acl2::member-equal-of-alist-vals-under-iff))

(defthm gpl-of-cons
  (equal (gpl key (cons key2 rest))
         (if (equal key key2)
             (car rest)
           (gpl key (cdr rest))))
  :hints(("Goal" :in-theory (enable gpl))))

(defsection similar-patternsp-of-al->pat

  (local (defthm l0
           (implies (not (member-equal nil (alist-vals al)))
                    (iff (cdr (hons-assoc-equal pat al))
                         (hons-assoc-equal pat al)))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (local (defthm l1
           (implies (atom-listp (alist-vals al))
                    (equal (consp (cdr (hons-assoc-equal pat al)))
                           nil))
           :hints(("Goal" :in-theory (enable hons-assoc-equal)))))

  (defthm similar-patternsp-of-al->pat
    (implies (and (subsetp-equal (pat-flatten1 pat) (alist-keys al))
                  (not (member nil (alist-vals al)))
                  (atom-listp (alist-vals al)))
             (similar-patternsp (al->pat pat al default) pat))
    :hints(("Goal"
            :do-not '(generalize fertilize)
            :in-theory (enable al->pat)
            :induct (al->pat pat al default)))))

(defthm good-esim-occsp-of-append
  (equal (good-esim-occsp (append x y))
         (and (good-esim-occsp x)
              (good-esim-occsp y)))
  :hints(("Goal"
          :induct (len x)
          :in-theory (enable good-esim-occsp))))


#!ACL2
(defthm-flag-bad-esim-modulep
 (defthm stringp-of-car-of-bad-esim-modulep
   (implies (not (good-esim-modulep x))
            (stringp (car (bad-esim-modulep x))))
   :flag mod)
  (defthm stringp-of-car-of-bad-esim-occp
    (implies (not (good-esim-occp x))
             (stringp (car (bad-esim-occp name x))))
    :flag occ)
  (defthm stringp-of-car-of-bad-esim-occsp
    (implies (not (good-esim-occsp x))
             (stringp (car (bad-esim-occsp name x))))
    :flag occs)
  :hints(("Goal"
          :expand ((good-esim-occp x)
                   (good-esim-occsp x)
                   (good-esim-modulep x)
                   (bad-esim-occp name x)
                   (bad-esim-occsp name x)
                   (bad-esim-modulep x)))))


; VL Verilog Toolkit
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>


; vl/util/esim-lemmas.lisp -- lemmas for reasoning about E stuff (patterns,
; gpl, etc.)
;
; This book is only intended to be locally included!

(in-package "VL")
(include-book "defs")
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


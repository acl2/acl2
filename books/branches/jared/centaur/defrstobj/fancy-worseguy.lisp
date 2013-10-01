; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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

(in-package "RSTOBJ")
(include-book "g-delete-keys")
(include-book "misc/equal-by-g-help" :dir :system) ;; NONLOCAL !!!

; fancy-worseguy.lisp
;
; This is an alternative to g-worseguy that can avoid returning certain keys.
; We use it to search for conflicting keys in the MISC elements of record
; stobjs.

(defund fancy-worseguy (keys x y)
  (acl2::g-worseguy (g-delete-keys keys x)
                    (g-delete-keys keys y)))

(local (in-theory (enable g-delete-keys fancy-worseguy)))

(local (in-theory (disable acl2::g-worseguy)))

(local (defthm l0
         (implies (and (equal (g key x) (g key y))
                       (acl2::g-worseguy x y))
                  (not (equal (cadr (acl2::g-worseguy x y)) key)))))

(local (defthm l1
         (let ((ex (acl2::g-worseguy (s key val x)
                                     (s key val y))))
           (implies ex
                    (not (equal (g (cadr ex) (s key val x))
                                (g (cadr ex) (s key val y))))))
         :hints(("Goal"
                 :in-theory (disable acl2::g-worseguy-finds-counterexample)
                 :use ((:instance acl2::g-worseguy-finds-counterexample
                                  (acl2::x (s key val x))
                                  (acl2::y (s key val y))))))))

(local (defthm l2
         (let ((ex (acl2::g-worseguy (g-delete-keys keys x)
                                     (g-delete-keys keys y))))
           (implies ex
                    (not (equal (g (cadr ex) (g-delete-keys keys x))
                                (g (cadr ex) (g-delete-keys keys y))))))))

(defthm fancy-worseguy-finds-counterexample
  (implies (fancy-worseguy keys x y)
           (not (equal (g (cadr (fancy-worseguy keys x y)) x)
                       (g (cadr (fancy-worseguy keys x y)) y)))))

(defthm fancy-worseguy-not-among-keys
  (implies (and (fancy-worseguy keys x y)
                (member-equal key keys))
           (not (equal (cadr (fancy-worseguy keys x y)) key))))

(defthm fancy-worseguy-unless-equal
  (implies (and (not (equal misc1 misc2))
                (equal misc1 (g-delete-keys keys misc1))
                (equal misc2 (g-delete-keys keys misc2)))
           (fancy-worseguy keys misc1 misc2)))


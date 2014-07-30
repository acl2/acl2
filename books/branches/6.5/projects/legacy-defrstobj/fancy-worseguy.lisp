; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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


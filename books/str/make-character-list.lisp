; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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
;
; Additional copyright notice for make-character-list.lisp:
;
; This file is adapted from the Unicode library, Copyright (C) 2005-2013 by
; Jared Davis, which was also released under the GPL.

(in-package "STR")
(include-book "char-fix")
(local (include-book "std/lists/append" :dir :system))

(in-theory (disable make-character-list))

(defsection str/make-character-list
  :parents (coercion make-character-list)
  :short "Lemmas about @(see make-character-list) in the @(see str) library."

  :long "<p>This function is normally not anything you would ever want to use.
It is notable mainly for the role it plays in the completion axiom for @(see
coerce).</p>"

  (local (in-theory (enable make-character-list)))

  (defthm make-character-list-when-atom
    (implies (atom x)
             (equal (make-character-list x)
                    nil)))

  (defthm make-character-list-of-cons
    (equal (make-character-list (cons a x))
           (cons (char-fix a)
                 (make-character-list x))))

  (defthm consp-of-make-character-list
    (equal (consp (make-character-list x))
           (consp x)))

  (defthm make-character-list-under-iff
    (iff (make-character-list x)
         (consp x)))

  (defthm len-of-make-character-list
    (equal (len (make-character-list x))
           (len x)))

  (defthm make-character-list-when-character-listp
    (implies (character-listp x)
             (equal (make-character-list x)
                    x)))

  (defthm character-listp-of-make-character-list
    (character-listp (make-character-list x)))

  (defthm make-character-list-of-append
    (equal (make-character-list (append x y))
           (append (make-character-list x)
                   (make-character-list y))))

  (defthm make-character-list-of-revappend
    (equal (make-character-list (revappend x y))
           (revappend (make-character-list x)
                      (make-character-list y)))))


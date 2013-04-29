; Make-character-list lemmas
; Copyright (C) 2005-2013 by Jared Davis <jared@cs.utexas.edu>
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 59 Temple Place - Suite 330, Boston, MA 02111-1307, USA.
;
; make-character-list.lisp
; This file was originally part of the Unicode library.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(in-theory (disable make-character-list))

(defsection std/lists/make-character-list
  :parents (std/lists make-character-list)
  :short "Lemmas about @(see make-character-list) available in the @(see
std/lists) library."

  :long "<p>This function is normally not anything you would ever want to use.
It is notable mainly for the role it plays in the completion axiom for @(see
coerce).</p>"

  (local (in-theory (enable make-character-list)))

  (defthm make-character-list-when-atom
    (implies (atom x)
             (equal (make-character-list x)
                    nil)))

  ;; BOZO I want to add a make-character-list of cons rule, but I want to write
  ;; it in terms of char-fix.  But char-fix is defined in str/eqv.lisp, so I
  ;; can't do this because then there'd be a circular dependency between
  ;; unicode/ and str/.  BLAH.  GG ACL2 Make.

  (defthm make-character-list-when-character-listp
    (implies (character-listp x)
             (equal (make-character-list x)
                    x)))

  (defthm character-listp-of-make-character-list
    (character-listp (make-character-list x)))

  (defthm len-of-make-character-list
    (equal (len (make-character-list x))
           (len x)))

  (defthm make-character-list-of-append
    (equal (make-character-list (append x y))
           (append (make-character-list x)
                   (make-character-list y))))

  (defthm make-character-list-of-revappend
    (equal (make-character-list (revappend x y))
           (revappend (make-character-list x)
                      (make-character-list y)))))


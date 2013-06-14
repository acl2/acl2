; Proof of termination for extend-pathname
; Copyright (C) 2012 Centaur Technology
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
; This just proves that EXTEND-PATHNAME terminates.  It doesn't look like we
; can verify its guards, because functions it calls don't have appropriate
; guards, e.g., remove-after-last-directory-separator obviously expects its
; argument to be a string but doesn't have any type/guard declaration for that.

(in-package "ACL2")
(set-state-ok t)


;; Substantially copied from VL/arithmetic
(local
 (encapsulate ()

  (local (in-theory (enable make-character-list)))

  (defthm make-character-list-when-character-listp
    (implies (character-listp x)
             (equal (make-character-list x)
                    x)))

  (defthm character-listp-of-make-character-list
    (character-listp (make-character-list x)))

  (defthm len-of-make-character-list
    (equal (len (make-character-list x))
           (len x)))))


(local (defthm coerce-inverse-1-better
         (equal (coerce (coerce x 'string) 'list)
                (if (stringp x)
                    nil
                  (make-character-list x)))
         :hints(("Goal"
                 :use ((:instance acl2::completion-of-coerce
                                  (acl2::x x)
                                  (acl2::y 'string)))))))

(in-theory (disable coerce-inverse-1))

(local (defthm len-revappend
         (equal (len (revappend x y))
                (+ (len x) (len y)))))

(local (defthm len-first-n-ac
         (equal (len (first-n-ac i l ac))
                (+ (nfix i) (len ac)))))

(verify-termination remove-after-last-directory-separator)

(verify-termination merge-using-dot-dot)

(verify-termination our-merge-pathnames)

(verify-termination directory-of-absolute-pathname)

(verify-termination expand-tilde-to-user-home-dir)

(verify-termination extend-pathname)


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

(in-package "STR")
(include-book "cat")
(include-book "strprefixp")

(local (include-book "misc/assert" :dir :system))
(local (include-book "arithmetic"))

(defsection strsubst-aux
  :parents (strsubst)
  :short "Fast implementation of @(see strsubst)."

  (defund strsubst-aux (old new x n xl oldl acc)
    (declare (type string old new x)
             (type (integer 0 *) n xl oldl)
             (xargs :guard (and (stringp old)
                                (stringp new)
                                (stringp x)
                                (natp n)
                                (natp xl)
                                (posp oldl)
                                (= oldl (length old))
                                (= xl (length x)))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (cond ((mbe :logic (zp oldl)
                :exec nil)
           acc)

          ((mbe :logic (zp (- (nfix xl) (nfix n)))
                :exec (>= n xl))
           acc)

          ((strprefixp-impl old x 0 n oldl xl)
           (let ((acc (revappend-chars new acc)))
             (strsubst-aux old new x
                           (the (integer 0 *)
                             (+ oldl (the (integer 0 *) (lnfix n))))
                           xl oldl acc)))

          (t
           (let ((acc (cons (char x n) acc)))
             (strsubst-aux old new x
                           (the (integer 0 *)
                             (+ 1 (the (integer 0 *) (lnfix n))))
                           xl oldl acc)))))

  (local (in-theory (enable strsubst-aux)))

  (defthm character-listp-of-strsubst-aux
    (implies (and (stringp old)
                  (stringp new)
                  (stringp x)
                  (natp n)
                  (natp xl)
                  (posp oldl)
                  (= oldl (length old))
                  (= xl (length x))
                  (character-listp acc))
             (character-listp (strsubst-aux old new x n xl oldl acc)))))


(defsection strsubst
  :parents (substitution substitute)
  :short "Replace substrings throughout a string."

  :long "<p>@(call strsubst) replaces each occurrence of @('old') with @('new')
throughout @('x').  Each argument is a string, and a new string is returned.
The replacement is done globally and non-recursively.</p>

<p>Examples:</p>
@({
 (strsubst \"World\" \"Star\" \"Hello, World!\")
   -->
 \"Hello, Star!\"

 (strsubst \"oo\" \"aa\" \"xoooyoo\")
   -->
 \"xaaoyaa\"
})

<p>ACL2 has a built in @(see substitute) function, but it only works on
individual characters, whereas @('strsubst') works on substrings.</p>"

;; BOZO probably worthwhile to check if old occurs, and if not don't bother to
;; do any coercion, etc.

  (defund strsubst (old new x)
    (declare (xargs :guard (and (stringp old)
                                (stringp new)
                                (stringp x))))
    (let ((oldl (mbe :logic (len (explode old))
                     :exec (length old))))
      (if (zp oldl)
          (mbe :logic (str-fix x)
               :exec x)
        (rchars-to-string (strsubst-aux old new x 0 (length x) oldl nil)))))

  (local (in-theory (enable strsubst)))

  (defthm stringp-of-strsubst
    (stringp (strsubst old new x))
    :rule-classes :type-prescription)

  (local (assert! (equal (strsubst "World" "Star" "Hello, World!")
                         "Hello, Star!")))

  (local (assert! (equal (strsubst "oo" "aa" "xoooyoo")
                         "xaaoyaa"))))



(defsection strsubst-list
  :parents (substitution)
  :short "Carry out a @(see strsubst) replacement throughout a list of strings."

  :long "<p>@(call strsubst-list) replaces every occurrence of @('old') with
@('new') throughout @('x').  Here, @('old') and @('new') are strings, but
@('x') is a list of strings.  A new list of strings is returned.</p>

<p>Example:</p>
@({
 (strsubst-list \"Sun\"
                \"Moon\"
                '(\"Sun Roof\" \"Hello Sun\" \"Sunny Sunshades\"))
   -->
 (\"Moon Roof\" \"Hello Moon\" \"Moonny Moonshades\")
})"

  ;; BOZO consider using defprojection

  (defund strsubst-list (old new x)
    (declare (xargs :guard (and (stringp old)
                                (stringp new)
                                (string-listp x))))
    (if (atom x)
        nil
      (cons (strsubst old new (car x))
            (strsubst-list old new (cdr x)))))

  (local (in-theory (enable strsubst-list)))

  (defthm strsubst-list-when-atom
    (implies (atom x)
             (equal (strsubst-list old new x)
                    nil)))

  (defthm strsubst-list-of-cons
    (equal (strsubst-list old new (cons a x))
           (cons (strsubst old new a)
                 (strsubst-list old new x))))

  (defthm string-listp-of-strsubst-list
    (string-listp (strsubst-list old new x)))

  (local (defthm l0
           (equal (strsubst-list old new (list-fix x))
                  (strsubst-list old new x))))

  (defcong list-equiv equal (strsubst-list old new x) 3
    :hints(("Goal"
            :in-theory (disable l0)
            :use ((:instance l0 (x x))
                  (:instance l0 (x acl2::x-equiv))))))

  (defthm strsubst-list-of-append
    (equal (strsubst-list old new (append x y))
           (append (strsubst-list old new x)
                   (strsubst-list old new y))))

  (defthm strsubst-list-of-revappend
    (equal (strsubst-list old new (revappend x y))
           (revappend (strsubst-list old new x)
                      (strsubst-list old new y))))

  (defthm strsubst-list-of-rev
    (equal (strsubst-list old new (rev x))
           (rev (strsubst-list old new x)))))

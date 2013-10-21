; Standard Typed Lists Library
; signed-byte-listp.lisp -- originally part of the Unicode library
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

(in-package "ACL2")
(set-verify-guards-eagerness 2)
(include-book "xdoc/top" :dir :system)

(local (in-theory (disable signed-byte-p)))

(defsection signed-byte-listp
  :parents (std/typed-lists signed-byte-p)
  :short "Recognizer for lists of @(see signed-byte-p)'s."
  :long "<p>BOZO consider switching this book to use deflist.</p>"

  (defund signed-byte-listp (n x)
    (if (atom x)
        (null x)
      (and (signed-byte-p n (car x))
           (signed-byte-listp n (cdr x)))))

  (defthm signed-byte-listp-when-atom
    (implies (atom x)
             (equal (signed-byte-listp n x)
                    (not x)))
    :hints(("Goal" :in-theory (enable signed-byte-listp))))

  (defthm signed-byte-listp-of-cons
    (equal (signed-byte-listp n (cons a x))
           (and (signed-byte-p n a)
                (signed-byte-listp n x)))
    :hints(("Goal" :in-theory (enable signed-byte-listp))))

  (defthm true-listp-when-signed-byte-listp
    (implies (signed-byte-listp bytes x)
             (true-listp x))
    :hints(("Goal" :induct (len x)))))


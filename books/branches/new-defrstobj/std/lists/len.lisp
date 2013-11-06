; Len lemmas
; Copyright (C) 2008-2013 Centaur Technology
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

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)
(local (include-book "arithmetic/top" :dir :system))

(defsection std/lists/len
  :parents (std/lists len)
  :short "Lemmas about @(see len) available in the @(see std/lists) library."

  (defthm len-when-atom
    (implies (atom x)
             (equal (len x)
                    0)))

  (defthm len-of-cons
    (equal (len (cons a x))
           (+ 1 (len x))))

  (defthm |(equal 0 (len x))|
    (equal (equal 0 (len x))
           (atom x)))

  (defthm |(< 0 (len x))|
    (equal (< 0 (len x))
           (consp x)))

  (defthm consp-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp x)
                    (< 0 n))))

  (defthm consp-of-cdr-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp (cdr x))
                    (< 1 n)))
    :hints(("Goal" :expand ((len x)
                            (len (cdr x))))))

  (defthm consp-of-cddr-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp (cddr x))
                    (< 2 n)))
    :hints(("Goal" :expand ((len x)
                            (len (cdr x))
                            (len (cddr x))))))

  (defthm consp-of-cdddr-by-len
    (implies (and (equal (len x) n)
                  (syntaxp (quotep n)))
             (equal (consp (cdddr x))
                    (< 3 n)))
    :hints(("Goal" :expand ((len x)
                            (len (cdr x))
                            (len (cddr x))
                            (len (cdddr x)))))))


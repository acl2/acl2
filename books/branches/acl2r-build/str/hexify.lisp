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
(include-book "coerce")
(include-book "tools/bstar" :dir :system)
(local (include-book "explode-atom"))
(local (include-book "arithmetic"))
(local (in-theory (disable explode-atom)))

(defsection insert-underscores
  :parents (hexify)

  (defund insert-underscores (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           x)
          ((equal (mod (len x) 4) 0)
           (list* #\_ (car x) (insert-underscores (cdr x))))
          (t
           (list* (car x) (insert-underscores (cdr x))))))

  (local (in-theory (enable insert-underscores)))

  (defthm character-listp-of-insert-underscores
    (implies (force (character-listp x))
             (character-listp (insert-underscores x)))))

(defsection hexify
  :parents (numbers)
  :short "Convert numbers into readable hex strings."

  :long "<p>@(call hexify) is a dumb but useful printing utility for displaying
numbers in hex.  It is typically used in @(see cw) statements, e.g.,:</p>

@({
    ACL2 !> (cw \"foo is ~s0~%\" (str::hexify (1- (expt 2 32))))
    foo is #uxFFFF_FFFF
    NIL
    ACL2 !>
})

<p>The @('#ux') is for compatibility with the @(see acl2::sharp-u-reader).</p>

<p>See also @(see natstr) which converts numbers into decimal strings (without
underscores) and @(see binify) which is like @('hexify') but for binary instead
of hex.</p>

<h3>Usage</h3>

<p>@(call hexify) always returns a @(see stringp).</p>

<p>@('x') must be an integer, string, or symbol; otherwise a @(see hard-error)
will be caused.</p>

<p>Normally @('x') is an integer.  In this case, we convert it into an
msb-first hex string with an underscore inserted every four characters.  This
makes it easier to read long values.</p>

<p>When @('x') is a string we just return it unchanged.</p>

<p>When @('x') is a symbol we just return its name.</p>"

  (defun hexify (x)
    (declare (xargs :guard t))
    (cond ((integerp x)
           (b* ((xsign (< x 0))
                (xabs (abs x))
                (chars (explode-atom xabs 16)) ;; looks like BEEF...
                (nice-chars (list* #\# #\u #\x
                                   (append (and xsign '(#\-))
                                           (cons (first chars)
                                                 (insert-underscores (nthcdr 1 chars)))))))
             (implode nice-chars)))
          ((symbolp x)
           (symbol-name x))
          ((stringp x)
           x)
          (t
           (prog2$ (er hard? 'hexify "Unexpected argument ~x0.~%" x)
                   "")))))

(defsection binify
  :parents (numbers)
  :short "Convert numbers into readable binary strings."
  :long "<p>@(call binify) is identical to @(see str::hexify) except that it
produces binary output instead of hex output.</p>"

  (defun binify (x)
    (declare (xargs :guard t))
    (cond ((integerp x)
           (b* ((xsign (< x 0))
                (xabs (abs x))
                (chars (explode-atom xabs 2))
                (nice-chars (list* #\# #\u #\b
                                   (append (and xsign '(#\-))
                                           (cons (first chars)
                                                 (insert-underscores (nthcdr 1 chars)))))))
             (implode nice-chars)))
          ((symbolp x)
           (symbol-name x))
          ((stringp x)
           x)
          (t
           (prog2$ (er hard? 'binify "Unexpected argument ~x0.~%" x)
                   "")))))

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

(in-package "VL")
(include-book "defs")

(defenum vl-bit-p (:vl-0val :vl-1val :vl-xval :vl-zval)
  :parents (vl-weirdint-p)
  :short "Representation of a single Verilog bit (0, 1, X, or Z)."

  :long "<p>Verilog has four register-transfer level values, @('0'), @('1'),
@('X'), and @('Z').  In @(see vl-weirdint-p) objects, We represent these values
using the keyword symbols:</p>

<ul>
 <li>@(':vl-0val') means 0,</li>
 <li>@(':vl-1val') means 1,</li>
 <li>@(':vl-xval') means X, and</li>
 <li>@(':vl-zval') means Z.</li>
</ul>")

(deflist vl-bitlist-p (x)
  (vl-bit-p x)
  :guard t
  :elementp-of-nil nil
  :parents (vl-weirdint-p))


(defsection vl-bit->char
  :parents (vl-weirdint-p)
  :short "Get the character for a @(see vl-bit-p)."

  :long "<p>@(call vl-bit->char) produces the ASCII character for a @(see vl-bit-p).
That is, it returns one of the characters: 0, 1, X, or Z.</p>"

  (defund vl-bit->char (x)
    (declare (xargs :guard (vl-bit-p x)
                    :guard-hints (("Goal" :in-theory (enable vl-bit-p)))))
    (case x
      (:vl-0val #\0)
      (:vl-1val #\1)
      (:vl-xval #\X)
      (:vl-zval #\Z)
      (otherwise
       ;; hack for unconditional type prescription
       (prog2$ (er hard 'vl-bit-char "Impossible")
               #\0))))

  (local (in-theory (enable vl-bit->char)))

  (defthm characterp-of-vl-bit->char
    (characterp (vl-bit->char x))
    :rule-classes :type-prescription))


(defprojection vl-bitlist->charlist (x)
  (vl-bit->char x)
  :guard (vl-bitlist-p x)
  :result-type character-listp
  :nil-preservingp nil
  :parents (vl-weirdint-p)
  :short "Get a character list for a @(see vl-bitlist-p)."

  :long "<p>@(call vl-bitlist->charlist) returns the list of ASCII characters
corresponding to a @(see vl-bitlist-p).  See also @(see vl-bitlist->string).</p>")


(defsection vl-bitlist->string
  :parents (vl-weirdint-p)
  :short "Get the string corresponding to a @(see vl-bitlist-p)."
  :long "<p>See @(see vl-bitlist->charlist).</p>"

  (defund vl-bitlist->string (x)
    (declare (xargs :guard (vl-bitlist-p x)))
    (coerce (vl-bitlist->charlist x) 'string))

  (local (in-theory (enable vl-bitlist->string)))

  (defthm stringp-of-vl-bitlist->string
    (stringp (vl-bitlist->string x))
    :rule-classes :type-prescription))

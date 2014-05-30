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
(include-book "centaur/fty/deftypes" :dir :system)
(local (std::add-default-post-define-hook :fix))

(defenum vl-bit-p
  (:vl-0val :vl-1val :vl-xval :vl-zval)
  :parents (vl-weirdint-p)
  :short "Representation of a single Verilog bit (0, 1, X, or Z)."

  :long "<p>Verilog has four register-transfer level values, @('0'), @('1'),
@('X'), and @('Z').  We represent these values using the keyword symbols
accepted by @('vl-bit-p'):</p>

<ul>
 <li>@(':vl-0val') means 0,</li>
 <li>@(':vl-1val') means 1,</li>
 <li>@(':vl-xval') means X, and</li>
 <li>@(':vl-zval') means Z.</li>
</ul>")

(fty::deflist vl-bitlist
  :elt-type vl-bit-p
  :true-listp nil)

(deflist vl-bitlist-p (x)
  (vl-bit-p x)
  :guard t
  :elementp-of-nil nil
  :parents (vl-weirdint-p)
  :already-definedp t)

(define vl-bit->char ((x vl-bit-p))
  :parents (vl-bit-p)
  :short "Get the character for a @(see vl-bit-p)."
  :returns (char characterp :rule-classes :type-prescription)
  :long "<p>@(call vl-bit->char) produces the ASCII character for a @(see vl-bit-p).
That is, it returns one of the characters: 0, 1, X, or Z.</p>"
  (let ((x (mbe :logic (vl-bit-fix x) :exec x)))
    (case x
      (:vl-0val #\0)
      (:vl-1val #\1)
      (:vl-xval #\X)
      (:vl-zval #\Z)
      (otherwise
       ;; hack for unconditional type prescription
       (progn$ (impossible)
               #\X)))))

(defprojection vl-bitlist->charlist ((x vl-bitlist-p))
  :returns (chars character-listp)
  :parents (vl-weirdint-p)
  :short "Get a character list for a @(see vl-bitlist-p)."
  (vl-bit->char x))

(define vl-bitlist->string ((x vl-bitlist-p))
  :parents (vl-weirdint-p)
  :short "Get the string corresponding to a @(see vl-bitlist-p)."
  :returns (str stringp :rule-classes :type-prescription)
  (implode (vl-bitlist->charlist x)))

(defenum vl-timeunit-p
  (:vl-s
   :vl-ms
   :vl-us
   :vl-ns
   :vl-ps
   :vl-fs)
  :parents (modules)
  :short "Representation for SystemVerilog time units (s, ms, ps, ...)")

(define vl-timeunit->string ((x vl-timeunit-p))
  :parents (vl-timeunit-p)
  :short "Get the string corresponding to a @(see vl-timeunit-p)."
  :returns (str stringp :rule-classes :type-prescription)
  (let ((x (mbe :logic (vl-timeunit-fix x)
                :exec x)))
    (case x
      (:vl-s "s")
      (:vl-ms "ms")
      (:vl-us "us")
      (:vl-ns "ns")
      (:vl-ps "ps")
      (:vl-fs "fs")
      (otherwise (progn$ (impossible)
                         "s")))))


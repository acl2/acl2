; FTY base list types
; Copyright (C) 2016 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
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
; Original author: Jared Davis <jared@kookamara.com>

(in-package "ACL2")
(include-book "deftypes")
(include-book "basetypes")
(include-book "std/strings/eqv" :dir :system)

(defxdoc fty::baselists
  :parents (fty::fty)
  :short "A book that associates various built-in ACL2 list recognizers with
suitable fixing functions and equivalence relations, for use in the @(see
fty::fty-discipline)."
  :long "<p>This is similar in spirit to the @(see fty::basetypes) book: it
arranges so that various list recognizers like @(see integer-listp), @(see
boolean-listp), etc., can be directly used with FTY.</p>

<p>Special note: even though @(see character-listp) and @(see string-listp)
aren't listed below, you will still be able to use them with FTY after
including the @('baselists') book.  For historical reasons these types are
defined in a special way in the @(see std/strings) library, see in particular
@(see str::equivalences).</p>")

(local (xdoc::set-default-parents fty::baselists))

;; BOZO think about adding other lists that are covered by, e.g.,
;; std/typed-lists, such as:

;; atom-listp
;; cons-listp
;; eqlable-listp
;; pseudo-term-listp
;; signed-byte-listp
;; unsigned-byte-listp

(fty::deflist acl2-number-list
  :elt-type acl2-number
  :pred acl2-number-listp
  :true-listp t
  :elementp-of-nil nil)

(fty::deflist boolean-list
  :elt-type bool
  :pred boolean-listp
  :true-listp t
  :elementp-of-nil t)

;; character-listp is handled specially in std/strings/eqv.

(fty::deflist integer-list
  :elt-type int
  :pred integer-listp
  :true-listp t
  :elementp-of-nil nil)

(fty::deflist nat-list
  :elt-type nat
  :pred nat-listp
  :true-listp t
  :elementp-of-nil nil)

(fty::deflist rational-list
  :elt-type rational
  :pred rational-listp
  :true-listp t
  :elementp-of-nil nil)

(fty::deflist symbol-list
  :elt-type symbol
  :pred symbol-listp
  :true-listp t
  :elementp-of-nil t)

(fty::deffixtype true-list :pred true-listp :fix list-fix :equiv list-equiv :forward t)

(fty::deflist true-list-list
  :elt-type true-list
  :true-listp t
  :pred true-list-listp
  :elementp-of-nil t)

;; string-listp is handled specially in std/strings/eqv.

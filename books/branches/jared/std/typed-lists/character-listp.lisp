; Standard Typed Lists Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "ACL2")
(include-book "std/util/deflist" :dir :system)

; We disable CHARACTER-LISTP itself, and also the following ACL2 built-in
; rules, since the DEFLIST adds stronger ones.
(in-theory (disable character-listp
                    character-listp-append
                    character-listp-revappend))

(defsection std/typed-lists/character-listp
  :parents (std/typed-lists character-listp)
  :short "Lemmas about @(see character-listp) available in the @(see
std/typed-lists) library."
  :long "<p>Most of these are generated automatically with @(see
std::deflist).</p>"

  (std::deflist character-listp (x)
    (characterp x)
    :true-listp t
    :elementp-of-nil nil
    :already-definedp t
    ;; Set :parents to nil to avoid overwriting the built-in ACL2 documentation
    :parents nil)

  (defthm true-listp-when-character-listp-rewrite
    ;; The deflist gives us a compound-recognizer, but in this case having a
    ;; rewrite rule seems worth it.
    (implies (character-listp x)
             (true-listp x))
    :rule-classes ((:rewrite :backchain-limit-lst 1)))

  (defthm character-listp-of-remove-equal
    ;; BOZO probably add to deflist
    (implies (character-listp x)
             (character-listp (remove-equal a x))))

  (defthm character-listp-of-make-list-ac
    (equal (character-listp (make-list-ac n x ac))
           (and (character-listp ac)
                (or (characterp x)
                    (zp n)))))

  (defthm eqlable-listp-when-character-listp
    (implies (character-listp x)
             (eqlable-listp x)))

  (defthm character-listp-of-rev
    ;; BOZO consider adding to deflist
    (equal (character-listp (rev x))
           (character-listp (list-fix x)))
    :hints(("Goal" :induct (len x)))))


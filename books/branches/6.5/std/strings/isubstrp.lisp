; ACL2 String Library
; Copyright (C) 2009-2013 Centaur Technology
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

(in-package "STR")
(include-book "istrpos")
(local (include-book "arithmetic"))

(defsection isubstrp
  :parents (substrings)
  :short "Case-insensitively test for the existence of a substring."
  :long "<p>@(call isubstrp) determines if x ever occurs as a case-insensitive
substring of y.</p>

<p>See also @(see substrp) for a case-sensitive version.</p>

<p>See also @(see istrpos) for an alternative that reports the position of the
matched substring.</p>"

  (definlined isubstrp (x y)
    (declare (type string x y))
    (if (istrpos x y)
        t
      nil))

  (local (in-theory (enable isubstrp)))

  (defthm iprefixp-when-isubstrp
    (implies (isubstrp x y)
             (iprefixp (explode x)
                       (nthcdr (istrpos x y) (explode y)))))

  (defthm completeness-of-isubstrp
    (implies (and (iprefixp (explode x)
                            (nthcdr m (explode y)))
                  (force (natp m)))
             (isubstrp x y))
    :hints(("Goal"
            :in-theory (disable completeness-of-istrpos)
            :use ((:instance completeness-of-istrpos)))))

  (local (in-theory (disable istreqv)))

  (defcong istreqv equal (isubstrp x y) 1)
  (defcong istreqv equal (isubstrp x y) 2))



(defsection collect-strs-with-isubstr
  :parents (substrings)
  :short "Gather strings that have some (case-insensitive) substring."

  :long "<p>@(call collect-strs-with-isubstr) returns a list of all the strings
in the list @('x') that have @('a') as a case-insensitve substring.  The
substring tests are carried out with @(see isubstrp).</p>

<p>See also @(see collect-syms-with-isubstr), which is similar but for symbol
lists instead of string lists.</p>"

  (defund collect-strs-with-isubstr (a x)
    (declare (xargs :guard (and (stringp a)
                                (string-listp x))))
    (cond ((atom x)
           nil)
          ((str::isubstrp a (car x))
           (cons (car x) (collect-strs-with-isubstr a (cdr x))))
          (t
           (collect-strs-with-isubstr a (cdr x)))))

  (local (in-theory (enable collect-strs-with-isubstr)))

  (defcong istreqv equal (collect-strs-with-isubstr a x) 1
    :hints(("Goal" :in-theory (disable istreqv))))

  (defthm collect-strs-with-isubstr-when-atom
    (implies (atom x)
             (equal (collect-strs-with-isubstr a x)
                    nil)))

  (defthm collect-strs-with-isubstr-of-cons
    (equal (collect-strs-with-isubstr a (cons b x))
           (if (str::isubstrp a b)
               (cons b (collect-strs-with-isubstr a x))
             (collect-strs-with-isubstr a x))))

  (defthm member-equal-collect-strs-with-isubstr
    (iff (member-equal b (collect-strs-with-isubstr a x))
         (and (member-equal b x)
              (str::isubstrp a b))))

  (defthm subsetp-equal-of-collect-strs-with-isubstr
    (implies (subsetp-equal x y)
             (subsetp-equal (collect-strs-with-isubstr a x) y)))

  (defthm subsetp-equal-collect-strs-with-isubstr-self
    (subsetp-equal (collect-strs-with-isubstr a x) x)))



(defsection collect-syms-with-isubstr
  :parents (substrings)
  :short "Gather symbols whose names have some (case-insensitive) substring."

  :long "<p>@(call collect-syms-with-isubstr) returns a list of all the symbols
in the list @('x') that have @('a') as a case-insensitve substring of their
@(see symbol-name).  The substring tests are carried out with @(see
isubstrp).</p>

<p>See also @(see collect-strs-with-isubstr), which is similar but for string
lists instead of symbol lists.</p>"

  (defund collect-syms-with-isubstr (a x)
    (declare (xargs :guard (and (stringp a)
                                (symbol-listp x))))
    (cond ((atom x)
           nil)
          ((str::isubstrp a (symbol-name (car x)))
           (cons (car x) (collect-syms-with-isubstr a (cdr x))))
          (t
           (collect-syms-with-isubstr a (cdr x)))))

  (local (in-theory (enable collect-syms-with-isubstr)))

  (defcong istreqv equal (collect-syms-with-isubstr a x) 1
    :hints(("Goal" :in-theory (disable istreqv))))

  (defthm collect-syms-with-isubstr-when-atom
    (implies (atom x)
             (equal (collect-syms-with-isubstr a x)
                    nil)))

  (defthm collect-syms-with-isubstr-of-cons
    (equal (collect-syms-with-isubstr a (cons b x))
           (if (str::isubstrp a (symbol-name b))
               (cons b (collect-syms-with-isubstr a x))
             (collect-syms-with-isubstr a x))))

  (defthm member-equal-collect-syms-with-isubstr
    (iff (member-equal b (collect-syms-with-isubstr a x))
         (and (member-equal b x)
              (str::isubstrp a (symbol-name b)))))

  (defthm subsetp-equal-of-collect-syms-with-isubstr
    (implies (subsetp-equal x y)
             (subsetp-equal (collect-syms-with-isubstr a x) y)))

  (defthm subsetp-equal-collect-syms-with-isubstr-self
    (subsetp-equal (collect-syms-with-isubstr a x) x)))


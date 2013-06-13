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
(include-book "xdoc/top" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(local (include-book "std/lists/equiv" :dir :system))
(local (include-book "std/lists/rev" :dir :system))
(local (include-book "std/lists/append" :dir :system))


(defsection symbol-list-names
  :parents (symbols symbol-name symbol-listp)
  :short "Extract the name of every symbol in a list."

  :long "<p>@(call symbol-list-names) just maps @(see symbol-name) across the
list @('x'), returning a new list that has the names of all the symbols in
@('x').</p>

<p>Example:</p>
@({
    (symbol-list-names '(:foo acl2::bar str::baz))
      -->
    (\"foo\" \"bar\" \"baz\")
})"

;; BOZO consider using defprojection instead

  (defund symbol-list-names (x)
    (declare (xargs :guard (symbol-listp x)))
    (if (atom x)
        nil
      (cons (symbol-name (car x))
            (symbol-list-names (cdr x)))))

  (local (in-theory (enable symbol-list-names)))

  (defthm symbol-list-names-when-atom
    (implies (atom x)
             (equal (symbol-list-names x)
                    nil)))

  (defthm symbol-list-names-of-cons
    (equal (symbol-list-names (cons a x))
           (cons (symbol-name a)
                 (symbol-list-names x))))

  (defthm string-listp-of-symbol-list-names
    (string-listp (symbol-list-names x)))

  (local (defthm l0
           (equal (symbol-list-names (list-fix x))
                  (symbol-list-names x))))

  (defcong list-equiv equal (symbol-list-names x) 1
    :hints(("Goal"
            :in-theory (disable l0)
            :use ((:instance l0 (x x))
                  (:instance l0 (x acl2::x-equiv))))))

  (defthm symbol-list-names-of-append
    (equal (symbol-list-names (append x y))
           (append (symbol-list-names x)
                   (symbol-list-names y))))

  (defthm symbol-list-names-of-revappend
    (equal (symbol-list-names (revappend x y))
           (revappend (symbol-list-names x)
                      (symbol-list-names y))))

  (defthm symbol-list-names-of-rev
    (equal (symbol-list-names (rev x))
           (rev (symbol-list-names x)))))



(defsection intern-list
  :parents (symbols intern-in-package-of-symbol intern$ symbol-listp)
  :short "Generate a list of symbols in some package."

  :long "<p>Examples:</p>

@({
 (intern-list '(\"FOO\" \"BAR\"))           --> (acl2::foo acl2::bar)
 (intern-list '(\"FOO\" \"BAR\") 'str::foo) --> (str::foo str::bar)
})

<p>@(call intern-list) is a macro that takes</p>

<ul>

<li>@('names'), a list of strings that will become the @(see symbol-name)s of
the new symbols, and optionally</li>

<li>@('pkg'), a symbol that is used as a package indicator, as in @(see
intern-in-package-of-symbol).</li>

</ul>"

;; BOZO consider using defprojection

  (defund intern-list-fn (x pkg)
    (declare (xargs :guard (and (string-listp x)
                                (symbolp pkg))))
    (if (atom x)
        nil
      (cons (intern-in-package-of-symbol (car x) pkg)
            (intern-list-fn (cdr x) pkg))))

  (defmacro intern-list (x &optional (pkg ''acl2::acl2-pkg-witness))
    `(intern-list-fn ,x ,pkg))

  (local (defthm intern-list-examples
           (and (equal (str::intern-list '("FOO" "BAR" "BAZ"))
                       '(acl2::foo acl2::bar acl2::baz))
                (equal (str::intern-list '("FOO" "BAR" "BAZ") 'str::foo)
                       '(str::foo str::bar str::baz)))))

  (add-macro-alias intern-list intern-list-fn)
  (local (in-theory (enable intern-list)))


  (defthm intern-list-fn-when-atom
    (implies (atom x)
             (equal (intern-list-fn x pkg)
                    nil)))

  (defthm intern-list-fn-of-cons
    (equal (intern-list-fn (cons a x) pkg)
           (cons (intern-in-package-of-symbol a pkg)
                 (intern-list-fn x pkg))))

  (defthm symbol-listp-of-intern-list-fn
    (symbol-listp (intern-list-fn x pkg)))

  (local (defthm l0
           (equal (intern-list-fn (list-fix x) pkg)
                  (intern-list-fn x pkg))))

  (defcong list-equiv equal (intern-list-fn x pkg) 1
    :hints(("Goal"
            :in-theory (disable l0)
            :use ((:instance l0 (x x))
                  (:instance l0 (x acl2::x-equiv))))))

  (defthm intern-list-fn-of-append
    (equal (intern-list-fn (append x y) pkg)
           (append (intern-list-fn x pkg)
                   (intern-list-fn y pkg))))

  (defthm intern-list-fn-of-revappend
    (equal (intern-list-fn (revappend x y) pkg)
           (revappend (intern-list-fn x pkg)
                      (intern-list-fn y pkg))))

  (defthm intern-list-fn-of-rev
    (equal (intern-list-fn (rev x) pkg)
           (rev (intern-list-fn x pkg)))))



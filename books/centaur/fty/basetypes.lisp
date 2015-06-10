; FTY type support library
; Copyright (C) 2014 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

(in-package "ACL2")
(include-book "std/basic/defs" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(include-book "fixtype")
(local (include-book "std/lists/equiv" :dir :system))

(defconst fty::*defbasetype-keys*
  '(:name
    :fix))

;; This is just deffixtype with defaults for the names and with :define t.  We
;; wouldn't need to take the equiv name as an input, but since we're defining
;; it we'd like it to be tags-searchable.
(defun fty::defbasetype-fn (equiv pred keys)
  (declare (xargs :mode :program))
  (b* ((__function__ 'fty::defbasetype-fn)
       ((mv kwd-alist args) (std::extract-keywords __function__
                                                   fty::*defbasetype-keys*
                                                   keys nil))
       ((when args) (raise "Bad args: ~x0" args))
       (pkg (if (equal (symbol-package-name pred) "COMMON-LISP")
                'acl2::foo
              pred))
       (typename (or (std::getarg :name nil kwd-alist)
                     (b* ((predname (symbol-name pred))
                          (len (length predname))
                          (p? (char predname (- len 1)))
                          ((unless (eql p? #\P)) pred)
                          (dash? (char predname (- len 2)))
                          (newlen (- len (if (eql dash? #\-) 2 1))))
                       (intern-in-package-of-symbol
                        (subseq predname 0 newlen)
                        pkg))))
       (fix (or (std::getarg :fix nil kwd-alist)
                (intern-in-package-of-symbol
                 (concatenate 'string (symbol-name typename) "-FIX")
                 pkg))))
    `(fty::deffixtype ,typename :pred ,pred :fix ,fix :equiv ,equiv :define t)))

(defmacro fty::defbasetype (equiv pred &rest keys)
  (fty::defbasetype-fn equiv pred keys))


(fty::defbasetype nat-equiv natp :fix nfix)

(fty::defbasetype int-equiv integerp :fix ifix :name int)

(fty::defbasetype rational-equiv rationalp :fix rfix)

(fty::defbasetype number-equiv acl2-numberp :fix fix)

(fty::deffixtype true-list
  :pred true-listp
  :fix list-fix
  :equiv list-equiv)

(local (in-theory (enable streqv)))
(fty::deffixtype string
  :pred stringp
  :fix str-fix
  :equiv streqv)

(defsection true-p
  :parents (fty::basetypes)
  :short "@(call true-p) recognizes only the symbol @('t')."

  (defun true-p (x)
    (declare (xargs :guard t))
    (eq x t)))

(defsection true-fix
  :parents (fty::basetypes)
  :short "@(call true-fix) ignores its argument and unconditionally returns @('t')."

  (defun true-fix (x)
    (declare (xargs :guard t)
             (ignore x))
    t))

(defsection true-equiv
  :parents (fty::basetypes)
  :short "@(call true-equiv) is a ``degenerate'' equivalence for @(see true-p) objects."
  :long "<p>Because of the way @(see true-fix) works, this is always just true.</p>"

  ;; bozo gross
  (local (set-default-hints '('(:in-theory (enable true-fix true-p)))))

  (fty::deffixtype true
    :pred true-p
    :fix true-fix
    :equiv true-equiv
    :define t))

(defsection symbol-fix
  :parents (fty::basetypes symbolp)
  :short "@(call symbol-fix) is a fixing function for @(see symbolp); it is the
identity for symbols and coerces non-symbols to @('acl2::||'), i.e., the empty
symbol in the ACL2 package."

  :long "<p>Unfortunately it's not currently possible to come up with a good
symbol-fixing function that induces the proper congruences for both @(see
symbol-name) and @(see symbol-package-name).  This definition at least gives us
a congruence for @(see symbol-name).</p>

<p>BOZO consider adding a symbolp guard, inlining it, and turning it into an
identity function for execution.</p>"

  (defund symbol-fix (x)
    (declare (xargs :guard t))
    (if (symbolp x)
        x
      'acl2::||))

  (local (in-theory (enable symbol-fix)))

  (defthm symbolp-of-symbol-fix
    (symbolp (symbol-fix x))
    :rule-classes :type-prescription)

  (defthm symbol-fix-when-symbolp
    (implies (symbolp x)
             (equal (symbol-fix x) x))))

(defsection symbol-equiv
  :parents (fty::basetypes symbolp)
  :short "@(call symbol-equiv) recognizes symbols that are identical under
@(see symbol-fix)."

  (local (in-theory (enable symbol-fix)))

  (fty::defbasetype symbol-equiv symbolp)

  (defcong symbol-equiv equal (symbol-name x) 1))


(defsection pos-fix
  :parents (fty::basetypes posp)
  :short "@(call pos-fix) is a fixing function for @(see posp): it is the
identity for positive integers, or returns 1 for any other object."

  :long "<p>This has no guard.  For better efficiency, see @(see lposfix).</p>"

  (defund pos-fix (x)
    (declare (xargs :guard t))
    (if (posp x) x 1))

  (local (in-theory (enable pos-fix)))

  (defthm posp-of-pos-fix
    (posp (pos-fix x))
    :rule-classes :type-prescription)

  (defthm pos-fix-when-posp
    (implies (posp x)
             (equal (pos-fix x) x))))


(defsection pos-equiv
  :parents (fty::basetypes posp)
  :short "@(call pos-equiv) is equality for positive numbers, i.e., equality up
to @(see pos-fix)."

  (fty::defbasetype pos-equiv posp :fix pos-fix))


(defsection lposfix
  :parents (fty::basetypes pos-fix)
  :short "@(call lposfix) is logically identical to @(call pos-fix), but its
guard requires that @('x') is a @(see posp) and, in the execution, it's just a
no-op that returns @('x')."

  (defun-inline lposfix (x)
    ;; enabled
    (declare (xargs :guard (posp x)))
    (mbe :logic (pos-fix x)
         :exec x)))


(fty::deffixtype character
  :pred characterp
  :fix char-fix
  :equiv chareqv)


(defsection any-p
  :parents (fty::basetypes)
  :short "@(call any-p) is always true; i.e., it recognizes any ACL2 object."

  :long "<p>This is a ``degenerate'' recognizer which is sometimes useful for
@(see fty).  For instance, it allows you to have fields within a @(see
fty::defprod) that are completely unconstrained, which may be especially useful
when you are in the early stages of development and haven't yet thought much
about types.</p>"

  (defun-inline any-p (x)
    (declare (xargs :guard t)
             (ignore x))
    t))

(fty::deffixtype any
  :pred any-p
  :fix  identity
  :equiv equal)


(defsection bool-fix
  :parents (fty::basetypes booleanp)
  :short "@(call bool-fix) is a fixing function for Booleans; it coerces any
non-@('nil') symbol to @('t')."
  :long "<p>BOZO: could consider putting a @(see booleanp) guard here.</p>"

  (defund-inline bool-fix (x)
    (declare (xargs :guard t))
    (and x t))

  (local (in-theory (enable bool-fix)))

  (defthm booleanp-of-bool-fix
    (booleanp (bool-fix x))
    :rule-classes :type-prescription)

  (defthm bool-fix-when-booleanp
    (implies (booleanp x)
             (equal (bool-fix x) x)))

  (fty::deffixtype bool
    :pred booleanp
    :fix bool-fix
    :equiv iff)

  (defcong iff equal (bool-fix x) 1)

  (defthm bool-fix-under-iff
    (iff (bool-fix x) x)))



(defthm maybe-natp-when-natp
  ;; BOZO non-local, move to std/defs instead?
  (implies (natp x)
           (maybe-natp x)))

(defthmd natp-when-maybe-natp
  ;; BOZO non-local, move to std/defs instead?
  (implies (and (maybe-natp x)
                (double-rewrite x))
           (natp x)))

(defsection maybe-natp-fix
  :parents (fty::basetypes maybe-natp)
  :short "@(call maybe-natp-fix) is the identity for @(see maybe-natp)s, or
  coerces any invalid object to @('nil')."
  :long "<p>Performance note.  In the execution this is just an inlined
  identity function, i.e., it should have zero runtime cost.</p>"

  (defund-inline maybe-natp-fix (x)
    (declare (xargs :guard (maybe-natp x)))
    (mbe :logic (if x (nfix x) nil)
         :exec x))

  (local (in-theory (enable maybe-natp-fix)))

  (defthm maybe-natp-of-maybe-natp-fix
    (maybe-natp (maybe-natp-fix x))
    :rule-classes (:rewrite :type-prescription))

  (defthm maybe-natp-fix-when-maybe-natp
    (implies (maybe-natp x)
             (equal (maybe-natp-fix x) x)))

  (defthm maybe-natp-fix-under-iff
    (iff (maybe-natp-fix x) x))

  (defthm maybe-natp-fix-under-nat-equiv
    (acl2::nat-equiv (maybe-natp-fix x) x)
    :hints(("Goal" :in-theory (enable maybe-natp-fix)))))

(defsection maybe-nat-equiv
  :parents (fty::basetypes maybe-natp)
  :short "@('(maybe-natp-equiv x y)') is an equivalence relation for @(see
  maybe-natp)s, i.e., equality up to @(see maybe-natp-fix)."
  :long "<p>Performance note.  In the execution, this is just an inlined call
  of @(see eql).</p>"

  (fty::deffixtype maybe-nat
    :pred maybe-natp
    :fix maybe-natp-fix
    :equiv maybe-nat-equiv
    :define t
    :inline t
    :equal eql))


(defthm maybe-posp-when-posp
  ;; BOZO non-local, move to std/defs instead?
  (implies (posp x)
           (maybe-posp x)))

(defthmd posp-when-maybe-posp
  ;; BOZO non-local, move to std/defs instead?
  (implies (and (maybe-posp x)
                (double-rewrite x))
           (posp x)))


(defsection maybe-posp-fix
  :parents (fty::basetypes maybe-posp)
  :short "@(call maybe-posp-fix) is the identity for @(see maybe-posp)s, or
  coerces any non-@(see posp) to @('nil')."
  :long "<p>Performance note.  In the execution this is just an inlined
  identity function, i.e., it should have zero runtime cost.</p>"

  (defund-inline maybe-posp-fix (x)
    (declare (xargs :guard (maybe-posp x)))
    (mbe :logic (if x (pos-fix x) nil)
         :exec x))

  (local (in-theory (enable maybe-posp-fix)))

  (defthm maybe-posp-of-maybe-posp-fix
    (maybe-posp (maybe-posp-fix x))
    :rule-classes (:rewrite :type-prescription))

  (defthm maybe-posp-fix-when-maybe-posp
    (implies (maybe-posp x)
             (equal (maybe-posp-fix x) x)))

  (defthm maybe-posp-fix-under-iff
    (iff (maybe-posp-fix x) x))

  (defthm maybe-posp-fix-under-pos-equiv
    (acl2::pos-equiv (maybe-posp-fix x) x)
    :hints(("Goal" :in-theory (enable maybe-posp-fix)))))


(defsection maybe-pos-equiv
  :parents (fty::basetypes maybe-posp)
  :short "@('(maybe-posp-equiv x y)') is an equivalence relation for @(see
  maybe-posp)s, i.e., equality up to @(see maybe-posp-fix)."
  :long "<p>Performance note.  In the execution, this is just an inlined call
  of @(see eql).</p>"

  (fty::deffixtype maybe-pos
    :pred maybe-posp
    :fix maybe-posp-fix
    :equiv maybe-pos-equiv
    :define t
    :inline t
    :equal eql))


(defun fty::make-basetypes-table-rchars (table acc)
  (declare (xargs :mode :program))
  (b* (((when (atom table)) acc)
       ((fty::fixtype type) (cdar table))
       (row (concatenate 'string
                         "<tr><td><sf>" (string-downcase (symbol-name type.name)) "</sf></td>"
                         ;; BOZO, can't use xdoc::see here because of horrible dependency loop
                         "<td>@(see |" (symbol-package-name type.pred) "|::|" (symbol-name type.pred) "|)</td>"
                         "<td>@(see |" (symbol-package-name type.fix) "|::|" (symbol-name type.fix) "|)</td>"
                         "<td><tt>" (string-downcase (symbol-name type.equiv)) "</tt></td>"
                         "</tr>"))
       (acc (revappend (coerce row 'list) acc))
       (acc (cons #\Newline acc)))
    (fty::make-basetypes-table-rchars (cdr table) acc)))

(make-event
 (let* ((types (cdar (table-alist 'fty::fixtypes (w state))))
        (rows  (reverse (coerce (fty::make-basetypes-table-rchars (reverse types) nil) 'string))))
   `(defxdoc fty::basetypes
      :parents (fty::fty)
      :short "A book that associates many built-in ACL2 predicates with
suitable fixing functions and equivalence relations, for use in the @(see
fty::fty-discipline)."

      :long (concatenate
             'string
             "<p>The @('centaur/fty/basetypes') book provides basic support for
using many built-in ACL2 types with the FTY discipline.  It introduces any
necessary fixing functions and equivalences, and then sets up @(see
fty::deffixtype) associations between the recognizers, fixing functions, and
equivalence relations for the following types.</p>

<table>
<tr><th>Type Name</th> <th>Recognizer</th> <th>Fix</th> <th>Equiv</th></tr>" ,rows "</table>

<p>Note: all of these associations are made in the ACL2 package.</p>
"))))

; S-Expressions for 4-Valued Logic
; Copyright (C) 2010-2012 Centaur Technology
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
; Original authors: Sol Swords <sswords@centtech.com>
;                   Jared Davis <jared@centtech.com>

; nsexprs.lisp
;  - recognizers for sexprs with natural-numbered variables
;  - optimized version of 4v-sexpr-vars for these restricted sexprs

(in-package "ACL2")
(include-book "sexpr-vars")
(include-book "centaur/bitops/bitsets" :dir :system)
(include-book "centaur/bitops/sbitsets" :dir :system)
(include-book "arithmetic/nat-listp" :dir :system)

(local (in-theory (disable natp)))


(defthm nat-listp-of-insert-strong
  (implies (sets::setp x)
           (equal (nat-listp (sets::insert a x))
                  (and (natp a)
                       (nat-listp x))))
  :hints(("Goal" :in-theory (enable* (:ruleset sets::primitive-rules)))))

(defthm nat-listp-of-union-strong
  (implies (and (sets::setp x)
                (sets::setp y))
           (equal (nat-listp (sets::union x y))
                  (and (nat-listp x)
                       (nat-listp y))))
  :hints(("Goal"
          :in-theory (enable* (:ruleset sets::primitive-rules))
          :induct (sets::union x y))))


(defsection 4v-nsexpr-p
  :parents (4v-sexprs)
  :short "@(call 4v-nsexpr-p) recognizes s-expressions where every variable
is a natural number."

  :long "<p>We can develop a faster version of @(see 4v-sexpr-vars) by
requiring all of the variables in an s-expression to be natural numbers; see
@(see 4v-nsexpr-vars).</p>

<p>Memoized.  You should probably clear its table when you clear the tables for
@(see 4v-nsexpr-vars-nonsparse) or @(see 4v-nsexpr-vars-sparse).</p>

<p>We typically leave these disabled and reason about, e.g.,</p>

<code>
 (nat-listp (4v-sexpr-vars x))
</code>"

  (mutual-recursion
   (defund 4v-nsexpr-p (x)
     (declare (xargs :guard t))
     (if (atom x)
         (or (not x)
             (natp x))
       (4v-nsexpr-list-p (cdr x))))

   (defund 4v-nsexpr-list-p (x)
     (declare (xargs :guard t))
     (if (atom x)
         t
       (and (4v-nsexpr-p (car x))
            (4v-nsexpr-list-p (cdr x))))))

  (memoize '4v-nsexpr-p
           :condition '(and (consp x) (consp (cdr x))))

  (local (in-theory (enable 4v-nsexpr-p
                            4v-nsexpr-list-p)))

  (defthm-4v-sexpr-flag
    (defthm 4v-nsexpr-p-when-nat-listp-4v-sexpr-vars
      (equal (4v-nsexpr-p x)
             (nat-listp (4v-sexpr-vars x)))
      :flag sexpr)
    (defthm 4v-nsexpr-list-p-when-nat-listp-4v-sexpr-vars-list
      (equal (4v-nsexpr-list-p x)
             (nat-listp (4v-sexpr-vars-list x)))
      :flag sexpr-list)))



(defsection 4v-nsexpr-alist-p
  :parents (4v-nsexpr-p)
  :short "@(call 4v-nsexpr-p) recognizes an alist where every value is
an @(see 4v-nsexpr-p)."

;; BOZO use cutil::defalist?

  (defun 4v-nsexpr-alist-p (x)
    "Alist whose values are sexprs with natp variables."
    (declare (xargs :guard t))
    (or (atom x)
        (and (consp (car x))
             ;; (natp (caar x))
             (4v-nsexpr-p (cdar x))
             (4v-nsexpr-alist-p (cdr x)))))

  (defthm 4v-nsexpr-p-sexpr-fix-lookup-in-sexpr-alistp
    (implies (and (4v-nsexpr-alist-p x)
                  (hons-assoc-equal k x))
             (nat-listp (4v-sexpr-vars (cdr (hons-assoc-equal k x))))))

  (defthm 4v-nsexpr-alist-p-fal-extract
    (implies (4v-nsexpr-alist-p x)
             (4v-nsexpr-alist-p (fal-extract keys x)))
    :hints(("Goal" :in-theory (enable fal-extract)))))



(defsection 4v-nsexpr-p-4v-sexpr-restrict
  :parents (4v-nsexpr-p 4v-sexpr-restrict)

  (defthm-4v-sexpr-flag
    (defthm 4v-nsexpr-p-4v-sexpr-restrict
      (implies (and (4v-nsexpr-alist-p al)
                    (4v-nsexpr-p x))
               (nat-listp (4v-sexpr-vars (4v-sexpr-restrict x al))))
      :flag sexpr)

    (defthm 4v-nsexpr-list-p-4v-sexpr-restrict-list
      (implies (and (4v-nsexpr-alist-p al)
                    (4v-nsexpr-list-p x))
               (nat-listp (4v-sexpr-vars-list (4v-sexpr-restrict-list x al))))
      :flag sexpr-list)))


(defsection 4v-nsexpr-p-4v-sexpr-compose
  :parents (4v-nsexpr-p 4v-sexpr-compose)

  (defthm-4v-sexpr-flag
    (defthm 4v-nsexpr-p-4v-sexpr-compose
      (implies (4v-nsexpr-alist-p al)
               (nat-listp (4v-sexpr-vars (4v-sexpr-compose x al))))
      :flag sexpr)

    (defthm 4v-nsexpr-list-p-4v-sexpr-compose-list
      (implies (4v-nsexpr-alist-p al)
               (nat-listp (4v-sexpr-vars-list (4v-sexpr-compose-list x al))))
      :flag sexpr-list))

  (defthm 4v-nsexpr-alist-p-4v-sexpr-compose-alist
    (implies (4v-nsexpr-alist-p al)
             (4v-nsexpr-alist-p (4v-sexpr-compose-alist x al)))))



(defsection 4v-nsexpr-vars-nonsparse
  :parents (4v-nsexpr-vars)
  :short "Non-sparse version."
  :long "<p>Don't use this directly; use @(see 4v-nsexpr-vars) instead.</p>"

  (mutual-recursion
   (defun 4v-nsexpr-vars-nonsparse (x)
     (declare (xargs :guard (4v-nsexpr-p x)))
     (if (atom x)
         (if x (bitset-singleton x) 0)
       (4v-sexpr-vars-list-mask-nonsparse (cdr x))))

   (defun 4v-sexpr-vars-list-mask-nonsparse (x)
     (declare (xargs :guard (4v-nsexpr-list-p x)))
     (if (atom x)
         0
       (bitset-union (4v-nsexpr-vars-nonsparse (car x))
                     (4v-sexpr-vars-list-mask-nonsparse (cdr x))))))

  (memoize '4v-nsexpr-vars-nonsparse
           :condition '(and (consp x) (consp (cdr x))))

  (defthm-4v-sexpr-flag
    (defthm bitset-members-4v-nsexpr-vars-nonsparse
      (implies (4v-nsexpr-p x)
               (equal (bitset-members (4v-nsexpr-vars-nonsparse x))
                      (4v-sexpr-vars x)))
      :flag sexpr)

    (defthm bitset-members-4v-sexpr-vars-list-mask-nonsparse
      (implies (4v-nsexpr-list-p x)
               (equal (bitset-members (4v-sexpr-vars-list-mask-nonsparse x))
                      (4v-sexpr-vars-list x)))
      :flag sexpr-list)))



(defsection 4v-nsexpr-vars-sparse
  :parents (4v-nsexpr-vars)
  :short "Sparse version."
  :long "<p>Don't use this directly; use @(see 4v-nsexpr-vars) instead.</p>"

  (mutual-recursion
   (defun 4v-nsexpr-vars-sparse (x)
     (declare (xargs :guard (4v-nsexpr-p x)
                     :verify-guards nil))
     (if (atom x)
         (if x (sbitset-singleton x) nil)
       (4v-sexpr-vars-list-mask-sparse (cdr x))))

   (defun 4v-sexpr-vars-list-mask-sparse (x)
     (declare (xargs :guard (4v-nsexpr-list-p x)))
     (if (atom x)
         nil
       (sbitset-union (4v-nsexpr-vars-sparse (car x))
                      (4v-sexpr-vars-list-mask-sparse (cdr x))))))

  (defthm-4v-sexpr-flag
    (defthm sbitsetp-of-4v-nsexpr-vars-sparse
      (sbitsetp (4v-nsexpr-vars-sparse x))
      :flag sexpr)
    (defthm bitset-members-4v-sexpr-vars-list-mask-sparse
      (sbitsetp (4v-sexpr-vars-list-mask-sparse x))
      :flag sexpr-list))

  (verify-guards 4v-nsexpr-vars-sparse)

  (memoize '4v-nsexpr-vars-sparse
           :condition '(and (consp x) (consp (cdr x))))

  (defthm-4v-sexpr-flag
    (defthm sbitset-members-4v-nsexpr-vars-sparse
      (implies (4v-nsexpr-p x)
               (equal (sbitset-members (4v-nsexpr-vars-sparse x))
                      (4v-sexpr-vars x)))
      :flag sexpr)
    (defthm sbitset-members-4v-sexpr-vars-list-mask-sparse
      (implies (4v-nsexpr-list-p x)
               (equal (sbitset-members (4v-sexpr-vars-list-mask-sparse x))
                      (4v-sexpr-vars-list x)))
      :flag sexpr-list)))


(defsection 4v-nsexpr-vars
  :parents (4v-sexpr-vars)
  :short "Optimized version of @(see 4v-sexpr-vars) for sexprs whose variables
are natural numbers."

  :long "<p><tt>(4v-nsexpr-vars x)</tt> is logically just @(see 4v-sexpr-vars).
However, its guard requires that all variables in the sexpr are natural
numbers; see @(see 4v-nsexpr-p).</p>

<p>In the execution, we use a strategy that is quite similar to the ordinary
<tt>4v-sexpr-vars</tt> function: we memoize the entire computation and build
variable sets for every sexpr subexpression.  But, instead of using ordered
lists of variables, we use either @(see bitsets) or <see topic='@(url
sbitsets)'>sparse bitsets</see> as our set representation.  This turns out to
make a very significant performance difference.</p>

<p>By default we use sparse bitsets since in our experiments they appear to
significantly outperform ordinary bitsets when dealing with large modules.
However, you can instead choose to use ordinary bitsets by running:</p>

<code>
 (4v-nsexpr-vars x :sparsep nil)
</code>

<p>The real computation is done by @(see 4v-nsexpr-vars-sparse) or by @(see
4v-nsexpr-vars-nonsparse).  You will probably want to clear the memo tables for
these functions occasionally.  You may also need to clear the table for @(see
4v-nsexpr-vars) unless your guards are strong enough to ensure it will not be
called.</p>"

  (defun 4v-nsexpr-vars-fn (x sparsep)
    (declare (xargs :guard (4v-nsexpr-p x)))
    (mbe :logic (4v-sexpr-vars x)
         :exec (if sparsep
                   (sbitset-members (4v-nsexpr-vars-sparse x))
                 (bitset-members (4v-nsexpr-vars-nonsparse x)))))

  (defmacro 4v-nsexpr-vars (x &key (sparsep 't))
    `(4v-nsexpr-vars-fn ,x ,sparsep))

  (add-macro-alias 4v-nsexpr-vars 4v-nsexpr-vars-fn))


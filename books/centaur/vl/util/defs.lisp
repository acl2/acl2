; VL Verilog Toolkit
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

(in-package "VL")

; defs.lisp
;
; This book is for definitions of general concepts.  Hopefully much of this
; can eventually be moved into proper libraries.
;
; This book is non-locally included.  Because of this, do NOT put theorems
; about general concepts which the ordinary ACL2 user may have written
; other, conflicting theorems about.

(include-book "cutil/top" :dir :system)
(include-book "tools/defconsts" :dir :system)
(include-book "std/ks/two-nats-measure" :dir :system)
(include-book "std/lists/list-defuns" :dir :system)
(include-book "centaur/bitops/integer-length" :dir :system)
(include-book "centaur/misc/alist-equiv" :dir :system)
(include-book "centaur/misc/hons-extra" :dir :system)
(include-book "str/top" :dir :system)
(include-book "str/fast-cat" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))
(local (include-book "data-structures/list-defthms" :dir :system))


(defxdoc utilities
  :parents (vl)
  :short "Generic utilities that are unrelated to Verilog processing, but which
are provided by the VL books.")

(defxdoc transforms
  :parents (vl)
  :short "High-level transformations for rewriting and simplifying Verilog
modules.")

(defxdoc mlib
  :parents (vl)
  :short "<b>M</b>odule <b>Lib</b>rary -- A collection of various functions for
working with Verilog modules.")



(defsection *nls*
  :parents (utilities)
  :short "A string consisting of a newline character."

  (defconst *nls*
    (coerce (list #\Newline) 'string)))


(define same-lengthp (x y)
  :parents (utilities)
  :short "Efficiently checks if two lists have the same length."

  :long "<p>In the logic this is just @('(equal (len x) (len y))').  But for
faster execution we walk down both lists together so that we can terminate
early.</p>

<p>We leave @('same-lengthp') enabled, and reason about @('len') instead.</p>"

  :enabled t

  (mbe :logic (equal (len x) (len y))
       :exec (if (consp x)
                 (and (consp y)
                      (same-lengthp (cdr x) (cdr y)))
               (not (consp y)))))


(define redundant-mergesort
  (x &key
     (warnp booleanp "print warnings when @('x') is not sorted?")
     (from symbolp   "context to help track down warnings."))
  :parents (utilities)
  :short "Same as @('mergesort'), but avoids re-sorting lists that are already
sorted."

  :long "<p>In the logic, @('(redundant-mergesort x)') is just @('(mergesort
x)').  But in the execution, it first checks to see if @('x') is already
sorted, and if so returns @('x') unchanged.</p>

<p>I use this function when I do not want to go to the trouble of proving that
some cons-based operation happens to produce a set.  In practice, this should
be much faster than a mergesort because checking @('(setp x)') is linear and
requires no consing.</p>

<p>By default, @('redundant-mergesort') is silent and will simply sort its
argument if necessary.  However, you can also instruct it to emit warnings.  A
typical example is:</p>

@({
 (defun my-function (x)
    (let ((x-sort (redundant-mergesort x :warnp t :from 'my-function)))
       ...))
})"

  :enabled t

  (mbe :logic
       (mergesort x)
       :exec
       (if (setp x)
           x
         (prog2$
          (cond ((and warnp from)
                 (cw "; Redundant-mergesort given unsorted list by ~s0.~%" from))
                (warnp
                 (cw "; Redundant-mergesort given unsorted list.~%"))
                (t
                 nil))
          (mergesort x)))))


(define vl-maybe-integerp (x)
  :parents (utilities)
  :short "Recognizer for integers and @('nil')."
  :long "<p>This is like an option type, where either there is some integer
value or nothing.</p>"
  :inline t
  (or (not x)
      (integerp x))
  ///
  (defrule vl-maybe-integerp-compound-recognizer
    (equal (vl-maybe-integerp x)
           (or (integerp x)
               (not x)))
    :rule-classes :compound-recognizer))


(define vl-maybe-natp (n)
  :parents (utilities)
  :short "Recognizer for naturals and @('nil')."
  :long "<p>This is like an option type, where either there is some natural
number value or nothing.</p>"
  :inline t
  (or (not n)
      (natp n))
  ///
  (defrule vl-maybe-natp-compound-recognizer
    (equal (vl-maybe-natp x)
           (or (not x)
               (natp x)))
    :rule-classes :compound-recognizer))


(define vl-maybe-posp (x)
  :parents (utilities)
  :short "Recognizer for positive naturals and @('nil')."
  :long "<p>This is like an option type, where either there is some positive,
natural number value or nothing.</p>"
  :inline t
  (or (not x)
      (posp x))
  ///
  (defrule vl-maybe-posp-compound-recognizer
    (equal (vl-maybe-posp x)
           (or (and (integerp x)
                    (< 0 x))
               (not x)))
    :rule-classes :compound-recognizer))


(define vl-maybe-string-p (x)
  ;; BOZO name consistency with other functions here
  :parents (utilities)
  :short "Recognizer for strings and @('nil')."
  :long "<p>This is like an option type, where either there is some string
value or nothing.</p>"
  :inline t
  (or (not x)
      (stringp x))
  ///
  (defrule vl-maybe-string-p-compound-recognizer
    (equal (vl-maybe-string-p x)
           (or (not x)
               (stringp x)))
    :rule-classes :compound-recognizer))


(deflist nat-listp (x)
  (natp x)
  :elementp-of-nil nil
  :parents (utilities))


(deflist vl-maybe-nat-listp (x)
  (vl-maybe-natp x)
  :elementp-of-nil t
  :parents (utilities)
  :rest
  ((defrule nat-listp-when-no-nils-in-vl-maybe-nat-listp
     (implies (and (not (member-equal nil x))
                   (vl-maybe-nat-listp x))
              (nat-listp x)))))


(deflist vl-maybe-string-listp (x)
  (vl-maybe-string-p x)
  :elementp-of-nil t
  :parents (utilities)
  :rest
  ((defrule string-listp-when-no-nils-in-vl-maybe-string-listp
     (implies (and (not (member-equal nil x))
                   (vl-maybe-string-listp x))
              (equal (string-listp x)
                     (true-listp x))))))



(defsection debuggable-and
  :parents (utilities)
  :short "Alternative to @('and') that prints a message where it fails."

  :long "<p>@('(debuggable-and ...)') is the same as @('(and ...)'), but prints
a message when any of the conjuncts fails.  For instance,</p>

@({
VL !>(debuggable-and (natp 3)
                     (symbolp 'foo)
                     (consp 4)
                     (symbolp 'bar))
Debuggable-and failure: (CONSP 4).
NIL
VL !>
})

<p>This can be useful when writing unit tests, checking guards, etc.</p>"

  (defun debuggable-and-fn (args)
    (cond ((atom args)
           t)
          (t
           `(and (or ,(car args)
                     (cw "Debuggable-and failure: ~x0.~%" ',(car args)))
                 ,(debuggable-and-fn (cdr args))))))

  (defmacro debuggable-and (&rest args)
    (debuggable-and-fn args)))



(define make-lookup-alist (x)
  :parents (utilities)
  :short "Make a fast-alist for use with @(see fast-memberp)."

  :long "<p>@(call make-lookup-alist) produces a fast-alist binding every
member of @('x') to @('t').</p>

<p>Constructing a lookup alist allows you to use @(see fast-memberp) in lieu of
@(see member) or @(see member-equal), which may be quite a lot faster on large
lists.</p>

<p>Don't forget to free the alist after you are done using it, via @(see
fast-alist-free).</p>"

  (if (consp x)
      (hons-acons (car x)
                  t
                  (make-lookup-alist (cdr x)))
    nil)

  :returns (ans alistp)

  ///
  (defrule hons-assoc-equal-of-make-lookup-alist
    (iff (hons-assoc-equal a (make-lookup-alist x))
         (member-equal a (double-rewrite x))))

  (defrule consp-of-make-lookup-alist
    (equal (consp (make-lookup-alist x))
           (consp x)))

  (defrule make-lookup-alist-under-iff
    (iff (make-lookup-alist x)
         (consp x)))

  (defrule strip-cars-of-make-lookup-alist
    (equal (strip-cars (make-lookup-alist x))
           (list-fix x)))

  (defrule alist-keys-of-make-lookup-alist
    (equal (alist-keys (make-lookup-alist x))
           (list-fix x))))



(define fast-memberp (a x (alist (equal alist (make-lookup-alist x))))
  :parents (utilities)
  :short "Fast list membership using @(see make-lookup-alist)."

  :long "<p>In the logic, @(call fast-memberp) is just a list membership check;
we leave @('fast-memberp') enabled and always reason about @('member-equal')
instead.</p>

<p>However, our guard requires that @('alist') is the result of running @(see
make-lookup-alist) on @('x').  Because of this, in the execution, the call of
@(see member-equal) call is instead carried out using @(see hons-get) on the
alist, and hence is a hash table lookup.</p>"

  :inline t
  :enabled t

  (mbe :logic (if (member-equal a x) t nil)
       :exec (if (hons-get a alist) t nil)))


(define all-equalp (a x)
  :parents (utilities)
  :short "@(call all-equalp) determines if every members of @('x') is equal to
@('a')."

  :long "<p>In the logic, we define @('all-equalp') in terms of
@('repeat').</p>

<p>We usually leave this enabled and prefer to reason about @('repeat')
instead.  On the other hand, we also sometimes disable it and reason about it
recursively, so we do prove a few theorems about it.</p>

<p>For better execution speed, we use a recursive definition that does no
consing.</p>"
  :enabled t

  (mbe :logic
       (equal (list-fix x) (repeat a (len x)))
       :exec
       (if (consp x)
           (and (equal a (car x))
                (all-equalp a (cdr x)))
         t))

  :guard-hints(("Goal" :in-theory (enable all-equalp repeat)))

  ///
  (defrule all-equalp-when-atom
    (implies (atom x)
             (all-equalp a x)))

  (defrule all-equalp-of-cons
    (equal (all-equalp a (cons b x))
           (and (equal a b)
                (all-equalp a x)))
    :enable repeat)

  (local (in-theory (disable all-equalp)))

  (defrule car-when-all-equalp
    (implies (all-equalp a x)
             (equal (car x)
                    (if (consp x) a nil))))

  (defrule all-equalp-of-cdr-when-all-equalp
    (implies (all-equalp a x)
             (all-equalp a (cdr x))))

  (defrule all-equalp-of-append
    (equal (all-equalp a (append x y))
           (and (all-equalp a x)
                (all-equalp a y)))
    :induct (len x))

  (defrule all-equalp-of-rev
    (equal (all-equalp a (rev x))
           (all-equalp a x))
    :induct (len x))

  (defrule all-equalp-of-repeat
    (equal (all-equalp a (repeat b n))
           (or (equal a b)
               (zp n)))
    :enable repeat)

  (defrule all-equalp-of-take
    (implies (all-equalp a x)
             (equal (all-equalp a (take n x))
                    (or (not a)
                        (<= (nfix n) (len x)))))
    :enable acl2::take-redefinition)

  (defrule all-equalp-of-nthcdr
    (implies (all-equalp a x)
             (all-equalp a (nthcdr n x)))
    :enable nthcdr)

  (defrule member-equal-when-all-equalp
    (implies (all-equalp a x)
             (iff (member-equal b x)
                  (and (consp x)
                       (equal a b))))
    :induct (len x)))



(define remove-equal-without-guard (a x)
  :parents (utilities)
  :short "Same as @('remove-equal'), but doesn't require @('true-listp')."
  :long "<p>In the logic, we define this function as @('remove-equal') and we
leave it enabled.  You should never reason about it directly; reason about
@('remove-equal') instead.</p>"
  :enabled t

  (mbe :logic (remove-equal a x)
       :exec (cond ((atom x)
                    nil)
                   ((equal a (car x))
                    (remove-equal-without-guard a (cdr x)))
                   (t
                    (cons (car x) (remove-equal-without-guard a (cdr x)))))))


(define all-have-len (x n)
  :parents (utilities)
  :short "@(call all-have-len) determines if every element of @('x') has length
@('n')."

  (if (consp x)
      (and (eql (len (car x)) n)
           (all-have-len (cdr x) n))
    t)

  ///
  (defrule all-have-len-when-not-consp
    (implies (not (consp x))
             (all-have-len x n)))

  (defrule all-have-len-of-cons
    (equal (all-have-len (cons a x) n)
           (and (equal (len a) n)
                (all-have-len x n))))

  (defrule all-have-len-of-strip-cdrs
    (implies (and (not (zp n))
                  (all-have-len x n))
             (all-have-len (strip-cdrs x) (1- n)))
    :enable len)

  (defrule alistp-when-all-have-len
    (implies (and (not (zp n))
                  (all-have-len x n))
             (equal (alistp x)
                    (true-listp x)))))


(define remove-from-alist (key (alist alistp))
  :returns (ans alistp :hyp :fguard)
  :parents (utilities)
  :short "@(call remove-from-alist) removes all bindings for @('key') from
@('alist')."

  (cond ((atom alist)
         nil)
        ((equal key (caar alist))
         (remove-from-alist key (cdr alist)))
        (t
         (cons (car alist)
               (remove-from-alist key (cdr alist)))))
  ///
  (defrule remove-from-alist-when-not-consp
    (implies (not (consp alist))
             (equal (remove-from-alist key alist)
                    nil)))

  (defrule remove-from-alist-of-cons
    (equal (remove-from-alist key (cons a x))
           (if (equal key (car a))
               (remove-from-alist key x)
             (cons a (remove-from-alist key x))))))


(define vl-remove-keys ((keys true-listp) x)
  :returns (ans alistp)
  :parents (utilities)
  :short "@(call vl-remove-keys) removes all bindings for the given @('keys')
from @('alist')."

  :long "<p><b>BOZO</b> name consistency with @(see remove-from-alist).</p>"

  (cond ((atom x)
         nil)
        ((atom (car x))
         ;; bad alist convention
         (vl-remove-keys keys (cdr x)))
        ((member-equal (caar x) keys)
         (vl-remove-keys keys (cdr x)))
        (t
         (cons (car x) (vl-remove-keys keys (cdr x)))))
  ///
  (defrule vl-remove-keys-when-not-consp
    (implies (not (consp x))
             (equal (vl-remove-keys keys x)
                    nil)))

  (defrule vl-remove-keys-of-cons
    (equal (vl-remove-keys keys (cons a x))
           (if (atom a)
               (vl-remove-keys keys x)
             (if (member-equal (car a) (double-rewrite keys))
                 (vl-remove-keys keys x)
               (cons a (vl-remove-keys keys x))))))

  (defrule true-listp-of-vl-remove-keys
    (true-listp (vl-remove-keys keys x))
    :rule-classes :type-prescription)

  (defrule consp-of-car-of-vl-remove-keys
    (equal (consp (car (vl-remove-keys keys x)))
           (consp (vl-remove-keys keys x))))

  (defrule acl2-count-of-vl-remove-keys
    (<= (acl2-count (vl-remove-keys keys x))
        (acl2-count x))
    :rule-classes ((:rewrite) (:linear))
    :enable acl2-count))


(define redundant-list-fix (x)
  :parents (utilities)
  :short "@(call redundant-list-fix) is the same as @('(list-fix x)'), but
avoids consing when @('x') is already a true-listp."

  :long "<p>I sometimes want to @('list-fix') something that I know is almost
certainly already a @('true-listp') in practice.  In such cases,
@('redundant-list-fix') may be a better choice than @('list-fix'), because
checking @('true-listp') is much cheaper than re-consing the a list.</p>

<p>I leave this function enabled.  Logically it is just an alias for
@('list-fix'), so you should never need to reason about it.</p>"

  :enabled t

  (mbe :logic (list-fix x)
       :exec (if (true-listp x)
                 x
               (list-fix x))))


(deflist string-list-listp (x)
  (string-listp x)
  :guard t
  :elementp-of-nil t
  :parents (utilities))


;; BOZO er --- why are these not in arithmetic??
(defrule prefixp-of-self
  (prefixp x x)
  :enable prefixp)

(defrule transitivity-of-prefixp
  (implies (and (prefixp x y)
                (prefixp y z))
           (prefixp x z))
  :enable prefixp)



(define longest-common-prefix (x y)
  :parents (utilities)
  :short "@(call longest-common-prefix) returns the longest list, @('p'), such
that @('p') is a prefix of both @('x') and @('y'), in the sense of
@('prefixp')."

  :long "<p>See also @(see longest-common-prefix-list), which extends this
function to a list of lists.</p>"

  (cond ((or (atom x)
             (atom y))
         nil)
        ((equal (car x) (car y))
         (cons (car x)
               (longest-common-prefix (cdr x) (cdr y))))
        (t
         nil))
  ///
  (defrule true-listp-of-longest-common-prefix
    (true-listp (longest-common-prefix x y))
    :rule-classes :type-prescription)

  (defrule string-listp-of-longest-common-prefix
    (implies (and (string-listp x)
                  (string-listp y))
             (string-listp (longest-common-prefix x y))))

  (defrule longest-common-prefix-of-list-fix-left
    (equal (longest-common-prefix (list-fix x) y)
           (longest-common-prefix x y)))

  (defrule longest-common-prefix-of-list-fix-right
    (equal (longest-common-prefix x (list-fix y))
           (longest-common-prefix x y)))

  (defrule prefixp-of-longest-common-prefix-left
    (prefixp (longest-common-prefix x y) x))

  (defrule prefixp-of-longest-common-prefix-right
    (prefixp (longest-common-prefix x y) y))

  (defrule longest-common-prefix-preserves-prefixp
    (implies (prefixp p a)
             (prefixp (longest-common-prefix p b) a))
    :enable prefixp))


(deflist prefix-of-eachp (p x)
  (prefixp p x)
  :guard t
  :parents (utilities)
  :short "@(call prefix-of-eachp) returns true exactly when @('p') is a
prefix of every member of @('x')."
  :rest
  ((defrule prefix-of-eachp-when-prefixp
     (implies (and (prefix-of-eachp a x)
                   (prefixp b a))
              (prefix-of-eachp b x)))

   (defrule prefix-of-eachp-when-prefixp-alt
     (implies (and (prefixp b a)
                   (prefix-of-eachp a x))
              (prefix-of-eachp b x)))))



(define longest-common-prefix-list (x)
  :parents (utilities)
  :short "@(call longest-common-prefix-list) returns the longest list, @('p'),
such that @('p') is a prefix of every list in @('x')."
  :long "<p>See also @(see longest-common-prefix).</p>"

  (cond ((atom x)
         nil)
        ((atom (cdr x))
         (list-fix (car x)))
        (t
         (longest-common-prefix (first x)
                                (longest-common-prefix-list (cdr x)))))

  ///
  (defrule true-listp-of-longest-common-prefix-list
    (true-listp (longest-common-prefix-list x))
    :rule-classes :type-prescription)

  (defrule string-listp-of-longest-common-prefix-list
    (implies (string-list-listp x)
             (string-listp (longest-common-prefix-list x))))

  (defrule longest-common-prefix-list-of-list-fix
    (equal (longest-common-prefix-list (list-fix x))
           (longest-common-prefix-list x)))

  (defrule prefix-of-eachp-of-longest-common-prefix-list
    (prefix-of-eachp (longest-common-prefix-list x) x)))


(define string-fix ((x stringp))
  :parents (utilities)
  :short "@(call string-fix) is the identity function for strings."
  :long "<p>Note that we leave this function enabled.</p>"
  :enabled t
  :inline t

  (mbe :logic (if (stringp x) x "")
       :exec x)

  ///
  (defrule stringp-of-string-fix
    (stringp (string-fix x))
    :rule-classes :type-prescription))



(defprojection symbol-list-names (x)
  (symbol-name x)
  :guard (symbol-listp x)
  :result-type string-listp
  :parents (utilities))


(defsection look-up-each

  ;; BOZO find me a home

  ;; (look-up-each (list a b c ...) alist)
  ;;    -->
  ;; (list (cdr (hons-assoc-equal a alist))
  ;;       (cdr (hons-assoc-equal b alist))
  ;;       (cdr (hons-assoc-equal c alist))
  ;;       ...)

  (defund look-up-each-fast (x fast-alist)
    (declare (xargs :guard t))
    (if (atom x)
        nil
      (let ((lookup (hons-get (car x) fast-alist)))
        (cons (if lookup
                  (cdr lookup)
                (er hard? 'look-up-each-fast "expected ~x0 to be bound.~%" (car x)))
              (look-up-each-fast (cdr x) fast-alist)))))

  (defund look-up-each (x alist)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic (if (atom x)
                    nil
                  (cons (cdr (hons-assoc-equal (car x) alist))
                        (look-up-each (cdr x) alist)))
         :exec
         (b* ((fal (make-fal alist (len alist)))
              (ret (look-up-each-fast x fal))
              (-   (fast-alist-free fal)))
           ret)))

  (local (in-theory (enable look-up-each look-up-each-fast)))

  (defrule look-up-each-fast-redefinition
    (equal (look-up-each-fast x alist)
           (look-up-each x alist)))

  (local (defrule l0
           (equal (hons-assoc-equal a (make-fal x y))
                  (or (hons-assoc-equal a x)
                      (hons-assoc-equal a y)))))

  (local (defrule l1
           (implies (atom tail)
                    (equal (look-up-each x (make-fal alist tail))
                           (look-up-each x alist)))))

  (verify-guards look-up-each)

  (defrule look-up-each-of-atom
    (implies (atom x)
             (equal (look-up-each x alist)
                    nil)))

  (defrule look-up-each-of-cons
    (equal (look-up-each (cons a x) alist)
           (cons (cdr (hons-assoc-equal a alist))
                 (look-up-each x alist))))

  (defrule true-listp-of-look-up-each
    (true-listp (look-up-each x alist))
    :rule-classes :type-prescription)

  (defrule len-of-look-up-each
    (equal (len (look-up-each x alist))
           (len x)))

  (defrule look-up-each-of-list-fix
    (equal (look-up-each (list-fix x) alist)
           (look-up-each x alist)))

  (defrule look-up-each-of-append
    (equal (look-up-each (append x y) alist)
           (append (look-up-each x alist)
                   (look-up-each y alist))))

  (defrule look-up-each-of-rev
    (equal (look-up-each (rev x) alist)
           (rev (look-up-each x alist))))

  (defrule symbol-listp-of-look-up-each
    (implies (symbol-listp (strip-cdrs alist))
             (symbol-listp (look-up-each x alist)))
    :hints(("Goal" :in-theory (enable hons-assoc-equal)))))


(deflist symbol-list-listp (x)
  (symbol-listp x)
  :guard t
  :elementp-of-nil t
  :parents (utilities))


(define vl-starname ((name stringp))
  :parents (utilities)
  :short "@(call vl-starname) is given a string, say @('\"foo\"'), and return a
symbol in the ACL2 package, e.g., @('ACL2::*foo*')."

  :long "<p>Such names are the convention for naming modules in E.</p>"

  (intern-in-package-of-symbol
   (coerce (cons #\* (str::append-chars name (list #\*))) 'string)
   'ACL2::foo)

  ///

  (defrule symbolp-of-vl-starname
    (symbolp (vl-starname name))
    :rule-classes :type-prescription))



(defsection longer-than-p
  :parents (utilities)
  :short "@(call longer-than-p) determines if the list @('x') is longer than
@('n')."

  :long "<p>This can be slightly faster than @('(len x)') when the list is long
and @('n') is small.  We leave this function enabled and reason about @('len')
instead.</p>"

  (local (defrule l0
           (equal (len (cdr x))
                  (if (consp x)
                      (+ -1 (len x))
                    0))))

  (defun longer-than-p (n x)
    (declare (xargs :guard (natp n)))
    (mbe :logic (< n (len x))
         :exec
         (cond ((zp n)
                (consp x))
               ((atom x)
                nil)
               (t
                (longer-than-p (+ -1 n) (cdr x)))))))


(deflist pos-listp (x)
  (posp x)
  :elementp-of-nil nil
  :parents (utilities))


(deflist true-list-listp (x)
  (true-listp x)
  :guard t
  :elementp-of-nil t
  :parents (utilities))




(defsection append-domains
  :parents (utilities)
  :short "@(call append-domains) appends all of the values from the alist
@('x') into a single list."

  :long "<p>Our guard is merely @('t'), but typically @('x') is an alist of
@('(key . value)') pairs where every @('value') is a list of elements.  We walk
through the alist, appending together all of the elements of each @('value')
into a single, flat list.</p>

<p>Note that we do not really treat @('x') as an association list.  That is, we
will include the values from any \"shadowed pairs\" in the list.</p>"

  (defund append-domains-exec (x acc)
    (declare (xargs :guard t))
    (mbe :logic
         (if (atom x)
             acc
           (append-domains-exec (cdr x)
                                (revappend (cdar x) acc)))
         :exec
         (cond ((atom x)
                acc)
               ((atom (car x))
                (append-domains-exec (cdr x) acc))
               (t
                (append-domains-exec (cdr x)
                                     (revappend-without-guard (cdar x) acc))))))

  (local (in-theory (enable append-domains-exec)))

  (local (defrule true-listp-of-append-domains-exec
           (implies (true-listp acc)
                    (equal (true-listp (append-domains-exec x acc))
                           t))
           :rule-classes :type-prescription))

  (defun append-domains (x)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom x)
             nil
           (append (cdar x) (append-domains (cdr x))))
         :exec (reverse (append-domains-exec x nil))))

  (local (in-theory (enable append-domains)))

  (defrule append-domains-exec-removal
    (equal (append-domains-exec x acc)
           (revappend (append-domains x) acc))
    :induct (append-domains-exec x acc))

  (verify-guards append-domains)

  (defrule append-domains-when-atom
    (implies (atom x)
             (equal (append-domains x)
                    nil)))

  (defrule append-domains-of-cons
    (equal (append-domains (cons a x))
           (append (cdr a) (append-domains x))))

  (defrule true-listp-of-append-domains
    (true-listp (append-domains x))
    :rule-classes :type-prescription)

  (defrule append-domains-of-append
    (equal (append-domains (append x y))
           (append (append-domains x) (append-domains y)))))



(define fast-alist-free-each-alist-val (x)
  :parents (utilities)
  :short "Applies @(see fast-alist-free) to every value bound in the alist x."
  :enabled t
  (mbe :logic nil
       :exec
       (cond ((atom x)
              nil)
             ((atom (car x))
              (fast-alist-free-each-alist-val (cdr x)))
             (t
              (prog2$ (fast-alist-free (cdar x))
                      (fast-alist-free-each-alist-val (cdr x)))))))


(define free-list-of-fast-alists (x)
  :parents (utilities)
  ;; BOZO very badly named, what does this free exactly?

  (declare (xargs :guard t))
  :enabled t
  (mbe :logic nil
       :exec
       (if (atom x)
           nil
         (prog2$ (fast-alist-free (car x))
                 (free-list-of-fast-alists (cdr x))))))



(define vl-plural-p (x)
  :parents (utilities)
  :short "@(call vl-plural-p) determines whether a description of a list should
be plural instead of singluar."

  :long "<p>Output sometimes needs to be customized depending on whether a list
contains only one element or many elements, e.g.,</p>

<ul>
 <li>Warning: foo, bar, and baz <b>are</b> mismatched <b>socks</b>, vs.</li>
 <li>Warning: foo <b>is a</b> mismatched <b>sock</b>.</li>
</ul>

<p>@(call vl-plural-p) is a stupid function to distinguish between the cases.
It returns true for a list like @('(foo bar baz)') with more than one element,
or false for a list like @('(foo)') with exactly one element.</p>

<p>We consider lists that have no elements to be plural.  This gives the proper
behavior in cases like:</p>

<ul>
 <li>0 <b>warnings</b> to report,</li>
 <li>1 <b>warning</b> to report,</li>
 <li>2 <b>warnings</b> to report,</li>
 <li>...</li>
</ul>"
  :inline t
  (mbe :logic (not (equal (len x) 1))
       :exec (or (atom x)
                 (not (atom (cdr x))))))



(defun tuplep (n x)
  (declare (xargs :guard (natp n)))
  (mbe :logic (and (true-listp x)
                   (equal (len x) n))
       :exec (and (true-listp x)
                  (eql (length x) n))))

(deflist cons-listp (x)
  (consp x)
  :elementp-of-nil nil)

(deflist cons-list-listp (x)
  (cons-listp x)
  :elementp-of-nil t)





(defsection and*
  :parents (utilities)
  :short "@('and*') is like @('and') but is a (typically disabled) function."

  :long "<p>This is occasionally useful for avoiding case-splitting in
theorems.</p>"

  (defund binary-and* (x y)
    (declare (xargs :guard t))
    (if x y nil))

  (defund and*-macro (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           t)
          ((atom (cdr x))
           (car x))
          (t
           `(binary-and* ,(car x)
                         ,(and*-macro (cdr x))))))

  (defmacro and* (&rest args)
    (and*-macro args))

  (add-binop and* binary-and*))



(defsection or*
  :parents (utilities)
  :short "@('or*') is like @('or') but is a (typically disabled) function."

  :long "<p>This is occasionally useful for avoiding case-splitting in
theorems.</p>"

  (defund binary-or* (x y)
    (declare (xargs :guard t))
    (if x x y))

  (defund or*-macro (x)
    (declare (xargs :guard t))
    (cond ((atom x)
           nil)
          ((atom (cdr x))
           (car x))
          (t
           `(binary-or* ,(car x)
                        ,(or*-macro (cdr x))))))

  (defmacro or* (&rest args)
    (or*-macro args))

  (add-binop or* binary-or*))


(defsection not*
  :parents (utilities)
  :short "@('not*') is like @('not') but is not built-in to ACL2 and is
typically disabled."

  :long "<p>This might occasionally be useful for avoiding case-splitting in
theorems.</p>"

  (defund not* (x)
    (declare (xargs :guard t))
    (not x)))




(defsection keys-boundp
  :parents (utilities)
  :short "@(call keys-boundp) determines if every key in @('keys') is bound in
the alist @('alist')."

  (defund keys-boundp-fal (keys alist)
    (declare (xargs :guard t))
    (if (atom keys)
        t
      (and (hons-get (car keys) alist)
           (keys-boundp-fal (cdr keys) alist))))

  (defund keys-boundp-slow-alist (keys alist)
    (declare (xargs :guard t))
    (if (atom keys)
        t
      (and (hons-assoc-equal (car keys) alist)
           (keys-boundp-slow-alist (cdr keys) alist))))

  (defund keys-boundp (keys alist)
    (declare (xargs :guard t :verify-guards nil))
    (mbe :logic
         (if (atom keys)
             t
           (and (hons-assoc-equal (car keys) alist)
                (keys-boundp (cdr keys) alist)))
         :exec
         (if (atom keys)
             t
           (if (and (acl2::worth-hashing keys)
                    (acl2::worth-hashing alist))
               (with-fast-alist alist (keys-boundp-fal keys alist))
             (keys-boundp-slow-alist keys alist)))))

  (local (in-theory (enable keys-boundp
                            keys-boundp-fal
                            keys-boundp-slow-alist)))

  (defrule keys-boundp-fal-removal
    (equal (keys-boundp-fal keys alist)
           (keys-boundp keys alist)))

  (defrule keys-boundp-slow-alist-removal
    (equal (keys-boundp-slow-alist keys alist)
           (keys-boundp keys alist)))

  (verify-guards keys-boundp)

  (defrule keys-boundp-when-atom
    (implies (atom keys)
             (equal (keys-boundp keys alist)
                    t)))

  (defrule keys-boundp-of-cons
    (equal (keys-boundp (cons a keys) alist)
           (and (hons-get a alist)
                (keys-boundp keys alist))))

  (defrule keys-boundp-of-list-fix
    (equal (keys-boundp (list-fix x) alist)
           (keys-boundp x alist)))

  (defrule keys-boundp-of-append
    (equal (keys-boundp (append x y) alist)
           (and (keys-boundp x alist)
                (keys-boundp y alist))))

  (defrule keys-boundp-of-rev
    (equal (keys-boundp (rev x) alist)
           (keys-boundp x alist)))

  (defrule keys-boundp-of-revappend
    (equal (keys-boundp (revappend x y) alist)
           (and (keys-boundp x alist)
                (keys-boundp y alist)))))

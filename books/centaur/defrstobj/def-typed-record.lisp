; Record Like Stobjs
; Copyright (C) 2011-2012 Centaur Technology
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

(in-package "RSTOBJ")
(include-book "typed-records")

(defsection def-typed-record
  :parents (defrstobj)
  :short "Introduce a typed record for use with @(see defrstobj)."

  :long "<p>A <b>typed record</b> is a record-like structure: it associates
keys with values, has a @('get') function to look up the value of some key, and
has a @('set') function to install some new value for some key.</p>

<p>Unlike an ordinary @('misc/record'), a typed record is homogeneous, i.e., we
unconditionally know: @({(foop (get a r))})  Meanwhile, the @('get') and
@('set') functions for a typed record are <b>almost</b> the same as for
ordinary records.  The only difference is that the @('g-same-s') theorem
becomes:</p>

@({
   (get a (set a v r)) = (foo-fix v)   ; instead of just being v
})

<p>The macro @('def-typed-record') can be used to introduce a new typed record
structure for use in @(see defrstobj) array fields.</p>


<h3>Usage</h3>

<p>You can use @('def-typed-record') to introduce the @('get-') and @('set-')
functions, the ordinary @('get-of-set') style theorems about them, and some
additional definitions such as a badguy for identifying differences between
typed records (which can be useful for pick-a-point style reasoning.)</p>

<h5>Example: typed record for naturals</h5>

@({
    (def-typed-record nat
      :elem-p (natp x)
      :elem-list-p (nat-listp x)
      :elem-default 0
      :elem-fix (nfix x))
})

<p>This introduces the recognizer function @('nat-tr-p'), the getter function
@('nat-tr-get'), the setter function @('nat-tr-set'), and related theorems.</p>

<h5>Example: typed-record for (8-bit) bytes</h5>

@({
   (defun ubp-listp (n x)
     (declare (xargs :guard t))
     (if (atom x)
         (not x)
       (and (unsigned-byte-p n (car x))
            (ubp-listp n (cdr x)))))

   (defun ubp-fix (n x)            ;; other fixing functions
     (declare (xargs :guard t))    ;; are also possible
     (if (unsigned-byte-p n x)
         x
       0))

   (def-typed-record ubp8
     :elem-p       (unsigned-byte-p 8 x)
     :elem-list-p  (ubp-listp 8 x)
     :elem-default 0
     :elem-fix     (ubp-fix 8 x))
})

<p>This produce @('ubp8-tr-p'), @('ubp8-tr-get'), @('ubp8-tr-set'), and related
theorems.</p>


<h5>General Form</h5>

@({
    (def-typed-record name
      :elem-p        [element recognizer, foop]
      :elem-list-p   [list recognizer, foo-listp]
      :elem-default  [default value, e.g., 0, nil, ...]
      :elem-fix      [fixing function, foo-fix]
      :in-package-of [symbol to use for new names])
})

<p>Note that the terms you use for @('elem-p') and so forth need to refer to
exactly the variable @('acl2::x').</p>


<h3>Related Work and History</h3>

<p>This version of typed records is very similar in spirit to the
@('coi/records/defrecord.lisp') book; see:</p>

<box><p>David Greve and Matthew Wilding.  <a
href='http://www.cs.utexas.edu/users/moore/acl2/workshop-2003/contrib/greve-wilding_defrecord/defrecord.ps'>Typed
ACL2 Records</a>. ACL2 Workshop 2003.</p></box>

<p>Greve and Wilding implemented typed records by starting with an ordinary
record, but instead of just storing values or fixed values into its slots, they
instead store ENTRIES of the form @('(FOO . NON-ENTRY)'), where the FOO must be
a foop that is not the default foop.</p>

<p>When developing rstobjs, I (Jared) started with Greve and Wilding's
approach; see @(see legacy-defrstobj).  But when I tried to extend their work
to be able to view a STOBJ array as a typed record, I ran into trouble.  I
didn't see a good way to prove something akin to @('equal-by-g'), and without
that it didn't seem easy to adapt the basic approach I'd developed for untyped
records to also deal with typed records.</p>

<p>I went to Sol's office to gripe about this, and we started to try to more
precisely understand what was problematic.  In a short time, we had come up
with a different way to implement typed records that seems to be much more
suitable.</p>

<p>In short, instead of using a @('misc/record') with some kind of special
entries, we directly develop a new kind of typed record where the well-formed
records are only allowed to have values of the proper type.  This lets us
nicely separate the bad part of the record (if any) from the good part, and
obtain a theorem in the spirit of @('EQUAL-BY-G').</p>")

(defun symbol-list-names (x)
  (declare (xargs :guard (symbol-listp x)))
  (if (atom x)
      nil
    (cons (symbol-name (car x))
          (symbol-list-names (cdr x)))))

(defmacro mksym (&rest args)
  `(intern-in-package-of-symbol
    (string-append-lst (symbol-list-names (list . ,args)))
    mksym-pkg))


(defun def-typed-record-fn
  (name          ; Prefix for all the names we'll generate

   elem-p        ; A term mentioning only X, the element recognizer
                 ;  e.g., (integerp x), or (unsigned-byte-p 8 x)

   elem-list-p   ; A term mentioning only X, the element list recognizer
                 ;  e.g., (integer-listp x)
                 ;  must recognize only true lists

   elem-default  ; A term with no free variables that is the default value
                 ;  e.g., nil, 0, (my-default), or similar.

   elem-fix      ; A term mentioning only X, the fixing function
                 ;  e.g., (nfix x), (ubp-fix 8 x), etc.

   in-package-of ; Package for names we'll generate

   )

  (let* ((mksym-pkg         in-package-of)
         (tr-p1             (mksym name '-tr-p1))
         (tr-p              (mksym name '-tr-p))
         (to-tr             (mksym name '-to-tr))
         (tr-bad-part       (mksym name '-tr-bad-part))
         (tr-get1           (mksym name '-tr-get1))
         (tr-set1           (mksym name '-tr-set1))
         (tr-get            (mksym name '-tr-get))
         (tr-set            (mksym name '-tr-set))
         (tr-badguy         (mksym name '-tr-badguy))
         (array-to-tr       (mksym name '-array-to-tr))
         (tr-to-array       (mksym name '-tr-to-array))
         (tr-delete-indices (mksym name '-tr-delete-indices))
         (array-rec-pair-p  (mksym name '-array-rec-pair-p))

         (fi-pairs    `((elem-p            (lambda (x) ,elem-p))
                        (elem-default      (lambda ()  ,elem-default))
                        (elem-fix          (lambda (x) ,elem-fix))
                        (elem-list-p       (lambda (x) ,elem-list-p))
                        (tr-p1             ,tr-p1)
                        (tr-p              ,tr-p)
                        (to-tr             ,to-tr)
                        (tr-bad-part       ,tr-bad-part)
                        (tr-get1           ,tr-get1)
                        (tr-set1           ,tr-set1)
                        (tr-get            ,tr-get)
                        (tr-set            ,tr-set)
                        (tr-badguy         ,tr-badguy)
                        (array-to-tr       ,array-to-tr)
                        (tr-to-array       ,tr-to-array)
                        (tr-delete-indices ,tr-delete-indices)
                        (array-rec-pair-p  ,array-rec-pair-p)))

         (booleanp-of-elem-p    (mksym 'booleanp-of-elem-p-for- tr-p))
         (elem-p-of-default     (mksym 'elem-p-of-default-for- tr-p))
         (elem-p-of-elem-fix    (mksym 'elem-p-of-elem-fix-for- tr-p))
         (elem-fix-idempotent   (mksym 'elem-fix-idempotent-for- tr-p))
         (elem-list-p-when-atom (mksym 'elem-list-p-when-atom-for- tr-p))
         (elem-list-p-of-cons   (mksym 'elem-list-p-of-cons-for- tr-p)))

    `(encapsulate
       ()
       (set-verify-guards-eagerness 2)
       (set-inhibit-warnings "non-rec" "subsume")
       (set-tau-auto-mode nil)
       ;; The user needs to be able to prove these in his current theory.

       (defthmd ,booleanp-of-elem-p
         (booleanp ,elem-p)
         :rule-classes :type-prescription)

       (defthmd ,elem-p-of-default
         ,(subst elem-default 'x elem-p)
         ;; Why the funny rule class?  As a rewrite rule this is fine
         ;; for things like (atom nil).  But ACL2 gets mad if you try
         ;; to write (symbolp nil) as a rewrite rule, or similar.
         :rule-classes :built-in-clause)

       (defthmd ,elem-p-of-elem-fix
         (let ((x ,elem-fix))
           ,elem-p))

       (defthmd ,elem-fix-idempotent
         (implies ,elem-p
                  (equal ,elem-fix x)))

       (defthmd ,elem-list-p-when-atom
         (implies (atom x)
                  (equal ,elem-list-p
                         (not x))))

       (defthmd ,elem-list-p-of-cons
         (equal ,(subst '(cons a x) 'x elem-list-p)
                (and ,(subst 'a 'x elem-p)
                     ,elem-list-p)))

       ;; We'll then try to do everything else in a basic theory, along
       ;; with the above rules.

       (local (in-theory (theory 'minimal-theory)))
       (local (in-theory (enable car-cons
                                 cdr-cons
                                 car-cdr-elim
                                 natp
                                 zp
                                 true-listp-update-nth
                                 posp
                                 len
                                 booleanp
                                 ,booleanp-of-elem-p
                                 ,elem-p-of-default
                                 ,elem-fix-idempotent
                                 ,elem-p-of-elem-fix
                                 ,elem-list-p-when-atom
                                 ,elem-list-p-of-cons)))

       ;; Main typed record definitions

       (defun ,tr-p1 (x)
         (or (null x)
             (and (consp x)
                  (consp (car x))
                  (,tr-p1 (cdr x))
                  ,(subst '(cdar x) 'x elem-p)
                  (not (equal (cdar x) ,elem-default))
                  (or (null (cdr x))
                      (<< (caar x) (caadr x))))))

       (defun ,tr-p (x)
         (and (consp x)
              (,tr-p1 (car x))
              (car x)
              (not (,tr-p (cdr x)))))

       (defun ,to-tr (x)
         (if (,tr-p x)
             x
           (cons nil x)))

       (defun ,tr-bad-part (r)
         (if (,tr-p r)
             (cdr r)
           r))

       (defun ,tr-get1 (k r)
         (declare (xargs :guard (,tr-p1 r)))
         (cond ((or (endp r)
                    (<< k (caar r)))
                ,elem-default)
               ((equal k (caar r))
                (cdar r))
               (t
                (,tr-get1 k (cdr r)))))

       (defun ,tr-set1 (k v r)
         (declare (xargs :guard (,tr-p1 r)))
         (cond ((or (endp r)
                    (<< k (caar r)))
                (if (equal v ,elem-default)
                    r
                  (cons (cons k v) r)))
               ((equal k (caar r))
                (if (equal v ,elem-default)
                    (cdr r)
                  (cons (cons k v) (cdr r))))
               (t
                (cons (car r) (,tr-set1 k v (cdr r))))))

       (defun ,tr-get (k r)
         (,tr-get1 k (car (,to-tr r))))

       (defun ,tr-set (k v r)
         (let* ((rec      (,to-tr r))
                (rec1     (car rec))
                (bad      (cdr rec))
                (new-rec1 (,tr-set1 k ,(subst 'v 'x elem-fix) rec1)))
           (if new-rec1
               (cons new-rec1 bad)
             bad)))

       (defun ,tr-badguy (x y)
         (declare (xargs :verify-guards nil))
         (tr-badguy1 (car (,to-tr x))
                     (car (,to-tr y))))

       ;; Record/array pair supporting definitions

       (defun ,array-to-tr (n arr rec)
         (declare (xargs :guard (and (natp n)
                                     (true-listp arr))))
         (if (zp n)
             rec
           (let ((n (- n 1)))
             (,array-to-tr n arr (,tr-set n (nth n arr) rec)))))

       (defun ,tr-to-array (n rec arr)
         (declare (xargs :guard (and (natp n)
                                     (true-listp arr))))
         (if (zp n)
             arr
           (let ((n (- n 1)))
             (,tr-to-array n rec (update-nth n (,tr-get n rec) arr)))))

       (defun ,tr-delete-indices (n rec)
         (declare (xargs :guard (natp n)))
         (if (zp n)
             rec
           (let ((n (- n 1)))
             (,tr-delete-indices n (,tr-set n ,elem-default rec)))))

       (defun ,array-rec-pair-p (arr rec len)
         (declare (xargs :guard (natp len)))
         (and ,(subst 'arr 'x elem-list-p)
              (= (len arr) len)
              (equal rec (,tr-delete-indices len rec))))


       (deflabel ,(mksym 'start-of- tr-p '-theorems))


       ;; Main typed record theorems

       (defthm ,(mksym 'elem-p-of- tr-get)
         ,(subst `(,tr-get a x) 'x elem-p)
         :hints(("Goal"
                 :use ((:functional-instance elem-p-of-tr-get
                                             . ,fi-pairs)))))

       (defthm ,(mksym tr-get '-of- tr-set '-same)
         (equal (,tr-get a (,tr-set a v r))
                ,(subst 'v 'x elem-fix))
         :hints(("Goal"
                 :use ((:functional-instance tr-get-of-tr-set-same
                                             . ,fi-pairs)))))

       (defthm ,(mksym tr-get '-of- tr-set '-diff)
         (implies (not (equal a b))
                  (equal (,tr-get a (,tr-set b v r))
                         (,tr-get a r)))
         :hints(("Goal" :use ((:functional-instance tr-get-of-tr-set-diff
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-set '-of- tr-get '-same)
         (equal (,tr-set a (,tr-get a r) r)
                r)
         :hints(("Goal" :use ((:functional-instance tr-set-of-tr-get-same
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-set '-of- tr-set '-diff)
         (implies (not (equal a b))
                  (equal (,tr-set b y (,tr-set a x r))
                         (,tr-set a x (,tr-set b y r))))
         ;; Otherwise ACL2 infers a bad loop stopper that considers the values
         ;; instead of just the keys!
         :rule-classes ((:rewrite :loop-stopper ((b a))))
         :hints(("Goal" :use ((:functional-instance tr-set-of-tr-set-diff
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-set '-of- tr-set '-same)
         (equal (,tr-set a y (,tr-set a x r))
                (,tr-set a y r))
         :hints(("Goal" :use ((:functional-instance tr-set-of-tr-set-same
                                                    . ,fi-pairs)))))



       ;; We leave the strong rule enabled even though it may be too expensive
       ;; in general.  If you disable it, you'll still have the weaker -SAME
       ;; and -DIFF rules available unless you disable them, too.
       (defthm ,(mksym tr-get '-of- tr-set '-strong)
         (equal (,tr-get a (,tr-set b v r))
                (if (equal a b)
                    ,(subst 'v 'x elem-fix)
                  (,tr-get a r)))
         :hints(("Goal" :use ((:functional-instance tr-get-of-tr-set-strong
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-get '-of-nil)
         (equal (,tr-get a nil)
                ,elem-default)
         :hints(("Goal" :use ((:functional-instance tr-get-of-nil
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-bad-part '-of- tr-set)
         (equal (,tr-bad-part (,tr-set k v r))
                (,tr-bad-part r))
         :hints(("Goal" :use ((:functional-instance tr-bad-part-of-tr-set
                                                    . ,fi-pairs)))))



       (defthm ,(mksym tr-badguy '-finds-counterexample)
         (implies (,tr-badguy x y)
                  (not (equal (,tr-get (cadr (,tr-badguy x y)) x)
                              (,tr-get (cadr (,tr-badguy x y)) y))))
         :hints(("Goal" :use ((:functional-instance tr-badguy-finds-counterexample
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-badguy '-unless-equal)
         (implies (and (not (equal x y))
                       (equal (,tr-bad-part x) (,tr-bad-part y)))
                  (,tr-badguy x y))
         :hints(("Goal" :use ((:functional-instance tr-badguy-unless-equal
                                                    . ,fi-pairs)))))


       (defthm ,(mksym 'equal-of- tr-set)
         ;; See the comments in typed-records.lisp to understand this theorem
         (implies
          (syntaxp (or (acl2::rewriting-positive-literal-fn
                        (list 'equal (list ',tr-set a v x) y) ;; Ugh... well, if you don't like it,
                        mfc state)                            ;; you can figure out how to double-
                       (acl2::rewriting-positive-literal-fn   ;; backquote it... ffs.
                        (list 'equal y (list ',tr-set a v x))
                        mfc state)))
          (equal (equal (,tr-set a v x) y)
                 (and (equal (,tr-bad-part (,tr-set a v x))
                             (,tr-bad-part y))
                      (let ((key (acl2::introduce-var 'arbitrary-key
                                                      (hide (cadr (,tr-badguy (,tr-set a v x) y))))))
                        (and (equal (,tr-get key (,tr-set a v x))
                                    (,tr-get key y)))))))
         :hints(("Goal"
                 :use ((:functional-instance equal-of-tr-set
                                             . ,fi-pairs)))))

       ;; Old alternative to equal-of-tr-set

       ;; (defthmd ,(mksym name '-decompose-with-key)
       ;;   (implies (syntaxp (or (not (equal v1 '',elem-default))
       ;;                         (not (equal v2 '',elem-default))))
       ;;            (equal (equal (,tr-set k v1 x)
       ;;                          (,tr-set k v2 y))
       ;;                   (and (equal ,(subst 'v1 'x elem-fix)
       ;;                               ,(subst 'v2 'x elem-fix))
       ;;                        (equal (,tr-set k ,elem-default x)
       ;;                               (,tr-set k ,elem-default y)))))
       ;;   :hints(("Goal" :use ((:functional-instance tr-decompose-with-key
       ;;                                              . ,fi-pairs)))))


       ;; Record/array pair supporting theorems

       (defthm ,(mksym name '-elem-p-of-nth)
         (implies (and ,(subst 'arr 'x elem-list-p)
                       (< (nfix n) (len arr)))
                  ,(subst '(nth n arr) 'x elem-p))
         :hints(("Goal" :use ((:functional-instance elem-p-of-nth
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-get '-of- array-to-tr)
         (equal (,tr-get key (,array-to-tr n arr rec))
                (if (and (natp key)
                         (< key (nfix n)))
                    ,(subst '(nth key arr) 'x elem-fix)
                  (,tr-get key rec)))
         :hints(("Goal" :use ((:functional-instance tr-get-of-array-to-tr
                                                    . ,fi-pairs)))))


       (defthm ,(mksym 'len-of- tr-to-array)
         (equal (len (,tr-to-array n rec arr))
                (max (nfix n) (len arr)))
         :hints(("Goal" :use ((:functional-instance len-of-tr-to-array
                                                    . ,fi-pairs)))))

       (defthm ,(mksym 'elem-list-p-of- tr-to-array)
         (implies (and ,(subst 'arr 'x elem-list-p)
                       (<= (nfix n) (len arr)))
                  ,(subst `(,tr-to-array n rec arr) 'x elem-list-p))
         :hints(("Goal" :use ((:functional-instance elem-list-p-of-tr-to-array
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-to-array '-idempotent)
         (implies (and (force (natp (len arr1)))
                       (force ,(subst 'arr1 'x elem-list-p)))
                  (equal (,tr-to-array n rec1 (,tr-to-array n rec2 arr1))
                         (,tr-to-array n rec1 arr1)))
         :hints(("Goal" :use ((:functional-instance tr-to-array-idempotent
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-to-array '-of- tr-set)
         (implies (and (natp n)
                       (natp i)
                       (< i n)
                       ,(subst 'val 'x elem-p)
                       ,(subst 'arr 'x elem-list-p))
                  (equal (,tr-to-array n (,tr-set i val rec) arr)
                         (update-nth i val (,tr-to-array n rec arr))))
         :hints(("Goal" :use ((:functional-instance tr-to-array-of-tr-set
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-to-array '-of- array-to-tr)
         (implies (and (force (equal (len arr1) (len arr2)))
                       (force (equal n (len arr1)))
                       (force (posp (len arr1)))
                       (force ,(subst 'arr1 'x elem-list-p))
                       (force ,(subst 'arr2 'x elem-list-p)))
                  (equal (,tr-to-array n (,array-to-tr n arr1 rec) arr2)
                         arr1))
         :hints(("Goal" :use ((:functional-instance tr-to-array-of-array-to-tr
                                                    . ,fi-pairs)))))




       (defthm ,(mksym tr-delete-indices '-of-nil)
         (equal (,tr-delete-indices n nil)
                nil)
         :hints(("Goal" :use ((:functional-instance tr-delete-indices-of-nil
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-delete-indices '-idempotent)
         (equal (,tr-delete-indices n (,tr-delete-indices n rec))
                (,tr-delete-indices n rec))
         :hints(("Goal" :use ((:functional-instance tr-delete-indices-idempotent
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-delete-indices '-of- tr-set)
         (implies (and (natp n)
                       (natp i)
                       (< i n))
                  (equal (,tr-delete-indices n (,tr-set i val rec))
                         (,tr-delete-indices n rec)))
         :hints(("Goal" :use ((:functional-instance tr-delete-indices-of-tr-set
                                                    . ,fi-pairs)))))

       (defthm ,(mksym tr-delete-indices '-of- array-to-tr)
         (equal (,tr-delete-indices n (,array-to-tr n arr rec))
                (,tr-delete-indices n rec))
         :hints(("Goal" :use ((:functional-instance tr-delete-indices-of-array-to-tr
                                                    . ,fi-pairs)))))


       (defthm ,(mksym array-to-tr '-inverse)
         (equal (,array-to-tr n
                             (,tr-to-array n rec arr)
                             (,tr-delete-indices n rec))
                rec)
         :hints(("Goal" :use ((:functional-instance array-to-tr-inverse
                                                    . ,fi-pairs)))))

       (defthmd ,(mksym 'equal-of- array-to-tr)
         (implies (and (,array-rec-pair-p arr1 rec1 len1)
                       (,array-rec-pair-p arr2 rec2 len2)
                       (equal len1 len)
                       (equal len2 len)
                       (natp len))
                  (equal (equal (,array-to-tr len arr1 rec1)
                                (,array-to-tr len arr2 rec2))
                         (and (equal arr1 arr2)
                              (equal rec1 rec2))))
         :hints(("Goal" :use ((:functional-instance equal-of-array-to-tr
                                                    . ,fi-pairs)))))


       ;; We save the FI-PAIRS and the theorems we've added in a table, so that
       ;; DEFRSTOBJ can easily look up the names of the record functions and
       ;; enable its theorems.
       (table typed-records ',tr-p
              (list (cons :fi-pairs ',fi-pairs)
                    (cons :theorems
                          (union-theories
                           '(,booleanp-of-elem-p
                             ,elem-p-of-default
                             ,elem-fix-idempotent
                             ,elem-p-of-elem-fix
                             ,elem-list-p-when-atom
                             ,elem-list-p-of-cons)
                           (set-difference-theories
                            (current-theory :here)
                            (current-theory
                             ',(mksym 'start-of- tr-p '-theorems)))))))

       (in-theory (disable ,tr-p1
                           ,tr-p
                           ,to-tr
                           ,tr-bad-part
                           ,tr-get1
                           ,tr-set1
                           ,tr-get
                           ,tr-set
                           ,tr-badguy
                           ,array-to-tr
                           ,tr-to-array
                           ,tr-delete-indices
                           ,array-rec-pair-p))

       )))


(defmacro def-typed-record (name &key
                                 elem-p
                                 elem-list-p
                                 elem-default
                                 elem-fix
                                 in-package-of)
  (def-typed-record-fn name elem-p elem-list-p elem-default elem-fix
    (or in-package-of name)))




(local
 (progn

; Some basic tests to make sure the macro is working

(def-typed-record nat
     :elem-p (natp x)
     :elem-list-p (nat-listp x)
     :elem-default 0
     :elem-fix (nfix x))


   (defun ubp-listp (n x)
     (declare (xargs :guard t))
     (if (atom x)
         (not x)
       (and (unsigned-byte-p n (car x))
            (ubp-listp n (cdr x)))))

   (defun ubp-fix (n x)
     (declare (xargs :guard t))
     (if (unsigned-byte-p n x)
         x
       0))

   (def-typed-record ubp8
     :elem-p       (unsigned-byte-p 8 x)
     :elem-list-p  (ubp-listp 8 x)
     :elem-default 0
     :elem-fix     (ubp-fix 8 x))


   (defun nonneg-fix (x)
     (declare (xargs :guard t))
     (if (integerp x)
         (if (< x 0)
             (- x)
           x)
       0))

   (def-typed-record nonneg
     :elem-p (natp x)
     :elem-list-p (nat-listp x)
     :elem-default 0
     :elem-fix (nonneg-fix x))

   ))

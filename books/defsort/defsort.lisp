; Defsort - Defines a stable sort when given a comparison function
; Copyright (C) 2008 Centaur Technology
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
(include-book "generic")
(include-book "std/util/support" :dir :system)

(defxdoc defsort
  ;; Note (Sol): I think this library should probably be moved into std/lists,
  ;; and its xdoc filed under there, maybe once the UI is made a bit nicer.
  :parents (std/lists)
  :short "Define a sorting function for a given comparator."
  :long "<h5>NOTE: Defsort's interface has a greater than average likelihood of
changing incompatibly in the future.</h5>

<p>Defsort creates a relatively-high-performance sorting function for a given
comparison function, and proves that its output is an ordered (with respect to
the comparison function) permutation of the input list.  It is currently
implemented as a mergesort on lists with some fixnum optimizations.</p>

<h3>Usage</h3>

<p>These two forms show two ways of invoking defsort:</p>
@({
  (defsort sort-by-foo<
           :prefix foosort
           :compare< foo<
           :comparablep foo-p
           :comparable-listp foolist-p
           :true-listp nil)           
 
  (defsort :comparablep rationalp
           :compare< <
           :prefix <
           :comparable-listp rational-listp
           :true-listp t)
})

<p>The first form is a new syntax that gives the name of the sorting function
explicitly; it is also good for etags generation since it is of the form
@('(def... name ...)').  In the first form, the prefix is optional; if it is
not provided, the sort name will be used as the prefix for generating other
function names.</p>

<p>The second form shows an older syntax in which the sort name is omitted and
every function name is generated from the prefix, so the name of the sorting
function will in this case be @('<-sort').</p>

<h4>Keyword Arguments</h4>
<ul>

<li>@(':compare<') gives the function to use to compare elements; this may be a
binary function name or a lambda such as @('(lambda (x y) (< y x))').</li>

<li>@(':prefix') defaults to the sort name when it is provided, but otherwise
is required.  It is used to generate function and theorem names.</li>

<li>@(':comparablep') gives the type of element to be compared.  The comparison
function's guards should be satisfied by any two elements that both satisfy
this predicate.  This may be a unary function symbol or lambda.  If it is
omitted, then it is treated as @('(lambda (x) t)'), i.e. all objects are
comparable.</li>

<li>@(':comparable-listp') gives the name of a function that recognizes a list
of comparable elements.  This may be omitted, in which case such a function
will be defined (named @('<prefix>-list-p')).</li>

<li>@(':true-listp') defaults to NIL and determines whether the
comparable-listp function requires the final cdr to be NIL.  If an existing
@(':comparable-listp') function name is provided, then the value of
@(':true-listp') must correspond to that function; i.e. true-listp must be true
iff the comparable-listp function requires the final cdr to be nil.  If
@(':comparable-listp') is not provided, then the comparable-listp function will
be generated so that this is true.</li>

</ul>")

; Inputs are as follows.
;
; Compare< is the name of a 2-ary function that compares objects.  It can be a
; strict or non-strict relation.  It must be known to be boolean and
; transitive.
;
; Comparablep is the name of a 1-ary function that says when objects are
; well-formed for compare<.  If compare< works on all inputs, comparablep may
; be set to t.
;
; Prefix is a symbol which will be used to create the names of all the
; functions and theorems we generate.

(defconst *defsort-keywords*
  '(:comparablep :compare< :prefix :comparable-listp :true-listp))

(defun defsort-fn (args)
  (declare (xargs :mode :program))
  (b* (((mv sort args) (if (keywordp (car args))
                             (mv nil args)
                           (mv (car args) (cdr args))))
         ((mv kwd-alist args)
          (std::extract-keywords 'defsort *defsort-keywords* args nil))

         ((when args)
          (er hard? 'defsort-fn "Defsort: extra arguments"))

         (prefix           (std::getarg :prefix sort kwd-alist))
         ((unless (and prefix (symbolp prefix) (not (keywordp prefix))))
          (er hard? 'defsort
              "Defsort requires either a sort name (non-keyword symbol as the ~
               first argument) or a :prefix argument, also a non-keyword ~
               symbol."))
         ((fun (mksym prefix x))
          (intern-in-package-of-symbol (concatenate 'string (symbol-name prefix) x)
                                       ;; We can't create symbols in the COMMON-LISP package,
                                       ;; so if something like < is used, switch it to the ACL2
                                       ;; package.
                                       (if (equal (symbol-package-name prefix) "COMMON-LISP")
                                           'ACL2::foo
                                         prefix)))
         (sort             (or sort (mksym prefix "-SORT")))
         

         (comparable-listp (std::getarg :comparable-listp nil kwd-alist))
         (compare<         (std::getarg :compare< nil kwd-alist))
         (comparablep      (std::getarg :comparablep nil kwd-alist))
         (true-listp       (std::getarg :true-listp nil kwd-alist))

         ((unless compare<)
          (er hard? 'defsort "Defsort requires :compare< to be specified"))

         (definedp         comparable-listp)
         (comparable-listp (or comparable-listp
                               (mksym prefix "-LIST-P")))
         (orderedp         (mksym prefix "-ORDERED-P"))
         (merge            (mksym prefix "-MERGE"))
         (merge-tr         (mksym prefix "-MERGE-TR"))
         (fixnum           (mksym prefix "-MERGESORT-FIXNUM"))
         (integer          (mksym prefix "-MERGESORT-INTEGERS"))
         (comparable-inst  (if comparablep comparablep `(lambda (x) t)))
         (comparable-listp-inst (if comparablep comparable-listp `(lambda (x) t)))
         (element-list-final-cdr-inst (if true-listp
                                          `(lambda (x) (not x))
                                        `(lambda (x) t))))
      `(encapsulate
        ()
        (local (defthm ,(mksym prefix "-TYPE-OF-COMPARE<")
                 (or (equal (,compare< x y) t)
                     (equal (,compare< x y) nil))
                 :rule-classes :type-prescription))

        ,@(and comparablep
               `((local (defthm ,(mksym prefix "-TYPE-OF-COMPARABLEP")
                          (or (equal (,comparablep x) t)
                              (equal (,comparablep x) nil))
                          :rule-classes :type-prescription))))

        (local (defthm ,(mksym prefix "-COMPARE<-TRANSITIVE")
                 (implies (and ,@(and comparablep
                                      `((,comparablep x)
                                        (,comparablep y)
                                        (,comparablep z)))
                               (,compare< x y)
                               (,compare< y z))
                          (,compare< x z))))
                          

        (local (in-theory (theory 'minimal-theory)))
        (local (in-theory (enable ,(mksym prefix "-TYPE-OF-COMPARE<")
                                  ,(mksym prefix "-COMPARE<-TRANSITIVE"))))
        ,@(and comparablep
               `((local (in-theory (enable ,(mksym prefix "-TYPE-OF-COMPARABLEP"))))))

        ,@(and definedp comparablep
               `((local
                  (make-event
                   '(:or (defthm defsort-comparable-list-check
                           t
                           :hints (("goal" :use
                                    ((:functional-instance 
                                      comparable-listp
                                      (comparable-listp ,comparable-listp)
                                      (comparablep      ,comparablep)
                                      (compare<         ,compare<)
                                      (element-list-final-cdr-p
                                       ,element-list-final-cdr-inst)))
                                    :in-theory (enable ,comparable-listp)))
                           :rule-classes nil)
                     (value-triple
                      (er hard 'defsort
                          "The provided value of comparable-listp, ~x0, ~
                           failed consistency checks: either it is not ~
                           defined, or the :true-listp setting was incorrect, ~
                           or the definition doesn't match what we expected."
                          ',comparable-listp)))))))

        ;; The following is a pretty gross hack.  But sometimes the guard for
        ;; compare< might not perfectly line up with comparablep.  For
        ;; instance, if you try to create a sort for NATP objects by using <,
        ;; then the real guard for < uses RATIONALP instead and you would run
        ;; into problems, in the minimal theory, of trying to show that natp
        ;; implies rationalp.

        ;; So, if one of our proofs below is just about to fail, we go back to
        ;; the user's current theroy and try to prove the remaining goals.
        ;; This allows us to see these kind of rules.

        (local (defun stupid-hint (stable-under-simplificationp)
                 (and stable-under-simplificationp
                      '(:in-theory (current-theory ',(mksym prefix "-COMPARE<-TRANSITIVE"))))))

        (set-default-hints '((stupid-hint stable-under-simplificationp)))

        ,@(and comparablep (not definedp)
               `((defund ,comparable-listp (x)
                   (declare (xargs :guard t))
                   (if (consp x)
                       (and (,comparablep (car x))
                            (,comparable-listp (cdr x)))
                     ,(if true-listp `(eq x nil) t)))))

        (defund ,orderedp (x)
          (declare (xargs :guard ,(if comparablep
                                      `(,comparable-listp x)
                                    t)
                          :verify-guards nil))
          (cond ((atom x)
                 t)
                ((atom (cdr x))
                 t)
                ((,compare< (first x) (second x))
                 (,orderedp (cdr x)))
                (t
                 (and (not (,compare< (second x) (first x)))
                      (,orderedp (cdr x))))))

        (verify-guards ,orderedp
                       :hints (("Goal"
                                ;; yuck?
                                ,@(if comparablep
                                      `(:in-theory (enable ,comparable-listp))
                                    nil)
                                :use ((:functional-instance comparable-orderedp-guard
                                                            (compare< ,compare<)
                                                            (comparablep ,comparable-inst)
                                                            (comparable-listp ,comparable-listp-inst)
                                                            (element-list-final-cdr-p
                                                             ,element-list-final-cdr-inst))))))


        (defund ,merge (x y)
          (declare (xargs :measure (+ (acl2-count x)
                                      (acl2-count y))
                          :hints(("Goal" :use ((:functional-instance comparable-merge-admission
                                                                     (compare< ,compare<)
                                                                     (comparablep ,comparable-inst)
                                                                     ))))
                          :guard ,(if comparablep
                                      `(and (,comparable-listp x)
                                            (,comparable-listp y))
                                    t)
                          :verify-guards nil))
          (cond ((atom x)
                 y)
                ((atom y)
                 x)
                ((,compare< (car y) (car x))
                 (cons (car y) (,merge x (cdr y))))
                (t
                 (cons (car x) (,merge (cdr x) y)))))

        (verify-guards ,merge
                       :hints(("Goal"
                               :use ((:functional-instance comparable-merge-guards
                                                           (compare< ,compare<)
                                                           (comparablep ,comparable-inst)
                                                           (comparable-listp ,comparable-listp-inst)
                                                           (comparable-merge ,merge)
                                                           (element-list-final-cdr-p
                                                             ,element-list-final-cdr-inst))))))

        (defund ,merge-tr (x y acc)
          (declare (xargs :measure (+ (acl2-count x)
                                      (acl2-count y))
                          :hints(("Goal" :use ((:functional-instance comparable-merge-admission
                                                                     (compare< ,compare<)
                                                                     (comparablep ,comparable-inst)
                                                                     ))))
                          :guard ,(if comparablep
                                      `(and (,comparable-listp x)
                                            (,comparable-listp y))
                                    t)
                          :verify-guards nil))
          (cond ((atom x)
                 (revappend-without-guard acc y))
                ((atom y)
                 (revappend-without-guard acc x))
                ((,compare< (car y) (car x))
                 (,merge-tr x (cdr y) (cons (car y) acc)))
                (t
                 (,merge-tr (cdr x) y (cons (car x) acc)))))

        (verify-guards ,merge-tr
                       :hints(("Goal"
                               ,@(if comparablep
                                     `(:in-theory (enable ,comparable-listp))
                                   nil)
                               :use ((:functional-instance comparable-merge-tr-guards
                                                           (compare< ,compare<)
                                                           (comparablep ,comparable-inst)
                                                           (comparable-listp ,comparable-listp-inst)
                                                           (comparable-merge-tr ,merge-tr)
                                                           (element-list-final-cdr-p
                                                             ,element-list-final-cdr-inst))))))

        (defund ,fixnum (x len)
          (declare (xargs :measure (nfix len)
                          :hints(("Goal" :use ((:functional-instance
                                                fast-comparable-mergesort-fixnums-admission
                                                (compare< ,compare<)
                                                (comparablep ,comparable-inst)
                                                (comparable-listp ,comparable-listp-inst)
                                                (comparable-merge ,merge)
                                                (comparable-merge-tr ,merge-tr)
                                                (element-list-final-cdr-p
                                                 ,element-list-final-cdr-inst)
                                                ))))
                          :guard (and ,(if comparablep
                                           `(,comparable-listp x)
                                         t)
                                      (natp len)
                                      (<= len (len x)))
                          :verify-guards nil)
                   (type (signed-byte 30) len))
          (cond ((mbe :logic (zp len)
                      :exec (eql (the (signed-byte 30) len) 0))
                 nil)

                ((eql (the (signed-byte 30) len) 1)
                 (list (car x)))

                (t
                 (let* ((len1  (the (signed-byte 30)
                                 (ash (the (signed-byte 30) len) -1)))
                        (len2  (the (signed-byte 30)
                                 (+ (the (signed-byte 30) len1)
                                    (the (signed-byte 30)
                                      (logand (the (signed-byte 30) len) 1)))))
                        (part1 (,fixnum x len1))
                        (part2 (,fixnum (rest-n len1 x) len2)))
                   (,merge-tr part1 part2 nil)))))

        (verify-guards ,fixnum
                       :hints(("Goal"
                               :in-theory (enable ,fixnum ,merge ,merge-tr) ;; yuck?
                               :use ((:functional-instance fast-comparable-mergesort-fixnums-guards
                                                           (compare< ,compare<)
                                                           (comparablep ,comparable-inst)
                                                           (comparable-listp ,comparable-listp-inst)
                                                           (comparable-merge ,merge)
                                                           (comparable-merge-tr ,merge-tr)
                                                           (fast-comparable-mergesort-fixnums ,fixnum)
                                                           (element-list-final-cdr-p
                                                             ,element-list-final-cdr-inst))))))

        (defund ,integer (x len)
          (declare (xargs :measure (nfix len)
                          :hints(("Goal" :use ((:functional-instance
                                                fast-comparable-mergesort-integers-admission
                                                (compare< ,compare<)
                                                (comparablep ,comparable-inst)
                                                (comparable-listp ,comparable-listp-inst)
                                                (comparable-merge ,merge)
                                                (comparable-merge-tr ,merge-tr)
                                                (fast-comparable-mergesort-fixnums ,fixnum)
                                                (element-list-final-cdr-p
                                                 ,element-list-final-cdr-inst)
                                                ))))
                          :guard (and ,(if comparablep
                                           `(,comparable-listp x)
                                         t)
                                      (natp len)
                                      (<= len (len x)))
                          :verify-guards nil)
                   (type integer len))
          (cond ((mbe :logic (zp len)
                      :exec (eql (the integer len) 0))
                 nil)
                ((eql (the integer len) 1)
                 (list (car x)))
                (t
                 (let* ((len1  (the integer (ash (the integer len) -1)))
                        (len2  (the integer
                                 (+ (the integer len1)
                                    (the integer (logand (the integer len) 1)))))
                        (part1 (if (< (the integer len1) (mergesort-fixnum-threshold))
                                   (,fixnum x len1)
                                 (,integer x len1)))
                        (part2 (if (< (the integer len2) (mergesort-fixnum-threshold))
                                   (,fixnum (rest-n len1 x) len2)
                                 (,integer (rest-n len1 x) len2))))
                   (,merge-tr part1 part2 nil)))))

        (verify-guards ,integer
                       :hints(("Goal"
                               :in-theory (enable ,integer ,merge ,merge-tr) ;; yuck?
                               :use ((:functional-instance fast-comparable-mergesort-integers-guards
                                                           (compare< ,compare<)
                                                           (comparablep ,comparable-inst)
                                                           (comparable-listp ,comparable-listp-inst)
                                                           (element-list-final-cdr-p
                                                             ,element-list-final-cdr-inst)
                                                           (comparable-merge ,merge)
                                                           (comparable-merge-tr ,merge-tr)
                                                           (fast-comparable-mergesort-fixnums ,fixnum)
                                                           (fast-comparable-mergesort-integers ,integer)
                                                           )))))

        (defund ,sort (x)
          (declare (xargs :guard ,(if comparablep
                                      `(,comparable-listp x)
                                    t)
                          :guard-hints (("Goal" :in-theory (enable signed-byte-p
                                                                   integer-range-p
                                                                   length
                                                                   natp
                                                                   (:type-prescription len)
                                                                   (:executable-counterpart expt))))))
          (let ((len (len x)))
            (if (< len (mergesort-fixnum-threshold))
                (,fixnum x len)
              (,integer x len))))

        (defthm ,(mksym prefix "-SORT-PRESERVES-DUPLICITY")
          (equal (duplicity a (,sort x))
                 (duplicity a x))
          :hints(("Goal"
                  :in-theory (enable ,sort)
                  :use ((:functional-instance duplicity-of-comparable-mergesort
                                              (compare< ,compare<)
                                              (comparablep ,comparable-inst)
                                              (comparable-listp ,comparable-listp-inst)
                                              (element-list-final-cdr-p
                                               ,element-list-final-cdr-inst)
                                              (comparable-merge ,merge)
                                              (comparable-merge-tr ,merge-tr)
                                              (fast-comparable-mergesort-fixnums ,fixnum)
                                              (fast-comparable-mergesort-integers ,integer)
                                              (comparable-mergesort ,sort))))))

        ,@(and comparablep
               `((defthm ,(mksym prefix "-SORT-CREATES-COMPARABLE-LISTP")
                   (implies (force (,comparable-listp x))
                            (,comparable-listp (,sort x)))
                   :hints(("Goal"
                           :use ((:functional-instance comparable-listp-of-comparable-mergesort
                                                       (compare< ,compare<)
                                                       (comparablep ,comparable-inst)
                                                       (comparable-listp ,comparable-listp-inst)

                                                       (element-list-final-cdr-p
                                                        ,element-list-final-cdr-inst)
                                                       (comparable-merge ,merge)
                                                       (comparable-merge-tr ,merge-tr)
                                                       (fast-comparable-mergesort-fixnums ,fixnum)
                                                       (fast-comparable-mergesort-integers ,integer)
                                                       (comparable-mergesort ,sort))))))))

        (defthm ,(mksym prefix "-SORT-SORTS")
          (,orderedp (,sort x))
          :hints(("Goal"
                  :in-theory (enable ,orderedp)
                  :use ((:functional-instance comparable-orderedp-of-comparable-mergesort
                                              (compare< ,compare<)
                                              (comparablep ,comparable-inst)
                                              (comparable-listp ,comparable-listp-inst)
                                              (element-list-final-cdr-p
                                               ,element-list-final-cdr-inst)
                                              (comparable-merge ,merge)
                                              (comparable-merge-tr ,merge-tr)
                                              (comparable-orderedp ,orderedp)
                                              (fast-comparable-mergesort-fixnums ,fixnum)
                                              (fast-comparable-mergesort-integers ,integer)
                                              (comparable-mergesort ,sort))))))

        (defthm ,(mksym prefix "-NO-DUPLICATESP-EQUAL")
          (equal (no-duplicatesp-equal (,sort x))
                 (no-duplicatesp-equal x))
          :hints(("Goal"
                  :use ((:functional-instance no-duplicatesp-equal-of-comparable-mergesort
                                              (compare< ,compare<)
                                              (comparablep ,comparable-inst)
                                              (comparable-listp ,comparable-listp-inst)
                                              (element-list-final-cdr-p
                                               ,element-list-final-cdr-inst)
                                              (comparable-merge ,merge)
                                              (comparable-merge-tr ,merge-tr)
                                              (comparable-orderedp ,orderedp)
                                              (fast-comparable-mergesort-fixnums ,fixnum)
                                              (fast-comparable-mergesort-integers ,integer)
                                              (comparable-mergesort ,sort))))))

        (defthm ,(mksym prefix "-TRUE-LISTP")
          (true-listp (,sort x))
          :rule-classes :type-prescription
          :hints(("Goal"
                  :use ((:functional-instance true-listp-of-comparable-mergesort
                                              (compare< ,compare<)
                                              (comparablep ,comparable-inst)
                                              (comparable-listp ,comparable-listp-inst)
                                              (element-list-final-cdr-p
                                               ,element-list-final-cdr-inst)
                                              (comparable-merge ,merge)
                                              (comparable-merge-tr ,merge-tr)
                                              (comparable-orderedp ,orderedp)
                                              (fast-comparable-mergesort-fixnums ,fixnum)
                                              (fast-comparable-mergesort-integers ,integer)
                                              (comparable-mergesort ,sort))))))


        )))

(defmacro defsort (&rest args)
  (defsort-fn args))


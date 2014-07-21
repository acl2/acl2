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

(defmacro defsort (&key comparablep
                        compare<
                        prefix)
  (flet ((mksym (prefix x)
                (intern-in-package-of-symbol (concatenate 'string (symbol-name prefix) x)
                                             ;; We can't create symbols in the COMMON-LISP package,
                                             ;; so if something like < is used, switch it to the ACL2
                                             ;; package.
                                             (if (equal (symbol-package-name prefix) "COMMON-LISP")
                                                 'ACL2::foo
                                               prefix))))
    (let* ((comparable-listp (mksym prefix "-LIST-P"))
           (orderedp         (mksym prefix "-ORDERED-P"))
           (merge            (mksym prefix "-MERGE"))
           (merge-tr         (mksym prefix "-MERGE-TR"))
           (fixnum           (mksym prefix "-MERGESORT-FIXNUM"))
           (integer          (mksym prefix "-MERGESORT-INTEGERS"))
           (sort             (mksym prefix "-SORT"))
           (comparable-inst  (if comparablep comparablep `(lambda (x) t)))
           (comparable-listp-inst (if comparablep comparable-listp `(lambda (x) t))))
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

        ,@(and comparablep
               `((defund ,comparable-listp (x)
                   (declare (xargs :guard t))
                   (if (consp x)
                       (and (,comparablep (car x))
                            (,comparable-listp (cdr x)))
                     t))))

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
                                                            (comparable-listp ,comparable-listp-inst))))))


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
                                                           (comparable-merge ,merge))))))

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
                                                           (comparable-merge-tr ,merge-tr))))))

        (defund ,fixnum (x len)
          (declare (xargs :measure (nfix len)
                          :hints(("Goal" :use ((:functional-instance
                                                fast-comparable-mergesort-fixnums-admission
                                                (compare< ,compare<)
                                                (comparablep ,comparable-inst)
                                                (comparable-listp ,comparable-listp-inst)
                                                (comparable-merge ,merge)
                                                (comparable-merge-tr ,merge-tr)
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
                                                           (fast-comparable-mergesort-fixnums ,fixnum))))))

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
                                              (comparable-merge ,merge)
                                              (comparable-merge-tr ,merge-tr)
                                              (comparable-orderedp ,orderedp)
                                              (fast-comparable-mergesort-fixnums ,fixnum)
                                              (fast-comparable-mergesort-integers ,integer)
                                              (comparable-mergesort ,sort))))))


        ))))


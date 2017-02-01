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

; def-typed-record.lisp
;
; We introduce the DEF-TYPED-RECORD macro which can be used to introduce a new
; kind of typed record.  Using this macro gives you definitions of the get and
; set functions, the ordinary get-of-set style theorems about them, and other
; stuff such as a badguy for finding differences between typed records.
;
; The generic theory that supports this macro is found in typed-records.lisp.
;
; For several examples of using the macro, see typed-record-tests.lisp.


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
                 ;  must be equal to (if elem-p x elem-default)

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
         (elem-fix-correct      (mksym 'elem-fix-correct-for- tr-p))
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

       (defthmd ,elem-fix-correct
         (equal ,elem-fix
                (if ,elem-p
                    x
                  ,elem-default)))

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
                                 ,elem-fix-correct
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
         (implies (and (force (posp (len arr1)))
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
                             ,elem-fix-correct
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

   ))

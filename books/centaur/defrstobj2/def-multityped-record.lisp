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
; Author: Sol Swords <sswords@centtech.com>
; Based on previous work by Jared Davis -- see ../defrstobj/def-typed-record.lisp.


(in-package "RSTOBJ2")
(include-book "multityped-records")

(defsection def-multityped-record
  :parents (defrstobj)
  :short "Introduce a multi-typed record for use with @(see defrstobj)."

  :long "<p>A <b>multi-typed record</b> is a record-like structure: it associates
keys with values, has a @('get') function to look up the value of some key, and
has a @('set') function to install some new value for some key.</p>

<p>Unlike an ordinary @('misc/record'), a multi-typed record has typed
elements.  The type of an element is parametrized by the key.  I.e., we have a
function @('elementp') such that we know @('(elementp key (get key r))').
Correspondingly, there are also @('element-fix') and @('element-default')
functions that also take the key as input. Meanwhile, the @('get') and @('set')
functions for a multityped record are <b>almost</b> the same as for ordinary
records.  The only difference is that the @('g-same-s') theorem becomes:</p>

@({
   (get a (set a v r)) = (elem-fix a v)   ; instead of just being v
})

<p>The macro @('def-multityped-record') can be used to introduce a new
multityped record structure.</p>

<p>Multityped records are a generalization of typed records (see @(see
rstobj::def-typed-record)).  A typed-record can be viewed as a multityped
record for which the @('elem-p'), @('elem-fix'), and @('elem-default')
functions ignore the key.</p>

<h3>Usage</h3>

<p>You can use @('def-multityped-record') to introduce the @('get-') and @('set-')
functions, the ordinary @('get-of-set') style theorems about them, and some
additional definitions such as a badguy for identifying differences between
typed records (which can be useful for pick-a-point style reasoning.)</p>

<h5>Example: uniformly typed record for naturals</h5>

@({
    (def-multityped-record natrec
      :elem-p (natp x)
      :elem-default 0
      :elem-fix (nfix x))
})

<p>This introduces the recognizer function @('natrec-p'), the getter function
@('natrec-get'), the setter function @('natrec-set'), and related theorems.</p>

<h5>Example: multiply typed record</h5>
<p>In this record, integer keys are associated with integer values, symbol keys have
symbol values, and any other key can contain objects of any type.</p>

@({
  (defun foo-elem-p (key x)
    (cond ((symbolp key) (symbolp x))
          ((integerp key) (integerp x))
          (t t)))

  (defun foo-elem-fix (key x)
    (cond ((symbolp key) (if (symbolp x) x nil))
          ((integerp x) (ifix x))
          (t x)))

  (defun foo-elem-default (key)
    (if (integerp key) 0 nil))

   (def-multityped-record foorec
     :elem-p       (foo-elem-p k x)
     :elem-default (foo-elem-default k)
     :elem-fix     (foo-elem-fix k x))
})

<p>This produces @('foorec-p'), @('foorec-get'), @('foorec-set'), and related
theorems.</p>


<h5>General Form</h5>

@({
    (def-multityped-record name
      :elem-p        [element recognizer, foop -- expression involving k and x]
      :elem-default  [default value, e.g., 0, nil, or an expression involving k]
      :elem-fix      [fixing function, foo-fix -- expression involving k and x]
      :in-package-of [symbol to use for new names])
})

<p>Note that the terms you use for @('elem-p') and so forth need to refer to
exactly the variables @('acl2::k') and @('acl2::x').</p>


<h3>Related Work and History</h3>

<p>This evolved from @('centaur/defrstobj/typed-record.lisp') when we needed a
record-like stobj with a more robust @('set-of-get') identity.</p>")


;; BOZO redundant with typed-record.lisp
(defun symbol-list-names (x)
  (declare (xargs :guard (symbol-listp x)))
  (if (atom x)
      nil
    (cons (symbol-name (car x))
          (symbol-list-names (cdr x)))))

;; BOZO redundant with typed-record.lisp
(defmacro mksym (&rest args)
  `(intern-in-package-of-symbol
    (string-append-lst (symbol-list-names (list . ,args)))
    mksym-pkg))


(defun def-multityped-record-fn
  (name          ; Prefix for all the names we'll generate

   elem-p        ; A term mentioning only X, the element recognizer
                 ;  e.g., (integerp x), or (unsigned-byte-p 8 x)

   elem-default  ; A term with no free variables that is the default value
                 ;  e.g., nil, 0, (my-default), or similar.

   elem-fix      ; A term mentioning only X, the fixing function
                 ;  e.g., (nfix x), (ubp-fix 8 x), etc.

   in-package-of ; Package for names we'll generate

   )

  (let* ((mksym-pkg         in-package-of)
         (mtr-p1             (mksym name '-p1))
         (mtr-p              (mksym name '-p))
         (to-mtr             (mksym name '-to-mtr))
         (mtr-bad-part       (mksym name '-bad-part))
         (mtr-get1           (mksym name '-get1))
         (mtr-set1           (mksym name '-set1))
         (mtr-get            (mksym name '-get))
         (mtr-set            (mksym name '-set))
         (mtr-badguy         (mksym name '-badguy))
         ;; (array-to-mtr       (mksym 'array-to- name))
         ;; (mtr-to-array       (mksym name '-to-array))
         ;; (mtr-delete-indices (mksym name '-delete-indices))
         ;; (array-rec-pair-p   (mksym name '-array-rec-pair-p))
         ;; (mtr-array-p1       (mksym name '-array-p1))
         ;; (mtr-array-p        (mksym name '-array-p))

         (fi-pairs    `((mtr-elem-p            (lambda (k x) ,elem-p))
                        (mtr-elem-default      (lambda (k)  ,elem-default))
                        (mtr-elem-fix          (lambda (k x) ,elem-fix))
                        ;; (elem-list-p       (lambda (x) ,elem-list-p))
                        (mtr-p1             ,mtr-p1)
                        (mtr-p              ,mtr-p)
                        (to-mtr             ,to-mtr)
                        (mtr-bad-part       ,mtr-bad-part)
                        (mtr-get1           ,mtr-get1)
                        (mtr-set1           ,mtr-set1)
                        (mtr-get            ,mtr-get)
                        (mtr-set            ,mtr-set)
                        (mtr-badguy         ,mtr-badguy)
                        ;; (array-to-mtr       ,array-to-mtr)
                        ;; (mtr-to-array       ,mtr-to-array)
                        ;; (mtr-delete-indices ,mtr-delete-indices)
                        ;; (array-mtr-pair-p  ,array-rec-pair-p)
                        ;; (mtr-array-p1      ,mtr-array-p1)
                        ;; (mtr-array-p       ,mtr-array-p)
                        ))

         (booleanp-of-elem-p    (mksym 'booleanp-of-elem-p-for- mtr-p))
         (elem-p-of-default     (mksym 'elem-p-of-default-for- mtr-p))
         (elem-p-of-elem-fix    (mksym 'elem-p-of-elem-fix-for- mtr-p))
         (elem-fix-idempotent   (mksym 'elem-fix-idempotent-for- mtr-p))
         ;; (elem-list-p-when-atom (mksym 'elem-list-p-when-atom-for- mtr-p))
         ;; (elem-list-p-of-cons   (mksym 'elem-list-p-of-cons-for- mtr-p))
         )

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

       ;; (defthmd ,elem-list-p-when-atom
       ;;   (implies (atom x)
       ;;            (equal ,elem-list-p
       ;;                   (not x))))

       ;; (defthmd ,elem-list-p-of-cons
       ;;   (equal ,(subst '(cons a x) 'x elem-list-p)
       ;;          (and ,(subst 'a 'x elem-p)
       ;;               ,elem-list-p)))

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
                                 ;; ,elem-list-p-when-atom
                                 ;; ,elem-list-p-of-cons
                                 )))

       ;; Main typed record definitions

       (defun ,mtr-p1 (x)
         (or (null x)
             (and (consp x)
                  (consp (car x))
                  (,mtr-p1 (cdr x))
                  ,(sublis '((k . (caar x))
                             (x . (cdar x)))
                           elem-p)
                  (not (equal (cdar x) ,(subst '(caar x) 'k elem-default)))
                  (or (null (cdr x))
                      (<< (caar x) (caadr x))))))

       (defun ,mtr-p (x)
         (and (consp x)
              (,mtr-p1 (car x))
              (car x)
              (not (,mtr-p (cdr x)))))

       (defun ,to-mtr (x)
         (if (,mtr-p x)
             x
           (cons nil x)))

       (defun ,mtr-bad-part (r)
         (if (,mtr-p r)
             (cdr r)
           r))

       (defun ,mtr-get1 (k r)
         (declare (xargs :guard (,mtr-p1 r)))
         (cond ((or (endp r)
                    (<< k (caar r)))
                ,elem-default)
               ((equal k (caar r))
                (cdar r))
               (t
                (,mtr-get1 k (cdr r)))))

       (defun ,mtr-set1 (k v r)
         (declare (xargs :guard (,mtr-p1 r)))
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
                (cons (car r) (,mtr-set1 k v (cdr r))))))

       (defun ,mtr-get (k r)
         (,mtr-get1 k (car (,to-mtr r))))

       (defun ,mtr-set (k v r)
         (let* ((rec      (,to-mtr r))
                (rec1     (car rec))
                (bad      (cdr rec))
                (new-rec1 (,mtr-set1 k ,(subst 'v 'x elem-fix) rec1)))
           (if new-rec1
               (cons new-rec1 bad)
             bad)))

       (defun ,mtr-badguy (x y)
         (declare (xargs :verify-guards nil))
         (mtr-badguy1 (car (,to-mtr x))
                     (car (,to-mtr y))))

       ;; ;; Record/array pair supporting definitions
       ;; (defun ,mtr-array-p1 (n x)
       ;;   (declare (xargs :measure (len x)
       ;;                   :guard (natp n)))
       ;;   (if (atom x)
       ;;       (eq x nil)
       ;;     (and ,(sublis '((k . (nfix n))
       ;;                     (x . (car x))) elem-p)
       ;;          (,mtr-array-p1 (+ 1 (nfix n)) (cdr x)))))

       ;; (defun ,array-to-mtr (n arr rec)
       ;;   (declare (xargs :guard (and (natp n)
       ;;                               (true-listp arr))))
       ;;   (if (zp n)
       ;;       rec
       ;;     (let ((n (- n 1)))
       ;;       (,array-to-mtr n arr (,mtr-set n (nth n arr) rec)))))

       ;; (defun ,mtr-to-array (n rec arr)
       ;;   (declare (xargs :guard (and (natp n)
       ;;                               (true-listp arr))))
       ;;   (if (zp n)
       ;;       arr
       ;;     (let ((n (- n 1)))
       ;;       (,mtr-to-array n rec (update-nth n (,mtr-get n rec) arr)))))

       ;; (defun ,mtr-delete-indices (n rec)
       ;;   (declare (xargs :guard (natp n)))
       ;;   (if (zp n)
       ;;       rec
       ;;     (let ((n (- n 1)))
       ;;       (,mtr-delete-indices n (,mtr-set n ,elem-default rec)))))

       ;; (defun ,array-rec-pair-p (arr rec len)
       ;;   (declare (xargs :guard (natp len)))
       ;;   (and ,(subst 'arr 'x elem-list-p)
       ;;        (= (len arr) len)
       ;;        (equal rec (,mtr-delete-indices len rec))))


       (deflabel ,(mksym 'start-of- mtr-p '-theorems))


       ;; Main typed record theorems

       (defthm ,(mksym 'elem-p-of- mtr-get)
         ,(sublis `((k . a) (x . (,mtr-get a x))) elem-p)
         :hints(("Goal"
                 :use ((:functional-instance mtr-elem-p-of-mtr-get
                        . ,fi-pairs)))))

       (defthm ,(mksym mtr-get '-of- mtr-set '-same)
         (equal (,mtr-get a (,mtr-set a v r))
                ,(sublis '((k . a)
                           (x . v)) elem-fix))
         :hints(("Goal"
                 :use ((:functional-instance mtr-get-of-mtr-set-same
                                             . ,fi-pairs)))))

       (defthm ,(mksym mtr-get '-of- mtr-set '-diff)
         (implies (not (equal a b))
                  (equal (,mtr-get a (,mtr-set b v r))
                         (,mtr-get a r)))
         :hints(("Goal" :use ((:functional-instance mtr-get-of-mtr-set-diff
                                                    . ,fi-pairs)))))

       (defthm ,(mksym mtr-set '-of- mtr-get '-same)
         (equal (,mtr-set a (,mtr-get a r) r)
                r)
         :hints(("Goal" :use ((:functional-instance mtr-set-of-mtr-get-same
                                                    . ,fi-pairs)))))

       (defthm ,(mksym mtr-set '-of- mtr-set '-diff)
         (implies (not (equal a b))
                  (equal (,mtr-set b y (,mtr-set a x r))
                         (,mtr-set a x (,mtr-set b y r))))
         ;; Otherwise ACL2 infers a bad loop stopper that considers the values
         ;; instead of just the keys!
         :rule-classes ((:rewrite :loop-stopper ((b a))))
         :hints(("Goal" :use ((:functional-instance mtr-set-of-mtr-set-diff
                                                    . ,fi-pairs)))))

       (defthm ,(mksym mtr-set '-of- mtr-set '-same)
         (equal (,mtr-set a y (,mtr-set a x r))
                (,mtr-set a y r))
         :hints(("Goal" :use ((:functional-instance mtr-set-of-mtr-set-same
                                                    . ,fi-pairs)))))



       ;; We leave the strong rule enabled even though it may be too expensive
       ;; in general.  If you disable it, you'll still have the weaker -SAME
       ;; and -DIFF rules available unless you disable them, too.
       (defthm ,(mksym mtr-get '-of- mtr-set '-strong)
         (equal (,mtr-get a (,mtr-set b v r))
                (if (equal a b)
                    ,(sublis '((k . a) (x . v)) elem-fix)
                  (,mtr-get a r)))
         :hints(("Goal" :use ((:functional-instance mtr-get-of-mtr-set-strong
                                                    . ,fi-pairs)))))

       (defthm ,(mksym mtr-get '-of-nil)
         (equal (,mtr-get a nil)
                ,(subst 'a 'k elem-default))
         :hints(("Goal" :use ((:functional-instance mtr-get-of-nil
                                                    . ,fi-pairs)))))

       (defthm ,(mksym mtr-bad-part '-of- mtr-set)
         (equal (,mtr-bad-part (,mtr-set k v r))
                (,mtr-bad-part r))
         :hints(("Goal" :use ((:functional-instance mtr-bad-part-of-mtr-set
                                                    . ,fi-pairs)))))



       (defthm ,(mksym mtr-badguy '-finds-counterexample)
         (implies (,mtr-badguy x y)
                  (not (equal (,mtr-get (cadr (,mtr-badguy x y)) x)
                              (,mtr-get (cadr (,mtr-badguy x y)) y))))
         :hints(("Goal" :use ((:functional-instance mtr-badguy-finds-counterexample
                                                    . ,fi-pairs)))))

       (defthm ,(mksym mtr-badguy '-unless-equal)
         (implies (and (not (equal x y))
                       (equal (,mtr-bad-part x) (,mtr-bad-part y)))
                  (,mtr-badguy x y))
         :hints(("Goal" :use ((:functional-instance mtr-badguy-unless-equal
                                                    . ,fi-pairs)))))


       (defthm ,(mksym 'equal-of- mtr-set)
         ;; See the comments in typed-records.lisp to understand this theorem
         (implies
          (syntaxp (or (acl2::rewriting-positive-literal-fn
                        (list 'equal (list ',mtr-set a v x) y) ;; Ugh... well, if you don't like it,
                        mfc state)                            ;; you can figure out how to double-
                       (acl2::rewriting-positive-literal-fn   ;; backquote it... ffs.
                        (list 'equal y (list ',mtr-set a v x))
                        mfc state)))
          (equal (equal (,mtr-set a v x) y)
                 (and (equal (,mtr-bad-part (,mtr-set a v x))
                             (,mtr-bad-part y))
                      (let ((key (acl2::introduce-var 'arbitrary-key
                                                      (hide (cadr (,mtr-badguy (,mtr-set a v x) y))))))
                        (and (equal (,mtr-get key (,mtr-set a v x))
                                    (,mtr-get key y)))))))
         :hints(("Goal"
                 :use ((:functional-instance equal-of-mtr-set
                                             . ,fi-pairs)))))

       ;; Old alternative to equal-of-mtr-set

       ;; (defthmd ,(mksym name '-decompose-with-key)
       ;;   (implies (syntaxp (or (not (equal v1 '',elem-default))
       ;;                         (not (equal v2 '',elem-default))))
       ;;            (equal (equal (,mtr-set k v1 x)
       ;;                          (,mtr-set k v2 y))
       ;;                   (and (equal ,(subst 'v1 'x elem-fix)
       ;;                               ,(subst 'v2 'x elem-fix))
       ;;                        (equal (,mtr-set k ,elem-default x)
       ;;                               (,mtr-set k ,elem-default y)))))
       ;;   :hints(("Goal" :use ((:functional-instance mtr-decompose-with-key
       ;;                                              . ,fi-pairs)))))


       ;; ;; Record/array pair supporting theorems

       ;; (defthm ,(mksym name '-elem-p-of-nth)
       ;;   (implies (and ,(subst 'arr 'x elem-list-p)
       ;;                 (< (nfix n) (len arr)))
       ;;            ,(subst '(nth n arr) 'x elem-p))
       ;;   :hints(("Goal" :use ((:functional-instance elem-p-of-nth
       ;;                                              . ,fi-pairs)))))

       ;; (defthm ,(mksym mtr-get '-of- array-to-mtr)
       ;;   (equal (,mtr-get key (,array-to-mtr n arr rec))
       ;;          (if (and (natp key)
       ;;                   (< key (nfix n)))
       ;;              ,(subst '(nth key arr) 'x elem-fix)
       ;;            (,mtr-get key rec)))
       ;;   :hints(("Goal" :use ((:functional-instance mtr-get-of-array-to-mtr
       ;;                                              . ,fi-pairs)))))


       ;; (defthm ,(mksym 'len-of- mtr-to-array)
       ;;   (equal (len (,mtr-to-array n rec arr))
       ;;          (max (nfix n) (len arr)))
       ;;   :hints(("Goal" :use ((:functional-instance len-of-mtr-to-array
       ;;                                              . ,fi-pairs)))))

       ;; (defthm ,(mksym 'elem-list-p-of- mtr-to-array)
       ;;   (implies (and ,(subst 'arr 'x elem-list-p)
       ;;                 (<= (nfix n) (len arr)))
       ;;            ,(subst `(,mtr-to-array n rec arr) 'x elem-list-p))
       ;;   :hints(("Goal" :use ((:functional-instance elem-list-p-of-mtr-to-array
       ;;                                              . ,fi-pairs)))))

       ;; (defthm ,(mksym mtr-to-array '-idempotent)
       ;;   (implies (and (force (natp (len arr1)))
       ;;                 (force ,(subst 'arr1 'x elem-list-p)))
       ;;            (equal (,mtr-to-array n rec1 (,mtr-to-array n rec2 arr1))
       ;;                   (,mtr-to-array n rec1 arr1)))
       ;;   :hints(("Goal" :use ((:functional-instance mtr-to-array-idempotent
       ;;                                              . ,fi-pairs)))))

       ;; (defthm ,(mksym mtr-to-array '-of- mtr-set)
       ;;   (implies (and (natp n)
       ;;                 (natp i)
       ;;                 (< i n)
       ;;                 ,(subst 'val 'x elem-p)
       ;;                 ,(subst 'arr 'x elem-list-p))
       ;;            (equal (,mtr-to-array n (,mtr-set i val rec) arr)
       ;;                   (update-nth i val (,mtr-to-array n rec arr))))
       ;;   :hints(("Goal" :use ((:functional-instance mtr-to-array-of-mtr-set
       ;;                                              . ,fi-pairs)))))

       ;; (defthm ,(mksym mtr-to-array '-of- array-to-mtr)
       ;;   (implies (and (force (equal (len arr1) (len arr2)))
       ;;                 (force (equal n (len arr1)))
       ;;                 (force (posp (len arr1)))
       ;;                 (force ,(subst 'arr1 'x elem-list-p))
       ;;                 (force ,(subst 'arr2 'x elem-list-p)))
       ;;            (equal (,mtr-to-array n (,array-to-mtr n arr1 rec) arr2)
       ;;                   arr1))
       ;;   :hints(("Goal" :use ((:functional-instance mtr-to-array-of-array-to-mtr
       ;;                                              . ,fi-pairs)))))




       ;; (defthm ,(mksym mtr-delete-indices '-of-nil)
       ;;   (equal (,mtr-delete-indices n nil)
       ;;          nil)
       ;;   :hints(("Goal" :use ((:functional-instance mtr-delete-indices-of-nil
       ;;                                              . ,fi-pairs)))))

       ;; (defthm ,(mksym mtr-delete-indices '-idempotent)
       ;;   (equal (,mtr-delete-indices n (,mtr-delete-indices n rec))
       ;;          (,mtr-delete-indices n rec))
       ;;   :hints(("Goal" :use ((:functional-instance mtr-delete-indices-idempotent
       ;;                                              . ,fi-pairs)))))

       ;; (defthm ,(mksym mtr-delete-indices '-of- mtr-set)
       ;;   (implies (and (natp n)
       ;;                 (natp i)
       ;;                 (< i n))
       ;;            (equal (,mtr-delete-indices n (,mtr-set i val rec))
       ;;                   (,mtr-delete-indices n rec)))
       ;;   :hints(("Goal" :use ((:functional-instance mtr-delete-indices-of-mtr-set
       ;;                                              . ,fi-pairs)))))

       ;; (defthm ,(mksym mtr-delete-indices '-of- array-to-mtr)
       ;;   (equal (,mtr-delete-indices n (,array-to-mtr n arr rec))
       ;;          (,mtr-delete-indices n rec))
       ;;   :hints(("Goal" :use ((:functional-instance mtr-delete-indices-of-array-to-mtr
       ;;                                              . ,fi-pairs)))))


       ;; (defthm ,(mksym array-to-mtr '-inverse)
       ;;   (equal (,array-to-mtr n
       ;;                       (,mtr-to-array n rec arr)
       ;;                       (,mtr-delete-indices n rec))
       ;;          rec)
       ;;   :hints(("Goal" :use ((:functional-instance array-to-mtr-inverse
       ;;                                              . ,fi-pairs)))))

       ;; (defthmd ,(mksym 'equal-of- array-to-mtr)
       ;;   (implies (and (,array-rec-pair-p arr1 rec1 len1)
       ;;                 (,array-rec-pair-p arr2 rec2 len2)
       ;;                 (equal len1 len)
       ;;                 (equal len2 len)
       ;;                 (natp len))
       ;;            (equal (equal (,array-to-mtr len arr1 rec1)
       ;;                          (,array-to-mtr len arr2 rec2))
       ;;                   (and (equal arr1 arr2)
       ;;                        (equal rec1 rec2))))
       ;;   :hints(("Goal" :use ((:functional-instance equal-of-array-to-mtr
       ;;                                              . ,fi-pairs)))))


       ;; We save the FI-PAIRS and the theorems we've added in a table, so that
       ;; DEFRSTOBJ can easily look up the names of the record functions and
       ;; enable its theorems.
       (table typed-records ',mtr-p
              (list (cons :fi-pairs ',fi-pairs)
                    (cons :theorems
                          (union-theories
                           '(,booleanp-of-elem-p
                             ,elem-p-of-default
                             ,elem-fix-idempotent
                             ,elem-p-of-elem-fix
                             ;; ,elem-list-p-when-atom
                             ;; ,elem-list-p-of-cons
                             )
                           (set-difference-theories
                            (current-theory :here)
                            (current-theory
                             ',(mksym 'start-of- mtr-p '-theorems)))))))

       (in-theory (disable ,mtr-p1
                           ,mtr-p
                           ,to-mtr
                           ,mtr-bad-part
                           ,mtr-get1
                           ,mtr-set1
                           ,mtr-get
                           ,mtr-set
                           ,mtr-badguy
                           ;; ,array-to-mtr
                           ;; ,mtr-to-array
                           ;; ,mtr-delete-indices
                           ;; ,array-rec-pair-p
                           ))

       )))


(defmacro def-multityped-record (name &key
                                      elem-p
                                      elem-default
                                      elem-fix
                                      in-package-of)
  (def-multityped-record-fn name elem-p elem-default elem-fix
    (or in-package-of name)))




(local
 (progn

; Some basic tests to make sure the macro is working

   (def-multityped-record natrec
     :elem-p (natp x)
     :elem-default 0
     :elem-fix (nfix x))


   (defun foo-elem-p (key x)
     (declare (xargs :guard t))
     (cond ((symbolp key) (symbolp x))
           ((integerp key) (integerp x))
           (t t)))

   (defun foo-elem-fix (key x)
     (declare (xargs :guard t))
     (cond ((symbolp key) (if (symbolp x) x nil))
           ((integerp key) (ifix x))
           (t x)))

   (defun foo-elem-default (key)
     (declare (xargs :guard t))
     (if (integerp key) 0 nil))

   (def-multityped-record foorec
     :elem-p       (foo-elem-p k x)
     :elem-default (foo-elem-default k)
     :elem-fix     (foo-elem-fix k x))
   ))

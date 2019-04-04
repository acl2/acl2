; Size of Set Represented As List
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "std/lists/list-defuns" :dir :system)
(include-book "xdoc/constructors" :dir :system)

(local (include-book "std/lists/top" :dir :system))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defxdoc set-size
  :parents (list-utilities lists)
  :short "Size of a set represented as a list."
  :long
  (xdoc::topstring
   (xdoc::codeblock
    "General Forms:"
    "(set-size x)"
    "(set-size x :test 'eql)   ; same as above (eql as equality test)"
    "(set-size x :test 'eq)    ; same, but eq is equality test"
    "(set-size x :test 'equal) ; same, but equal is equality test")
   (xdoc::p
    "This is the number of unique elements in the set.
     For example, @('(set-size '(1 3 3 2 7))') is equal to @('4').")
   (xdoc::p
    "The optional keyword, @(':test'), has no effect logically,
     but provides the test (default @(tsee eql)) used for comparing
     the elements of the list for duplicates.")
   (xdoc::p
    "The @(see guard) for a call of @('set-size') depends on the test.
     In all cases, the argument must satisfy @(tsee true-listp).
     If the test is @(tsee eql),
     the argument must satisfy @(tsee eqlable-listp).
     If the test is @(tsee eq),
     the argument must satisfy @(tsee symbol-listp).")
   (xdoc::p
    "See @(see equality-variants) for a discussion of
     the relation between @('set-size') and its variants:")
   (xdoc::blockquote
    (xdoc::p
     "@('(set-size-eq x)') is equivalent to
      @('(set-size x :test 'eq)');")
    (xdoc::p
     "@('(set-size-equal x)') is equivalent to
      @('(set-size x :test 'equal)')."))
   (xdoc::p
    "In particular, reasoning about any of these primitives
     reduces to reasoning about the function @('set-size-equal').")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set-size-functions-and-macros
  :parents (set-size)
  :short "Definitions of the @(tsee set-size) functions and macros,
          and basic theorems about them."

  ;; definitions:

  (defun set-size-equal (x)
    (declare (xargs :guard (true-listp x)))
    (len (remove-duplicates-equal x)))

  (defun-with-guard-check set-size-eq-exec (x)
    (symbol-listp x)
    (len (remove-duplicates-eq x)))

  (defun-with-guard-check set-size-eql-exec (x)
    (eqlable-listp x)
    (len (remove-duplicates x)))

  (defmacro set-size (x &key (test ''eql))
    (declare (xargs :guard (or (equal test ''eq)
                               (equal test ''eql)
                               (equal test ''equal))))
    (cond
     ((equal test ''eq)
      `(let-mbe ((x ,x))
                :logic (set-size-equal x)
                :exec (set-size-eq-exec x)))
     ((equal test ''eql)
      `(let-mbe ((x ,x))
                :logic (set-size-equal x)
                :exec (set-size-eql-exec x)))
     (t ; (equal test ''equal)
      `(set-size-equal ,x))))

  (defmacro set-size-eq (x)
    `(set-size ,x :test 'eq))

  ;; basic theorems:

  (defthm set-size-eq-exec-is-set-size-equal
    (equal (set-size-eq-exec x)
           (set-size-equal x)))

  (defthm set-size-eql-exec-is-set-size-equal
    (equal (set-size-eql-exec x)
           (set-size-equal x)))

  (defthm natp-of-set-size-equal
    (natp (set-size-equal x)))

  (defthm natp-of-set-size-eq-exec
    (natp (set-size-eq-exec x)))

  (defthm natp-of-set-size-eql-exec
    (natp (set-size-eql-exec x)))

  ;; these will just rewrite to SET-SIZE-EQUAL:

  (in-theory (disable set-size-eq-exec set-size-eql-exec)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set-size-lemmas
  :parents (set-size-theorems)
  :short "Lemmas useful to prove some of the theorems about @(tsee set-size)."
  :long
  (xdoc::topstring
   (xdoc::p
    "The lemma @('len-when-no-duplicatesp-and-subsetp')
     is used to prove the theorem @('set-size-when-subsetp'), and
     the lemma @('len-when-no-duplicatesp-and-strict-subsetp')
     is similarly used to prove the theorem @('set-size-when-strict-subsetp).
     @(tsee set-size') is defined as @(tsee len) of @(tsee remove-duplicates),
     which produces lists satisfying @(tsee no-duplicatesp),
     making the lemmas applicable to the theorems."))

  ;; The lemma LEN-WHEN-NO-DUPLICATESP-AND-SUBSETP is proved,
  ;; by induction on X,
  ;; by first proving the universal quantification UNIV over Y
  ;; of the lemma's formula.
  ;; The induction step involves not Y, but (REMOVE (CAR X) Y),
  ;; so the universally quantified induction hypothesis
  ;; is instantiated like that.
  ;; Note that, in the induction conclusion,
  ;; the arbitrary Y is the DEFUN-SK's witness with argument X.
  ;; Since (CAR X) is in Y by the definition of SUBSETP,
  ;; (REMOVE (CAR X) Y) is strictly shorter than Y.

  (local
   (defun-sk univ (x)
     (forall y
             (implies (and (no-duplicatesp-equal x)
                           (subsetp-equal x y))
                      (<= (len x) (len y))))))

  (local
   (defthm prove-univ-base-case
     (implies (not (consp x))
              (univ x))))

  (local
   (defthm prove-univ-induction-step
     (implies (and (consp x)
                   (univ (cdr x)))
              (univ x))
     :hints (("Goal"
              :use (:instance univ-necc
                    (x (cdr x))
                    (y (remove (car x) (univ-witness x))))
              :in-theory (disable univ-necc)))))

  (local
   (defthm prove-univ
     (univ x)
     :hints (("Goal" :in-theory (disable univ) :induct (len x)))))

  (defthmd len-when-no-duplicatesp-and-subsetp
    (implies (and (no-duplicatesp-equal x)
                  (subsetp-equal x y))
             (<= (len x) (len y)))
    :hints (("Goal"
             :use (prove-univ univ-necc)
             :in-theory (disable prove-univ univ-necc))))

  ;; The lemma LEN-WHEN-NO-DUPLICATESP-AND-STRICT-SUBSETP is proved
  ;; via the lemma LEN-WHEN-NO-DUPLICATESP-AND-SUBSETP,
  ;; with Y instantiated by removing the witness
  ;; of the fact that Y is not a subset of X:
  ;; the resulting the non-strict inequality is composed with
  ;; the inequality between (LEN (REMOVE WITNESS Y)) and (LEN Y),
  ;; which is strict because the witness is in Y by hypothesis.

  (defthmd len-when-no-duplicatesp-and-strict-subsetp
    (implies (and (no-duplicatesp-equal x)
                  (subsetp-equal x y)
                  (not (subsetp-equal y x)))
             (< (len x) (len y)))
    :hints (("Goal"
             :use ((:instance subsetp-witness-correct
                    (x y) (y x))
                   (:instance len-when-no-duplicatesp-and-subsetp
                    (y (remove (subsetp-witness y x) y))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defsection set-size-theorems
  :parents (set-size)
  :short "Theorems about @(tsee set-size)."

  (defthm set-size-zero-empty
    (equal (equal (set-size-equal x) 0)
           (atom x)))

  (defthm set-size-of-true-list-fix
    (equal (set-size-equal (true-list-fix x))
           (set-size-equal x)))

  (defthm set-size-of-cons
    (equal (set-size-equal (cons a x))
           (if (member-equal a x)
               (set-size-equal  x)
             (1+ (set-size-equal x)))))

  (defthm set-size-of-add-to-set
    (equal (set-size-equal (add-to-set-equal a x))
           (if (member-equal a x)
               (set-size-equal  x)
             (1+ (set-size-equal x)))))

  (defthm set-size-of-remove
    (equal (set-size-equal (remove-equal a x))
           (if (member-equal a x)
               (1- (set-size-equal x))
             (set-size-equal x))))

  (defcong list-equiv equal (set-size-equal x) 1)

  (defthm set-size-when-subsetp
    (implies (subsetp-equal x y)
             (<= (set-size-equal x)
                 (set-size-equal y)))
    :hints (("Goal"
             :use (:instance len-when-no-duplicatesp-and-subsetp
                   (x (remove-duplicates-equal x))
                   (y (remove-duplicates-equal y))))))

  (defthm set-size-when-subsetp-linear
    (implies (subsetp-equal x y)
             (<= (set-size-equal x)
                 (set-size-equal y)))
    :hints (("Goal" :by set-size-when-subsetp))
    :rule-classes :linear)

  (defthm set-size-when-strict-subsetp
    (implies (and (subsetp-equal x y)
                  (not (subsetp-equal y x)))
             (< (set-size-equal x)
                (set-size-equal y)))
    :hints (("Goal"
             :use (:instance len-when-no-duplicatesp-and-strict-subsetp
                   (x (remove-duplicates-equal x))
                   (y (remove-duplicates-equal y))))))

  (defthm set-size-when-strict-subsetp-linear
    (implies (and (subsetp-equal x y)
                  (not (subsetp-equal y x)))
             (< (set-size-equal x)
                (set-size-equal y)))
    :hints (("Goal" :by set-size-when-strict-subsetp))
    :rule-classes :linear)

  (defthm set-size-when-set-equiv
    (implies (set-equiv x y)
             (equal (set-size-equal x)
                    (set-size-equal y)))
    :hints (("Goal"
             :in-theory (e/d (set-equiv) (set-size-when-subsetp))
             :use (set-size-when-subsetp
                   (:instance set-size-when-subsetp (x y) (y x))))))

  (defthm set-size-when-set-equiv-linear
    (implies (set-equiv x y)
             (equal (set-size-equal x)
                    (set-size-equal y)))
    :hints (("Goal" :by set-size-when-set-equiv))
    :rule-classes :linear)

  (defcong set-equiv equal (set-size-equal x) 1
    :hints (("Goal"
             :use (:instance set-size-when-set-equiv (y x-equiv))
             :in-theory (disable set-size-when-set-equiv)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-theory (disable set-size-equal))

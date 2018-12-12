; This book contains the standard mini-proveall from ACL2 Version 2.9.4 (and
; perhaps beyond), with comments ";;;" added as necessary.

; This book is used in mini-proveall-plus.lisp, which discusses Double-rewrite
; warnings from this book.

(in-package "ACL2")

;;; (defmacro mini-proveall nil

; ACL2 (a)>:mini-proveall

; will change the default-defun-mode to :logic and do a short proveall.  The
; final defun-mode will be :logic.

;;;  '(ld
;;;    '(:logic

; We start with a nice example of forcing, involving primitive fns.

;;;      (thm (implies (and (true-listp x)
;;;                         (true-listp y))
;;;                    (equal (revappend (append x y) z)
;;;                           (revappend y (revappend x z)))))
      (defun app (x y)
        (if (consp x)
            (cons (car x) (app (cdr x) y))
            y))
      (defthm assoc-of-app
        (equal (app (app a b) c) (app a (app b c))))
      (defun rev (x)
        (if (consp x)
            (app (rev (cdr x)) (cons (car x) nil))
            nil))
      (defthm true-listp-rev
        (true-listp (rev x))
        :rule-classes (:REWRITE :GENERALIZE))

; Here we test the proof-builder using the same theorem as the one that
; follows (but not storing it as a :rewrite rule).

      (defthm rev-app-proof-builder
        (equal (rev (app a b)) (app (rev b) (rev a)))
        :rule-classes nil
        :instructions
        (:induct :bash :induct :bash :split (:dv 1)
                 :x :nx (:dv 1)
                 :x :top :s :bash (:dive 1 1)
                 := (:drop 2)
                 :top :bash))
      (defthm rev-app
        (equal (rev (app a b)) (app (rev b) (rev a))))
      (defthm rev-rev
        (implies (true-listp x) (equal (rev (rev x)) x)))

;    The following events are the big example in deflabel equivalence.

      (encapsulate (((lt * *) => *))
                   (local (defun lt (x y) (declare (ignore x y)) nil))
                   (defthm lt-non-symmetric (implies (lt x y) (not (lt y x)))))

      (defun insert (x lst)
        (cond ((atom lst) (list x))
              ((lt x (car lst)) (cons x lst))
              (t (cons (car lst) (insert x (cdr lst))))))

      (defun insert-sort (lst)
        (cond ((atom lst) nil)
              (t (insert (car lst) (insert-sort (cdr lst))))))

      (defun del (x lst)
        (cond ((atom lst) nil)
              ((equal x (car lst)) (cdr lst))
              (t (cons (car lst) (del x (cdr lst))))))

      (defun mem (x lst)
        (cond ((atom lst) nil)
              ((equal x (car lst)) t)
              (t (mem x (cdr lst)))))

      (defun perm (lst1 lst2)
        (cond ((atom lst1) (atom lst2))
              ((mem (car lst1) lst2)
               (perm (cdr lst1) (del (car lst1) lst2)))
              (t nil)))

      (defthm perm-reflexive
        (perm x x))

      (defthm perm-cons
        (implies (mem a x)
                 (equal (perm x (cons a y))
                        (perm (del a x) y)))
        :hints (("Goal" :induct (perm x y))))

      (defthm perm-symmetric
        (implies (perm x y) (perm y x)))

      (defthm mem-del
        (implies (mem a (del b x)) (mem a x))
        :rule-classes ((:rewrite :match-free :once)))

      (defthm perm-mem
        (implies (and (perm x y)
                      (mem a x))
                 (mem a y))
        :rule-classes ((:rewrite :match-free :once)))

      (defthm mem-del2
        (implies (and (mem a x)
                      (not (equal a b)))
                 (mem a (del b x))))

      (defthm comm-del
        (equal (del a (del b x)) (del b (del a x))))

      (defthm perm-del
        (implies (perm x y)
                 (perm (del a x) (del a y))))

      (defthm perm-transitive
        (implies (and (perm x y) (perm y z)) (perm x z))
        :rule-classes ((:rewrite :match-free :once)))

      (defequiv perm)

      (in-theory (disable perm perm-reflexive perm-symmetric perm-transitive))

      (defcong perm perm (cons x y) 2)

      (defcong perm iff (mem x y) 2)

      (defthm atom-perm
        (implies (not (consp x)) (perm x nil))
        :rule-classes :forward-chaining
        :hints (("Goal" :in-theory (enable perm))))

      (defthm insert-is-cons
        (perm (insert a x) (cons a x)))

      (defthm insert-sort-is-id
        (perm (insert-sort x) x))

      (defcong perm perm (app x y) 2)

      (defthm app-cons
        (perm (app a (cons b c)) (cons b (app a c))))

      (defthm app-commutes
        (perm (app a b) (app b a)))

      (defcong perm perm (app x y) 1 :hints (("Goal" :induct (app y x))))

      (defthm rev-is-id (perm (rev x) x))

      (defun == (x y)
        (if (consp x)
            (if (consp y)
                (and (equal (car x) (car y))
                     (== (cdr x) (cdr y)))
                nil)
            (not (consp y))))

      (defthm ==-symmetric (== x x))

      (defthm ==-reflexive (implies (== x y) (== y x)))

      (defequiv ==)

      (in-theory (disable ==-symmetric ==-reflexive))

      (defcong == == (cons x y) 2)

      (defcong == iff (consp x) 1)

      (defcong == == (app x y) 2)

      (defcong == == (app x y) 1)

      (defthm rev-rev-again (== (rev (rev x)) x))

; This next block tests forcing.

      (defun ends-in-a-0 (x)
        (declare (xargs :guard t))
        (if (consp x) (ends-in-a-0 (cdr x)) (equal x 0)))

      (defun app0 (x y)
        (declare (xargs :guard (ends-in-a-0 x)))
        (if (ends-in-a-0 x)
            (if (equal x 0) y (cons (car x) (app0 (cdr x) y)))
            'default))

      (defun rev0 (x)
        (declare (xargs :guard (ends-in-a-0 x)))
        (if (ends-in-a-0 x)
            (if (equal x 0) 0 (app0 (rev0 (cdr x)) (cons (car x) 0)))
            'default))

      (defthm app0-right-id
        (implies (force (ends-in-a-0 x)) (equal (app0 x 0) x)))

      (defun ends-in-a-zero (x) (ends-in-a-0 x))

      (defthm ends-in-a-zero-app0
        (implies (force (ends-in-a-zero x)) (ends-in-a-0 (app0 x (cons y 0)))))

      (in-theory (disable ends-in-a-zero))

; The following theorem causes two forcing rounds.  In the first, there
; are three goals, all variants of one another.  An inductive proof of one
; of them is done and generates the second forcing round.

      (defthm force-test
        (and (implies (ends-in-a-0 x) (equal (app0 (rev0 x) 0) (rev0 x)))
             (implies (ends-in-a-0 y) (equal (app0 (rev0 y) 0) (rev0 y)))
             (implies (ends-in-a-0 z) (equal (app0 (rev0 z) 0) (rev0 z))))
        :hints (("[2]Goal" :in-theory (enable ends-in-a-zero))))

; This defun does a lot of proving for both termination and guard verification.

      (defun proper-cons-nest-p (x)
        (declare (xargs :guard (pseudo-termp x)))
        (cond ((symbolp x) nil)
              ((fquotep x) (true-listp (cadr x)))
              ((eq (ffn-symb x) 'cons)
               (proper-cons-nest-p (fargn x 2)))
              (t nil)))

; This defthm has two forcing rounds and is very realistic.

      (defthm ordered-symbol-alistp-remove1-assoc-eq-test
        (implies (and (ordered-symbol-alistp l)
                      (symbolp key)
                      (assoc-eq key l))
                 (ordered-symbol-alistp (remove1-assoc-eq key l)))
        :hints (("Goal" :in-theory (disable ordered-symbol-alistp-remove1-assoc-eq))))

;;;      )
;;;    :ld-skip-proofsp nil
;;;    :ld-redefinition-action nil
;;;    :ld-pre-eval-print t
;;;    :ld-error-action :return))

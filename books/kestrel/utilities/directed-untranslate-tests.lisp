; Copyright (C) 2016, Regents of the University of Texas
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

(in-package "ACL2")

(include-book "directed-untranslate")

; Examples below includes annotated traces with DU for directed-untranslate, LF
; for lambdafy, and WO for weak-one-way-unify.  Note that all of these examples
; were developed to help guide code development; thus, all traces shown were
; created by hand.  Moreover, while the comments (including by-hand traces)
; below are perhaps useful, they have generally not been kept up-to-date.  If
; one of them looks wrong, consider tracing the relevant functions and perhaps
; fixing the corresponding trace below.

; ------------------------------
; EXAMPLES.
; ------------------------------

(logic)
(local (include-book "misc/assert" :dir :system))
(local (include-book "misc/eval" :dir :system))
(defmacro local-test (&rest args)
  `(local (encapsulate () (local (progn ,@args)))))

; ------------------------------

; Example 1:

(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (assert! ; check lambdafy
  (equal (let ((tterm '((LAMBDA (X Y) (< Y (FOO X)))
                        (CONS A (CONS B 'NIL))
                        Y))
               (sterm '(< Y (BAR (CONS A (CONS B 'NIL))))))
           (lambdafy tterm sterm nil (w state)))
         '((LAMBDA (X Y) (< Y (BAR X)))
           (CONS A (CONS B 'NIL))
           Y)))
 (assert! ; check directed-untranslate
  (equal (let ((uterm '(let ((x (cons a (list b))))
                         (> (foo x) y)))
               (tterm '((LAMBDA (X Y) (< Y (FOO X)))
                        (CONS A (CONS B 'NIL))
                        Y))
               (sterm '(< Y (BAR (CONS A (CONS B 'NIL)))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET ((X (CONS A (LIST B))))
               (> (BAR X) Y)))))

; Below we show a motivating hand trace.  Before adding support for
; lambda applications, the call above of directed-untranslate
; returned the simple untranslation of sterm, (< Y (BAR (LIST A B)))

; 0> DU
; uterm: (let ((x (cons a (list b))))
;          (> (foo x) y))
; tterm: ((LAMBDA (X Y) (< Y (FOO X)))
;         (CONS A (CONS B 'NIL))
;         Y)
; sterm: (< Y (BAR (CONS A (CONS B 'NIL))))
; lflg: t

; 1> LF
; uterm: (let ((x (cons a (list b))))
;          (> (foo x) y))
; tterm: ((LAMBDA (X Y) (< Y (FOO X)))
;         (CONS A (CONS B 'NIL))
;         Y)
; sterm: (< Y (BAR (CONS A (CONS B 'NIL))))

; 2> WO
; tterm: (< Y (FOO X))
; sterm: (< Y (BAR (CONS A (CONS B 'NIL))))
; vars:  (x y)

; <2 WO
; ((x . (CONS A (CONS B 'NIL)))
;  (y . y))

; <1 LF
; ((LAMBDA (X Y) (< Y (BAR X)))
;  (CONS A (CONS B 'NIL))
;  Y)

; 1> DU
; uterm: (let ((x (cons a (list b))))
;          (> (foo x) y))
; tterm: ((LAMBDA (X Y) (< Y (FOO X)))
;         (CONS A (CONS B 'NIL))
;         Y)
; sterm: ((LAMBDA (X Y) (< Y (BAR X)))
;         (CONS A (CONS B 'NIL))
;         Y)
; lflg: nil

; 2> DU [lambda body]
; uterm: (> (foo x) y)
; tterm: (< Y (FOO X))
; sterm: (< Y (BAR X))
; lflg: nil

; <2 DU
; (> (BAR X) Y)

; 2> DU [lambda actuals]
; uterm: (cons a (list b))
; tterm: (CONS A (CONS B 'NIL))
; sterm: (CONS A (CONS B 'NIL))
; lflg: nil

; <2 DU
; (CONS A (LIST B))

; <1 DU [flg=nil]
; (LET ((X (CONS A (LIST B))))
;      (> (BAR X) Y))

; <0 DU [flg=t]
; (LET ((X (CONS A (LIST B))))
;      (> (BAR X) Y))

; ------------------------------

; Example 2:

; Next let's try nested let and let* expressions.

(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (defun g (x) (car x))
 (defun h (x) (car x))
 (defthm g-is-h
   (equal (foo x) (bar x)))
 (in-theory (disable g h))
 (assert!
  (equal (let ((tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (CONS A (CONS B 'NIL))
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (BAR (CONS A (CONS B 'NIL))))))
           (lambdafy tterm sterm nil (w state)))
         '((LAMBDA (X D C)
                   ((LAMBDA (Y X) (< Y (BAR X)))
                    (H (CONS C (CONS D 'NIL)))
                    X))
           (CONS A (CONS B 'NIL))
           D C)))
 (assert!
  (equal (let ((uterm '(let ((x (cons a (list b))))
                         (let ((y (g (cons c (list d)))))
                           (> (foo x) y))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (CONS A (CONS B 'NIL))
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (BAR (CONS A (CONS B 'NIL)))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET ((X (CONS A (LIST B))))
               (LET ((Y (H (CONS C (LIST D)))))
                    (> (BAR X) Y))))))

; Note this variant involving let*.

(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (defun g (x) (car x))
 (defun h (x) (car x))
 (defthm g-is-h
   (equal (foo x) (bar x)))
 (in-theory (disable g h))
 (assert!
  (equal (let ((uterm '(let* ((x (cons a (list b)))
                              (y (g (cons c (list d)))))
                         (> (foo x) y)))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (CONS A (CONS B 'NIL))
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (BAR (CONS A (CONS B 'NIL)))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET* ((X (CONS A (LIST B)))
                 (Y (H (CONS C (LIST D)))))
                (> (BAR X) Y)))))

; Before handling lambda applications, directed-untranslate lost > and (cons a
; (list b)), instead returning: (< (H (LIST C D)) (BAR (LIST A B))).

; 0> DU
; uterm: (let ((x (cons a (list b))))
;          (let ((y (g (cons c (list d)))))
;            (> (foo x) y)))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (CONS A (CONS B 'NIL))
;         D C)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))
; lflg: t

; 1> LF
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (CONS A (CONS B 'NIL))
;         D C)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))

; 2> WO
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))
; vars:  (x d c)

; 3> LF
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))

; 4> WO
; tterm: (< Y (FOO X))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (BAR (CONS A (CONS B 'NIL))))
; vars: (y x)

; <4 WO
; ((y . (H (CONS C (CONS D 'NIL))))
;  (x . (CONS A (CONS B 'NIL))))

; <3 LF
; ((LAMBDA (Y X) (< Y (BAR X)))
;  (H (CONS C (CONS D 'NIL)))
;  (CONS A (CONS B 'NIL)))

; 3> WO [with lambda in sterm]
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X) (< Y (BAR X)))
;         (H (CONS C (CONS D 'NIL)))
;         (CONS A (CONS B 'NIL)))
; vars:  (x d c)

; <3 WO [lflg=nil]
; ((x . (CONS A (CONS B 'NIL)))
;  (d . d)
;  (c . c))

; <2 WO [lflg=t]
; ((x . (CONS A (CONS B 'NIL)))
;  (d . d)
;  (c . c))

; <1 LF
; ((LAMBDA (X D C)
;          ((LAMBDA (Y X) (< Y (BAR X)))
;           (H (CONS C (CONS D 'NIL)))
;           X))
;  (CONS A (CONS B 'NIL))
;  D C)

; 1> DU [lflg=nil]
; uterm: (let ((x (cons a (list b))))
;          (let ((y (g (cons c (list d)))))
;            (> (foo x) y)))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (CONS A (CONS B 'NIL))
;         D C)
; sterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (BAR X)))
;                  (H (CONS C (CONS D 'NIL)))
;                  X))
;         (CONS A (CONS B 'NIL))
;         D C)
; lflg: nil

; 2> DU [lambda body]
; uterm: (let ((y (g (cons c (list d)))))
;          (> (foo x) y))
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X) (< Y (BAR X)))
;         (H (CONS C (CONS D 'NIL)))
;         X)
; lflg: nil

; 3> DU [lambda body]
; uterm: (> (foo x) y)
; tterm: (< Y (FOO X))
; sterm: (< Y (BAR X))
; lflg: nil

; <3 DU
; (> (BAR X) Y)

; 3> DU [lambda actuals]
; uterm: (g (cons c (list d)))
; tterm: (G (CONS C (CONS D 'NIL)))
; sterm: (H (CONS C (CONS D 'NIL)))
; lflg: nil

; <3 DU
; (H (CONS C (LIST D)))

; <2 DU
; (LET ((Y (H (CONS C (LIST D)))))
;      (> (BAR X) Y))

; 2> DU [lambda actuals]
; uterm: (cons a (list b))
; tterm: (CONS A (CONS B 'NIL))
; sterm: (CONS A (CONS B 'NIL))
; lflg: nil

; <2 DU
; (CONS A (LIST B))

; <1 DU [lflg=nil]
; (LET ((X (CONS A (LIST B))))
;      (LET ((Y (H (CONS C (LIST D)))))
;           (> (BAR X) Y)))

; <0 DU [lflg=t]
; (LET ((X (CONS A (LIST B))))
;      (LET ((Y (H (CONS C (LIST D)))))
;           (> (BAR X) Y)))

; ------------------------------

; Example 3:

; This example shows how to handle the case that matching isn't as
; straightforward.  (The example below will make clear what that means.)

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))
 (assert!
  (equal (let ((tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A))))
           (lambdafy tterm sterm nil (w state)))
         '((LAMBDA (X D C)
                   ((LAMBDA (Y X) (< Y (MESS X)))
                    (H (CONS C (CONS D 'NIL)))
                    X))
           A D C)))
 (assert!
  (equal (let ((uterm '(let ((x (dup a)))
                         (let ((y (g (cons c (list d)))))
                           (> (foo x) y))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET ((X A))
               (LET ((Y (H (CONS C (LIST D)))))
                    (> (MESS X) Y))))))

; Note this variant involving let*.

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))
 (assert!
  (equal (let ((uterm '(let* ((x (dup a))
                              (y (g (cons c (list d)))))
                         (> (foo x) y)))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X) (< Y (FOO X)))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET* ((X A)
                 (Y (H (CONS C (LIST D)))))
                (> (MESS X) Y)))))

; Before directed-untranslate gave special handling for lambda applications,
; the call of directed-untranslate above returned (< (H (LIST C D)) (MESS A)).

; What result would we actually like?  Here are some reasonable choices.

; (a)
; (> (MESS A) (H (CONS C (LIST D))))

; (b)
; (LET ((Y (H (CONS C (LIST D)))))
;      (> (MESS A) Y))

; (c)
; (LET ((X (MESS A)))
;      (LET ((Y (H (CONS C (LIST D)))))
;           (> X Y)))

; Clearly (b) is better than (a).  Each of (b) and (c) has its advantages.  At
; first glance (c) is better, because it preserves the lambda-related structure
; of tterm.  But (c) is perhaps confusing, because x is bound to the
; simplification of (foo (dup a)), rather than (dup a) as in tterm.  A big
; advantage of (c) is that if there were many occurrences of (mess a), and if
; (mess a) were instead a large expression, then (b) could execute very slowly.
; Consider our real goal here: we want lambdafy to set things up so that
; directed-untranslate can produce a nice result.  In (b), (mess a) would be
; compared with (foo x).  In (c), (mess a) would be compared with (dup a).
; There isn't a clear winner as far as I can tell, though perhaps (c) is a bit
; more natural since both involve the variable, a.  So it is tempting go with
; (c) because of its better execution efficiency.

; However, if we look more closely at the original uterm, we see that if (mess
; a) occurs many times in sterm, then (foo x) could easily occur many times in
; uterm.  So we aren't necessarily losing execution efficiency.  See Example 4.

; In short: we always preserve the lambda structure in whatever way seems
; natural algorithmically.  If examples later suggest that this approach needs
; revising, they can provide guidance for how to proceed.

; 0> DU
; uterm: (let ((x (dup a)))
;          (let ((y (g (cons c (list d)))))
;            (> (foo x) y)))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; lflg: t

; 1> LF
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 2> WO
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars:  (x d c)

; 3> LF
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 4> WO
; tterm: (< Y (FOO X))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars: (y x)

; NOTE: Here is where trying to obtain a result of type (c) seems to break
; down.  The natural solution to this (weak-)one-way-unification problem is to
; bind x to a.

; <4 WO
; ((y . (H (CONS C (CONS D 'NIL))))
;  (x . A))

; <3 LF (matching y only, not x)
; ((LAMBDA (Y X) (< Y (MESS X)))
;  (H (CONS C (CONS D 'NIL)))
;  A)

; 3> WO [after lambdafying sterm]
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X) (< Y (MESS X)))
;         (H (CONS C (CONS D 'NIL)))
;         A)
; vars:  (x d c)

; <3 WO [after lambdafying sterm]
; ((x . a)
;  (d . d)
;  (c . c))

; <2 WO
; ((x . a)
;  (d . d)
;  (c . c))

; <1 LF
; ((LAMBDA (X D C)
;          ((LAMBDA (Y X) (< Y (MESS X)))
;           (H (CONS C (CONS D 'NIL)))
;           X))
;  A D C)

; 1> DU [lflg=nil]
; uterm: (let ((x (dup a)))
;          (let ((y (g (cons c (list d)))))
;            (> (foo x) y)))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (FOO X)))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X) (< Y (MESS X)))
;                  (H (CONS C (CONS D 'NIL)))
;                  X))
;         A D C)
; lflg: nil

; 2> DU [lambda body]
; uterm: (let ((y (g (cons c (list d)))))
;          (> (foo x) y))
; tterm: ((LAMBDA (Y X) (< Y (FOO X)))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X) (< Y (MESS X)))
;         (H (CONS C (CONS D 'NIL)))
;         X)
; lflg: nil

; 3> DU [lambda body]
; uterm: (> (foo x) y)
; tterm: (< Y (FOO X))
; sterm: (< Y (MESS X))
; lflg: nil

; <3 DU
; (> (MESS X) Y)

; 3> DU [lambda actuals]
; uterm: (g (cons c (list d)))
; tterm: (G (CONS C (CONS D 'NIL)))
; sterm: (H (CONS C (CONS D 'NIL)))
; lflg: nil

; <3 DU
; (H (CONS C (LIST D)))

; <2 DU
; (LET ((Y (H (CONS C (LIST D)))))
;      (> (MESS X) Y))

; 2> DU [lambda actuals]
; uterm: (dup a)
; tterm: (DUP A)
; sterm: A
; lflg: nil

; <2 DU
; A

; <1 DU
; (LET ((X A))
;      (LET ((Y (H (CONS C (LIST D)))))
;           (> (MESS X) Y)))

; I suppose we could consider beta-reducing when the variable only occurs once,
; as above (though that would require some thought).  But it seems to make
; sense to preserve the structure when reasonably possible.

; ------------------------------

; Example 4:

; In Example 3 we discussed a concern about preserving sharing.  This example
; shows how that can work out OK.

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))

 (assert!
  (equal (let ((tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A))))
           (lambdafy tterm sterm nil (w state)))
         '((LAMBDA (X D C)
                   ((LAMBDA (Y X)
                            ((LAMBDA (Z Y) (< Y Z)) (MESS X) Y))
                    (H (CONS C (CONS D 'NIL)))
                    X))
           A D C)))
 (assert!
  (equal (let ((uterm '(let ((x (dup a)))
                         (let ((y (g (cons c (list d)))))
                           (let ((z (foo x)))
                             (> z y)))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET ((X A))
               (LET ((Y (H (CONS C (LIST D)))))
                    (LET ((Z (MESS X)))
                         (> Z Y)))))))

; Note these variants involving let*.

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))

 (assert!
  (equal (let ((uterm '(let* ((x (dup a))
                              (y (g (cons c (list d))))
                              (z (foo x)))
                         (> z y)))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET* ((X A)
                 (Y (H (CONS C (LIST D))))
                 (Z (MESS X)))
                (> Z Y)))))

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))

 (assert!
  (equal (let ((uterm '(let* ((x (dup a))
                              (y (g (cons c (list d)))))
                         (let ((z (foo x)))
                           (> z y))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET* ((X A)
                 (Y (H (CONS C (LIST D)))))
                (LET ((Z (MESS X)))
                     (> Z Y))))))

(local-test
 (defun foo (x) (car x)) ; as before
 (defund g (x) (car x))  ; as before
 (defund h (x) (car x))  ; as before
 (defund mess (x) ; imagine a complicated expression in place of (mess a)
   (expt x x))
 (defun dup (x) (cons (mess x) x))
 (defthm foo-dup
   (equal (foo (dup x)) (mess x)))
 (in-theory (disable dup))
 (defthm g-is-h
   (equal (g x) (h x))
   :hints (("Goal" :in-theory (enable g h))))

 (assert!
  (equal (let ((uterm '(let ((x (dup a)))
                         (let* ((y (g (cons c (list d))))
                                (z (foo x)))
                           (> z y))))
               (tterm '((LAMBDA (X D C)
                                ((LAMBDA (Y X)
                                         ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
                                 (G (CONS C (CONS D 'NIL)))
                                 X))
                        (DUP A)
                        D C))
               (sterm '(< (H (CONS C (CONS D 'NIL)))
                          (MESS A)))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET ((X A))
               (let* ((Y (H (CONS C (LIST D))))
                      (Z (MESS X)))
                 (> Z Y))))))

; Without attention to lambdas, the result above was formerly
; (< (H (LIST C D)) (MESS A)).

; 0> DU
; uterm: (let ((x (dup a)))
;          (let ((y (g (cons c (list d)))))
;            (let ((z (foo x)))
;              (> z y))))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X)
;                          ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; lflg: t

; 1> LF
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X)
;                          ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 2> WO
; tterm: ((LAMBDA (Y X)
;                 ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars:  (x d c)
; lflg: t

; 3> LF
; tterm: ((LAMBDA (Y X)
;                 ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 4> WO
; tterm: ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars: (y x)

; 5> LF
; tterm: ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))

; 6> WO
; tterm: (< Y Z)
; sterm: (< (H (CONS C (CONS D 'NIL)))
;           (MESS A))
; vars: (z y)

; <6 WO
; ((y . (H (CONS C (CONS D 'NIL))))
;  (z . (MESS A)))

; <5 LF
; ((LAMBDA (Z Y) (< Y Z))
;  (MESS A)
;  (H (CONS C (CONS D 'NIL))))

; 4> WO [after lambdafy]
; tterm: ((LAMBDA (Z Y) (< Y Z))
;         (FOO X)
;         Y)
; sterm: ((LAMBDA (Z Y) (< Y Z))
;         (MESS A)
;         (H (CONS C (CONS D 'NIL))))
; vars: (y x)

; <4 WO [after lambdafy]
; ((y . (H (CONS C (CONS D 'NIL))))
;  (x . a))

; <3 LF
; ((LAMBDA (Y X)
;          ((LAMBDA (Z Y) (< Y Z))
;           (MESS X)
;           Y))
;  (H (CONS C (CONS D 'NIL)))
;  A)

; 2> WO [after lambdafy]
; tterm: ((LAMBDA (Y X)
;                 ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;         (G (CONS C (CONS D 'NIL)))
;         X)
; sterm: ((LAMBDA (Y X)
;                 ((LAMBDA (Z Y) (< Y Z)) (MESS X) Y))
;         (H (CONS C (CONS D 'NIL)))
;         A)
; vars:  (x d c)

; <2 WO
; ((x . a) (d . d) (c . c))

; <1 LF
; ((LAMBDA (X D C)
;          ((LAMBDA (Y X)
;                   ((LAMBDA (Z Y) (< Y Z)) (MESS X) Y))
;           (H (CONS C (CONS D 'NIL)))
;           X))
;  A D C)

; 1> DU [lflg=nil]
; uterm: (let ((x (dup a)))
;          (let ((y (g (cons c (list d)))))
;            (let ((z (foo x)))
;              (> z y))))
; tterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X)
;                          ((LAMBDA (Z Y) (< Y Z)) (FOO X) Y))
;                  (G (CONS C (CONS D 'NIL)))
;                  X))
;         (DUP A)
;         D C))
; sterm: ((LAMBDA (X D C)
;                 ((LAMBDA (Y X)
;                          ((LAMBDA (Z Y) (< Y Z)) (MESS X) Y))
;                  (H (CONS C (CONS D 'NIL)))
;                  X))
;         A D C)
; lflg: nil

; <1 DU
; (let ((x a))
;   (let ((y (h (cons c (list d)))))
;     (let ((z (mess x)))
;       (> z y))))

; <0 DU
; (let ((x a))
;   (let ((y (h (cons c (list d)))))
;     (let ((z (mess x)))
;       (> z y))))

; ------------------------------

; Example 5: In this set of examples we deal with avoiding variable capture.

; Adapted from Example 2:
(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (defun g (x) (car x))
 (defun h (x) (car x))
 (defthm g-is-h
   (equal (foo x) (bar x)))
 (in-theory (disable g h))

 (assert!
  (equal (let ((tterm '((LAMBDA (X A)
                                ((LAMBDA (X A) (< A (FOO X))) (G X) A))
                        (CONS A (CONS B 'NIL))
                        A))
               (sterm '(< A (BAR (H (CONS A (CONS B 'NIL)))))))
           (lambdafy tterm sterm nil (w state)))
         '((LAMBDA (X A)
                   ((LAMBDA (X A) (< A (BAR X)))
                    (H X)
                    A))
           (CONS A (CONS B 'NIL))
           A)))
 (assert!
  (equal (let ((uterm '(let ((x (cons a (list b))))
                         (let ((x (g x)))
                           (> (foo x) a))))
               (tterm '((LAMBDA (X A)
                                ((LAMBDA (X A) (< A (FOO X))) (G X) A))
                        (CONS A (CONS B 'NIL))
                        A))
               (sterm '(< A (BAR (H (CONS A (CONS B 'NIL))))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET ((X (CONS A (LIST B))))
               (LET ((X (H X)))
                    (> (BAR X) A))))))

; Note this variant involving let*.

(local-test
 (defun foo (x) (car x))
 (defun bar (x) (car x))
 (defthm foo-is-bar
   (equal (foo x) (bar x)))
 (in-theory (disable foo bar))
 (defun g (x) (car x))
 (defun h (x) (car x))
 (defthm g-is-h
   (equal (foo x) (bar x)))
 (in-theory (disable g h))

 (assert!
  (equal (let ((uterm '(let* ((x (cons a (list b)))
                              (x (g x)))
                         (> (foo x) a)))
               (tterm '((LAMBDA (X A)
                                ((LAMBDA (X A) (< A (FOO X))) (G X) A))
                        (CONS A (CONS B 'NIL))
                        A))
               (sterm '(< A (BAR (H (CONS A (CONS B 'NIL))))))
               (iff-flg nil)
               (wrld (w state)))
           (directed-untranslate uterm tterm sterm iff-flg nil wrld))
         '(LET* ((X (CONS A (LIST B)))
                 (X (H X)))
                (> (BAR X) A)))))

; Before handling lambdas specially, directed-untranslate returned
; (< A (BAR (H (LIST A B)))).

; 0> DU
; uterm: (let ((x (cons a (list b))))
;          (let ((x (g x)))
;            (> (foo x) a)))
; tterm: ((LAMBDA (X A)
;                 ((LAMBDA (X A) (< A (FOO X))) (G X) A))
;         (CONS A (CONS B 'NIL))
;         A)
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))
; lflg: t

; 1> LF
; tterm: ((LAMBDA (X A)
;                 ((LAMBDA (X A) (< A (FOO X))) (G X) A))
;         (CONS A (CONS B 'NIL))
;         A)
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))

; 2> WO
; tterm: ((LAMBDA (X A) (< A (FOO X))) (G X) A)
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))
; vars:  (x a)

; 3> LF
; tterm: ((LAMBDA (X A) (< A (FOO X))) (G X) A)
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))

; 4> WO
; tterm: (< A (FOO X))
; sterm: (< A (BAR (H (CONS A (CONS B 'NIL)))))
; vars: (x a)

; <4 WO
; ((A . A)
;  (X . (H (CONS A (CONS B 'NIL)))))

; <3 LF
; ((LAMBDA (X A) (< A (BAR X)))
;  (H (CONS A (CONS B 'NIL)))
;  A)

; 3> WO [after lambdafy]
; tterm: ((LAMBDA (X A) (< A (FOO X)))
;         (G X)
;         A)
; sterm: ((LAMBDA (X A) (< A (BAR X)))
;         (H (CONS A (CONS B 'NIL)))
;         A)
; vars:  (x a)

; <3 WO [after lambdafy]
; ((X . (CONS A (CONS B 'NIL)))
;  (A . A))

; <2 WO
; ((X . (CONS A (CONS B 'NIL)))
;  (A . A))

; <1 LF
; ((LAMBDA (X A)
;          ((LAMBDA (X A) (< A (BAR X)))
;           (H X)
;           A))
;  (CONS A (CONS B 'NIL))
;  A)

; 1> DU [lflg=nil]
; uterm: (let ((x (cons a (list b))))
;          (let ((x (g x)))
;            (> (foo x) a)))
; tterm: ((LAMBDA (X A)
;                 ((LAMBDA (X A) (< A (FOO X))) (G X) A))
;         (CONS A (CONS B 'NIL))
;         A)
; sterm: ((LAMBDA (X A)
;                 ((LAMBDA (X A) (< A (BAR X))) (H X) A))
;         (CONS A (CONS B 'NIL))
;         A)
; lflg: nil

; 2> DU [lambda body]
; uterm: (let ((x (g x)))
;          (> (foo x) a))
; tterm: ((LAMBDA (X A) (< A (FOO X))) (G X) A)
; sterm: ((LAMBDA (X A) (< A (BAR X))) (H X) A)
; lflg: nil

; 3> DU [lambda body]
; uterm: (> (foo x) a)
; tterm: (< A (FOO X))
; sterm: (< A (BAR X))
; lflg: nil

; <3 DU
; (> (BAR X) A)

; 3> DU [lambda actuals]
; uterm: (g x)
; tterm: (G X)
; sterm: (H X)
; lflg: nil

; <3 DU
; (H X)

; <2 DU
; (LET ((X (H X)))
;      (> (BAR X) A))

; 2> DU [lambda actuals]
; uterm: (cons a (list b))
; tterm: (CONS A (CONS B 'NIL))
; sterm: (CONS A (CONS B 'NIL))
; lflg: nil

; <2 DU
; (CONS A (LIST B))

; <1 DU [lflg=nil]
; (LET ((X (CONS A (LIST B))))
;      (LET ((X (H X)))
;           (> (BAR X) A)))

; <0 DU [lflg=t]
; (LET ((X (CONS A (LIST B))))
;      (LET ((X (H X)))
;           (> (BAR X) A)))

; ------------------------------

; Validate claims made in the documentation:

(local-test
 (assert!
  (let ((sterm '(if a2 (if b2 c2 'nil) 'nil)))
    (and (equal (directed-untranslate
                 '(and a (if b c nil))     ; uterm
                 '(if a (if b c 'nil) 'nil) ; tterm
                 sterm                      ; sterm, a form to be untranslated
                 nil nil
                 (w state))
                '(AND A2 (IF B2 C2 NIL)))
         (equal (untranslate sterm nil (w state))
                '(AND A2 B2 C2))))))

; Example: A challenge for avoiding capture.

(local-test

(defconst *uterm0*
  '(let ((y (cons x y))) (cons (cdr y) y)))

(defconst *tterm0*
  '((LAMBDA (Y) (CONS (CDR Y) Y))
    (CONS X Y)))

(defconst *sterm0*
  '(cons y (cons x y)))

; The following shows that uterm and tterm correspond:

(assert!
 (equal (untranslate '((LAMBDA (Y) (CONS (CDR Y) Y))
                       (CONS X Y))
                     nil
                     (w state))
        '(let ((y (cons x y))) (cons (cdr y) y))))

; Notice that uterm and sterm agree, though that's not really important here.

(must-succeed
 (thm (equal (let ((y (cons x y))) (cons (cdr y) y))
             (cons y (cons x y)))))


; Now let's apply directed-untranslate to get a version of *sterm0*, namely
; *sterm0-simp*, that is a LET (since *uterm0* is a LET).

(make-event
 `(defconst *sterm0-simp*
    ',(directed-untranslate *uterm0* *tterm0* *sterm0* nil nil (w state))))

; In our initial implementation, we had capture!
; Compare with *sterm0*: (CONS Y (CONS X Y))
; Fortunately, that capture no longer happens:

(assert! ; no longer have capture:
 (not (equal *sterm0-simp*
             '(LET ((Y (CONS X Y))) (CONS Y Y)))))

(assert! ; instead we get this:
 (equal *sterm0-simp*
        '(LET ((Y1 (CONS X Y))) (CONS Y Y1))))

; The prover validates this:

(make-event
 `(defthm s0-simp-test
    (equal ,*sterm0* ,*sterm0-simp*)
    :rule-classes nil))

; The real problem was with lambdafy.  Notice that this isn't a problem:

(assert!
 (equal
  (lambdafy '((LAMBDA (Y1) (CONS (CDR Y1) Y1))
              (CONS X Y))
            '(CONS Y (CONS X Y))
            nil
            (w state))
  '((LAMBDA (Y1 Y) (CONS Y Y1))
    (CONS X Y)
    Y)))

; But when the lambda variable is y, there was capture.

(assert!
 (equal
  (lambdafy '((LAMBDA (Y) (CONS (CDR Y) Y))
              (CONS X Y))
            '(CONS Y (CONS X Y))
            nil
            (w state))
; Formerly ((LAMBDA (Y) (CONS Y Y)) (CONS X Y))
  '((LAMBDA (Y1 Y) (CONS Y Y1))
    (CONS X Y)
    Y)))

; Notice that there needn't always be capture even when it looks like that
; might be possible.  Consider the following example, which succeeded even
; before we dealt with the capture problem, because weak-one-way-unify binds y
; to (cons x y) and there is no occurrence of the "outer" (global) y remaining
; after the abstraction.

(assert!
 (let ((tterm '((LAMBDA (Y) (CONS Y Y))
                (CONS X Y)))
       (sterm '(CONS (CONS X Y) (CONS X Y))))
   (equal (lambdafy tterm sterm nil (w state))
          tterm)))

; But imagine that we alpha-convert tterm in this example, replacing y by y1.
; Then the result would contain y1.  But that's not so bad, as it eliminates some
; potential confusion; for example, the untranslated result would then be
; (LET ((Y1 (CONS X Y))) (CONS Y1 Y1)),
; which makes clear the distinction between the two "Y" variables.

(assert!
 (let ((tterm '((LAMBDA (Y1) (CONS Y1 Y1))
                (CONS X Y)))
       (sterm '(CONS (CONS X Y) (CONS X Y))))
   (equal (lambdafy tterm sterm nil (w state))
          tterm)))

; So for purposes of lambdafy, we will initially rename top-level lambda
; formals in tterm that occur in sterm.  This may do more renaming than
; necessary, so we fix that; see lambdafy-restore and lambdafy-restore1.

)

; Example: A very thorny problem with capture.

(local-test

(defstub f1 (x1 x2) T)

(defun f2 (x1 x2 x3)
  (declare (ignore x2))
  (append x1 x3))

(defstub f3 (x1) t)

(defun f4 (x1 x2)
  (let* ((x3 (f3 x1))
	 (x4 (f2 x3 x1 x2)))
    (f1 x1 x4)))

; A preliminary attempt to deal with capture led to the following ugly (though
; correct) result.

#|
  (let ((x3 (f3 x1))
        (x2 x4)
        (x5 x2))
    (let* ((x4 (append x3 x5)))
      (f1 x1 x4)))
|#

; Now we get a nicer result.  See a long comment in weak-one-way-unify-rec
; about why an attempt to match and f2 call with a binary-append call fails
; (which leads to the dropping of the outer let* binding).

(assert!
 (equal
  (directed-untranslate '(let* ((x3 (f3 x1))
                                (x4 (f2 x3 x1 x2)))
                           (f1 x1 x4))
                        '((lambda (x3 x2 x1)
                            ((lambda (x4 x1) (f1 x1 x4))
                             (f2 x3 x1 x2)
                             x1))
                          (f3 x1)
                          x2
                          x1)
                        '(f1 x1 (binary-append (f3 x1) x2))
                        nil nil
                        (w state))
  '(LET* ((X3 (F3 X1))
          (X4 (APPEND X3 X2)))
         (F1 X1 X4))))

; Worse yet, the result could be not only ugly, but confusing.  Consider the
; following variant of f4.

(defun f5 (x y)
  (let* ((z (f3 x))
	 (y (f2 z x y)))
    (f1 x y)))

; We expect (f2 z x y) to simplify to (append z y), and happily, with the
; current version of directed-untranslate, it does:

(assert!
 (equal
  (directed-untranslate '(let* ((z (f3 x))
                                (y (f2 z x y)))
                           (f1 x y))
                        '((lambda (z y x)
                            ((lambda (y x) (f1 x y)) (f2 z x y) x))
                          (f3 x)
                          y
                          x)
                        '(f1 x (binary-append (f3 x) y))
                        nil nil
                        (w state))
  '(let* ((z (f3 x))
          (y (append z y)))
     (f1 x y))))

; A preliminary attempt to deal with capture produced the following, which is
; quite confusing (though correct) because the second argument to append is
; based on the symbol X rather than, as above, on the symbol Y.

#||
  (let ((z (f3 x))
        (y y1)
        (x1 y))
    (let* ((y (append z x1)))
      (f1 x y)))
||#

)

; The following once produced this bad result for directed-untranslate:
; (LET ((ALL-R R)) (APPEND (F1 C) C))

(local-test
 (defstub f1 (x) t)
 (defun app3 (r c ign)
   (declare (ignore ign))
   (append r c))
 (defun f2 (c)
   (f1 c))
 (defun g (c)
   (let* ((all-r (f2 c))
          (r all-r))
     (app3 r c 17)))
 (assert!
  (equal (directed-untranslate
          '(let* ((all-r (f2 c)) (r all-r))
             (app3 r c 17))
          '((lambda (all-r c)
              ((lambda (r c) (app3 r c '17)) all-r c))
            (f2 c)
            c)
          '(binary-append (f1 c) c)
          nil nil (w state))
         '(APPEND (F1 C) C))))

; ------------------------------

; Example 6: Handling of mv and mv-let

(local-test

(assert!
 (equal (let ((uterm '(mv (first x) (car (cons y y))))
              (tterm '(cons (car x) (cons (car (cons y y)) 'nil)))
              (sterm '(cons (car x) (cons y 'nil))))
          (directed-untranslate uterm tterm sterm nil nil (w state)))
        '(mv (first x) y)))

(defund foo (x y) (mv x y))
(defund foo2 (x y) (mv x y))
(defund bar (x y) (mv x y))
(defund bar2 (x y) (mv x y))

(assert!
 (equal (let ((uterm '(mv-let (x y) (foo x y) (bar x y)))
              (tterm '((lambda (mv) ((lambda (x y) (bar x y))
                                     (mv-nth '0 mv)
                                     (mv-nth '1 mv)))
                       (foo x y)))
              (sterm '(bar2 (mv-nth '0 (foo2 x y))
                            (mv-nth '1 (foo2 x y)))))
; !! Try '(nil nil) for exec-p.
          (directed-untranslate uterm tterm sterm nil nil (w state)))
        '(mv-let (x y) (foo2 x y) (bar2 x y))))

(assert!
 (equal (let ((uterm '(mv-let (x y) (foo x y) (bar x y)))
              (tterm '((lambda (mv) ((lambda (x y) (bar x y))
                                     (mv-nth '0 mv)
                                     (mv-nth '1 mv)))
                       (foo x y)))
              (sterm '(bar2 (car (foo2 x y))
                            (nth 1 (foo2 x y)))))
          (directed-untranslate uterm tterm sterm nil nil (w state)))
        '(mv-let (x y) (foo2 x y) (bar2 x y))))
)

; ------------------------------

; Example 7: List*

(local-test

(assert!
 (equal (let ((uterm '(list* a (car (cons y y))))
              (tterm '(cons a (car (cons y y))))
              (sterm '(cons a y))
              (iff-flg nil)
              (stobjs-out '(nil))
              (wrld (w state)))
          (directed-untranslate
           uterm tterm sterm iff-flg stobjs-out wrld))
        '(list* a y)))
)

; ------------------------------

; Example 8: Handling declare forms under LET, LET*, and MV-LET

; Handling of LET with type declaration form.

(local-test

(assert!
 (equal (let ((uterm '(let ((y (+ x x)))
                        (declare (type integer y))
                        (+ 0 y)))
              (tterm '((lambda (y)
                         (return-last 'progn
                                      (check-dcl-guardian (integerp y)
                                                          '(integerp y))
                                      (binary-+ '0 y)))
                       (binary-+ x x)))
              (sterm '(binary-+ x x))
              (iff-flg nil)
              (stobjs-out '(nil))
              (wrld (w state)))
          (directed-untranslate
           uterm tterm sterm iff-flg stobjs-out wrld))
        '(let ((y (+ x x))) y)))

; Handling of LET* with type declaration form.

(assert!
 (equal (let ((uterm '(let* ((y (* (first x) (first x)))
                             (y2 (+ y y)))
                        (declare (type integer y y2))
                        (+ 0 y2)))
              (tterm '((lambda
                         (y)
                         (return-last
                          'progn
                          (check-dcl-guardian (integerp y)
                                              '(integerp y))
                          ((lambda (y2)
                             (return-last
                              'progn
                              (check-dcl-guardian (integerp y2)
                                                  '(integerp y2))
                              (binary-+ '0 y2)))
                           (binary-+ y y))))
                       (binary-* (car x) (car x))))
              (sterm '(binary-+ (binary-* (car x) (car x))
                                (binary-* (car x) (car x))))
              (iff-flg nil)
              (stobjs-out '(nil))
              (wrld (w state)))
          (directed-untranslate
           uterm tterm sterm iff-flg stobjs-out wrld))
        '(let* ((y (* (first x) (first x)))
                (y2 (+ y y)))
           y2)))

; Handling of MV-LET with type declaration forms.

(defund foo (x y) (mv x y))
(defund foo2 (x y) (mv x y))
(defund bar (x y) (mv x y))
(defund bar2 (x y) (mv x y))

(assert!
 (equal (let ((uterm '(mv-let (x y)
                        (foo x y)
                        (declare (type integer x y))
                        (bar x y)))
              (tterm '((lambda
                         (mv)
                         ((lambda (x y)
                            (return-last
                             'progn
                             (return-last
                              'progn
                              (check-dcl-guardian (integerp x)
                                                  '(integerp x))
                              (check-dcl-guardian (integerp y)
                                                  '(integerp y)))
                             (bar x y)))
                          (mv-nth '0 mv)
                          (mv-nth '1 mv)))
                       (foo x y)))
              (sterm '(bar2 (mv-nth 0 (foo2 x y))
                            (mv-nth 1 (foo2 x y)))))
          (directed-untranslate uterm tterm sterm nil nil (w state)))
        '(mv-let (x y) (foo2 x y) (bar2 x y))))

; Handling of LET with ignore declaration form.

(assert!
 (equal (let ((uterm '(let ((y (first x)) (z x))
                        (declare (ignore z))
                        (+ y y)))
              (tterm '((lambda (y z) (binary-+ y y))
                       (car x)
                       (hide x)))
              (sterm '(binary-+ (car x) (car x))))
          (directed-untranslate uterm tterm sterm nil nil (w state)))
        '(let ((y (first x))) (+ y y))))
)

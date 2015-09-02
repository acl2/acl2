#|

In this book, we give counterexamples to the following formulas which are
theorems of arithmetic on the natural numbers.

  a+b = b+a             (a,b := 1,w)
  b < c  =>  b+a < c+a  (a,b,c := w,1,2)

  (b - a) + a  =  b     (a,b := 1, w)
                        (a,b := 2, 1)
  (a+b)-c  =  a+(b-c)   (a,b,c := w+1,1,2)
                        (a,b,c := 1,1,2)

  ab = ba               (a,b := 2,w)
  (b + c)a = ba + ca    (a,b,c := w,1,1)
  b < c  =>  ba < ca    (a,b,c := w,1,2)

  (ab)^c = (a^c)(b^c)   (a,b,c := 2,2,w)
  b < c  =>  b^a < c^a  (a,b,c := w,2,3)

|#

(in-package "ACL2")
(include-book "ordinal-definitions")
(local (disable-forcing))

(defconst *w* '((1 . 1) . 0))

(defthm |[a+b = b+a] counterexample|
  (let ((a 1)
        (b *w*))
    (not (implies (and (o-p a)
                       (o-p b))
                  (equal (o+ a b)
                         (o+ b a)))))
  :rule-classes nil)

(defthm |[b < c  =>  b+a < c+a] counterexample|
  (let ((a *w*)
        (b 1)
        (c 2))
    (not (implies (and (o-p a)
                       (o-p b)
                       (o-p c)
                       (o< b c))
                  (o< (o+ b a)
                      (o+ c a)))))
  :rule-classes nil)

(defthm |[(b - a) + a  =  b] counterexample|
  (let ((a 1)
        (b *w*))
    (not (implies (and (o-p a)
                       (o-p b))
                  (equal (o+ (o- b a) a)
                         b))))
  :rule-classes nil)

(defthm |[(b - a) + a  =  b] counterexample2|
  (let ((a 2)
        (b 1))
    (not (implies (and (o-p a)
                       (o-p b))
                  (equal (o+ (o- b a) a)
                         b))))
  :rule-classes nil)

(defthm |[(a+b)-c  =  a+(b-c)] counterexample|
  (let ((a (o+ *w* 1))
        (b 1)
        (c 2))
    (not (implies (and (o-p a)
                       (o-p b)
                       (o-p c))
                  (equal (o- (o+ a b) c)
                         (o+ a (o- b c))))))
  :rule-classes nil)

(defthm |[(a+b)-c  =  a+(b-c)] counterexample2|
  (let ((a 1)
        (b 1)
        (c 2))
    (not (implies (and (o-p a)
                       (o-p b)
                       (o-p c))
                  (equal (o- (o+ a b) c)
                         (o+ a (o- b c))))))
  :rule-classes nil)

(defthm |[ab = ba] counterexample|
  (let ((a 2)
        (b *w*))
    (not (implies (and (o-p a)
                       (o-p b))
                  (equal (o* a b)
                         (o* b a)))))
  :rule-classes nil)

(defthm |[(b + c)a = ba + ca] counterexample|
  (let ((a *w*)
        (b 1)
        (c 1))
    (not (implies (and (o-p a)
                       (o-p b)
                       (o-p c))
                  (equal (o* (o+ b c) a)
                         (o+ (o* b a) (o* c a))))))
  :rule-classes nil)

(defthm |[b < c  =>  ba < ca] counterexample|
  (let ((a *w*)
        (b 1)
        (c 2))
    (not (implies (and (o-p a)
                       (o-p b)
                       (o-p c)
                       (o< b c))
                  (o< (o* b a)
                      (o* c a)))))
  :rule-classes nil)

(defthm |[(ab)^c = (a^c)(b^c)] counterexample|
  (let ((a 2)
        (b 2)
        (c *w*))
    (not (implies (and (o-p a)
                       (o-p b)
                       (o-p c))
                  (equal (o^ (o* a b) c)
                         (o* (o^ a c) (o^ b c))))))
  :rule-classes nil)

(defthm |[b < c  =>  b^a < c^a] counterexample|
  (let ((a *w*)
        (b 2)
        (c 3))
    (not (implies (and (o-p a)
                       (o-p b)
                       (o-p c)
                       (o< b c))
                  (o< (o^ b a)
                      (o^ c a)))))
  :rule-classes nil)












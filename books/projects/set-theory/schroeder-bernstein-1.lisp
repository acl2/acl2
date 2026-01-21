; Copyright (C) 2025, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; See schroeder-bernstein.lisp.  The present book is an intermediate book that
; hides most of the work done in schroeder-bernstein-support.lisp.  The parent
; book, schroeder-bernstein.lisp, hides the rest.

(in-package "ZF")

(include-book "injective-funp")
(include-book "zify")
(local (include-book "schroeder-bernstein-support"))

(set-enforce-redundancy t)

(extend-zfc-table sbt-prop
                  zfc prod2$prop inverse$prop domain$prop)

; The events below this point, other than the final two events, serve the sole
; purpose of defining fun-bij$prop.

(defun good-f-g (f g)

; Recognize injective functions f:A->B and g:B->A where A and B are the
; respective domains of f and g.  Only consider these when sbt-prop holds.

  (declare (xargs :guard t))
  (and (injective-funp f)
       (injective-funp g)
       (subset (image f) (domain g))
       (subset (image g) (domain f))
       (sbt-prop)))

(defun f-fn (f g x)
  (declare (xargs :guard t)
           (ignore g))
  (apply f x))
(defun g-fn (f g x)
  (declare (xargs :guard t)
           (ignore f))
  (apply g x))
(defun p-fn (f g x)
  (declare (xargs :guard t))
  (and (good-f-g f g)
       (in x (domain f))))
(defun q-fn (f g x)
  (declare (xargs :guard t))
  (and (good-f-g f g)
       (in x (domain g))))

(defmacro f (x)
  `(f-fn fun-f fun-g ,x))
(defmacro g (x)
  `(g-fn fun-f fun-g ,x))
(defmacro p (x)
  `(p-fn fun-f fun-g ,x))
(defmacro q (x)
  `(q-fn fun-f fun-g ,x))

(encapsulate
  (((my-sb-witness * * *) => *)
   ((my-sb-inverse * * *) => *))

; We put parameter x first to support the use of zify below.

  (local (defun my-sb-witness (x fun-f fun-g)
           (sb-witness fun-f fun-g x)))

  (local (defun my-sb-inverse (x fun-f fun-g)
           (sb-inverse fun-f fun-g x)))

  (defthm q-of-my-sb-witness-when-p
    (implies (p x)
             (q (my-sb-witness x fun-f fun-g)))
    :hints (("Goal"
             :in-theory (disable q-of-sb-witness-when-p)
             :use q-of-sb-witness-when-p)))

  (defthm injectivity-of-my-sb-witness
    (implies (and (p x)
                  (p y)
                  (equal (my-sb-witness x fun-f fun-g)
                         (my-sb-witness y fun-f fun-g)))
             (equal x y))
    :hints (("Goal" :use injectivity-of-sb-witness-alt))
    :rule-classes nil)

  (defthm surjectivity-of-my-sb-witness-alt
    (implies (q x)
             (let ((inv (my-sb-inverse x fun-f fun-g)))
               (and (p inv)
                    (equal (my-sb-witness inv fun-f fun-g) x))))
    :hints (("Goal"
             :in-theory (disable surjectivity-of-sb-witness-alt)
             :use surjectivity-of-sb-witness-alt))))

(zify fun-bij (my-sb-witness x fun-f fun-g)
      :dom (if (good-f-g fun-f fun-g) (domain fun-f) 0)
      :ran (if (good-f-g fun-f fun-g) (domain fun-g) 0))

; All events above this point (other than the initial include-book and
; set-enforce-redundancy events) serve the sole purpose of defining
; fun-bij$prop.

(defun-sk exists-bijection (s1 s2)
  (exists fn
    (and (injective-funp fn)
         (equal (domain fn) s1)
         (equal (image fn) s2))))

(defthmz schroeder-bernstein
  (implies (and (injective-funp f)
                (injective-funp g)
                (equal s1 (domain f))
                (equal s2 (domain g))
                (subset (image f) s2)
                (subset (image g) s1))
           (exists-bijection s1 s2))
  :props (sbt-prop fun-bij$prop)
  :hints (("Goal" :restrict ((exists-bijection-suff
                              ((fn (fun-bij f g))))))))

; Copyright (C) 2026, Matt Kaufmann
; Written by Matt Kaufmann
; License: A 3-clause BSD license.  See the LICENSE file distributed with ACL2.

; This book provides set-theoretic analogues of some commonly used ACL2
; functions.  For example, given a relation r, (car x) is realized as a
; set-theoretic function (zcar r) -- a set of ordered pairs -- so that under
; suitable hypotheses including that x \in r, then (apply (zcar r) x) = (car
; x).

; This book initially only adds set-theoretic analogues of car and cdr, but
; additional analogues may be added over time.

(in-package "ZF")

(include-book "zify")

(defthmz consp-implies-in-singleton
  (implies (consp x)
           (in (pair (car x) (car x))
               x))
  :hints (("Goal" :use ((:instance cons-as-ordered-pair
                                   (x (car x))
                                   (y (cdr x)))))))

(defthmz in-in-singleton
  (implies (and (in x r)
                (consp x))
           (in-in (pair (car x) (car x))
                  r))
  :hints (("Goal" :restrict ((in-in-suff ((y x)))))))

(defthmz in-in-car-union
  (implies (and (in x r)
                (consp x))
           (in-in (car x) (union r)))
  :hints (("Goal"
           :in-theory (disable in-in-suff)
           :use ((:instance in-in-suff
                            (a (car x))
                            (y (singleton (car x)))
                            (x (union r)))))))

(local (defthm car-implies-consp
         (implies (car x)
                  (consp x))))

; Example: If r = {<1,2>} then r = {{{1},{1,2}}}, (union r) = {{1},{1,2}},
; and (union (union r)) = {1,2}.

(zify zcar car
      :dom r
      :ran (union2 (singleton nil) (union (union r)))
      :args (r)
      )

(defthmz consp-implies-in-pair
  (implies (consp x)
           (in (pair (car x) (cdr x))
               x))
  :hints (("Goal" :use ((:instance cons-as-ordered-pair
                                   (x (car x))
                                   (y (cdr x)))))))

(defthmz in-in-pair
  (implies (and (in x r)
                (consp x))
           (in-in (pair (car x) (cdr x))
                  r))
  :hints (("Goal" :restrict ((in-in-suff ((y x)))))))

(defthmz in-in-cdr-union
  (implies (and (in x r)
                (consp x))
           (in-in (cdr x) (union r)))
  :hints (("Goal"
           :in-theory (disable in-in-suff)
           :use ((:instance in-in-suff
                            (a (cdr x))
                            (y (pair (car x) (cdr x)))
                            (x (union r)))))))

(local (defthm cdr-implies-consp
         (implies (cdr x)
                  (consp x))))

(zify zcdr cdr
      :dom r
      :ran (union2 (singleton nil) (union (union r)))
      :args (r)
      )

(extend-zfc-table zfns-prop
                  zify-prop
; Be sure to extend with additional props as they are developed in this book:
                  zcar$prop zcdr$prop)

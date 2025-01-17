; Copyright (C) 2025 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "SBT")

(include-book "std/util/define" :dir :system)
(include-book "std/util/define-sk" :dir :system)
(include-book "std/util/defrule" :dir :system)

(local (include-book "setup"))
(local (include-book "witness"))

(local (include-book "kestrel/built-ins/disable" :dir :system))
(local (acl2::disable-most-builtin-logic-defuns))
(local (acl2::disable-builtin-rewrite-rules-for-defaults))
(set-induction-depth-limit 0)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Setup

(encapsulate
  (((f *) => *)
   ((g *) => *)
   ((p *) => *)
   ((q *) => *))

  (local (define p (x) (declare (ignore x)) t))
  (local (define q (x) (declare (ignore x)) t))

  (local (define f (x) x))
  (local (define g (x) x))

  (defrule q-of-f-when-p
    (implies (p x)
             (q (f x))))

  (defrule injectivity-of-f
    (implies (and (p x)
                  (p y)
                  (equal (f x) (f y)))
             (equal x y))
    :rule-classes nil
    :enable f)

  (defrule p-of-g-when-q
    (implies (q x)
             (p (g x))))

  (defrule injectivity-of-g
    (implies (and (q x)
                  (q y)
                  (equal (g x) (g y)))
             (equal x y))
    :rule-classes nil
    :enable g))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Conclusion

(encapsulate
  (((sb *) => *))

  (local
   ;; Our constructed bijection
   (define sb ((x p))
     (if (in-q-stopper (chain-elem t x))
         (g-inverse x)
       (f x))))

  (define-sk exists-sb-inv (x)
    ;; Guard verified below (otherwise encapsulate complains that guard
    ;; verification may depend on local porperties)
    :verify-guards nil
    (exists inv
            (and (p inv)
                 (equal (sb inv) x))))

  (defrule q-of-sb-when-p
    (implies (p x)
             (q (sb x)))
    :enable (sb sb-witness)
    :use q-of-sb-witness-when-p)

  (defrule injectivity-of-sb
    (implies (and (p x)
                  (p y)
                  (equal (sb x) (sb y)))
             (equal x y))
    :rule-classes nil
    :enable (sb sb-witness)
    :use injectivity-of-sb-witness)

  (defrule surjectivity-of-sb
    (implies (q x)
             (exists-sb-inv x))
    :use ((:instance surjectivity-of-sb-witness)
          (:instance exists-sb-inv-when-exists-sb-inverse))
    :prep-lemmas
    ((defrule exists-sb-inv-when-exists-sb-inverse
       (implies (exists-sb-inverse x)
                (exists-sb-inv x))
       :enable (exists-sb-inverse
                is-sb-inverse
                sb
                sb-witness)
       :use (:instance exists-sb-inv-suff
                       (inv (sb-inverse x))
                       (x x))))))

(verify-guards exists-sb-inv)

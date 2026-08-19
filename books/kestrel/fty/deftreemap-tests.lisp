; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Based on deftreeset tests

(in-package "ACL2")

(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The deftreemap generator ships with deftypes, but using it requires the
;; treemap library, which is supplied by the deftreemap book included below.

(must-fail
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string))

(include-book "deftreemap")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string)

  (assert! (function-symbolp 'nat-string-map-p (w state)))
  (assert! (function-symbolp 'nat-string-map-fix (w state)))
  (assert! (function-symbolp 'nat-string-map-equiv$inline (w state)))
  ;; No count unless :count is supplied (as with deftreeset).
  (assert! (not (function-symbolp 'nat-string-map-count (w state))))
  (assert! (let ((m (treemap::update 1 "one"
                                     (treemap::update 2 "two"
                                                      (treemap::empty)))))
             (and (nat-string-map-p m)
                  (nat-string-map-p (treemap::empty))
                  (not (nat-string-map-p (treemap::update 'a "x" (treemap::empty))))
                  (not (nat-string-map-p (treemap::update 1 'x (treemap::empty))))
                  (not (nat-string-map-p 7))
                  (equal (nat-string-map-fix m) m)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail ; malformed name
  (fty::deftreemap nat string-map
    :key-type nat
    :val-type string))

(must-fail ; unknown keyword
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string
    :cheap t))

(must-fail ; missing :key-type
  (fty::deftreemap nat-string-map
    :val-type string))

(must-fail ; missing :val-type
  (fty::deftreemap nat-string-map
    :key-type nat))

(must-fail ; no such key fixtype
  (fty::deftreemap nat-string-map
    :key-type no-such-fixtype
    :val-type string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string
    :pred nat-string-mapp)

  (assert! (function-symbolp 'nat-string-mapp (w state)))
  (assert! (function-symbolp 'nat-string-map-fix (w state)))
  (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

(must-succeed*
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string
    :fix nat-string-mfix)

  (assert! (function-symbolp 'nat-string-map-p (w state)))
  (assert! (function-symbolp 'nat-string-mfix (w state)))
  (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

(must-succeed*
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string
    :equiv nat-string-mequiv)

  (assert! (function-symbolp 'nat-string-map-p (w state)))
  (assert! (function-symbolp 'nat-string-map-fix (w state)))
  (assert! (function-symbolp 'nat-string-mequiv$inline (w state))))

(must-succeed*
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string
    :count nat-string-map-size)

  (assert! (function-symbolp 'nat-string-map-size (w state)))
  (assert! (not (function-symbolp 'nat-string-map-count (w state))))
  (assert! (let ((m (treemap::update 1 "one"
                                     (treemap::update 2 "two"
                                                      (treemap::empty)))))
             (and (equal (nat-string-map-size m) 2)
                  (equal (nat-string-map-size (treemap::empty)) 0)))))

(must-succeed*
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string
    :no-count t)

  (assert! (function-symbolp 'nat-string-map-p (w state)))
  (assert! (not (function-symbolp 'nat-string-map-count (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string
    :parents (fty::deftreemap)))

(must-succeed
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string
    :short "short"))

(must-succeed
  (fty::deftreemap nat-string-map
    :key-type nat
    :val-type string
    :long "long"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
  (fty::deftreemap sym-nat-map
    :key-type symbol
    :val-type nat))

(must-succeed*
  (fty::defprod point
    ((xc natp)
     (yc natp)))
  (fty::deftreemap sym-point-map
    :key-type symbol
    :val-type point)
  (assert! (let ((m (treemap::update 'origin (make-point :xc 0 :yc 0)
                                     (treemap::empty))))
             (and (sym-point-map-p m)
                  (not (sym-point-map-p (treemap::update 'p 3 (treemap::empty))))
                  (equal (sym-point-map-fix m) m)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A recursive clique: environments mapping symbols to terms.

(must-succeed*
  (fty::deftypes env-term
    (fty::deftagsum env-term
      (:v ((s symbolp)))
      (:closure ((env term-env))))

    (fty::deftreemap term-env
      :key-type symbol
      :val-type env-term))

  (defines sum-env-term/env
    :verify-guards :after-returns

    (define count-env-term ((tm env-term-p))
      :returns (n natp)
      (case (env-term-kind tm)
        (:v 1)
        (:closure (+ 1 (count-term-env (env-term-closure->env tm)))))
      :measure (env-term-count tm))

    (define count-term-env ((env term-env-p))
      :returns (n natp)
      (if (or (not (mbt (term-env-p env)))
              (treemap::emptyp env))
          0
        (+ (count-env-term (treemap::lookup (treeset::min (treemap::keys env))
                                            env))
           (count-term-env (treemap::delete (treeset::min (treemap::keys env))
                                            env))))
      :measure (term-env-count env)))

  (assert!
    (let* ((v1 (env-term-v 'a))
           (v2 (env-term-v 'b))
           (env (treemap::update 'x v1
                                 (treemap::update 'y v2 (treemap::empty))))
           (c (env-term-closure env)))
      (and (env-term-p c)
           (term-env-p env)
           (equal (count-env-term c) 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A head-delete recursion over the same clique, using the head linear rule.

(must-succeed*
  (fty::deftypes env-term
    (fty::deftagsum env-term
      (:v ((s symbolp)))
      (:closure ((env term-env))))

    (fty::deftreemap term-env
      :key-type symbol
      :val-type env-term))

  (define count-env-entries ((env term-env-p))
    :measure (term-env-count env)
    :verify-guards nil
    (if (or (not (mbt (term-env-p env)))
            (treemap::emptyp env))
        0
      (+ 1 (count-env-entries (treemap::delete (treemap::head-key env) env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (in-theory nil)
  (set-induction-depth-limit 0)

  (fty::deftypes env-term
    (fty::deftagsum env-term
      (:v ((s)))
      (:closure ((env term-env)))
      :measure (acl2-count x))

    (fty::deftreemap term-env
      :key-type env-term
      :val-type env-term
      :measure (acl2-count x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes tnode
    (fty::defprod tnode
      ((label symbolp)
       (kids tnode-map))
      :layout :tree
      :measure (two-nats-measure (acl2-count x) 1))

    (fty::deftreemap tnode-map
      :key-type nat
      :val-type tnode
      :measure (two-nats-measure (acl2-count x) 0)))

  (assert!
    (let* ((leaf (make-tnode :label 'a :kids (treemap::empty)))
           (kids (treemap::update 0 leaf (treemap::empty)))
           (parent (make-tnode :label 'b :kids kids)))
      (and (tnode-p leaf)
           (tnode-map-p kids)
           (tnode-p parent)
           (not (tnode-map-p (treemap::update 0 7 (treemap::empty))))
           (equal (tnode->kids parent) kids)
           (natp (tnode-map-count kids))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recursion through the keys rather than the values.

(must-succeed*
  (fty::deftypes kexpr
    (fty::deftagsum kexpr
      (:leaf ((n natp)))
      (:node ((kids kexpr-nat-map))))

    (fty::deftreemap kexpr-nat-map
      :key-type kexpr
      :val-type nat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes uterm
    (fty::deftagsum uterm
      (:v ((s symbolp)))
      (:app ((args sym-uterm-map)))
      :count nil)

    (fty::deftreemap sym-uterm-map
      :key-type symbol
      :val-type uterm))

  (assert!
    (let* ((v1 (uterm-v 'a))
           (v2 (uterm-v 'b))
           (m (treemap::update 'x v1
                               (treemap::update 'y v2 (treemap::empty)))))
      (and (uterm-p v1)
           (sym-uterm-map-p m)
           (uterm-p (uterm-app m))
           (equal (sym-uterm-map-count m) 2)   ; entries only
           (equal (sym-uterm-map-count (treemap::empty)) 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes ncx
    (fty::deftagsum ncx
      (:v ((s symbolp)))
      (:app ((args sym-ncx-map))))

    (fty::deftreemap sym-ncx-map
      :key-type symbol
      :val-type ncx
      :no-count t))

  (assert! (not (function-symbolp 'sym-ncx-map-count (w state))))
  (assert! (let ((m (treemap::update 'x (ncx-v 'a) (treemap::empty))))
             (and (sym-ncx-map-p m)
                  (ncx-p (ncx-app m))
                  (natp (ncx-count (ncx-app m)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Two treemaps in one clique, sharing element types.

(must-succeed*
  (fty::deftypes dup
    (fty::deftagsum dup
      (:leaf ((n natp)))
      (:pair ((as sym-dup-amap)
              (bs sym-dup-bmap))))

    (fty::deftreemap sym-dup-amap
      :key-type symbol
      :val-type dup)

    (fty::deftreemap sym-dup-bmap
      :key-type symbol
      :val-type dup)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A treeset and a treemap in one clique.

(include-book "deftreeset")

(must-succeed*
  (fty::deftypes mixed
    (fty::deftagsum mixed
      (:leaf ((n natp)))
      (:node ((set mixed-set)
              (map sym-mixed-map))))

    (fty::deftreeset mixed-set
      :elt-type mixed)

    (fty::deftreemap sym-mixed-map
      :key-type symbol
      :val-type mixed)))

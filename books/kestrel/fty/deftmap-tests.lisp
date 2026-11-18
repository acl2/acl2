; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Based on deftset tests

(in-package "ACL2")

(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The deftmap generator ships with deftypes, but using it requires the
;; tmap library, which is supplied by the deftmap book included below.

(must-fail
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string))

(include-book "deftmap")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string)

  (assert! (function-symbolp 'nat-string-map-p (w state)))
  (assert! (function-symbolp 'nat-string-map-fix (w state)))
  (assert! (function-symbolp 'nat-string-map-equiv$inline (w state)))
  ;; No count unless :count is supplied (as with deftset).
  (assert! (not (function-symbolp 'nat-string-map-count (w state))))
  (assert! (let ((m (tmap::update 1 "one"
                                  (tmap::update 2 "two"
                                                (tmap::empty)))))
             (and (nat-string-map-p m)
                  (nat-string-map-p (tmap::empty))
                  (not (nat-string-map-p (tmap::update 'a "x" (tmap::empty))))
                  (not (nat-string-map-p (tmap::update 1 'x (tmap::empty))))
                  (not (nat-string-map-p 7))
                  (equal (nat-string-map-fix m) m))))
  ;; The fixer is bounded by any bound of its argument.
  (defthm submap-of-nat-string-map-fix-test
    (implies (tmap::submap x y)
             (tmap::submap (nat-string-map-fix x) y))
    :hints (("Goal" :in-theory '(submap-of-nat-string-map-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail ; malformed name
  (fty::deftmap nat string-map
    :key-type nat
    :val-type string))

(must-fail ; unknown keyword
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string
    :cheap t))

(must-fail ; missing :key-type
  (fty::deftmap nat-string-map
    :val-type string))

(must-fail ; missing :val-type
  (fty::deftmap nat-string-map
    :key-type nat))

(must-fail ; no such key fixtype
  (fty::deftmap nat-string-map
    :key-type no-such-fixtype
    :val-type string))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string
    :pred nat-string-mapp)

  (assert! (function-symbolp 'nat-string-mapp (w state)))
  (assert! (function-symbolp 'nat-string-map-fix (w state)))
  (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

(must-succeed*
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string
    :fix nat-string-mfix)

  (assert! (function-symbolp 'nat-string-map-p (w state)))
  (assert! (function-symbolp 'nat-string-mfix (w state)))
  (assert! (function-symbolp 'nat-string-map-equiv$inline (w state))))

(must-succeed*
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string
    :equiv nat-string-mequiv)

  (assert! (function-symbolp 'nat-string-map-p (w state)))
  (assert! (function-symbolp 'nat-string-map-fix (w state)))
  (assert! (function-symbolp 'nat-string-mequiv$inline (w state))))

(must-succeed*
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string
    :count nat-string-map-size)

  (assert! (function-symbolp 'nat-string-map-size (w state)))
  (assert! (not (function-symbolp 'nat-string-map-count (w state))))
  (assert! (let ((m (tmap::update 1 "one"
                                  (tmap::update 2 "two"
                                                (tmap::empty)))))
             (and (equal (nat-string-map-size m) 2)
                  (equal (nat-string-map-size (tmap::empty)) 0)))))

(must-succeed*
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string
    :no-count t)

  (assert! (function-symbolp 'nat-string-map-p (w state)))
  (assert! (not (function-symbolp 'nat-string-map-count (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string
    :parents (fty::deftmap)))

(must-succeed
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string
    :short "short"))

(must-succeed
  (fty::deftmap nat-string-map
    :key-type nat
    :val-type string
    :long "long"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
  (fty::deftmap sym-nat-map
    :key-type symbol
    :val-type nat))

(must-succeed*
  (fty::defprod point
    ((xc natp)
     (yc natp)))
  (fty::deftmap sym-point-map
    :key-type symbol
    :val-type point)
  (assert! (let ((m (tmap::update 'origin (make-point :xc 0 :yc 0)
                                  (tmap::empty))))
             (and (sym-point-map-p m)
                  (not (sym-point-map-p (tmap::update 'p 3 (tmap::empty))))
                  (equal (sym-point-map-fix m) m)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A recursive clique: environments mapping symbols to terms.

(must-succeed*
  (fty::deftypes env-term
    (fty::deftagsum env-term
      (:v ((s symbolp)))
      (:closure ((env term-env))))

    (fty::deftmap term-env
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
              (tmap::emptyp env))
          0
        (+ (count-env-term (tmap::lookup (tset::min (tmap::keys env))
                                         env))
           (count-term-env (tmap::delete (tset::min (tmap::keys env))
                                         env))))
      :measure (term-env-count env)))

  (assert!
    (let* ((v1 (env-term-v 'a))
           (v2 (env-term-v 'b))
           (env (tmap::update 'x v1
                              (tmap::update 'y v2 (tmap::empty))))
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

    (fty::deftmap term-env
      :key-type symbol
      :val-type env-term))

  (define count-env-entries ((env term-env-p))
    :measure (term-env-count env)
    :verify-guards nil
    (if (or (not (mbt (term-env-p env)))
            (tmap::emptyp env))
        0
      (+ 1 (count-env-entries (tmap::delete (tmap::head-key env) env))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (in-theory nil)
  (set-induction-depth-limit 0)

  (fty::deftypes env-term
    (fty::deftagsum env-term
      (:v ((s)))
      (:closure ((env term-env)))
      :measure (acl2-count x))

    (fty::deftmap term-env
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

    (fty::deftmap tnode-map
      :key-type nat
      :val-type tnode
      :measure (two-nats-measure (acl2-count x) 0)))

  (assert!
    (let* ((leaf (make-tnode :label 'a :kids (tmap::empty)))
           (kids (tmap::update 0 leaf (tmap::empty)))
           (parent (make-tnode :label 'b :kids kids)))
      (and (tnode-p leaf)
           (tnode-map-p kids)
           (tnode-p parent)
           (not (tnode-map-p (tmap::update 0 7 (tmap::empty))))
           (equal (tnode->kids parent) kids)
           (natp (tnode-map-count kids))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Recursion through the keys rather than the values.

(must-succeed*
  (fty::deftypes kexpr
    (fty::deftagsum kexpr
      (:leaf ((n natp)))
      (:node ((kids kexpr-nat-map))))

    (fty::deftmap kexpr-nat-map
      :key-type kexpr
      :val-type nat)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes uterm
    (fty::deftagsum uterm
      (:v ((s symbolp)))
      (:app ((args sym-uterm-map)))
      :count nil)

    (fty::deftmap sym-uterm-map
      :key-type symbol
      :val-type uterm))

  (assert!
    (let* ((v1 (uterm-v 'a))
           (v2 (uterm-v 'b))
           (m (tmap::update 'x v1
                            (tmap::update 'y v2 (tmap::empty)))))
      (and (uterm-p v1)
           (sym-uterm-map-p m)
           (uterm-p (uterm-app m))
           (equal (sym-uterm-map-count m) 2)   ; entries only
           (equal (sym-uterm-map-count (tmap::empty)) 0)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes ncx
    (fty::deftagsum ncx
      (:v ((s symbolp)))
      (:app ((args sym-ncx-map))))

    (fty::deftmap sym-ncx-map
      :key-type symbol
      :val-type ncx
      :no-count t))

  (assert! (not (function-symbolp 'sym-ncx-map-count (w state))))
  (assert! (let ((m (tmap::update 'x (ncx-v 'a) (tmap::empty))))
             (and (sym-ncx-map-p m)
                  (ncx-p (ncx-app m))
                  (natp (ncx-count (ncx-app m)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Two tmaps in one clique, sharing element types.

(must-succeed*
  (fty::deftypes dup
    (fty::deftagsum dup
      (:leaf ((n natp)))
      (:pair ((as sym-dup-amap)
              (bs sym-dup-bmap))))

    (fty::deftmap sym-dup-amap
      :key-type symbol
      :val-type dup)

    (fty::deftmap sym-dup-bmap
      :key-type symbol
      :val-type dup)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A tset and a tmap in one clique.

(include-book "deftset")

(must-succeed*
  (fty::deftypes mixed
    (fty::deftagsum mixed
      (:leaf ((n natp)))
      (:node ((set mixed-set)
              (map sym-mixed-map))))

    (fty::deftset mixed-set
      :elt-type mixed)

    (fty::deftmap sym-mixed-map
      :key-type symbol
      :val-type mixed)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A loop over a typed tmap. A cursor carries no key or value type, so the
;; guards of symbol-name at (tmap::entry-key cursor) and of nat-id at
;; (tmap::entry-val cursor) are discharged by the generated
;; symbolp-of-entry-key-when-sym-nat-map-p-of-from-cursor and
;; natp-of-entry-val-when-sym-nat-map-p-of-from-cursor, with no hints.

(include-book "kestrel/data/tmap/cursor/top" :dir :system)

(must-succeed*
  (fty::deftmap sym-nat-map
    :key-type symbol
    :val-type nat)

  (define nat-id ((n natp))
    (mbe :logic (nfix n) :exec n))

  (define sym-nat-map-loop ((cursor tmap::cursorp))
    :guard (and (sym-nat-map-p (tmap::from-cursor cursor))
                (or (tmap::entryp cursor)
                    (tmap::endp cursor)))
    (if (not (tmap::entryp cursor))
        nil
      (cons (cons (symbol-name (tmap::entry-key cursor))
                  (nat-id (tmap::entry-val cursor)))
            (sym-nat-map-loop (tmap::next cursor))))
    :measure (tmap::nexts cursor))

  (assert! (equal (sym-nat-map-loop
                   (tmap::seek-min
                    (tmap::update 'b 2 (tmap::update 'a 1 (tmap::empty)))))
                  '(("A" . 1) ("B" . 2))))

  ;; A walk that replaces values. The map under the cursor stays typed, by
  ;; the generated rule for tmap::update, so the guard of the recursive call
  ;; needs no hints either.

  (define sym-nat-map-inc-loop ((cursor tmap::cursorp))
    :guard (and (sym-nat-map-p (tmap::from-cursor cursor))
                (or (tmap::entryp cursor)
                    (tmap::endp cursor)))
    (if (not (tmap::entryp cursor))
        (tmap::from-cursor cursor)
      (sym-nat-map-inc-loop
       (tmap::next
        (tmap::cursor-update (+ 1 (nat-id (tmap::entry-val cursor)))
                             cursor))))
    :measure (tmap::nexts cursor))

  (assert! (equal (tmap::lookup
                   'b
                   (sym-nat-map-inc-loop
                    (tmap::seek-min
                     (tmap::update 'b 2 (tmap::update 'a 1 (tmap::empty))))))
                  3)))

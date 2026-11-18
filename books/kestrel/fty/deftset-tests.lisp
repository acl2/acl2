; FTY Library
;
; Copyright (C) 2026 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Grant Jurgensen (grant@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Based on defoset tests

(in-package "ACL2")

(include-book "std/basic/two-nats-measure" :dir :system)
(include-book "std/testing/assert-bang" :dir :system)
(include-book "std/testing/must-succeed-star" :dir :system)
(include-book "std/testing/must-fail" :dir :system)

(include-book "centaur/fty/basetypes" :dir :system)
(include-book "centaur/fty/deftypes" :dir :system)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The deftset generator ships with deftypes, but using it requires the
;; tset library, which is supplied by the deftset book included below.

(must-fail
  (fty::deftset nat-set
    :elt-type nat))

(include-book "deftset")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftset nat-set
    :elt-type nat)

  (assert! (function-symbolp 'nat-set-p (w state)))
  (assert! (function-symbolp 'nat-set-fix (w state)))
  (assert! (function-symbolp 'nat-set-equiv$inline (w state)))
  ;; No count unless :count is supplied (as with defset).
  (assert! (not (function-symbolp 'nat-set-count (w state))))
  (assert! (let ((s (tset::insert 1 (tset::insert 2 (tset::empty)))))
             (and (nat-set-p s)
                  (nat-set-p (tset::empty))
                  (not (nat-set-p (tset::insert 'a (tset::empty))))
                  (not (nat-set-p 7))
                  (equal (nat-set-fix s) s))))
  ;; The fixer is bounded by any bound of its argument.
  (defthm subset-of-nat-set-fix-test
    (implies (tset::subset x y)
             (tset::subset (nat-set-fix x) y))
    :hints (("Goal" :in-theory '(subset-of-nat-set-fix)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail ; malformed name
  (fty::deftset nat set
    :elt-type nat))

(must-fail ; unknown keyword
  (fty::deftset nat-set
    :elt-type nat
    :cheap t))

(must-fail ; missing :elt-type
  (fty::deftset nat-set))

(must-fail ; no such element fixtype
  (fty::deftset nat-set
    :elt-type no-such-fixtype))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftset nat-set
    :elt-type nat
    :pred nat-setp)

  (assert! (function-symbolp 'nat-setp (w state)))
  (assert! (function-symbolp 'nat-set-fix (w state)))
  (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

(must-succeed*
  (fty::deftset nat-set
    :elt-type nat
    :fix nat-sfix)

  (assert! (function-symbolp 'nat-set-p (w state)))
  (assert! (function-symbolp 'nat-sfix (w state)))
  (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

(must-succeed*
  (fty::deftset nat-set
    :elt-type nat
    :equiv nat-sequiv)

  (assert! (function-symbolp 'nat-set-p (w state)))
  (assert! (function-symbolp 'nat-set-fix (w state)))
  (assert! (function-symbolp 'nat-sequiv$inline (w state))))

(must-succeed*
  (fty::deftset nat-set
    :elt-type nat
    :pred nat-setp
    :fix nat-sfix
    :equiv nat-sequiv)

  (assert! (function-symbolp 'nat-setp (w state)))
  (assert! (function-symbolp 'nat-sfix (w state)))
  (assert! (function-symbolp 'nat-sequiv$inline (w state))))

(must-succeed*
  (fty::deftset nat-set
    :elt-type nat
    :count nat-set-size)

  (assert! (function-symbolp 'nat-set-size (w state)))
  (assert! (not (function-symbolp 'nat-set-count (w state))))
  (assert! (let ((s (tset::insert 1 (tset::insert 2 (tset::empty)))))
             (and (equal (nat-set-size s) 2)
                  (equal (nat-set-size (tset::empty)) 0)))))

(must-succeed*
  (fty::deftset nat-set
    :elt-type nat
    :no-count t)

  (assert! (function-symbolp 'nat-set-p (w state)))
  (assert! (not (function-symbolp 'nat-set-count (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
  (fty::deftset nat-set
    :elt-type nat
    :parents (fty::deftset)))

(must-succeed
  (fty::deftset nat-set
    :elt-type nat
    :short "short"))

(must-succeed
  (fty::deftset nat-set
    :elt-type nat
    :short (concatenate 'string "sh" "ort")))

(must-succeed
  (fty::deftset nat-set
    :elt-type nat
    :long "long"))

(must-succeed
  (fty::deftset nat-set
    :elt-type nat
    :long (concatenate 'string "lo" "ng")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
  (fty::deftset sym-set
    :elt-type symbol))

(must-succeed*
  (fty::defprod point
    ((xc natp)
     (yc natp)))
  (fty::deftset point-set
    :elt-type point)
  (assert! (let ((s (tset::insert (make-point :xc 1 :yc 2) (tset::empty))))
             (and (point-set-p s)
                  (not (point-set-p (tset::insert 3 (tset::empty))))
                  (equal (point-set-fix s) s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes int-term-ts
    (fty::deftagsum int-term-ts
      (:num ((val integerp)))
      (:plus ((args int-term-ts-set))))

    (fty::deftset int-term-ts-set
      :elt-type int-term-ts))

  (defines eval-int-term-ts/s
    :verify-guards :after-returns

    (define eval-int-term-ts ((tm int-term-ts-p))
      :returns (i integerp)
      (case (int-term-ts-kind tm)
        (:num (int-term-ts-num->val tm))
        (:plus (eval-int-term-ts-set (int-term-ts-plus->args tm))))
      :measure (int-term-ts-count tm))

    (define eval-int-term-ts-set ((tms int-term-ts-set-p))
      :returns (i integerp)
      (if (or (not (mbt (int-term-ts-set-p tms)))
              (tset::emptyp tms))
          0
        (+ (eval-int-term-ts (tset::min tms))
           (eval-int-term-ts-set (tset::delete (tset::min tms) tms))))
      :measure (int-term-ts-set-count tms)))

  (assert!
    (let* ((n1 (int-term-ts-num 1))
           (n2 (int-term-ts-num 2))
           (s (tset::insert n1 (tset::insert n2 (tset::empty))))
           (p (int-term-ts-plus s)))
      (and (int-term-ts-p p)
           (equal (eval-int-term-ts p) 3)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (in-theory nil)
  (set-induction-depth-limit 0)

  (fty::deftypes int-term-ts
    (fty::deftagsum int-term-ts
      (:num ((val)))
      (:plus ((args int-term-ts-set)))
      :measure (acl2-count x))

    (fty::deftset int-term-ts-set
      :elt-type int-term-ts
      :measure (acl2-count x))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes tnode
    (fty::defprod tnode
      ((label symbolp)
       (kids tnode-set))
      :layout :tree
      :measure (two-nats-measure (acl2-count x) 1))

    (fty::deftset tnode-set
      :elt-type tnode
      :measure (two-nats-measure (acl2-count x) 0)))

  (assert!
    (let* ((leaf (make-tnode :label 'a :kids (tset::empty)))
           (kids (tset::insert leaf (tset::empty)))
           (parent (make-tnode :label 'b :kids kids)))
      (and (tnode-p leaf)
           (tnode-set-p kids)
           (tnode-p parent)
           (not (tnode-set-p (tset::insert 7 (tset::empty))))
           (equal (tnode->kids parent) kids)
           (natp (tnode-set-count kids))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes rec-tset
    (fty::deftagsum rec-tset
      (:sset ((args rec-tset-set)))
      :base-case-override :sset
      :measure (two-nats-measure (acl2-count x) 1))

    (fty::deftset rec-tset-set
      :elt-type rec-tset
      :measure (two-nats-measure (acl2-count x) 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes uterm
    (fty::deftagsum uterm
      (:v ((s symbolp)))
      (:app ((args uterm-set)))
      :count nil)

    (fty::deftset uterm-set
      :elt-type uterm))

  (assert!
    (let* ((v1 (uterm-v 'a))
           (v2 (uterm-v 'b))
           (s (tset::insert v1 (tset::insert v2 (tset::empty)))))
      (and (uterm-p v1)
           (uterm-set-p s)
           (uterm-p (uterm-app s))
           (equal (uterm-set-count s) 2)   ; nodes only
           (equal (uterm-set-count (tset::empty)) 0))))

  (define sum-uterm-set-sizes ((s uterm-set-p))
    :measure (uterm-set-count s)
    :verify-guards nil
    (if (or (not (mbt (uterm-set-p s)))
            (tset::emptyp s))
        0
      (+ 1 (sum-uterm-set-sizes (tset::delete (tset::min s) s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes ncx
    (fty::deftagsum ncx
      (:v ((s symbolp)))
      (:app ((args ncx-set))))

    (fty::deftset ncx-set
      :elt-type ncx
      :no-count t))

  (assert! (not (function-symbolp 'ncx-set-count (w state))))
  (assert! (let ((s (tset::insert (ncx-v 'a) (tset::empty))))
             (and (ncx-set-p s)
                  (ncx-p (ncx-app s))
                  (natp (ncx-count (ncx-app s)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes dexpr
    (fty::deftagsum dexpr
      (:leaf ((n natp)))
      (:node ((kids dexpr-set)
              (attrs attr-set))))

    (fty::deftset dexpr-set
      :elt-type dexpr)

    (fty::deftagsum attr
      (:a ((s symbolp)))
      (:sub ((sub dexpr))))

    (fty::deftset attr-set
      :elt-type attr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two tsets of the same element type in one clique: fine (each member's
; internal names derive from the member name).
(must-succeed*
  (fty::deftypes dup
    (fty::deftagsum dup
      (:leaf ((n natp)))
      (:pair ((as dup-aset)
              (bs dup-bset))))

    (fty::deftset dup-aset
      :elt-type dup)

    (fty::deftset dup-bset
      :elt-type dup)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; A loop over a typed tset. A cursor carries no element type, so the guard
;; of nat-id at (tset::entry cursor) is discharged by the generated
;; natp-of-entry-when-nat-set-p-of-from-cursor, with no hints.

(include-book "kestrel/data/tset/cursor/top" :dir :system)

(must-succeed*
  (fty::deftset nat-set
    :elt-type nat)

  (define nat-id ((n natp))
    (mbe :logic (nfix n) :exec n))

  (define nat-set-loop ((cursor tset::cursorp))
    :guard (and (nat-set-p (tset::from-cursor cursor))
                (or (tset::entryp cursor)
                    (tset::endp cursor)))
    (if (not (tset::entryp cursor))
        nil
      (cons (nat-id (tset::entry cursor))
            (nat-set-loop (tset::next cursor))))
    :measure (tset::nexts cursor))

  (assert! (equal (nat-set-loop
                   (tset::seek-min
                    (tset::insert 2 (tset::insert 1 (tset::empty)))))
                  '(1 2)))

  ;; Adding a value where a search for it ends, and a walk that removes
  ;; elements. The set under the cursor stays typed, by the generated rules
  ;; for tset::insert and tset::delete.

  (define nat-set-insert-by-cursor ((x natp)
                                    (set nat-set-p))
    :returns (set$ nat-set-p :hyp :guard)
    (let ((cursor (tset::seek x set)))
      (tset::from-cursor (if (tset::entryp cursor)
                             cursor
                           (tset::insert-hole x cursor)))))

  (define nat-set-drop-zeros-loop ((cursor tset::cursorp))
    :guard (and (nat-set-p (tset::from-cursor cursor))
                (or (tset::entryp cursor)
                    (tset::endp cursor)))
    (cond ((not (tset::entryp cursor))
           (tset::from-cursor cursor))
          ((equal (nat-id (tset::entry cursor)) 0)
           (nat-set-drop-zeros-loop
            (tset::step-forward (tset::delete-entry cursor))))
          (t (nat-set-drop-zeros-loop (tset::next cursor))))
    :measure (tset::nexts cursor))

  (assert! (equal (nat-set-drop-zeros-loop
                   (tset::seek-min
                    (nat-set-insert-by-cursor
                     0
                     (nat-set-insert-by-cursor 1 (tset::empty)))))
                  (tset::insert 1 (tset::empty)))))

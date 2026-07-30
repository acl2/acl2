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

(include-book "deftreeset")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftreeset nat-set
    :elt-type nat)

  (assert! (function-symbolp 'nat-set-p (w state)))
  (assert! (function-symbolp 'nat-set-fix (w state)))
  (assert! (function-symbolp 'nat-set-equiv$inline (w state)))
  ;; No count unless :count is supplied (as with defset).
  (assert! (not (function-symbolp 'nat-set-count (w state))))
  (assert! (let ((s (treeset::insert 1 (treeset::insert 2 (treeset::empty)))))
             (and (nat-set-p s)
                  (nat-set-p (treeset::empty))
                  (not (nat-set-p (treeset::insert 'a (treeset::empty))))
                  (not (nat-set-p 7))
                  (equal (nat-set-fix s) s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-fail ; malformed name
  (fty::deftreeset nat set
    :elt-type nat))

(must-fail ; unknown keyword
  (fty::deftreeset nat-set
    :elt-type nat
    :cheap t))

(must-fail ; missing :elt-type
  (fty::deftreeset nat-set))

(must-fail ; no such element fixtype
  (fty::deftreeset nat-set
    :elt-type no-such-fixtype))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftreeset nat-set
    :elt-type nat
    :pred nat-setp)

  (assert! (function-symbolp 'nat-setp (w state)))
  (assert! (function-symbolp 'nat-set-fix (w state)))
  (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

(must-succeed*
  (fty::deftreeset nat-set
    :elt-type nat
    :fix nat-sfix)

  (assert! (function-symbolp 'nat-set-p (w state)))
  (assert! (function-symbolp 'nat-sfix (w state)))
  (assert! (function-symbolp 'nat-set-equiv$inline (w state))))

(must-succeed*
  (fty::deftreeset nat-set
    :elt-type nat
    :equiv nat-sequiv)

  (assert! (function-symbolp 'nat-set-p (w state)))
  (assert! (function-symbolp 'nat-set-fix (w state)))
  (assert! (function-symbolp 'nat-sequiv$inline (w state))))

(must-succeed*
  (fty::deftreeset nat-set
    :elt-type nat
    :pred nat-setp
    :fix nat-sfix
    :equiv nat-sequiv)

  (assert! (function-symbolp 'nat-setp (w state)))
  (assert! (function-symbolp 'nat-sfix (w state)))
  (assert! (function-symbolp 'nat-sequiv$inline (w state))))

(must-succeed*
  (fty::deftreeset nat-set
    :elt-type nat
    :count nat-set-size)

  (assert! (function-symbolp 'nat-set-size (w state)))
  (assert! (not (function-symbolp 'nat-set-count (w state))))
  (assert! (let ((s (treeset::insert 1 (treeset::insert 2 (treeset::empty)))))
             (and (equal (nat-set-size s) 2)
                  (equal (nat-set-size (treeset::empty)) 0)))))

(must-succeed*
  (fty::deftreeset nat-set
    :elt-type nat
    :no-count t)

  (assert! (function-symbolp 'nat-set-p (w state)))
  (assert! (not (function-symbolp 'nat-set-count (w state)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
  (fty::deftreeset nat-set
    :elt-type nat
    :parents (fty::deftreeset)))

(must-succeed
  (fty::deftreeset nat-set
    :elt-type nat
    :short "short"))

(must-succeed
  (fty::deftreeset nat-set
    :elt-type nat
    :short (concatenate 'string "sh" "ort")))

(must-succeed
  (fty::deftreeset nat-set
    :elt-type nat
    :long "long"))

(must-succeed
  (fty::deftreeset nat-set
    :elt-type nat
    :long (concatenate 'string "lo" "ng")))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed
  (fty::deftreeset sym-set
    :elt-type symbol))

(must-succeed*
  (fty::defprod point
    ((xc natp)
     (yc natp)))
  (fty::deftreeset point-set
    :elt-type point)
  (assert! (let ((s (treeset::insert (make-point :xc 1 :yc 2) (treeset::empty))))
             (and (point-set-p s)
                  (not (point-set-p (treeset::insert 3 (treeset::empty))))
                  (equal (point-set-fix s) s)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes int-term-ts
    (fty::deftagsum int-term-ts
      (:num ((val integerp)))
      (:plus ((args int-term-ts-set))))

    (fty::deftreeset int-term-ts-set
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
              (treeset::emptyp tms))
          0
        (+ (eval-int-term-ts (treeset::min tms))
           (eval-int-term-ts-set (treeset::delete (treeset::min tms) tms))))
      :measure (int-term-ts-set-count tms)))

  (assert!
    (let* ((n1 (int-term-ts-num 1))
           (n2 (int-term-ts-num 2))
           (s (treeset::insert n1 (treeset::insert n2 (treeset::empty))))
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

    (fty::deftreeset int-term-ts-set
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

    (fty::deftreeset tnode-set
      :elt-type tnode
      :measure (two-nats-measure (acl2-count x) 0)))

  (assert!
    (let* ((leaf (make-tnode :label 'a :kids (treeset::empty)))
           (kids (treeset::insert leaf (treeset::empty)))
           (parent (make-tnode :label 'b :kids kids)))
      (and (tnode-p leaf)
           (tnode-set-p kids)
           (tnode-p parent)
           (not (tnode-set-p (treeset::insert 7 (treeset::empty))))
           (equal (tnode->kids parent) kids)
           (natp (tnode-set-count kids))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes rec-tset
    (fty::deftagsum rec-tset
      (:sset ((args rec-tset-set)))
      :base-case-override :sset
      :measure (two-nats-measure (acl2-count x) 1))

    (fty::deftreeset rec-tset-set
      :elt-type rec-tset
      :measure (two-nats-measure (acl2-count x) 0))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes uterm
    (fty::deftagsum uterm
      (:v ((s symbolp)))
      (:app ((args uterm-set)))
      :count nil)

    (fty::deftreeset uterm-set
      :elt-type uterm))

  (assert!
    (let* ((v1 (uterm-v 'a))
           (v2 (uterm-v 'b))
           (s (treeset::insert v1 (treeset::insert v2 (treeset::empty)))))
      (and (uterm-p v1)
           (uterm-set-p s)
           (uterm-p (uterm-app s))
           (equal (uterm-set-count s) 2)   ; nodes only
           (equal (uterm-set-count (treeset::empty)) 0))))

  (define sum-uterm-set-sizes ((s uterm-set-p))
    :measure (uterm-set-count s)
    :verify-guards nil
    (if (or (not (mbt (uterm-set-p s)))
            (treeset::emptyp s))
        0
      (+ 1 (sum-uterm-set-sizes (treeset::delete (treeset::min s) s))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(must-succeed*
  (fty::deftypes ncx
    (fty::deftagsum ncx
      (:v ((s symbolp)))
      (:app ((args ncx-set))))

    (fty::deftreeset ncx-set
      :elt-type ncx
      :no-count t))

  (assert! (not (function-symbolp 'ncx-set-count (w state))))
  (assert! (let ((s (treeset::insert (ncx-v 'a) (treeset::empty))))
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

    (fty::deftreeset dexpr-set
      :elt-type dexpr)

    (fty::deftagsum attr
      (:a ((s symbolp)))
      (:sub ((sub dexpr))))

    (fty::deftreeset attr-set
      :elt-type attr)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Two treesets of the same element type in one clique: fine (each member's
; internal names derive from the member name).
(must-succeed*
  (fty::deftypes dup
    (fty::deftagsum dup
      (:leaf ((n natp)))
      (:pair ((as dup-aset)
              (bs dup-bset))))

    (fty::deftreeset dup-aset
      :elt-type dup)

    (fty::deftreeset dup-bset
      :elt-type dup)))

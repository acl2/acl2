; SOFT (Second-Order Functions and Theorems) Library
;
; Copyright (C) 2019 Kestrel Institute (http://www.kestrel.edu)
;
; License: A 3-clause BSD license. See the LICENSE file distributed with ACL2.
;
; Author: Alessandro Coglio (coglio@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "implementation")

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; Below are the examples in the ACL2-2015 Workshop paper
; "Second-Order Functions and Theorems in ACL2".
; Comments indicate the sections and subsections of the paper.
; The examples look slightly different from the paper
; due to the changes to SOFT since the Workshop
; (see :DOC UPDATES-TO-WORKSHOP-MATERIAL).

; 1  Second-Order Functions and Theorems

; 1.1  Function Variables

(defunvar ?f (*) => *)

(defunvar ?p (*) => *)

(defunvar ?g (* *) => *)

; 1.2   Second-Order Functions

; 1.2.1   Plain Functions

(defun2 quad[?f] (x)
  (declare (xargs :guard t))
  (?f (?f (?f (?f x)))))

(defun2 all[?p] (l)
  (declare (xargs :guard t))
  (cond ((atom l) (null l))
        (t (and (?p (car l))
                (all[?p] (cdr l))))))

(defun2 map[?f][?p] (l)
  (declare (xargs :guard (all[?p] l)))
  (cond ((endp l) nil)
        (t (cons (?f (car l))
                 (map[?f][?p] (cdr l))))))

(defun2 fold[?f][?g] (bt)
  (declare (xargs :guard t))
  (cond ((atom bt) (?f bt))
        (t (?g (fold[?f][?g] (car bt))
               (fold[?f][?g] (cdr bt))))))

; 1.2.2  Choice Functions

(defchoose2 fixpoint[?f] x ()
  (equal (?f x) x))

; 1.2.3  Quantifier Functions

(defun-sk2 injective[?f] ()
  (forall (x y)
          (implies (equal (?f x) (?f y))
                   (equal x y))))

(verify-guards injective[?f])

; 1.3  Instances of Second-Order Functions

(defun wrap (x)
  (declare (xargs :guard t))
  (list x))

(defun-inst quad[wrap]
  (quad[?f] (?f . wrap)))

(defun octetp (x)
  (declare (xargs :guard t))
  (and (natp x) (< x 256)))

(defun-inst all[octetp]
  (all[?p] (?p . octetp)))

(defun-inst map[code-char]
  (map[?f][?p] (?f . code-char) (?p . octetp)))

(defun-inst fold[nfix][plus]
  (fold[?f][?g] (?f . nfix) (?g . binary-+)))

(defun twice (x)
  (declare (xargs :guard t))
  (* 2 (fix x)))

(defun-inst fixpoint[twice]
  (fixpoint[?f] (?f . twice)))

(defun-inst injective[quad[?f]]
  (injective[?f] (?f . quad[?f])))

(verify-guards injective[quad[?f]])

; 1.4  Second-Order Theorems

(defthm len-of-map[?f][?p]
  (equal (len (map[?f][?p] l))
         (len l)))

(defthm injective[quad[?f]]-when-injective[?f]
  (implies (injective[?f])
           (injective[quad[?f]]))
  :hints
  (("Goal" :use
    ((:instance
      injective[?f]-necc
      (x (?f (?f (?f (?f (mv-nth 0 (injective[quad[?f]]-witness)))))))
      (y (?f (?f (?f (?f (mv-nth 1 (injective[quad[?f]]-witness))))))))
     (:instance
      injective[?f]-necc
      (x (?f (?f (?f (mv-nth 0 (injective[quad[?f]]-witness))))))
      (y (?f (?f (?f (mv-nth 1 (injective[quad[?f]]-witness)))))))
     (:instance
      injective[?f]-necc
      (x (?f (?f (mv-nth 0 (injective[quad[?f]]-witness)))))
      (y (?f (?f (mv-nth 1 (injective[quad[?f]]-witness))))))
     (:instance
      injective[?f]-necc
      (x (?f (mv-nth 0 (injective[quad[?f]]-witness))))
      (y (?f (mv-nth 1 (injective[quad[?f]]-witness)))))
     (:instance
      injective[?f]-necc
      (x (mv-nth 0 (injective[quad[?f]]-witness)))
      (y (mv-nth 1 (injective[quad[?f]]-witness))))))))

(defunvar ?io (* *) => *)

(defun-sk2 atom-io[?f][?io] ()
  (forall x (implies (atom x)
                     (?io x (?f x))))
  :rewrite :direct)

(verify-guards atom-io[?f][?io])

(defun-sk2 consp-io[?g][?io] ()
  (forall (x y1 y2)
          (implies (and (consp x)
                        (?io (car x) y1)
                        (?io (cdr x) y2))
                   (?io x (?g y1 y2))))
  :rewrite :direct)

(verify-guards consp-io[?g][?io])

(defthm fold-io[?f][?g][?io]
  (implies (and (atom-io[?f][?io])
                (consp-io[?g][?io]))
           (?io x (fold[?f][?g] x))))

; 1.5  Instances of Second-Order Theorems

(defthm-inst len-of-map[code-char]
  (len-of-map[?f][?p] (?f . code-char) (?p . octetp)))

(defun-inst injective[quad[wrap]]
  (injective[quad[?f]] (?f . wrap)))

(verify-guards injective[quad[wrap]])

(defun-inst injective[wrap]
  (injective[?f] (?f . wrap)))

(verify-guards injective[wrap])

(defthm-inst injective[quad[wrap]]-when-injective[wrap]
  (injective[quad[?f]]-when-injective[?f] (?f . wrap)))

; 2  Use in Program Refinement

(set-verify-guards-eagerness 0) ; to keep the program refinement example shorter

; 2.1  Specifications as Second-Order Predicates

(defun leaf (e bt)
  (cond ((atom bt) (equal e bt))
        (t (or (leaf e (car bt))
               (leaf e (cdr bt))))))

(defunvar ?h (*) => *)

(defun-sk io (x y)
  (forall e (iff (member e y)
                 (and (leaf e x)
                      (natp e))))
  :rewrite :direct)

(defun-sk2 spec[?h] ()
  (forall x (io x (?h x)))
  :rewrite :direct)

(defthm natp-of-member-of-output
  (implies (and (spec[?h])
                (member e (?h x)))
           (natp e))
  :hints (("Goal" :use (spec[?h]-necc
                        (:instance io-necc (y (?h x)))))))

; 2.2  Refinement as Second-Order Predicate Strengthening

; Step 1

(defun-sk2 def-?h-fold[?f][?g] ()
  (forall x (equal (?h x)
                   (fold[?f][?g] x)))
  :rewrite :direct)

(defun2 spec1[?h][?f][?g]  ()
  (and (def-?h-fold[?f][?g])
       (spec[?h])))

(defthm step1
  (implies (spec1[?h][?f][?g])
           (spec[?h]))
  :hints (("Goal" :in-theory '(spec1[?h][?f][?g]))))

; Step 2

(defun-inst atom-io[?f]
  (atom-io[?f][?io] (?io . io)))

(defun-inst consp-io[?g]
  (consp-io[?g][?io] (?io . io)))

(defthm-inst fold-io[?f][?g]
  (fold-io[?f][?g][?io] (?io . io)))

(defun2 spec2[?h][?f][?g] ()
  (and (def-?h-fold[?f][?g])
       (atom-io[?f])
       (consp-io[?g])))

(defthm step2
  (implies (spec2[?h][?f][?g])
           (spec1[?h][?f][?g]))
  :hints (("Goal" :in-theory '(spec1[?h][?f][?g]
                               spec2[?h][?f][?g]
                               spec[?h]
                               def-?h-fold[?f][?g]-necc
                               fold-io[?f][?g]))))

; Step 3

(defun f (x)
  (if (natp x)
      (list x)
    nil))

(defun-inst atom-io[f]
  (atom-io[?f] (?f . f)))

(defthm atom-io[f]!
  (atom-io[f]))

(defun-sk2 def-?f ()
  (forall x (equal (?f x) (f x)))
  :rewrite :direct)

(defun2 spec3[?h][?f][?g] ()
  (and (def-?h-fold[?f][?g])
       (def-?f)
       (consp-io[?g])))

(defthm step3-lemma
  (implies (def-?f)
           (atom-io[?f]))
  :hints (("Goal" :in-theory '(atom-io[?f]
                               atom-io[f]-necc
                               atom-io[f]!
                               def-?f-necc))))

(defthm step3
  (implies (spec3[?h][?f][?g])
           (spec2[?h][?f][?g]))
  :hints (("Goal" :in-theory '(spec2[?h][?f][?g]
                               spec3[?h][?f][?g]
                               step3-lemma))))

; Step 4

(defun g (y1 y2)
  (append y1 y2))

(defun-inst consp-io[g]
  (consp-io[?g] (?g . g)))

; member-of-append is already included here

(defthm consp-io[g]-lemma
  (implies (and (consp x)
                (io (car x) y1)
                (io (cdr x) y2))
           (io x (g y1 y2)))
  :hints (("Goal"
           :in-theory (disable io)
           :expand (io x (append y1 y2)))))

(defthm consp-io[g]!
  (consp-io[g])
  :hints (("Goal" :in-theory (disable g))))

(defun-sk2 def-?g ()
  (forall (y1 y2)
          (equal (?g y1 y2) (g y1 y2)))
  :rewrite :direct)

(defun2 spec4[?h][?f][?g] ()
  (and (def-?h-fold[?f][?g])
       (def-?f)
       (def-?g)))

(defthm step4-lemma
  (implies (def-?g)
           (consp-io[?g]))
  :hints (("Goal" :in-theory '(consp-io[?g]
                               consp-io[g]-necc
                               consp-io[g]!
                               def-?g-necc))))

(defthm step4
  (implies (spec4[?h][?f][?g])
           (spec3[?h][?f][?g]))
  :hints (("Goal" :in-theory '(spec3[?h][?f][?g]
                               spec4[?h][?f][?g]
                               step4-lemma))))

; Step 5

(defun-inst h
  (fold[?f][?g] (?f . f) (?g . g))
  :verify-guards nil)

(defun-sk2 def-?h ()
  (forall x (equal (?h x) (h x)))
  :rewrite :direct)

(defun2 spec5[?h][?f][?g] ()
  (and (def-?h)
       (def-?f)
       (def-?g)))

(defthm step5-lemma
  (implies (and (def-?f)
                (def-?g))
           (equal (h x) (fold[?f][?g] x)))
  :hints (("Goal" :in-theory '(h fold[?f][?g] def-?f-necc def-?g-necc))))

(defthm step5
  (implies (spec5[?h][?f][?g])
           (spec4[?h][?f][?g]))
  :hints (("Goal" :in-theory '(spec4[?h][?f][?g]
                               spec5[?h][?f][?g]
                               def-?h-fold[?f][?g]
                               def-?h-necc
                               step5-lemma))))

(defthm chain[?h][?f][?g]
  (implies (spec5[?h][?f][?g])
           (spec[?h]))
  :hints (("Goal" :in-theory '(step1 step2 step3 step4 step5))))

(defun-inst def-h
  (def-?h (?h . h))
  :rewrite :default)

(defun-inst def-f
  (def-?f (?f . f))
  :rewrite :default)

(defun-inst def-g
  (def-?g (?g . g))
  :rewrite :default)

(defun-inst spec5[h][f][g]
  (spec5[?h][?f][?g] (?h . h) (?f . f) (?g . g)))

(defun-inst spec[h]
  (spec[?h] (?h . h)))

(defthm-inst chain[h][f][g]
  (chain[?h][?f][?g] (?h . h) (?f . f) (?g . g)))

(defthm spec5[h][f][g]!
  (spec5[h][f][g])
  :hints (("Goal" :in-theory '(spec5[h][f][g]))))

(defthm spec[h]!
  (spec[h])
  :hints (("Goal" :in-theory '(chain[h][f][g] spec5[h][f][g]!))))

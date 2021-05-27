; Stuff that supports the (simple) rewriter.
;
; Copyright (C) 2008-2011 Eric Smith and Stanford University
; Copyright (C) 2013-2020 Kestrel Institute
; Copyright (C) 2016-2020 Kestrel Technology, LLC
;
; License: A 3-clause BSD license. See the file books/3BSD-mod.txt.
;
; Author: Eric Smith (eric.smith@kestrel.edu)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(in-package "ACL2")

(include-book "axe-trees")
(include-book "all-dargp-less-than")
(include-book "bounded-dag-exprs")
(local (include-book "kestrel/lists-light/cdr" :dir :system))
(local (include-book "kestrel/lists-light/len" :dir :system))
(local (include-book "kestrel/arithmetic-light/plus" :dir :system))
(local (include-book "kestrel/lists-light/nth" :dir :system))

;; TODO: Move some of these to better places:

;move
;number of lambda vars is number of args
(defthmd len-of-cadar-when-pseudo-termp
  (implies (and (pseudo-termp term)
                (consp (car term)))
           (equal (len (car (cdr (car term))))
                  (len (fargs term))))
  :hints (("Goal" :expand (pseudo-termp term)
           :in-theory (enable pseudo-termp))))

(defthmd len-of-cadar-when-axe-treep
  (implies (and (axe-treep tree)
                (consp (car tree)))
           (equal (len (car (cdr (car tree))))
                  (len (fargs tree))))
  :hints (("Goal" :expand (axe-treep tree)
           :in-theory (enable axe-treep))))

;; the lambda body is a pseudo-term
(defthmd pseudo-termp-of-cadddr-when-axe-treep
  (implies (and (axe-treep tree)
                (consp (car tree)))
           (pseudo-termp (car (cddr (car tree)))))
  :hints (("Goal" :expand (axe-treep tree)
           :in-theory (enable axe-treep))))

(defthm all-dargp-of-if
  (equal (all-dargp (if test items1 items2))
         (if test
             (all-dargp items1)
           (all-dargp items2))))

(defthm all-dargp-less-than-of-if
  (equal (all-dargp-less-than (if test items1 items2) bound)
         (if test
             (all-dargp-less-than items1 bound)
           (all-dargp-less-than items2 bound))))

(defthm all-axe-treep-when-all-dargp-less-than
  (implies (all-dargp-less-than args dag-len) ;dag-len is a free var
           (all-axe-treep args))
  :hints (("Goal" :in-theory (enable all-axe-treep
                                     all-dargp-less-than
                                     axe-treep
                                     dargp-less-than))))

(defthm all-axe-treep-of-cons
  (equal (all-axe-treep (cons tree trees))
         (and (axe-treep tree)
              (all-axe-treep trees)))
  :hints (("Goal" :in-theory (enable all-axe-treep))))

;(local (in-theory (disable CONSP-FROM-LEN-CHEAP)))

(DEFTHM DARGP-LESS-THAN-WHEN-not-quotep-cheap
  (IMPLIES (not (quotep ITEM))
           (EQUAL (DARGP-LESS-THAN ITEM LEN)
                  (and (natp item)
                       (< ITEM LEN))))
  :rule-classes ((:rewrite :backchain-limit-lst (0)))
  :HINTS
  (("Goal" :IN-THEORY (ENABLE DARGP-LESS-THAN))))

;move
(defthmd symbol-alistp-when-alistp
  (implies (alistp x)
           (equal (symbol-alistp x)
                  (symbol-listp (strip-cars x))))
  :hints (("Goal" :in-theory (enable symbol-alistp))))

(defthm len-when-axe-treep-and-consp-of-car
  (implies (and (axe-treep tree)
                (consp (car tree)))
           (equal (len (car tree))
                  3))
  :rule-classes ((:rewrite :backchain-limit-lst (0 0)))
  :hints (("Goal" :in-theory (enable axe-treep))))

(DEFTHMd INTEGERP-WHEN-DARGP
  (IMPLIES (DARGP ITEM)
           (EQUAL (INTEGERP ITEM)
                  (NOT (CONSP ITEM)))))

(DEFTHMd natp-WHEN-DARGP
  (IMPLIES (DARGP ITEM)
           (EQUAL (natp ITEM)
                  (NOT (CONSP ITEM)))))

(defthmd quotep-when-dargp
  (implies (dargp item)
           (equal (quotep item)
                  (consp item))))

(DEFTHMd <=-of-0-WHEN-DARGP
  (IMPLIES (DARGP ITEM)
           (<= 0 ITEM)))

(defthmd <-when-dargp-less-than
  (implies (and (dargp-less-than item bound)
                (not (consp item)))
           (< item bound)))

(defthmd len-when-dargp
  (implies (dargp item)
           (equal (len item)
                  (if (consp item) 2 0)))
  :hints
  (("Goal" :in-theory (enable dargp))))

(defthmd <-of--1-when-dargp
  (implies (dargp item)
           (not (< item -1)))
  :hints
  (("Goal" :in-theory (enable dargp))))

(defthmd <-of--0-when-dargp
  (implies (dargp item)
           (not (< item 0)))
  :hints
  (("Goal" :in-theory (enable dargp))))

(defthm integerp-of-if
  (equal (integerp (if test tp ep))
         (if test
             (integerp tp)
           (integerp ep))))

(defthm symbol-listp-of-cons
  (equal (symbol-listp (cons a x))
         (and (symbolp a)
              (symbol-listp x)))
  :hints (("Goal" :in-theory (enable symbol-listp))))

(defthm symbol-alistp-when-alistp-and-equal-of-strip-cars
  (implies (and (alistp x)
                (equal (strip-cars x) cars)
                (symbol-listp cars)
                )
           (symbol-alistp x))
  :hints (("Goal" :in-theory (enable symbol-alistp))))

(defthm <-trans
  (implies (and (< x z)
                (<= z y))
           (< x y)))

(defthm equal-of-quote-and-nth-1-of-assoc-equal-when-all-dargp-of-strip-cdrs
  (implies (and (all-dargp (strip-cdrs node-replacement-alist))
                (assoc-equal tree node-replacement-alist))
           (equal (equal 'quote (nth 1 (assoc-equal tree node-replacement-alist)))
                  (consp (cdr (assoc-equal tree node-replacement-alist)))))
  :hints (("Goal" :in-theory (enable assoc-equal all-dargp strip-cdrs))))

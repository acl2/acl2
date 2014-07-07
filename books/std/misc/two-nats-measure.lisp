; Two Naturals Measure
; Copyright (C) 2005-2006 Kookamara LLC
;
; Contact:
;
;   Kookamara LLC
;   11410 Windermere Meadows
;   Austin, TX 78759, USA
;   http://www.kookamara.com/
;
; License: (An MIT/X11-style license)
;
;   Permission is hereby granted, free of charge, to any person obtaining a
;   copy of this software and associated documentation files (the "Software"),
;   to deal in the Software without restriction, including without limitation
;   the rights to use, copy, modify, merge, publish, distribute, sublicense,
;   and/or sell copies of the Software, and to permit persons to whom the
;   Software is furnished to do so, subject to the following conditions:
;
;   The above copyright notice and this permission notice shall be included in
;   all copies or substantial portions of the Software.
;
;   THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
;   IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
;   FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
;   AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
;   LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING
;   FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER
;   DEALINGS IN THE SOFTWARE.
;
; Original author: Jared Davis <jared@kookamara.com>
;
; two-nats-measure.lisp
; This file was originally part of the Unicode library.


(in-package "ACL2")

(include-book "xdoc/top" :dir :system)
(local (include-book "arithmetic/top-with-meta" :dir :system))

(defsection two-nats-measure
  :parents (ordinals)
  :short "One of the simplest non-natural ordinal measures imaginable"
  :long "Two-nats-measure provides one of the simplest non-natural ordinal
   measures imaginable.  It is useful if one has a one count that is decreasing
   most of the time but not always and another count that decreases the rest of
   the time but might be reset to some value after a chunk of work is finished.

   Imagine one has a pile of red socks and a pile of blue socks, and that one
   wants to place them in drawers.  Everytime one puts away a red sock a bunch
   more blue socks are allowed to be added.  But when one puts away a blue
   sock, neither red nor blue socks can be added.  One can use two-nats-measure
   to show that one will eventually finish putting away the socks.  The number
   of red socks is the first argument to the two-nats-measure, and the number
   of blue socks is the second argument to the two-nats-measure."

(defund two-nats-measure (a b)
  (declare (xargs :guard (and (natp a)
                              (natp b))))
  (make-ord 2
            (+ 1 (nfix a))
            (make-ord 1 (+ 1 (nfix b)) 0)))

(in-theory (disable (:executable-counterpart two-nats-measure)))

(defthm o-p-of-two-nats-measure
  (equal (o-p (two-nats-measure a b))
         t)
  :hints(("Goal" :in-theory (enable two-nats-measure))))

(defthm o<-of-two-nats-measure
  (equal (o< (two-nats-measure a b)
             (two-nats-measure c d))
         (or (< (nfix a) (nfix c))
             (and (equal (nfix a) (nfix c))
                  (< (nfix b) (nfix d)))))
  :hints(("Goal" :in-theory (enable two-nats-measure))))



(defund nat-list-measure (a)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (atom a)
      (nfix a)
    (make-ord (len a) (+ 1 (nfix (car a)))
              (nat-list-measure (cdr a)))))

(in-theory (disable (:executable-counterpart nat-list-measure)))

(defthm consp-nat-list-measure
  (equal (consp (nat-list-measure a))
         (consp a))
  :hints(("Goal" :in-theory (enable nat-list-measure))))

(defthm atom-caar-nat-list-measure
  (equal (caar (nat-list-measure a))
         (and (consp a)
              (len a)))
  :hints(("Goal" :in-theory (enable nat-list-measure))))

(defthm o-p-of-nat-list-measure
  (o-p (nat-list-measure a))
  :hints(("Goal" :in-theory (enable o-p nat-list-measure))))


(defun cons-list-or-quotep (x)
  (if (atom x)
      (equal x nil)
    (case (car x)
      (quote t)
      (cons (and (eql (len x) 3)
                 (cons-list-or-quotep (third x)))))))

(defthm o<-of-nat-list-measure
  (implies (syntaxp (and (cons-list-or-quotep a)
                         (cons-list-or-quotep b)))
           (equal (o< (nat-list-measure a)
                      (nat-list-measure b))
                  (or (< (len a) (len b))
                      (and (equal (len a) (len b))
                           (if (consp a)
                               (or (< (nfix (car a)) (nfix (car b)))
                                   (and (equal (nfix (car a)) (nfix (car b)))
                                        (o< (nat-list-measure (cdr a))
                                            (nat-list-measure (cdr b)))))
                             (< (nfix a) (nfix b)))))))
  :hints(("Goal" :in-theory (enable nat-list-measure))))

(defun nat-list-< (a b)
  (o< (nat-list-measure a) (nat-list-measure b)))

(defthm nat-list-wfr
  (and (o-p (nat-list-measure x))
       (implies (nat-list-< x y)
                (o< (nat-list-measure x)
                    (nat-list-measure y))))
  :rule-classes :well-founded-relation)


(defthm open-nat-list-<
  (implies (syntaxp (and (cons-list-or-quotep a)
                         (cons-list-or-quotep b)))
           (equal (nat-list-< a b)
                  (or (< (len a) (len b))
                      (and (equal (len a) (len b))
                           (if (consp a)
                               (or (< (nfix (car a)) (nfix (car b)))
                                   (and (equal (nfix (car a)) (nfix (car b)))
                                        (nat-list-< (cdr a) (cdr b))))
                             (< (nfix a) (nfix b)))))))
  :hints (("goal" :use o<-of-nat-list-measure
           :in-theory (disable o<-of-nat-list-measure))))

(defthm natp-nat-list-<
  (implies (and (atom a) (atom b))
           (equal (nat-list-< a b)
                  (< (nfix a) (nfix b))))
  :hints (("goal" :use o<-of-nat-list-measure
           :in-theory (disable o<-of-nat-list-measure))))

(in-theory (disable nat-list-<))

) ; defsection

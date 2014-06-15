; Standard Utilities Library
; Copyright (C) 2008-2014 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
;
; This program is free software; you can redistribute it and/or modify it under
; the terms of the GNU General Public License as published by the Free Software
; Foundation; either version 2 of the License, or (at your option) any later
; version.  This program is distributed in the hope that it will be useful but
; WITHOUT ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
; FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License for
; more details.  You should have received a copy of the GNU General Public
; License along with this program; if not, write to the Free Software
; Foundation, Inc., 51 Franklin Street, Suite 500, Boston, MA 02110-1335, USA.
;
; Original author: Jared Davis <jared@centtech.com>

(in-package "STD")
(include-book "../define")
(include-book "misc/assert" :dir :system)

(define foo ()
  :returns (ans integerp)
  3)

(define foo2 ()
  (mv 3 "hi"))

(define foo3 ()
  (mv 3 "hi"))

(define foo4 ()
  :returns (ans integerp)
  44)

(assert! (equal (defguts->name (cdr (assoc 'foo4 (get-define-guts-alist (w state)))))
                'foo4))

(define foo5 ((x oddp :type integer))
  :returns (ans integerp :hyp :guard)
  (- x 1))

(define foo6 ((x oddp :type (integer 0 *)))
  :returns (ans natp :hyp :guard)
  (- x 1))

(define foo7
  :parents (|look ma, parents before formals, even!|)
  (x)
  (consp x))

(encapsulate
  ()
  (logic)
  (define foo8 (x)
    :mode :program
    (+ 1 x)))

(encapsulate
  ()
  (logic)
  (define foo9 (x)
    (declare (xargs :mode :program))
    (+ 2 x)))

(encapsulate
  ()
  (program)
  (define foo10 ((x natp))
    (declare (xargs :mode :logic))
    (+ 2 x)))

(encapsulate
  ()
  (program)
  (define foo11 (x)
    (declare (xargs :mode :program))
    (+ 3 x)))

(encapsulate
  ()
  (program)
  (define foo12 (x)
    :mode :program
    (+ 3 x)))




(encapsulate
  ()
  (logic)
  (define bar8 (x &optional y)
    :mode :program
    (+ 1 x y)))

(encapsulate
  ()
  (logic)
  (define bar9 (x &optional y)
    (declare (xargs :mode :program))
    (+ 2 x y)))

(encapsulate
  ()
  (program)
  (define bar10 ((x natp) &optional (y natp))
    (declare (xargs :mode :logic))
    (+ 2 x y)))

(encapsulate
  ()
  (program)
  (define bar11 (x &optional y)
    (declare (xargs :mode :program))
    (+ 3 x y)))

(encapsulate
  ()
  (program)
  (define bar12 (x &optional y)
    :mode :program
    (+ 3 x y)))




(define m0 (x)
  (consp x))

(assert! (let ((topic (xdoc::find-topic 'm0 (xdoc::get-xdoc-table (w state)))))
           (not topic)))

(xdoc::set-default-parents foo bar)

(define m1 (x)
  (consp x))

(assert! (let ((topic (xdoc::find-topic 'm1 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(foo bar)))))

(define m2 (x)
  (consp x)
  :parents (bar))

(assert! (let ((topic (xdoc::find-topic 'm2 (xdoc::get-xdoc-table (w state)))))
           (and topic
                (equal (cdr (assoc :parents topic))
                       '(bar)))))

(define m3 (x)
  (consp x)
  :parents nil)

(assert! (let ((topic (xdoc::find-topic 'm3 (xdoc::get-xdoc-table (w state)))))
           (not topic)))





;; Basic testing of hook installation/removal

(defun my-hook (guts opts state)
  (declare (xargs :mode :program :stobjs state))
  (declare (ignore guts opts))
  (value '(value-triple :invisible)))

(defun my-hook2 (guts opts state)
  (declare (xargs :mode :program :stobjs state))
  (declare (ignore guts opts))
  (value '(value-triple :invisible)))

(assert! (not (get-post-define-hooks-alist (w state))))
(add-post-define-hook :foo my-hook)
(assert! (equal (get-post-define-hooks-alist (w state)) '((:foo . my-hook))))
(add-post-define-hook :bar my-hook2)
(assert! (equal (get-post-define-hooks-alist (w state)) '((:bar . my-hook2)
                                                          (:foo . my-hook))))
(remove-post-define-hook :foo)
(assert! (equal (get-post-define-hooks-alist (w state)) '((:bar . my-hook2))))
(add-post-define-hook :foo my-hook)
(assert! (equal (get-post-define-hooks-alist (w state)) '((:foo . my-hook)
                                                          (:bar . my-hook2))))

(assert! (let ((guts (make-defguts :name 'myfun)))
           (equal (post-hook-make-events '(:foo (:bar 3) (:foo 5))
                                         (get-post-define-hooks-alist (w state))
                                         guts)
                  `((make-event (my-hook ',guts 'nil state))
                    (make-event (my-hook2 ',guts '(3) state))
                    (make-event (my-hook ',guts '(5) state))))))


(assert! (not (get-default-post-define-hooks (w state))))
(add-default-post-define-hook :bar)
(assert! (equal (get-default-post-define-hooks (w state))
                '((:bar . NIL))))
(add-default-post-define-hook :foo 3)
(assert! (equal (get-default-post-define-hooks (w state))
                '((:foo . (3))
                  (:bar))))
(remove-default-post-define-hook :bar)
(assert! (equal (get-default-post-define-hooks (w state))
                '((:foo . (3)))))
(remove-default-post-define-hook :foo)
(assert! (not (get-default-post-define-hooks (w state))))


(remove-post-define-hook :foo)
(remove-post-define-hook :bar)
(assert! (not (get-post-define-hooks-alist (w state))))




(defun my-hook-1 (guts opts state)
  ;; Trivial, stupid hook test.
  ;; To test user-defined options, opts is expected to have a hyp for the theorem.
  (declare (xargs :mode :program :stobjs state))
  (b* (((defguts guts) guts)
       (mksym-package-symbol guts.name)
       (- (cw "My-hook-1: Proving dumb theorem about ~x0.~%" guts.name))
       ((unless (tuplep 1 opts))
        (er soft 'my-hook-1 "Expected a single option (a hyp for the theorem), but got: ~x0." opts))
       (hyp (first opts))
       (event `(defthm ,(mksym guts.name '-silly-thm)
                 (implies ,hyp
                          (equal (,guts.name-fn . ,guts.raw-formals)
                                 (,guts.name-fn . ,guts.raw-formals)))
                 :rule-classes nil)))
    (value event)))

(add-post-define-hook :silly my-hook-1)

(define hooktest1 (x)
  :hooks ((:silly (consp a)))
  x
  :verbosep nil)

(encapsulate
  ()
  (set-enforce-redundancy t)
  (defthm hooktest1-silly-thm
    (implies (consp a)
             (equal (hooktest1 x) (hooktest1 x)))
    :rule-classes nil))

(define hooktest2 (x)
  :hooks ((:silly t))
  x
  :verbosep nil)

(encapsulate
  ()
  (set-enforce-redundancy t)
  (defthm hooktest2-silly-thm
    (implies t
             (equal (hooktest2 x) (hooktest2 x)))
    :rule-classes nil))

(add-default-post-define-hook :silly (integerp b))

(define hooktest3 (x) x)

(encapsulate
  ()
  (set-enforce-redundancy t)
  (defthm hooktest3-silly-thm
    (implies (integerp b)
             (equal (hooktest3 x) (hooktest3 x)))
    :rule-classes nil))

(define hooktest4 (x)
  ;; Make sure we can defeat default hooks
  :hooks nil
  x)

(assert! (acl2::logical-namep 'hooktest3-silly-thm (w state)))
(assert! (not (acl2::logical-namep 'hooktest4-silly-thm (w state))))

(define my-make-alist (keys)
  :returns (alist alistp)
  (if (atom keys)
      nil
    (cons (cons (car keys) nil)
          (my-make-alist (cdr keys))))
  ///
  (more-returns
   (alist true-listp :rule-classes :type-prescription)
   (alist (equal (len alist) (len keys))
          :name len-of-my-make-alist)))

(local (in-theory (enable my-make-alist)))

(include-book "std/lists/list-fix" :dir :system)

(more-returns my-make-alist
  (alist (equal (strip-cars alist) (list-fix keys))
         :name strip-cars-of-my-make-alist))



(define my-make-alist-and-len (keys)
  :returns (mv (len natp :rule-classes :type-prescription)
               (alist alistp))
  (b* (((when (atom keys))
        (mv 0 nil))
       ((mv cdr-len cdr-alist) (my-make-alist-and-len (cdr keys))))
    (mv (+ 1 cdr-len)
        (cons (cons (car keys) nil) cdr-alist)))
  ///
  (more-returns
   (len (equal len (len keys))
        :name my-make-alist-and-len.len-removal)
   (alist (integer-listp (strip-cars alist))
          :hyp (integer-listp keys)
          :name integer-listp-strip-cars-my-make-alist-and-len)
   (alist true-listp :rule-classes :type-prescription)))





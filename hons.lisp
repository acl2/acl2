; ACL2 Version 8.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2021, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78712 U.S.A.

; hons.lisp -- Logical definitions for hash cons and fast alists.  Note that
; the memoization and watch functionality previously provided by this file have
; been moved into "memoize.lisp".  A closely related file is "hons-raw.lisp"
; that provides the Common Lisp implementation of many of the concepts
; introduced below.

; The original version of this file was contributed by Bob Boyer and Warren
; A. Hunt, Jr.  The design of this system of hash cons, function memoization,
; and fast association lists (applicative hash tables) was initially
; implemented by Boyer and Hunt.  The code has since been improved by Boyer and
; Hunt, and also by Sol Swords, Jared Davis, and Matt Kaufmann.

(in-package "ACL2")

(defmacro defn (f a &rest r)
  `(defun ,f ,a (declare (xargs :guard t)) ,@r))

(defmacro defnd (f a &rest r)
  `(defund ,f ,a (declare (xargs :guard t)) ,@r))

#+(or acl2-loop-only (not hons))
(defn hons-equal (x y)
  (declare (xargs :mode :logic))
  ;; Has an under-the-hood implementation
  (equal x y))

(defn hons-assoc-equal (key alist)
  (declare (xargs :mode :logic))
  (cond ((atom alist)
         nil)
        ((and (consp (car alist))
              (hons-equal key (caar alist)))
         (car alist))
        (t
         (hons-assoc-equal key (cdr alist)))))

#+(or acl2-loop-only (not hons))
(defn hons-get (key alist)
  (declare (xargs :mode :logic))
  ;; Has an under-the-hood implementation
  (hons-assoc-equal key alist))

#+(or acl2-loop-only (not hons))
(defn hons-acons (key val alist)
  (declare (xargs :mode :logic))
  ;; Has an under-the-hood implementation
  (cons (cons key val) alist))

#+(or acl2-loop-only (not hons))
(defmacro fast-alist-free-on-exit-raw (alist form)
  ;; Has an under-the-hood implementation
  (declare (ignore alist))
  form)

#+(or acl2-loop-only (not hons))
(defn fast-alist-free (alist)
  (declare (xargs :mode :logic))
  ;; Has an under-the-hood implementation
  alist)

(defmacro fast-alist-free-on-exit (alist form)
  `(return-last 'fast-alist-free-on-exit-raw ,alist ,form))

#+(or acl2-loop-only (not hons))
(defn hons-copy (x)
  ;; Has an under-the-hood implementation
  (declare (xargs :mode :logic)) ; for attaching early to acl2x-expansion-alist
  x)

#+(or acl2-loop-only (not hons))
(defn hons-copy-persistent (x)
  ;; Has an under-the-hood implementation
  x)

#+(or acl2-loop-only (not hons))
(defn hons (x y)
  ;; Has an under-the-hood implementation
  (cons x y))

#+(or acl2-loop-only (not hons))
(defn hons-equal-lite (x y)
  ;; Has an under-the-hood implementation
  (equal x y))

#+(or acl2-loop-only (not hons))
(defn hons-clear (gc)
  ;; Has an under-the-hood implementation
  (declare (ignore gc))
  nil)

#+(or acl2-loop-only (not hons))
(defn hons-clear! (gc)
  ;; Has an under-the-hood implementation
  (declare (ignore gc))
  nil)

#+(or acl2-loop-only (not hons))
(defn hons-wash ()
  ;; Has an under-the-hood implementation
  nil)

#+(or acl2-loop-only (not hons))
(defn hons-wash! ()
  ;; Has an under-the-hood implementation
  nil)

#+(or acl2-loop-only (not hons))
(defn hons-summary ()
  ;; Has an under-the-hood implementation
  nil)

(defmacro hons-resize (&key str-ht nil-ht cdr-ht cdr-ht-eql
                            addr-ht other-ht sbits
                            fal-ht persist-ht)
  `(hons-resize-fn ,str-ht ,nil-ht ,cdr-ht ,cdr-ht-eql
                   ,addr-ht ,other-ht ,sbits
                   ,fal-ht ,persist-ht))

#+(or acl2-loop-only (not hons))
(defn hons-resize-fn (str-ht nil-ht cdr-ht cdr-ht-eql
                                 addr-ht other-ht sbits
                                 fal-ht persist-ht)
  (declare (ignore str-ht nil-ht cdr-ht cdr-ht-eql
                   addr-ht other-ht sbits
                   fal-ht persist-ht))
  ;; Has an under-the-hood implementation
  nil)

(table hons 'slow-alist-warning

; By default, ensure that the ACL2 user sees any violation of fast alist
; discipline.

       #-acl2-par :break

; Except: In ACL2(p), when waterfall-parallelism is enabled, hons-get will fail
; the fast alist discipline when it is called from any any thread other than
; the top-level thread.  We avoid breaking in that case.

       #+acl2-par :warning)

(defmacro set-slow-alist-action (action)
  (declare (xargs :guard (or (eq action :warning)
                             (eq action :break)
                             (not action))))
  `(table hons 'slow-alist-warning ,action))

#+(or acl2-loop-only (not hons))
(defn hons-acons! (key val alist)
  ;; Has an under-the-hood implementation
  (cons (cons key val) alist))

#+(or acl2-loop-only (not hons))
(defn make-fast-alist (alist)
  ;; Has an under-the-hood implementation
  alist)

#+(or acl2-loop-only (not hons))
(defn fast-alist-fork (alist ans)
  ;; Has an under-the-hood implementation
  (cond ((atom alist)
         ans)
        ((atom (car alist))
         (fast-alist-fork (cdr alist) ans))
        ((hons-assoc-equal (car (car alist)) ans)
         (fast-alist-fork (cdr alist) ans))
        (t
         (fast-alist-fork (cdr alist) (cons (car alist) ans)))))

#+(or acl2-loop-only (not hons))
(defn fast-alist-fork! (alist ans)
  ;; Has an under-the-hood implementation
  (fast-alist-fork alist ans))

; Deprecated:

(defmacro hons-shrink-alist (alist ans)
  `(fast-alist-fork ,alist ,ans))
(defmacro hons-shrink-alist! (alist ans)
  `(fast-alist-fork! ,alist ,ans))
(add-macro-alias hons-shrink-alist fast-alist-fork)
(add-macro-alias hons-shrink-alist! fast-alist-fork!)

#+(or acl2-loop-only (not hons))
(defn fast-alist-clean (alist)
  ;; Has an under-the-hood implementation
  (fast-alist-fork alist
                   (if (consp alist)
                       (cdr (last alist))
                     alist)))

#+(or acl2-loop-only (not hons))
(defn fast-alist-clean! (alist)
  ;; Has an under-the-hood implementation
  (fast-alist-clean alist))

#+(or acl2-loop-only (not hons))
(defn fast-alist-len (alist)
  ;; Has an under-the-hood implementation
  (len (fast-alist-fork alist nil)))

#+(or acl2-loop-only (not hons))
(defn fast-alist-summary ()
  ;; Has an under-the-hood implementation
  nil)

#+(or acl2-loop-only (not hons))
(defmacro with-fast-alist-raw (alist form)
  ;; Has an under-the-hood implementation
  (declare (ignore alist))
  form)

(defmacro with-fast-alist (alist form)
  `(return-last 'with-fast-alist-raw ,alist ,form))

#+(or acl2-loop-only (not hons))
(defmacro with-stolen-alist-raw (alist form)
  ;; Has an under-the-hood implementation
  (declare (ignore alist))
  form)

(defmacro with-stolen-alist (alist form)
  `(return-last 'with-stolen-alist-raw ,alist ,form))

(defn cons-subtrees (x al)
  (cond ((atom x)
         al)
        ((hons-get x al)
         al)
        (t
         (cons-subtrees
          (car x)
          (cons-subtrees (cdr x) (hons-acons x t al))))))

#+(or acl2-loop-only (not hons))
(defn number-subtrees (x)
  ;; Has an under-the-hood implementation
  (len (cons-subtrees x 'number-subtrees)))

(defn flush-hons-get-hash-table-link (alist)
  (fast-alist-free alist))

(in-theory (disable

; The execution of honsing and fast alist functions during theorem proving
; could be very subtle.  It is easy to imagine discipline failures, inadvertent
; norming, inadvertent clearing of hash tables, etc.  We try to prevent this at
; least somewhat by disabling the executable-counterparts of many of the above
; functions.  This is not a total solution, but seems like a good idea anyway.

            ;; These would probably be pretty harmless
            (:executable-counterpart hons)
            (:executable-counterpart hons-copy)
            (:executable-counterpart hons-copy-persistent)
            (:executable-counterpart hons-summary)
            (:executable-counterpart fast-alist-summary)

            ;; These could be particularly bad to call by mistake
            (:executable-counterpart hons-clear)
            (:executable-counterpart hons-clear!)
            (:executable-counterpart hons-wash)
            (:executable-counterpart hons-wash!)
            (:executable-counterpart hons-resize-fn)

            ;; These could lead to discipline failures
            (:executable-counterpart hons-get)
            (:executable-counterpart hons-acons)
            (:executable-counterpart hons-acons!)
            (:executable-counterpart fast-alist-fork)
            (:executable-counterpart fast-alist-fork!)
            (:executable-counterpart fast-alist-clean)
            (:executable-counterpart fast-alist-clean!)
            (:executable-counterpart fast-alist-len)
            (:executable-counterpart fast-alist-free)
            (:executable-counterpart flush-hons-get-hash-table-link)
            ))

(defun remove-keyword (word l)
  (declare (xargs :guard (and (keywordp word)
                              (keyword-value-listp l))))
  (cond ((endp l) nil)
        ((eq word (car l))
         (remove-keyword word (cddr l)))
        (t (list* (car l) (cadr l) (remove-keyword word (cddr l))))))

; For some additional helper functions and lemmas, see the community books
; books/misc/hons-help.lisp and books/misc/hons-help2.lisp.

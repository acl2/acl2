; Serializing ACL2 Objects
; Copyright (C) 2009-2012 Centaur Technology
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

(in-package "ACL2")

(defdoc unsound-read
  ":Doc-Section Serialize

Unsound alternative to ~ilc[serialize-read]~/

The ~c[unsound-read] command is like ~ilc[serialize-read] except that it does
not take ~ilc[state].  This means it works even in ordinary ~il[defconst]
events, which avoids the performance penalty of using ~ilc[make-event] to read
files; see ~ilc[serialize-in-books].

As its name suggests, ~c[unsound-read] is not sound and it can easily be used
to prove ~c[nil]; see below.  Because of this, we don't build it into ACL2; to
use it you must first include the ~c[serialize/unsound-read] book, e.g.,

~bv[]
  (include-book \"serialize/unsound-read\" :dir :system :ttags (:unsound-read))
~ev[]

and accept the ~c[:unsound-read] trust tag.

General form:
~bv[]
  (unsound-read filename
                [:hons-mode {:always, :never, :smart}]
                [:verbose   {t, nil}])
    -->
  obj
~ev[]

The arguments are as in ~ilc[serialize-read].
~/

EXPLANATION OF UNSOUNDNESS.

The logical problem with ~c[unsound-read] is that, since it is a function, it
is expected to satisfy the functional equality axiom schema, namely,

~bv[]
  (equal (unsound-read-fn filename hons-mode verbosep)
         (unsound-read-fn filename hons-mode verbosep))
~ev[]

But we can violate this property by modifying the file system between calls of
~c[unsound-read].  For instance, here is a proof of nil that is carried out in
~c[serialize/serialize-tests.lisp] by exploiting this fact.

~bv[]
  (local
   (encapsulate
    ()
    ;; Write NIL to test.sao
    (make-event
     (let ((state (serialize-write \"test.sao\" nil)))
       (value '(value-triple :invisible))))

    ;; Prove that test.sao contains NIL.
    (defthm lemma-1
      (equal (unsound-read \"test.sao\") nil)
      :rule-classes nil)

    ;; Write T to test.sao
    (make-event
     (let ((state (serialize-write \"test.sao\" t)))
       (value '(value-triple :invisible))))

    ;; Prove that test.sao contains T.
    (defthm lemma-2
      (equal (unsound-read \"test.sao\") t)
      :rule-classes nil)

    ;; Arrive at our contradiction.
    (defthm qed
      nil
      :rule-classes nil
      :hints((\"Goal\"
              :use ((:instance lemma-1)
                    (:instance lemma-2))
              :in-theory (disable (unsound-read-fn)))))))
~ev[]

In short, if you want to use ~c[unsound-read] soundly, then you need to make
sure the files you are reading aren't changing out from under you.")

(defttag :unsound-read)

; We use this stub in the logical definition, so that you can't
; directly reason about the value of unsound-read.

(defstub unsound-read-fn-logical-def (filename honsp verbosep)
  t)

(defun unsound-read-fn (filename hons-mode verbosep)
  (declare (xargs :guard (and (stringp filename)
                              (member-eq hons-mode '(:always :never :smart))
                              (booleanp verbosep))))
  (prog2$
   (er hard? 'unsound-read-fn "Raw-lisp definition not installed??")
   (unsound-read-fn-logical-def filename hons-mode verbosep)))

(defmacro unsound-read (filename &key
                                 (hons-mode ':smart)
                                 verbosep)
  `(unsound-read-fn ,filename ,hons-mode ,verbosep))

(progn!
 (set-raw-mode t)
 (defun unsound-read-fn (filename hons-mode verbosep)
   (let ((*ser-verbose* verbosep))
     (with-open-file (stream filename :direction :input)
       (ser-decode-from-stream t hons-mode stream)))))


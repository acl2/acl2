; Serializing ACL2 Objects
; Copyright (C) 2009-2010 Centaur Technology
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

(in-package "SERIALIZE")
(include-book "tools/include-raw" :dir :system)

(defdoc unsound-read
  ":Doc-Section Serialize

Unsound alternative to ~ilc[ACL2::serialize-read]~/

For better performance, it may be useful to avoid the use of ~ilc[make-event]
when reading files, because ~c[make-event] incurs certain kinds of overhead;
see ~ilc[serialize-in-books] for details.

As its name suggests, ~c[unsound-read] is known to be unsound and you may
easily use it to prove ~c[nil].  See below for details.  Because of this, it is
not included in ACL2 by default and is instead only available by additionally
including the ~c[serialize/unsound-read] book, e.g.,

~bv[]
  (include-book \"serialize/unsound-read\" :dir :system :ttags (:unsound-read))
~ev[]

and accepting the ~c[:unsound-read] trust tag.

The ~c[unsound-read] command is essentially like ~ilc[serialize-read], except
that it does not take ~c[state].

General form:
~bv[]
  (SERIALIZE::unsound-read filename
                           [:hons-mode {:always, :never, :smart}]
                           [:verbose   {t, nil}])
    -->
  obj
~ev[] ~/

Because it does not take state, ~c[unsound-read] may be used in ordinary
~il[defconst] commands, whereas ordinary ~c[serialize-read] may only be used in
~il[make-event]s or other contexts where the ~c[state] is available.


EXPLANATION OF UNSOUNDNESS.

The logical problem with ~c[unsound-read] is that, since it is a function, it
is expected to satisfy the functional equality axiom schema, namely,

~bv[]
  (equal (SERIALIZE::unsound-read-fn filename hons-mode verbosep)
         (SERIALIZE::unsound-read-fn filename hons-mode verbosep))
~ev[]

But we can violate this property by modifying the file system between calls of
~c[unsound-read], and the dependence of ~c[unsound-read] upon the state is
nowhere evident.  For instance, here is a proof of nil that is carried out in
~c[serialize/serialize-tests.lisp] by exploiting this fact.

~bv[]
  (local
   (encapsulate
    ()
    ;; Write NIL to test.sao
    (make-event
     (let ((state (serialize::write \"test.sao\" nil)))
       (value '(value-triple :invisible))))

    ;; Prove that test.sao contains NIL.
    (defthm lemma-1
      (equal (serialize::unsound-read \"test.sao\") nil)
      :rule-classes nil)

    ;; Write T to test.sao
    (make-event
     (let ((state (serialize::write \"test.sao\" t)))
       (value '(value-triple :invisible))))

    ;; Prove that test.sao contains T.
    (defthm lemma-2
      (equal (serialize::unsound-read \"test.sao\") t)
      :rule-classes nil)

    ;; Arrive at our contradiction.
    (defthm qed
      nil
      :rule-classes nil
      :hints((\"Goal\"
              :use ((:instance lemma-1)
                    (:instance lemma-2))
              :in-theory (disable (serialize::unsound-read-fn)))))))
~ev[]

In short, anyone who wishes to use ~c[unsound-read] does so at their peril, and
must be able to justify to themselves that nobody has changed the files out
from under them.")

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

; (depends-on "unsound-read-raw.lsp")
(acl2::include-raw "unsound-read-raw.lsp")

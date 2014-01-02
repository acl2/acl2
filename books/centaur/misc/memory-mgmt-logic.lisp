; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
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
; Original author: Sol Swords <sswords@centtech.com>

; memory-mgmt-logic.lisp
;
; Note: This book should be included in conjunction with memory-mgmt-raw.lisp;
; otherwise, these functions won't do much of anything interesting.

(in-package "ACL2")
(include-book "xdoc/top" :dir :system)

(defun hons-analyze-memory (slowp)
  (declare (xargs :guard t)
           (ignore slowp))
  (er hard? 'hons-analyze-memory "Raw lisp definition not installed?"))

(defun maybe-wash-memory-fn (n clear)
  (declare (xargs :guard t)
           (ignore n clear))
  (cw "maybe-wash-memory is defined under the hood~%"))

(defun print-quick-memory-summary ()
  (declare (xargs :guard t))
  (cw "print-quick-memory-summary is defined under the hood~%"))

(defmacro maybe-wash-memory (n &optional clear)
  `(maybe-wash-memory-fn ,n ,clear))

(add-macro-alias maybe-wash-memory maybe-wash-memory-fn)

(defxdoc set-max-mem
  :parents (hons-and-memoization)
  :short "An enhanced memory management scheme for ACL2(h). (CCL only; requires
  a trust tag)"

  :long "<p>Typical usage:</p>

@({
 (include-book \"centaur/misc/memory-mgmt\" :dir :system) ;; adds ttag
 (value-triple (set-max-mem (* 4 (expt 2 30))))           ;; 4 GB
})

<p>Logically @(call set-max-mem) just returns @('nil').</p>

<p>Under the hood, loading the @('centaur/misc/memory-mgmt') book adds some
special garbage collection hooks into CCL, and @('set-max-mem') influences the
behavior of these hooks.</p>

<p>Roughly speaking, @(call set-max-mem) means: <b>try</b> to use no more than
@('n') bytes of <b>heap</b> memory.  You should think of this as a soft cap.
Generally the limit will grow by increments of 1 GB as you start to run out of
memory.</p>

<p>Note that this only influences the heap memory.  To avoid swapping death,
you should typically pick an @('n') that leaves space for the stacks and other
processes on your system.  For instance, if your machine has only 8 GB of
physical memory, you may wish to reserve no more than about 6 GB for the
heap.</p>


<h3>Interaction with @(see cert.pl)</h3>

<p>The @(see cert.pl) build system scans for calls of @('set-max-mem') and uses
them to infer how much memory a book will need.  This information may be useful
for scheduling jobs when carrying out distributed builds on a cluster.</p>

<p>Note that this parsing is done by a simple Perl script, so you can't just
use an arbitrary Lisp expression here.  Explicitly supported expressions
are:</p>

<ul>
 <li>@('(* n (expt 2 30))')</li>
 <li>@('(expt 2 n)')</li>
</ul>


<h3>Using @('set-max-mem') in Pure ACL2 Books</h3>

<p>To make it possible to embed calls of @(see set-max-mem) into ordinary,
trust-tag free ACL2 code, the logical definition of @('set-max-mem') is found
in the book:</p>

@({
   (include-book \"centaur/misc/memory-mgmt-logic\" :dir :system)
})

<p>Note that if you load only this @('-logic') book, without also loading the
raw book, then @('set-max-mem') will <b>do nothing</b> except print a message
saying it is doing nothing.</p>")

(defun set-max-mem (n)
  (declare (xargs :guard t)
           (ignore n))
  (cw "set-max-mem is defined under the hood~%"))


(defun print-rwx-size ()
  (declare (xargs :guard t))
  (cw "print-rwx-size is defined under the hood~%"))


(defun last-chance-wash-memory-fn ()
  (declare (xargs :guard t))
  ;; Sol: I removed this printing because in certain places I use BDD functions
  ;; without loading the -raw book, and if it prints this line each time it's
  ;; messy.
  ;; (cw "last-chance-wash-memory is defined under the hood~%")
  nil)

(defmacro last-chance-wash-memory ()
  `(last-chance-wash-memory-fn))

(add-macro-alias last-chance-wash-memory last-chance-wash-memory-fn)


(defund set-max-time (minutes)

; In ACL2, this does nothing.
;
; The cert.pl build system scans for calls of set-max-time.  Loosely speaking,
; if a book contains something like:
;
;   (value-triple (set-max-time 10))
;
; Then this means a time limit of 10 minutes should be put on the job.  This
; time limit is probably ignored unless you are using a clustering system like
; PBS.  We generally use a time limit of 3 hours as the default, so that we
; only need to include a set-max-time command in books that take a really long
; time to certify.
;
; NOTE: A perl script is going to parse this directive, so the argument should
; typically be a constant number, rather than any kind of complex expression.
; It also needs to be on the same line as the set-max-time call, etc.
;
; We generally interpret this as, "There's no way this book should ever take
; longer than 10 minutes, so just kill the job if it hasn't finished within
; that amount of time."

  (declare (xargs :guard t)
           (ignore minutes))
  nil)


(in-theory (disable maybe-wash-memory
                    (maybe-wash-memory)
                    (:type-prescription maybe-wash-memory-fn)
                    last-chance-wash-memory
                    (last-chance-wash-memory)
                    (:type-prescription last-chance-wash-memory-fn)
                    set-max-mem
                    (set-max-mem)
                    (:type-prescription set-max-mem)))


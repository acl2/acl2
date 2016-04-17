; Centaur Miscellaneous Books
; Copyright (C) 2008-2011 Centaur Technology
;
; Contact:
;   Centaur Technology Formal Verification Group
;   7600-C N. Capital of Texas Highway, Suite 300, Austin, TX 78731, USA.
;   http://www.centtech.com/
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
  #+Clozure
  (cw "; hons-analyze-memory: raw lisp definition not installed?~%")
  #-Clozure
  (cw "; hons-analyze-memory: not implemented on this lisp~%"))

(defun maybe-wash-memory-fn (n clear)
  (declare (xargs :guard t)
           (ignore n clear))
  #+Clozure
  (cw "; maybe-wash-memory: raw lisp definition not installed?~%")
  #-Clozure
  (cw "; maybe-wash-memory: not implemented on this lisp~%"))


(defun print-quick-memory-summary ()
  (declare (xargs :guard t))
  #+Clozure
  (cw "; print-quick-memory-summary: raw lisp definition not installed?~%")
  #-Clozure
  (cw "; print-quick-memory-summary: not implemented on this lisp~%"))


(defsection maybe-wash-memory
  :parents (hons)
  :short "Conditionally trigger a @(see hons-wash) and also @(see
  clear-memoize-tables) to reclaim memory.  (CCL only; requires a
  trust tag)"

  :long "<p>@(call maybe-wash-memory) will clear out unused honses and throw
away all currently memoized results, but only if fewer than @('n') bytes of
memory are currently free.  If more than @('n') bytes are free, it does
nothing.</p>

<p>The general idea here is that garbage collection is slow, so you only want
to do it if you are starting to run out of memory.  At the same time, garbage
collection is cheaper if you can do it \"in between\" computations that are
creating a lot of garbage, where there are fewer live objects.  Moreover, if
you still have a lot of memory still available, then you may prefer to keep
currently memoized results so that you aren't repeating work.</p>

<p>You can use @('maybe-wash-memory') in between computations to trigger
garbage collections in an opportunistic way: if there's ample memory still
available, no GC will be triggered, but if memory is getting scarce, then it's
time to trigger an expensive collection, wiping out the memo tables and
cleaning up honses in the process.</p>

<p>Here's a basic example:</p>

@({
 (include-book \"centaur/misc/memory-mgmt\" :dir :system) ;; adds ttag
 (value-triple (set-max-mem (* 8 (expt 2 30))))           ;; 8 GB
 ... some memory intensive stuff ...
 (value-triple (maybe-wash-memory (* 3 (expt 2 30))))
 ... more memory intensive stuff ...
 (value-triple (maybe-wash-memory (* 3 (expt 2 30))))
 ... etc ...
})

<p>If the optional @('clear') argument is @('t'), honses will be cleared using
@(see hons-clear) instead of @(see hons-wash).  (This is generally ill
advised.)</p>

<p>This can be a good way to clean up memory in between @(see
gl::def-gl-param-thm) cases, and in other situations.</p>")

(defmacro maybe-wash-memory (n &optional clear)
  `(maybe-wash-memory-fn ,n ,clear))

(add-macro-alias maybe-wash-memory maybe-wash-memory-fn)

(defxdoc set-max-mem
  :parents (hons-and-memoization)
  :short "An enhanced memory management scheme. (CCL only; requires
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


<h3>Interaction with @(see build::cert.pl)</h3>

<p>The @(see build::cert.pl) build system scans for calls of @('set-max-mem')
and uses them to infer how much memory a book will need.  This information may
be useful for scheduling jobs when carrying out distributed builds on a
cluster.</p>

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
  #+Clozure
  (cw "; set-max-mem: raw lisp definition not installed?~%")
  #-Clozure
  (cw "; set-max-mem: not implemented on this Lisp.~%"))

(defun print-rwx-size ()
  (declare (xargs :guard t))
  #+Clozure
  (cw "; print-rwx-size: raw lisp definition not installed?~%")
  #-Clozure
  (cw "; print-rwx-size: not implemented on this Lisp.~%"))


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


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
; Original authors: Jared Davis <jared@centtech.com>
;                   Sol Swords <sswords@centtech.com>


(in-package "ACL2")

(include-book "tools/include-raw" :dir :system)
(include-book "tools/bstar" :dir :system)

(defn make-fast-alist (alist)
  ":Doc-Section Hons-and-Memoization

~c[(make-fast-alist alist)] creates a fast-alist from the input alist,
returning ~c[alist] itself or, in some cases, a new object equal to it.~/

Note: it is often better to use ~ilc[with-fast-alist]; see its documentation
for more information.

Logically, ~c[make-fast-alist] is the identity function.

Under the hood, we construct and return an object that is ~c[equal] to
~c[alist] and which is a fast alist.  If ~c[alist] is already a fast alist,
almost no work is required: we simply return it unchanged.

When ~c[alist] is not fast, we must minimally construct a hash table for its
bindings.  It is often possible to bind this new hash table to ~c[alist]
itself.  But in certain cases when the alist keys are not ~il[normed], a new
alist ust be constructed, also, and so we may return an ~c[equal] but not
~c[eq] alist.  (In these cases, we still try to avoid at least some consing by
reusing the \"longest normed tail\" of the alist.)~/~/"

  ;; Has an under-the-hood implementation
  alist)

(defttag hons-extra)

;; (depends-on "hons-extra-raw.lsp")
(include-raw "hons-extra-raw.lsp")




(defdoc with-fast-alist
  ":Doc-Section Hons-and-Memoization

~c[(with-fast-alist name form)] causes ~c[name] to be a fast alist for the
execution of ~c[form].~/

Logically, ~c[with-fast-alist] just returns ~c[form].

Under the hood, we cause ~c[alist] to become a fast alist before executing
~c[form].  If doing so caused us to introduce a new hash table, the hash table
is automatically freed after ~c[form] completes.

More accurately, under the hood ~c[(with-fast-alist name form)] essentially
expands to something like:

~bv[]
 (if (already-fast-alist-p name)
     form
   (let ((<temp> (make-fast-alist name)))
     (prog1 form
            (fast-alist-free <temp>))))
~ev[]

Practically speaking, ~c[with-fast-alist] is frequently a better choice then
just using ~ilc[make-fast-alist], and is particularly useful for writing
functions that can take either fast or slow alists as arguments.  That is,
consider the difference between:

~bv[]
 (defun bad (alist ...)
   (let* ((fast-alist (make-fast-alist alist))
          (answer     (expensive-computation fast-alist ...)))
    (prog2$ (fast-alist-free fast-alist)
            answer)))

 (defun good (alist ...)
    (with-fast-alist alist
      (expensive-computation alist ...)))
~ev[]

Either approach is fine if the caller provides a slow ~c[alist].  But if the
input ~c[alist] is already fast, ~c[bad] will (perhaps unexpectedly) free it!
On the other hand, ~c[good] is able to take advantage of an already-fast
argument and will not cause it to be inadvertently freed.

See also ~ilc[with-fast-alists], which allows you to call ~ilc[with-fast-alist]
on several alists simultaneously.

Note that we also extend the ~ilc[b*] macro with ~c[with-fast] pattern binder.
That is, you may write something like this:

~bv[]
 (b* (...
      ((with-fast a b c ...))
      ...)
   ...)
~ev[]

which causes ~c[a], ~c[b], and ~c[c] to become fast alists until the completion
of the ~c[b*] form.

Note that with-fast-alist will cause logically tail-recursive functions not to
execute tail-recursively if its cleanup phase happens after the tail-recursive
call returns.~/~/")

(defmacro-last with-fast-alist)

(defun with-fast-alists-fn (alists form)
  (if (atom alists)
      form
    `(with-fast-alist ,(car alists)
                      ,(with-fast-alists-fn (cdr alists) form))))

(defmacro with-fast-alists (alists form)
  ":Doc-Section Hons-and-Memoization

Concisely call ~ilc[with-fast-alist] on multiple alists.~/~/

Example:
~bv[]
 (with-fast-alists (a b c) form)
~ev[]
is just shorthand for:
~bv[]
 (with-fast-alist a
  (with-fast-alist b
   (with-fast-alist c
    form)))
~ev[]"

  (with-fast-alists-fn alists form))

(def-b*-binder with-fast
  (declare (xargs :guard (not forms))
           (ignorable forms))
  `(with-fast-alists ,args ,rest-expr))



#||

(b* ((a '((1 . a) (2 . b) (3 . c)))
     (b '((1 . a) (2 . b) (3 . d)))
     (- (cw "Before with-fast-alists:~%"))
     (- (fast-alist-summary)))

    (with-fast-alists
     (a b)
     (b* ((- (cw "After with-fast-alists:~%"))
          (- (fast-alist-summary))
          (x (hons-get 2 a))
          (a ())
          (y (hons-get 3 b)))
       (list (cdr x) (cdr y) a))))

(fast-alist-summary)

(b* ((a '((1 . a) (2 . b) (3 . c)))
     (b '((1 . a) (2 . b) (3 . d)))
     (- (cw "Before with-fast:~%"))
     (- (fast-alist-summary))
     ((with-fast a b))      ;; a and b become fast until the end of the b*.
     (- (cw "After with-fast:~%"))
     (- (fast-alist-summary))
     (x (hons-get 2 a))
     (a ())
     (y (hons-get 3 b)))
  (list (cdr x) (cdr y) a))

(fast-alist-summary)

||#





(defdoc with-stolen-alist
  ":Doc-Section Hons-and-Memoization

~c[(with-stolen-alist name form)] ensures that ~c[name] is a fast alist at the
start of the execution of ~c[form].  At the end of execution, it ensures that
~c[name] is a fast alist if and only if it was originally.  That is, if
~c[name] was not a fast alist originally, its hash table link is freed, and if
it was a fast alist originally but its table was modified during the execution
of ~c[form], that table is restored.  Note that any extended table created from
the original fast alist during ~c[form] must be manually freed.~/

Logically, ~c[with-stolen-alist] just returns ~c[form].

Under the hood, we cause ~c[alist] to become a fast alist before executing
~c[form], and we check the various conditions outlined above before returning
the final value.

Note that with-stolen-alist will cause logically tail-recursive functions not to
execute tail-recursively if its cleanup phase happens after the tail-recursive
call returns.~/~/")

(defmacro-last with-stolen-alist)

(defun with-stolen-alists-fn (alists form)
  (if (atom alists)
      form
    `(with-stolen-alist ,(car alists)
                      ,(with-stolen-alists-fn (cdr alists) form))))

(defmacro with-stolen-alists (alists form)
  ":Doc-Section Hons-and-Memoization

Concisely call ~ilc[with-stolen-alist] on multiple alists.~/~/

Example:
~bv[]
 (with-stolen-alists (a b c) form)
~ev[]
is just shorthand for:
~bv[]
 (with-stolen-alist a
  (with-stolen-alist b
   (with-stolen-alist c
    form)))
~ev[]"

  (with-stolen-alists-fn alists form))

(def-b*-binder with-stolen
  (declare (xargs :guard (not forms))
           (ignorable forms))
  `(with-stolen-alists ,args ,rest-expr))



#||

(b* ((a '((1 . a) (2 . b) (3 . c)))
     (b '((1 . a) (2 . b) (3 . d)))
     (- (cw "Before with-stolen-alists:~%"))
     (- (fast-alist-summary))
     (res (with-stolen-alists
            (a b)
            (b* ((- (cw "Inside with-stolen-alists:~%"))
                 (- (fast-alist-summary))
                 (x (hons-get 2 a))
                 (a ())
                 (y (hons-get 3 b)))
              (list (cdr x) (cdr y) a)))))
  (cw "After with-stolen-alists:~%")
  (fast-alist-summary)
  res)

(b* ((a '((1 . a) (2 . b) (3 . c)))
     (b (make-fast-alist '((1 . a) (2 . b) (3 . d))))
     (- (cw "Before with-stolen-alists:~%"))
     (- (fast-alist-summary))
     (res (with-stolen-alists
            (a b)
            (b* ((- (cw "Inside with-stolen-alists:~%"))
                 (- (fast-alist-summary))
                 (x (hons-get 2 a))
                 (a ())
                 (b (hons-acons 5 'f b))
                 (y (hons-get 5 b)))
              (fast-alist-free b)
              (list (cdr x) (cdr y) a))))
     (b (hons-acons 4 'e b)))
  (cw "After with-stolen-alists:~%")
  (fast-alist-summary)
  (fast-alist-free b)
  res)

||#




(defdoc fast-alist-free-on-exit
  ":Doc-Section Hons-and-Memoization
Free a fast alist after the completion of some form.~/

Logically, ~c[(fast-alist-free-on-exit name form)] is the identity and returns
~c[form].

Under the hood, this essentially expands to:
~bv[]
 (prog1 form
        (fast-alist-free name))
~ev[]

In other words, ~c[name] is not freed immediately, but instead remains a fast
alist until the form completes.  This may be useful when you are writing code
that uses a fast alist but has many return points.

See also ~ilc[fast-alists-free-on-exit], which can be used to free several
alists.

We also provide a ~c[b*] binder, ~c[free-on-exit], e.g.,
~bv[]
 (b* (...
      ((free-on-exit a b c))
      ...)
   ...)
~ev[]

causes ~c[a], ~c[b], and ~c[c] to be freed when the ~c[b*] completes, but they
remain fast alists until then.~/~/")

(progn!
 (set-raw-mode t)
 (defmacro fast-alist-free-on-exit-raw (alist form)
   `(our-multiple-value-prog1
     ,form
     (fast-alist-free ,alist))))

(defmacro-last fast-alist-free-on-exit)

(defun fast-alists-free-on-exit-fn (alists form)
  (if (atom alists)
      form
    `(fast-alist-free-on-exit ,(car alists)
                              ,(fast-alists-free-on-exit-fn (cdr alists) form))))

(defmacro fast-alists-free-on-exit (alists form)
  ":Doc-Section Hons-and-Memoization
Concisely call ~ilc[fast-alist-free-on-exit] for several alists.~/

For example:
~bv[]
 (fast-alists-free-on-exit (a b c) form)
~ev[]
is just shorthand for:
~bv[]
 (fast-alist-free-on-exit a
  (fast-alist-free-on-exit b
   (fast-alist-free-on-exit c
    form)))
~ev[]~/~/"
  (fast-alists-free-on-exit-fn alists form))

(def-b*-binder free-on-exit
  (declare (xargs :guard (not forms))
           (ignorable forms))
  `(fast-alists-free-on-exit ,args ,rest-expr))


#|

(fast-alist-summary)

(let ((a (hons-acons 'a 1 'a-alist)))
  (fast-alist-free-on-exit a            ;; a is still fast until the end of the
    (hons-get 'a a)))                   ;; fast-alist-free-on-exit form

(fast-alist-summary)

(let ((a (hons-acons 'a 1 'a-alist))    ;; a and b are still fast until the
      (b (hons-acons 'b 2 'b-alist)))   ;; exit of the fast-alists-free-on-exit
  (fast-alists-free-on-exit             ;; form.
   (a b)
   (+ (cdr (hons-get 'a a))
      (cdr (hons-get 'b b)))))

(fast-alist-summary)



(b* ((- (fast-alist-summary))

     (a (hons-acons 'a 1 'a-alist))
     (b (hons-acons 'b 2 'b-alist))
     (- (cw "After creating a and b.~%"))
     (- (fast-alist-summary))

     ((free-on-exit a b))           ;; a and b are still fast until the end of

     (c (hons-acons 'c 3 'c-alist))
     (- (cw "After creating c.~%"))
     (- (fast-alist-summary))
     (- (fast-alist-free c)))

  (+ (cdr (hons-get 'a a))
     (cdr (hons-get 'b b))))

(fast-alist-summary) ;; all alists freed

|#

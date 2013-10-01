; ACL2 Version 6.3 -- A Computational Logic for Applicative Common Lisp
; Copyright (C) 2013, Regents of the University of Texas

; This version of ACL2 is a descendent of ACL2 Version 1.9, Copyright
; (C) 1997 Computational Logic, Inc.  See the documentation topic NOTE-2-0.

; This program is free software; you can redistribute it and/or modify
; it under the terms of the LICENSE file distributed with ACL2.

; This program is distributed in the hope that it will be useful,
; but WITHOUT ANY WARRANTY; without even the implied warranty of
; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
; LICENSE for more details.

; Regarding authorship of ACL2 in general:

; Written by:  Matt Kaufmann               and J Strother Moore
; email:       Kaufmann@cs.utexas.edu      and Moore@cs.utexas.edu
; Department of Computer Science
; University of Texas at Austin
; Austin, TX 78701 U.S.A.

; serialize.lisp -- logical definitions for "serialization" routines,
;                   i.e., saving ACL2 objects in files for later loading

; This file was developed and contributed by Jared Davis on behalf of
; Centaur Technology.

; Note: The serialization routines are restricted to work only in
; ACL2(h).  However, they are independent of the remainder of the HONS
; extension and might some day become part of ordinary ACL2.

; Please direct correspondence about this file to Jared Davis
; <jared@centtech.com>.

(in-package "ACL2")

(defdoc serialize
  ":Doc-Section serialize

routines for saving ACL2 objects to files, and later restoring them~/

This documentation topic relates to an experimental extension of ACL2 that
supports ~ilc[hons], memoization, and fast alists.  ~l[hons-and-memoization].
Thanks to Jared Davis for contributing the ``serialization'' routines for
saving ACL2 objects in files for later loading.

We implement some routines for writing arbitrary ACL2 objects to files, and for
loading those files later.  We usually call these \".sao\" files, which stands
for (S)erialized (A)CL2 (O)bject.

Our serialization scheme uses a compact, binary format that preserves structure
sharing in the original object.  We optimize for read performance.~/~/")

(defmacro serialize-write (filename obj &key verbosep)
  ":Doc-Section serialize

write an ACL2 object into a file~/

General form:
~bv[]
 (serialize-write filename obj
                  [:verbosep  {t, nil}])    ; nil by default
  -->
 state
~ev[]

In the logic this carries out an oracle read.

Under the hood, we try to save ~c[obj] into the file indicated by ~c[filename],
which must be a string.  The object can later be recovered with
~ilc[serialize-read].  We just return ~c[state], and any failures (e.g., file
not openable) will result in a hard Lisp error.

Writing objects to disk is generally slower than reading them back in since
some analysis is required to convert an object into our ~il[serialize]d object
format.

The ~c[verbosep] flag just says whether to print some low-level details related
to timing and memory usage as the file is being read.~/~/"

  `(serialize-write-fn ,filename ,obj ,verbosep state))

(defun serialize-write-fn (filename obj verbosep state)
  (declare (xargs :guard (and (stringp filename)
                              (booleanp verbosep)
                              (state-p state))
                  :stobjs state)
           (ignorable filename obj verbosep))
  #-acl2-loop-only
  (cond
   ((live-state-p state)
    #-hons
    (er hard? 'serialize-write-fn
        "Serialization routines are currently only available in the HONS ~
         version of ACL2.")
    #+hons
    (with-open-file
     (stream filename
             :direction :output
             :if-exists :supersede)
     (let* ((*ser-verbose* verbosep))
       (ser-encode-to-stream obj stream)))
    (return-from serialize-write-fn state))
   (t

; We fall through to the logic code if we are doing a proof, where
; *hard-error-returns-nilp* is true.  Otherwise, we throw here with an error
; message.

    (er hard? 'serialize-write-fn "Serialization requires a live state.")))
  (mv-let (erp val state)
          (read-acl2-oracle state)
          (declare (ignore erp val))
          state))

(defmacro serialize-read (filename &key
                                   (hons-mode ':smart)
                                   verbosep)
  ":Doc-Section serialize

read a serialized ACL2 object from a file~/

General form:
~bv[]
 (serialize-read filename
                 [:hons-mode {:always, :never, :smart}]   ; :smart by default
                 [:verbosep  {t, nil}])                   ; nil by default
  -->
 (mv obj state)
~ev[]

In the logic this is an oracle read.

Under the hood, we try to read and return a serialized object from a file that
was presumably created by ~ilc[serialize-write].  On success we return the
contents of the file.  Any failures (e.g., file not found, bad file contents,
etc.) will result in a hard Lisp error.

The ~c[filename] should be a string that gives the path to the file.

The ~c[hons-mode] controls how whether to use ~ilc[hons] or ~ilc[cons] to
restore the object.  The default mode is ~c[:smart], which means that conses
that were ~il[normed] at the time of the file's creation should be restored
with ~c[hons].  But you can override this and insist that ~c[hons] is to
~c[:always] or ~c[:never] be used, instead.

Why would you use ~c[:never]?  If your object previously had a lot of honses,
but you no longer have any need for them to be normed, then using ~c[:never]
may sometimes be a lot faster since it can avoid ~c[hons] calls.  On the other
hand, if you are going to ~ilc[hons-copy] some part of the file's contents,
then it is likely faster to use ~c[:smart] or ~c[:always] instead of first
creating normal conses and then copying them to build honses.

The ~c[:verbosep] flag just controls whether to print some low-level details
related to timing and memory usage as the file is being read.~/~/"

  `(serialize-read-fn ,filename ,hons-mode ,verbosep state))

(defun serialize-read-fn (filename hons-mode verbosep state)
  (declare (xargs :guard (and (stringp filename)
                              (member hons-mode '(:never :always :smart))
                              (booleanp verbosep)
                              (state-p state))
                  :stobjs state)
           (ignorable filename hons-mode verbosep))

  #-acl2-loop-only
  (cond
   ((live-state-p state)
    (return-from
     serialize-read-fn
     #-hons
     (progn (er hard? 'serialize-read-fn
                "Serialization routines are currently only available in the ~
                 HONS version of ACL2.")
            (mv nil state))
     #+hons
     (with-open-file
      (stream filename :direction :input)
      (let* ((*ser-verbose* verbosep)
             (val           (ser-decode-from-stream t hons-mode stream)))
        (mv val state)))))
   (t

; We fall through to the logic code if we are doing a proof, where
; *hard-error-returns-nilp* is true.  Otherwise, we throw here with an error
; message.

    (er hard? 'serialize-read-fn "Serialization requires a live state.")))
  (mv-let (erp val state)
          (read-acl2-oracle state)
          (declare (ignore erp))
          (mv val state)))

(defdoc serialize-alternatives
  ":Doc-Section serialize

alternatives to the ~il[serialize] routines~/

~il[Hons] users could previously use the routines ~c[compact-print-file] and
~c[compact-read-file].  These are deprecated and are no longer built into ACL2.
However, they are still available by loading the new community book,
~c[serialize/compact-print].  Note that loading this book requires a ttag, and
these routines are still only available in raw lisp.

Another predecessor of the serialization routines were hons archives, which are
still available in the ~c[hons-archive] library.  The serialization routines
are generally better and we recommend against using hons archives for new
projects.~/~/")

(defdoc serialize-in-books
  ":Doc-Section serialize

using serialization efficiently in books~/

Our serialize scheme was developed in order to allow very large ACL2 objects to
be loaded into books.  Ordinarily this is carried out using
~ilc[serialize-read] within a ~ilc[make-event], e.g.,

~bv[]
  (make-event (mv-let (obj state)
                      (serialize-read \"my-file\")
                      (value `(defconst *my-file* ',obj))))
~ev[]

But this scheme is not particularly efficient.

During ~ilc[certify-book], the actual call of ~c[serialize-read] is carried
out, and this is typically pretty fast.  But then a number of possibly
inefficient things occur.~bq[]

- The ACL2 function ~c[bad-lisp-object] is run on the resulting object.  This
is memoized for efficiency, but may still take considerable time when the file
is very large.

- The checksum of the resulting object is computed.  This is also memoized, but
as before may still take some time.

- The object that was just read is then written into book.cert, essentially
with ~ilc[serialize-write].  This can take some time, and results in large
certifiate files.~eq[]

Then, during ~il[include-book], the ~c[make-event] expansion of is loaded.
This is now basically just a ~c[serialize-read].

The moral of the story is that using serialize will only help your
~c[certify-book] time, and it only impacts a portion of the overall time.

To avoid this overhead, we have developed an UNSOUND alternative to
~c[serialize-read], which is available only by loading an additional book.  So,
if the above scheme is not performing well for you, you may wish to see
the community book ~c[serialize/unsound-read].~/~/")

(defmacro with-serialize-character (val form)
  (declare (xargs :guard (member val '(nil #\Y #\Z))))

  ":Doc-Section serialize

control output mode for ~c[print-object$]~/

This documentation topic relates to an experimental extension of ACL2 that
supports ~ilc[hons], memoization, and fast alists.  ~l[hons-and-memoization].
~l[serialize] for a discussion of ``serialization'' routines, contributed by
Jared Davis for saving ACL2 objects in files for later loading.

The expression ~c[(with-serialize-character char form)] evaluates to the value
of ~c[form], but with the serialize-character of the ~ilc[state] assigned to
~c[char], which should be one of ~c[nil], ~c[#\\Y], or ~c[#\\Z].  We describe
the effect of that assignment below.  But note that if you are doing this
because of one or more specific calls of ~c[print-object$], such as
~c[(print-object$ x channel state)], then you may wish instead to evaluate
~c[(print-object$-ser x serialize-character channel state)], in which case you
will not need to use ~c[with-serialize-character].  (Note however that
~c[serialize-character] is treated as ~c[nil] for other than a HONS version.)

~bv[]
General forms:
(with-serialize-character nil form)
(with-serialize-character #\Y form)
(with-serialize-character #\Z form)
~ev[]
where ~c[form] should evaluate to an error triple (~pl[error-triples]).

Note that if you prefer to obtain the same behavior (as described below)
globally, rather than only within the scope of ~c[with-serialize-character],
then use ~c[set-serialize-character] in a corresponding manner:

~bv[]
(set-serialize-character nil state)
(set-serialize-character #\Y state)
(set-serialize-character #\Z state)
~ev[]

In each case above, calls of ~c[print-object$] (~pl[io]) in ~c[form] will
produce an object that can be read by the HONS version of ACL2.  In the first
case, that object is printed as one might expect at the terminal, as an
ordinary Lisp s-expression.  But in the other cases, the object is printed by
first laying down either ~c[#Y] or ~c[#Z] (as indicated) and then calling
~ilc[serialize-write] (or more precisely, the underlying function called by
~c[serialize-write] that prints to a stream).

Consider what happens when the ACL2 reader encounters an object produced as
described above (in the ~c[#Y] or ~c[#Z] case).  When the object was written,
information was recorded on whether that object was a ~il[hons].  In the case
of ~c[#Z], the object will be read as a hons if and only if it was originally
written as a hons.  But in the case of ~c[#Y], it will never be read as a hons.
Thus, ~c[#Y] and ~c[#Z] will behave the same if the original written object was
not a hons, creating an object that is not a hons.  For an equivalent
explanation and a bit more discussion, ~pl[serialize-read], in particular the
discussion of the hons-mode.  The value ~c[:smart] described there corresponds
to ~c[#Z], while ~c[:never] corresponds to ~c[#Y].~/~/"

  `(state-global-let*
    ((serialize-character ,val set-serialize-character))
    ,form))

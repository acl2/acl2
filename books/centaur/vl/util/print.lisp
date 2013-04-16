; VL Verilog Toolkit
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
; Original author: Jared Davis <jared@centtech.com>

(in-package "VL")
(include-book "defs")
(include-book "print-urlencode")
(include-book "print-htmlencode")
(include-book "cw-unformatted")
(include-book "str/natstr" :dir :system)
(local (include-book "arithmetic"))
(local (include-book "misc/assert" :dir :system))
(local (include-book "std/io/base" :dir :system))
(local (in-theory (disable acl2::print-base-p)))


(defxdoc printer
  :parents (vl)
  :short "Applicative \"printer\" for building strings."

  :long "<p>We implement a printer as a stobj name @(see ps), and use it as the
back-end for formatting our source code and for other output tasks.  Our
printer is applicative and the act of printing only accumulates characters or
strings into a list.  These printed elements are kept in reverse order, which
makes the sequential printing of small chunks of text reasonably
efficient.</p>")


(define vl-printed-p (x)
  :parents (printer)
  :short "Recognize a printed object (string or character)."
  (or (characterp x)
      (stringp x))
  ///
  (defthm vl-printed-p-cr
    (equal (vl-printed-p x)
           (or (characterp x)
               (stringp x)))
    :rule-classes :compound-recognizer
    :hints(("Goal" :in-theory (enable vl-printed-p))))

  (defthm vl-printed-p-by-backchaining
    (implies (or (characterp x)
                 (stringp x))
             (vl-printed-p x))))


(deflist vl-printedlist-p (x)
  (vl-printed-p x)
  :guard t
  :elementp-of-nil nil
  :parents (printer)
  :short "Recognizer for mixed lists of strings and characters."
  :rest
  ((defthm vl-printedlist-p-when-character-listp
     (implies (character-listp x)
              (vl-printedlist-p x)))

   (defthm vl-printedlist-p-when-string-listp
     (implies (string-listp x)
              (vl-printedlist-p x)))

   (local (in-theory (e/d (repeated-revappend)
                          ((:executable-counterpart force)))))

   (defthm vl-printedlist-p-of-repeated-revappend
     (implies (and (vl-printedlist-p x)
                   (force (vl-printedlist-p y)))
              (vl-printedlist-p (repeated-revappend n x y))))

   (defthm vl-printedlist-p-of-make-list-ac
     (implies (and (vl-printed-p x)
                   (force (vl-printedlist-p y)))
              (vl-printedlist-p (make-list-ac n x y))))

   (defthm vl-printedlist-p-of-vl-html-encode-chars-aux
     (implies (and (character-listp x)
                   (natp col)
                   (vl-printedlist-p acc))
              (vl-printedlist-p
               (mv-nth 1 (vl-html-encode-chars-aux x col tabsize acc))))
     :hints(("Goal" :in-theory (enable vl-html-encode-chars-aux))))

   (defthm vl-printedlist-p-of-revappend-chars
     (implies (and (stringp x)
                   (vl-printedlist-p acc))
              (vl-printedlist-p (str::revappend-chars x acc)))
     :hints(("Goal" :in-theory (enable str::revappend-chars))))

   (defthm vl-printedlist-p-of-vl-html-encode-string-aux
     (implies (and (stringp x)
                   (natp n)
                   (natp xl)
                   (natp col)
                   (vl-printedlist-p acc)
                   (<= n xl)
                   (= xl (length x)))
              (vl-printedlist-p
               (mv-nth 1 (vl-html-encode-string-aux x n xl col tabsize acc))))
     :hints(("Goal" :in-theory (enable vl-html-encode-string-aux))))

   (defthm vl-printedlist-p-of-vl-url-encode-chars-aux
     (implies (vl-printedlist-p acc)
              (vl-printedlist-p (vl-url-encode-chars-aux x acc)))
     :hints(("Goal" :in-theory (enable vl-url-encode-chars-aux))))

   (defthm vl-printedlist-p-of-vl-url-encode-string-aux
     (implies (and (stringp x)
                   (vl-printedlist-p acc)
                   (natp n)
                   (natp xl)
                   (<= n xl)
                   (= xl (length x)))
              (vl-printedlist-p (vl-url-encode-string-aux x n xl acc)))
     :hints(("Goal" :in-theory (enable vl-url-encode-string-aux))))))

(define vl-printedlist-length ((x vl-printedlist-p)
                               (acc natp))
  :returns (len natp :rule-classes :type-prescription)
  :parents (vl-printedlist-p)
  :short "Compute the total length of the list, in characters."
  :long "<p>This is different than ordinary @(see len) because any strings
within the list may have their own lengths.</p>"
  (if (atom x)
      (lnfix acc)
    (vl-printedlist-length (cdr x)
                           (+ (if (characterp (car x))
                                  1
                                (length (car x)))
                              acc))))

(define vl-printedlist-peek
  ((x vl-printedlist-p "The printed list, which we assume is in reverse order!"))
  :returns (maybe-char (or (not maybe-char)
                           (characterp maybe-char))
                       :rule-classes :type-prescription)
  :parents (vl-printedlist-p)
  :short "Extract the last character that was printed."
  :long "<p>This is generally useful for things like <i>insert a space unless
we just printed a newline</i>, etc.</p>"
  (and (consp x)
       (if (characterp (car x))
           (car x)
         (let ((len (length (car x))))
           (if (= len 0)
               ;; Degenerate case where we printed an empty string, look
               ;; further.
               (vl-printedlist-peek (cdr x))
             (char (car x) (1- len)))))))


(define print-base-p (x)
  :parents (ps)
  :short "Fixed version of ACL2's @(see acl2::print-base-p) function that
returns a Boolean."
  :long "<p>ACL2's built-in version of this just calls @(see member) and hence
can return a non-Boolean.  That makes it incompatible with @(see stobj) field
@('satisfies') types, so we have to introduce our own version.</p>"
  (if (acl2::print-base-p x)
      t
    nil))


(defxdoc ps
  :parents (printer)
  :short "The <b>p</b>rinter <b>s</b>tate stobj."

  :long "<p>Our printer's state is a represented as the stobj @('ps'), whose
definition is as follows.</p>

@(def ps)

<p>The main fields are:</p>

<ul>

<li>@('rchars') -- holds the printed elements (characters and strings) in
reverse order.  The is badly named because originally it only held characters,
but we later extended it to strings to make string-printing more
efficient.</li>

<li>@('col') -- records the current column number.</li>

</ul>

<p>These fields are typically altered by every printing function.</p>

<p>The printer also includes some configuration fields which allow you to
influence the behavior of certain printing functions.  These fields are
typically not changed by printing functions.  They can also be easily loaded
and saved into a @(see vl-psconfig-p) object.</p>

<ul>

<li>@('autowrap-col'), a column number for autowrapping,</li>

<li>@('autowrap-ind'), number of spaces to indent after autowrapping,</li>

<li>@('htmlp'), a flag indicating whether we are printing html,</li>

<li>@('tabsize'), the tab size to use for &amp;nbsp; expansion in html mode,</li>

<li>@('package'), a symbol which specifies the \"home\" package for printing
symbols (e.g., @('ACL2::foo') vs. @('VL::foo').</li>

<li>@('base'), an @('acl2::print-base-p') for base 10, 16, etc.</li>

</ul>

<p>Finally, the printer includes a @('misc') field which must be an alist, and
which can be used to pass along any custom parameters that your own printing
functions would like to inspect.</p>

<p>I once considered changing the way @('ps') works, so that we would use an
array of characters and write into the array, instead of consing characters.
This is appealing because we might be able to avoid consing during printing at
the cost of having to allocate a buffer at the beginning.  But, preliminary
tests suggested that there is not much of a speed improvement, and while it
might have some nice memory characteristics, the current solution is
particularly nice in that it makes @(see with-local-ps) very cheap, etc.</p>

<p>We generally hide the existence of @('ps') by introducing @('ps')-free
wrapper @(see ps-macros).  We ask that you not use the primitive stobj
functions directly, but instead use these wrappers.</p>")

(defstobj ps

  ;; The accumulated characters
  (rchars       :type (satisfies vl-printedlist-p))

  ;; The current column number.
  (col          :initially 0 :type unsigned-byte)

  ;; This setting specifies which column long lines are to be broken up at.
  ;; This is not a hard boundary, and we only insert a newline after we have
  ;; exceeded this threshold when routines like vl-println? are called.
  (autowrap-col :initially 80 :type unsigned-byte)
  (autowrap-ind :initially 5 :type unsigned-byte)

  ;; Are we printing html?
  (htmlp        :type (satisfies booleanp) :initially nil)

  ;; What is the desired tab size?  This is only used in HTML mode to decide
  ;; how many &nbsp; characters to insert.
  (tabsize      :initially 8 :type (integer 1 *))

  (pkg          :initially VL::a-symbol-that-is-not-imported :type symbol)
  (base         :initially 10 :type (satisfies print-base-p))

  (misc         :initially nil :type (satisfies alistp))

  :inline t

  :renaming ((psp                 vl-ps-p)
             (rchars              vl-ps->rchars-raw)
             (col                 vl-ps->col-raw)
             (autowrap-col        vl-ps->autowrap-col-raw)
             (autowrap-ind        vl-ps->autowrap-ind-raw)
             (htmlp               vl-ps->htmlp-raw)
             (tabsize             vl-ps->tabsize-raw)
             (pkg                 vl-ps->package-raw)
             (base                vl-ps->base-raw)
             (misc                vl-ps->misc-raw)
             (update-rchars       vl-ps-update-rchars-fn)
             (update-col          vl-ps-update-col-fn)
             (update-autowrap-col vl-ps-update-autowrap-col-fn)
             (update-autowrap-ind vl-ps-update-autowrap-ind-fn)
             (update-htmlp        vl-ps-update-htmlp-fn)
             (update-tabsize      vl-ps-update-tabsize-fn)
             (update-pkg          vl-ps-update-package-fn)
             (update-base         vl-ps-update-base-fn)
             (update-misc         vl-ps-update-misc-fn)
             ))

(defsection ps-macros
  :parents (ps)
  :short "Low-level interface to @(see ps).")


(defsection vl-ps->rchars
  :parents (ps-macros)
  :short "@('(vl-ps->rchars) --> rchars')"
  :long "<p>This is misnamed for historic reasons.  It used to return a
character list in reverse order.  It now returns a @(see vl-printedlist-p),
also in reverse order.</p>

@(def vl-ps->rchars)"

  (define vl-ps->rchars-fn (ps)
    :returns (rchars vl-printedlist-p)
    :inline t
    (mbe :logic (let ((rchars (vl-ps->rchars-raw ps)))
                  (if (vl-printedlist-p rchars)
                      rchars
                    nil))
         :exec (vl-ps->rchars-raw ps)))

  (remove-macro-alias vl-ps->rchars-fn) ;; so we can add our own

  (defmacro vl-ps->rchars ()
    `(vl-ps->rchars-fn ps))

  (add-macro-alias vl-ps->rchars vl-ps->rchars-fn$inline))


(defsection vl-ps->col
  :parents (ps-macros)
  :short "@('(vl-ps->col) --> col')"
  :long "@(def vl-ps->col)"

  (define vl-ps->col-fn (ps)
    :returns (col natp :rule-classes :type-prescription)
    :inline t
    (mbe :logic (nfix (vl-ps->col-raw ps))
         :exec (vl-ps->col-raw ps)))

  (remove-macro-alias vl-ps->col-fn)

  (defmacro vl-ps->col ()
    `(vl-ps->col-fn ps))

  (add-macro-alias vl-ps->col vl-ps->col-fn$inline))


(defsection vl-ps->autowrap-col
  :parents (ps-macros)
  :short "@('(vl-ps->autowrap-col) --> autowrap-col')"
  :long "@(def vl-ps->autowrap-col)"

  (define vl-ps->autowrap-col-fn (ps)
    :returns (autowrap-col natp :rule-classes :type-prescription)
    :inline t
    (mbe :logic (nfix (vl-ps->autowrap-col-raw ps))
         :exec (vl-ps->autowrap-col-raw ps)))

  (remove-macro-alias vl-ps->autowrap-col-fn)

  (defmacro vl-ps->autowrap-col ()
    `(vl-ps->autowrap-col-fn ps))

  (add-macro-alias vl-ps->autowrap-col vl-ps->autowrap-col-fn$inline))


(defsection vl-ps->autowrap-ind
  :parents (ps-macros)
  :short "@('(vl-ps->autowrap-ind) --> autowrap-ind')"
  :long "@(def vl-ps->autowrap-ind)"

  (define vl-ps->autowrap-ind-fn (ps)
    :returns (autowrap-ind natp :rule-classes :type-prescription)
    :inline t
    (mbe :logic (nfix (vl-ps->autowrap-ind-raw ps))
         :exec (vl-ps->autowrap-ind-raw ps)))

  (remove-macro-alias vl-ps->autowrap-ind-fn)

  (defmacro vl-ps->autowrap-ind ()
    `(vl-ps->autowrap-ind-fn ps))

  (add-macro-alias vl-ps->autowrap-ind vl-ps->autowrap-ind-fn$inline))


(defsection vl-ps->htmlp
  :parents (ps-macros)
  :short "@('(vl-ps->htmlp) --> htmlp')"
  :long "@(def vl-ps->htmlp)"

  (define vl-ps->htmlp-fn (ps)
    :returns (htmlp booleanp :rule-classes :type-prescription)
    :inline t
    (mbe :logic (if (vl-ps->htmlp-raw ps) t nil)
         :exec (vl-ps->htmlp-raw ps)))

  (remove-macro-alias vl-ps->htmlp-fn)

  (defmacro vl-ps->htmlp ()
    `(vl-ps->htmlp-fn ps))

  (add-macro-alias vl-ps->htmlp vl-ps->htmlp-fn$inline))


(defsection vl-ps->tabsize
  :parents (ps-macros)
  :short "@('(vl-ps->tabsize) --> tabsize')"
  :long "@(def vl-ps->tabsize)"

  (define vl-ps->tabsize-fn (ps)
    :returns (tabsize posp :rule-classes :type-prescription)
    :inline t
    (mbe :logic (if (posp (vl-ps->tabsize-raw ps))
                    (vl-ps->tabsize-raw ps)
                  1)
         :exec (vl-ps->tabsize-raw ps)))

  (remove-macro-alias vl-ps->tabsize-fn)

  (defmacro vl-ps->tabsize ()
    `(vl-ps->tabsize-fn ps))

  (add-macro-alias vl-ps->tabsize vl-ps->tabsize-fn$inline))


(defsection vl-ps->package
  :parents (ps-macros)
  :short "@('(vl-ps->package) --> package')"
  :long "@(def vl-ps->package)"

  (define vl-ps->package-fn (ps)
    :returns (package symbolp :rule-classes :type-prescription)
    :inline t
    (mbe :logic (if (symbolp (vl-ps->package-raw ps))
                    (vl-ps->package-raw ps)
                  nil)
         :exec (vl-ps->package-raw ps)))

  (remove-macro-alias vl-ps->package-fn)

  (defmacro vl-ps->package ()
    `(vl-ps->package-fn ps))

  (add-macro-alias vl-ps->package vl-ps->package-fn$inline))


(defsection vl-ps->base
  :parents (ps-macros)
  :short "@('(vl-ps->base) --> base')"
  :long "@(def vl-ps->base)"

  (local (in-theory (enable print-base-p)))

  (local (defthm natp-when-print-base-p
           (implies (acl2::print-base-p x)
                    (natp x))
           :hints(("Goal" :in-theory (enable acl2::print-base-p)))))

  (define vl-ps->base-fn (ps)
    :returns (base natp :rule-classes :type-prescription)
    :inline t
    (mbe :logic (if (print-base-p (vl-ps->base-raw ps))
                    (vl-ps->base-raw ps)
                  10)
         :exec (vl-ps->base-raw ps))
    ///
    (defthm print-base-p-of-vl-ps->base-fn
      (print-base-p (vl-ps->base-fn ps)))
    (defthm acl2-print-base-p-of-vl-ps->base-fn
      (acl2::print-base-p (vl-ps->base-fn ps))))

  (remove-macro-alias vl-ps->base-fn)

  (defmacro vl-ps->base ()
    `(vl-ps->base-fn ps))

  (add-macro-alias vl-ps->base vl-ps->base-fn$inline))


(defsection vl-ps->misc
  :parents (ps-macros)
  :short "@('(vl-ps->misc) --> misc')"
  :long "@(def vl-ps->misc)"

  (define vl-ps->misc-fn (ps)
    :returns (misc alistp)
    :inline t
    (mbe :logic (if (alistp (vl-ps->misc-raw ps))
                    (vl-ps->misc-raw ps)
                  nil)
         :exec (vl-ps->misc-raw ps)))

  (remove-macro-alias vl-ps->misc-fn)

  (defmacro vl-ps->misc ()
    `(vl-ps->misc-fn ps))

  (add-macro-alias vl-ps->misc vl-ps->misc-fn$inline))


(defsection vl-ps-update-rchars
  :parents (ps-macros)
  :short "@('(vl-ps-update-rchars rchars)')"
  :long "@(def vl-ps-update-rchars)"

  (defmacro vl-ps-update-rchars (rchars)
    `(vl-ps-update-rchars-fn ,rchars ps))

  (add-macro-alias vl-ps-update-rchars vl-ps-update-rchars-fn))


(defsection vl-ps-update-col
  :parents (ps-macros)
  :short "@('(vl-ps-update-col col)')"
  :long "@(def vl-ps-update-col)"

  (defmacro vl-ps-update-col (col)
    `(vl-ps-update-col-fn ,col ps))

  (add-macro-alias vl-ps-update-col vl-ps-update-col-fn))


(defsection vl-ps-update-autowrap-col
  :parents (ps-macros)
  :short "@('(vl-ps-update-autowrap-col autowrap-col)')"
  :long "@(def vl-ps-update-autowrap-col)"

  (defmacro vl-ps-update-autowrap-col (autowrap-col)
    `(vl-ps-update-autowrap-col-fn ,autowrap-col ps))

  (add-macro-alias vl-ps-update-autowrap-col vl-ps-update-autowrap-col-fn))


(defsection vl-ps-update-autowrap-ind
  :parents (ps-macros)
  :short "@('(vl-ps-update-autowrap-ind autowrap-ind)')"
  :long "@(def vl-ps-update-autowrap-ind)"

  (defmacro vl-ps-update-autowrap-ind (autowrap-ind)
    `(vl-ps-update-autowrap-ind-fn ,autowrap-ind ps))

  (add-macro-alias vl-ps-update-autowrap-ind vl-ps-update-autowrap-ind-fn))


(defsection vl-ps-update-htmlp
  :parents (ps-macros)
  :short "@('(vl-ps-update-htmlp htmlp)')"
  :long "@(def vl-ps-update-htmlp)"

  (defmacro vl-ps-update-htmlp (htmlp)
    `(vl-ps-update-htmlp-fn ,htmlp ps))

  (add-macro-alias vl-ps-update-htmlp vl-ps-update-htmlp-fn))


(defsection vl-ps-update-tabsize
  :parents (ps-macros)
  :short "@('(vl-ps-update-tabsize tabsize)')"
  :long "@(def vl-ps-update-tabsize)"

  (defmacro vl-ps-update-tabsize (tabsize)
    `(vl-ps-update-tabsize-fn ,tabsize ps))

  (add-macro-alias vl-ps-update-tabsize vl-ps-update-tabsize-fn))


(defsection vl-ps-update-package
  :parents (ps-macros)
  :short "@('(vl-ps-update-package package)')"
  :long "@(def vl-ps-update-package)"

  (defmacro vl-ps-update-package (package)
    `(vl-ps-update-package-fn ,package ps))

  (add-macro-alias vl-ps-update-package vl-ps-update-package-fn))


(defsection vl-ps-update-base
  :parents (ps-macros)
  :short "@('(vl-ps-update-base base)')"
  :long "@(def vl-ps-update-base)"

  (defmacro vl-ps-update-base (base)
    `(vl-ps-update-base-fn ,base ps))

  (add-macro-alias vl-ps-update-base vl-ps-update-base-fn))


(defsection vl-ps-update-misc
  :parents (ps-macros)
  :short "@('(vl-ps-update-misc misc)')"
  :long "@(def vl-ps-update-misc)"

  (defmacro vl-ps-update-misc (misc)
    `(vl-ps-update-misc-fn ,misc ps))

  (add-macro-alias vl-ps-update-misc vl-ps-update-misc-fn))


(in-theory (disable vl-ps-p

                    vl-ps->rchars-raw
                    vl-ps->col-raw
                    vl-ps->autowrap-col-raw
                    vl-ps->autowrap-ind-raw
                    vl-ps->htmlp-raw
                    vl-ps->tabsize-raw
                    vl-ps->package-raw
                    vl-ps->base-raw
                    vl-ps->misc-raw

                    vl-ps->rchars
                    vl-ps->col
                    vl-ps->autowrap-col
                    vl-ps->autowrap-ind
                    vl-ps->htmlp
                    vl-ps->tabsize
                    vl-ps->package
                    vl-ps->base
                    vl-ps->misc

                    vl-ps-update-rchars
                    vl-ps-update-col
                    vl-ps-update-autowrap-col
                    vl-ps-update-autowrap-ind
                    vl-ps-update-htmlp
                    vl-ps-update-tabsize
                    vl-ps-update-package
                    vl-ps-update-base
                    vl-ps-update-misc))


(defsection vl-ps-seq
  :parents (basic-printing)
  :short "Macro for issuing a sequence of printer commands."

  :long "<p>The macro @('(vl-ps-seq ...)') can be used to combine printing
commands.  For instance,</p>

@({
 (vl-ps-seq
   (vl-print \"foo\")
   (vl-println \"bar\")
   ...)
})

<p>Is short for:</p>

@({
 (let* ((ps (vl-print \"foo\"))
        (ps (vl-println \"bar\"))
        ...)
   ps)
})"

  (defun vl-ps-seq-pairs (x)
    (if (consp x)
        (cons `(ps ,(car x))
              (vl-ps-seq-pairs (cdr x)))
      nil))

  (defmacro vl-ps-seq (&rest args)
    (if (atom args)
        'ps
      (list* 'let* (vl-ps-seq-pairs (butlast args 1)) (last args)))))


(defsection vl-when-html
  :parents (basic-printing)
  :short "Like @(see vl-ps-seq), but the commands are only executed when
HTML mode is enabled."

  (defmacro vl-when-html (&rest args)
    `(if (vl-ps->htmlp)
         (vl-ps-seq ,@args)
       ps)))



(defsection vl-ps-span
  :parents (basic-printing)
  :short "Like @(see vl-ps-seq), except that in HTML mode the contents are also
wrapped in a @('<span>') tag of the given class."

  (defmacro vl-ps-span (class &rest args)
    (declare (xargs :guard (stringp class)))
    `(if (vl-ps->htmlp)
         (vl-ps-seq (vl-print-markup "<span class=\"")
                    (vl-print-markup ,class)
                    (vl-print-markup "\">")
                    ,@args
                    (vl-print-markup "</span>"))
       (vl-ps-seq ,@args))))




(defsection accessing-printed-output
  :parents (printer)
  :short "How to access the characters that have been printed."

  :long "<p>Once you are done printing, you typically want to access the
characters that have been printed, e.g., as a character list or string.  You
might directly access the @('rchars') field of @(see ps), using, e.g., @(call
vl-ps->rchars), but it is a weird @(see vl-printedlist-p) structure, is in
reverse order, and is generally not very convenient to work with.  So, it is
typically more convenient to use these alternatives.</p>")

(define vl-rchars-to-chars ((x vl-printedlist-p)
                            acc)
  :returns (chars character-listp
                  :hyp (and (vl-printedlist-p x)
                            (character-listp acc)))
  :parents (vl-ps->chars)
  :short "Convert a printed list (in reverse order) into characters (in proper
  order)."
  :long "<p>BOZO this is misnamed for historic reasons.</p>"

  (cond ((atom x)
         acc)
        ((characterp (car x))
         ;; Prefer to test characterp instead of stringp, since characters
         ;; are immediates in CCL.
         (vl-rchars-to-chars (cdr x) (cons (car x) acc)))
        (t
         ;; Subtle: the rchars are in reverse order, but the strings within
         ;; it are in proper order, so we need to use append-chars instead of
         ;; revappend-chars here.
         (vl-rchars-to-chars (cdr x) (str::append-chars (car x) acc)))))

(define vl-ps->chars (&key (ps 'ps))
  :returns (chars character-listp)
  :parents (accessing-printed-output)
  :short "@('(vl-ps->chars)') returns what was printed as a character list in
the proper, non-reversed, printed order."
  :long "<p>This is expensive.  It necessarily involves creating @('n') conses,
where @('n') is the number of characters printed.  If you really want a string,
@(see vl-ps->string) will be faster.</p>"
  (vl-rchars-to-chars (vl-ps->rchars) nil))

(define vl-ps->string (&key (ps 'ps))
  :returns (str stringp :rule-classes :type-prescription)
  :parents (accessing-printed-output)
  :short "@('(vl-ps->string)') returns the printed characters as a string in
the proper, non-reversed, printed order."
  :long "<p>This is logically just @('(coerce (vl-ps->chars) 'string)'), but we
install a more efficient definition under the hood in raw Lisp.</p>"
  (coerce (vl-ps->chars) 'string)
  ///
  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)

   (defund vl-ps->string-fn (ps)

     ;; Optimized PS->STRING routine.  We're going to build the return string in
     ;; two passes.  In the first pass we'll determine how big of an array we
     ;; need.  In the second, we'll fill in its characters with the reverse of
     ;; the elems.

     (let* ((elems (vl-ps->rchars))
            (size  (vl-printedlist-length elems 0)))
       (unless (typep size 'fixnum)
         (er hard? 'vl-ps->string-fn
             "Printed list will will be longer than a fixnum (~x0).  You don't ~
            actually want to turn it into a string, I think." size))

       ;; Since the elems are in reverse order, we'll work backwards from the end
       ;; of the array.
       (let* ((ret (make-array size :element-type 'character))
              (i   (the fixnum (- (the fixnum size) 1))))
         (declare (type fixnum i))
         (loop while (consp elems)
               do
               (let ((elem (car elems)))
                 (if (characterp elem)
                     (progn (setf (schar ret i) elem)
                            (decf i))

                   ;; For strings, things are trickier because the characters of
                   ;; the string *are* in the right order.  It's very helpful to
                   ;; think of a concrete example.  Suppose we do:
                   ;;
                   ;;   print #\A
                   ;;   print #\B
                   ;;   print #\C
                   ;;   print "abc"
                   ;;   print #\D
                   ;;   print #\E
                   ;;
                   ;; Then the rchars we'll have are (#\E #\D "abc" #\C #\B #\A).
                   ;; The ret array is 8 entries long and we've already set
                   ;;   ret[7] = #\E
                   ;;   ret[6] = #\D
                   ;; So we now want to set
                   ;;   ret[5] = #\c
                   ;;   ret[4] = #\b
                   ;;   ret[3] = #\a
                   ;;
                   ;; I think it's easiest to just go down from the end of the
                   ;; string so we can (decf i) like before.
                   (loop for j fixnum from (- (length (the string elem)) 1) downto 0 do
                         (setf (schar ret i) (schar elem j))
                         (decf i))))
               (setq elems (cdr elems)))
         ret))))
  (defttag nil))


(define vl-print-to-file ((filename stringp) &key (ps 'ps) (state 'state))
  :returns (state state-p1 :hyp (force (state-p1 state)))
  :parents (accessing-printed-output)
  :short "Write the printed characters to a file."
  :long "<p>@('(vl-print-to-file filename)') writes the printed characters to
the indicated file.</p>"
  (b* ((filename (string-fix filename))
       ((mv channel state)
        (open-output-channel filename :character state))
       ((unless channel)
        (raise "Error opening file ~s0 for writing." filename)
        state)
       (state (princ$ (vl-ps->string) channel state)))
    (close-output-channel channel state)))


(defsection with-ps-file
  :parents (accessing-printed-output)
  :short "Convenient wrapper for @(see vl-print-to-file)."
  :long "<p>The basic idea of this is that you can do, e.g.,</p>

@({
 (with-ps-file \"my-file.txt\"
    (vl-print \"Hello,\")
    (vl-println \"World!\"))
})

<p>And end up with a file called @('my-file.txt') that says @('Hello, World!').
The general form is:</p>

@(ccall with-ps-file)

<p>Basically we just wrap the @('forms') in a @(see vl-ps-seq) and then add a
call of @(see vl-print-to-file) at the end.  This is done in a @(see
with-local-stobj), so previously printed content isn't included.</p>

<p>This implicitly takes, modifies, and returns @(see state).</p>"

  (defmacro with-ps-file (filename &rest forms)
    `(acl2::with-local-stobj
      ps
      (mv-let (ps state)
        (let* ((ps     (vl-ps-seq ,@forms))
               (state  (vl-print-to-file ,filename)))
          (mv ps state))
        state))))



(defsection printing-locally
  :parents (printer)
  :short "How to use @(see ps) to build strings in a local context."

  :long "<p>A disadvantage of using a stobj to represent the printer's state is
that it is generally non-instantiable, which makes localized string building
more difficult because printing from one function may interfere with printing
from another.</p>

<p>We provide two mechanisms for coping with this.</p>

<p>The recommended approach is to use @(see with-local-ps), which in turn uses
@('with-local-stobj') to give you a temporary @('ps') to work with.</p>

<p>An alternative, which we do not often use, is to explicitly manage saving
and restoring of the printer's state.  To support this, we provide some
routines for saving and restoring configurations, and for resetting the
printer's fields.</p>")

(defsection with-local-ps
  :parents (printing-locally)
  :short "Print using a local instance of @(see ps)."

  :long "<p>The convenient (but trivial) macro @('with-local-ps') allows you to
print using a local copy of @(see ps), and returns the result of printing as a
string.</p>

<p>Note: @('with-local-stobj') cannot be used at the top level loop; see @(see
top-level) for a workaround.</p>"

  (defmacro with-local-ps (&rest forms)
    `(acl2::with-local-stobj ps
                             (mv-let (result ps)
                                     (let* ((ps     (vl-ps-seq ,@forms))
                                            (result (vl-ps->string)))
                                       (mv result ps))
                                     result)))

  (local (defun test-ps-writing ()
           (flet ((test (rchars result)
                        (or (equal (with-local-ps (vl-ps-update-rchars rchars)) result)
                            (er hard? 'test-ps-writing
                                "PS test failed for rchars = ~x0." rchars))))
             (and
              (test nil "")
              (test '(#\a) "a")
              (test '(#\a #\b) "ba")
              (test '("foo") "foo")
              (test '("foo" #\a #\b) "bafoo")
              (test '("foo" "bar") "barfoo")
              (test '(#\a "foo" #\b "bar" #\c) "cbarbfooa")
              (test 5 "")
              (test '(#\a . 5) "a")))))

  (local (assert! (test-ps-writing))))


(defsection vl-cw-ps-seq
  :parents (basic-printing)
  :short "Print to standard-out using @(see ps)"

  :long "<p>@('(vl-cw-ps-seq ...)') expands to @('(cw-unformatted (@(see
with-local-ps) ...))').  Due to the use of @(see with-local-ps), this macro can
only be used within functions, and cannot be called from the top level.</p>"

  (defmacro vl-cw-ps-seq (&rest args)
    `(cw-unformatted (with-local-ps ,@args))))



(define vl-ps-full-reset (&key (ps 'ps))
  :parents (printing-locally)
  :short "Erase all contents and reset @(see ps) to its default configuration."
  :long "<p>@('(vl-ps-full-reset)') restores @(see ps) to its initial state.
This erases any text that has been printed, sets the column number to 0, and
also sets all of the config variables to their defaults (text mode, 80 column
autowrap with 5 space autoindent, and a tab size of 8.)  See also @(see
vl-ps-text-reset) for an alternative that does not alter the
configuration.</p>"
  (vl-ps-seq
   (vl-ps-update-rchars nil)
   (vl-ps-update-col 0)
   (vl-ps-update-autowrap-col 80)
   (vl-ps-update-autowrap-ind 5)
   (vl-ps-update-htmlp nil)
   (vl-ps-update-tabsize 8)
   (vl-ps-update-package 'VL::a-symbol-that-is-not-imported)
   (vl-ps-update-base 10)))


(define vl-ps-text-reset (&key (ps 'ps))
  :parents (printing-locally)
  :short "Erase the contents of @(see ps) without altering its configuration."
  :long "<p>@('(vl-ps-text-reset)') erases any text in @(see ps) and sets the
column number to 0.  It does not alter any of the configuration variables.  See
also @(see vl-ps-full-reset) for a way to completely restore @(see ps) to its
default state.</p>"
  (vl-ps-seq
   (vl-ps-update-rchars nil)
   (vl-ps-update-col 0)))


(defaggregate vl-psconfig
  :parents (printing-locally)
  :short "Configuration object for saving and loading printer state."
  :long "See @(see vl-ps-load-config) and @(see vl-ps-save-config)."
  ((autowrap-col natp     :rule-classes :type-prescription)
   (autowrap-ind natp     :rule-classes :type-prescription)
   (htmlp        booleanp :rule-classes :type-prescription)
   (tabsize      posp     :rule-classes :type-prescription)
   (package      symbolp  :rule-classes :type-prescription)
   (base         print-base-p))
  :tag :vl-psconfig)


(define vl-ps-load-config ((config vl-psconfig-p) &key (ps 'ps))
  :parents (printing-locally)
  :short "Load configuration settings from a @(see vl-psconfig-p) object into
@(see ps)."
  :long "<p>Note that this does not change the currently-printed text or update
the column number; it only changes the configuration settings.</p>"
  (b* (((vl-psconfig config) config))
    (vl-ps-seq (vl-ps-update-autowrap-col config.autowrap-col)
               (vl-ps-update-autowrap-ind config.autowrap-ind)
               (vl-ps-update-htmlp config.htmlp)
               (vl-ps-update-tabsize config.tabsize)
               (vl-ps-update-package config.package)
               (vl-ps-update-base config.base))))


(define vl-ps-save-config (&key (ps 'ps))
  :returns (config vl-psconfig-p)
  :parents (printing-locally)
  :short "Save the current configuration of @(see ps) into a @(see
vl-psconfig-p) object."
  :long "<p>Note that this does not save the currently-printed text and column
number; only the configuration settings are saved.</p>"
  (make-vl-psconfig :autowrap-col (vl-ps->autowrap-col)
                    :autowrap-ind (vl-ps->autowrap-ind)
                    :htmlp        (if (vl-ps->htmlp) t nil)
                    :tabsize      (vl-ps->tabsize)
                    :package      (vl-ps->package)
                    :base         (vl-ps->base)))




(defsection basic-printing
  :parents (printer)
  :short "Primitive routines for printing objects."
  :long "<p>Our printer is intended to support both text and html output.
Printing HTML is subtle because one may wish to write:</p>

<ul>

<li><b>HTML markup</b> (e.g., &lt;b&gt;, &lt;code&gt;, ...), wherein the
special characters like &lt; are not to be changed, are going to be invisible
to the user, and should not affect the column number,</li>

<li><b>Parts of URLs</b> (e.g., filenames), which must be \"percent encoded\"
per RFC 3986, e.g., spaces become %20.  These, too, do not affect the column
number because they take part only in tags such as &lt;a href=\"...\"&gt;,
and</li>

<li><b>Encoded HTML text</b>, where special characters like &amp; and &lt;
become &amp;amp; and &amp;lt;, and where tabs become a litany of &amp;nbsp;
characters, and where the column should be advanced as the text is
printed.</li>

</ul>")

(define vl-col-after-printing-chars
  ((col   natp            "Current column we're at.")
   (chars character-listp "Characters we're about to print, not yet reversed."))
  :returns (new-col natp
                    "Column we'll be at after printing @('chars')."
                    :rule-classes :type-prescription)
  :parents (basic-printing)
  :short "Figure out where we'll be after printing some characters."
  (declare (type (integer 0 *) col))
  (cond ((atom chars)
         (lnfix col))
        ((eql (car chars) #\Newline)
         (vl-col-after-printing-chars 0 (cdr chars)))
        (t
         (vl-col-after-printing-chars (+ 1 col) (cdr chars)))))

(define vl-col-after-printing-string-aux
  ((col natp    "Current column we're at.")
   (x   stringp "String we're about to print, not yet reversed.")
   (n   natp    "Current position in X.")
   (xl  natp    "Pre-computed length of X."))
  :returns (new-col natp :rule-classes :type-prescription)
  :parents (vl-col-after-printing-string)
  :guard (and (<= n xl)
              (= xl (length x)))
  :measure (nfix (- (nfix xl) (nfix n)))
  (declare (type (integer 0 *) col n xl)
           (type string x))
  (cond ((mbe :logic (zp (- (nfix xl) (nfix n)))
              :exec (= n xl))
         (lnfix col))
        ((eql (char x n) #\Newline)
         (vl-col-after-printing-string-aux 0 x (+ 1 (lnfix n)) xl))
        (t
         (vl-col-after-printing-string-aux (+ 1 col) x (+ 1 (lnfix n)) xl)))
  ///
  (defthm vl-col-after-printing-string-aux-correct
    (implies (and (natp col)
                  (stringp x)
                  (natp n)
                  (natp xl)
                  (<= n xl)
                  (= xl (length x)))
             (equal (vl-col-after-printing-string-aux col x n xl)
                    (vl-col-after-printing-chars col (nthcdr n (coerce x 'list)))))
    :hints(("Goal"
            :induct (vl-col-after-printing-string-aux col x n xl)
            :in-theory (enable vl-col-after-printing-string-aux
                               vl-col-after-printing-chars)))))

(define vl-col-after-printing-string
  ((col    natp    "Current column we're at.")
   (string stringp "String we're about to print, not yet reversed."))
  :parents (basic-printing)
  :returns (new-col natp :rule-classes :type-prescription)
  :short "Figure out where we'll be after printing a string."
  :inline t
  (declare (type integer col)
           (type string string))
  (mbe :logic (vl-col-after-printing-chars col (coerce string 'list))
       :exec (vl-col-after-printing-string-aux col string 0 (length string))))

(define vl-indent ((n natp) &key (ps 'ps))
  :parents (basic-printing)
  :short "@(call vl-indent) indents to column @('n')."
  :long "<p>In text mode we indent by printing spaces; in HTML mode we instead
print @('&nbsp;') characters.  Note that this function has no effect if we are
already past column @('n').</p>"
  (declare (type (integer 0 *) n))
  (let ((rchars (vl-ps->rchars))
        (col    (vl-ps->col))
        (htmlp  (vl-ps->htmlp)))
    (declare (type (integer 0 *) col))
    (cond ((>= col n)
           ps)
          (htmlp
           (vl-ps-seq
            (vl-ps-update-rchars (make-list-ac (- n col) "&nbsp;" rchars))
            (vl-ps-update-col n)))
          (t
           (vl-ps-seq
            (vl-ps-update-rchars (make-list-ac (- n col) #\Space rchars))
            (vl-ps-update-col n))))))


(define vl-printable-p (x)
  :parents (basic-printing)
  :short "@(call vl-printable-p) recognizes strings, character lists, numbers,
and ordinary characters."
  :long "<p>We use this function as the guard for functions such as @(see
vl-print), @(see vl-println), etc.  We do not allow @('x') to be a symbol
because of the potential confusion between the symbol @('nil') and character
lists.</p>"
  (or (stringp x)
      (character-listp x)
      (acl2-numberp x)
      (characterp x))
  ///
  (defthm vl-printable-p-when-stringp
    (implies (stringp x)
             (vl-printable-p x)))

  (defthm vl-printable-p-when-character-listp
    (implies (character-listp x)
             (vl-printable-p x)))

  (defthm vl-printable-p-when-acl2-numberp
    (implies (acl2-numberp x)
             (vl-printable-p x)))

  (defthm vl-printable-p-when-characterp
    (implies (characterp x)
             (vl-printable-p x))))

(local (in-theory (enable vl-printable-p)))

(define vl-string-needs-html-encoding-p ((x stringp)
                                         (n natp)
                                         (xl natp))
  :parents (basic-printing)
  :guard (and (<= n xl)
              (= xl (length x)))
  :measure (nfix (- (nfix xl) (nfix n)))
  (declare (type string x)
           (type (integer 0 *) n xl))
  (if (mbe :logic (zp (- (nfix xl) (nfix n)))
           :exec (eql xl n))
      nil
    (let ((char (char x n)))
      (declare (type character char))
      (or (eql char #\Space)
          (eql char #\Newline)
          (eql char #\<)
          (eql char #\>)
          (eql char #\&)
          (eql char #\")
          (eql char #\Tab)
          (vl-string-needs-html-encoding-p x (+ 1 (lnfix n)) xl)))))

(define vl-print-str-main ((x stringp) &key (ps 'ps))
  :parents (vl-print)
  (declare (type string x))
  (let ((rchars  (vl-ps->rchars))
        (col     (vl-ps->col)))
    (if (vl-ps->htmlp)
        ;; Need to do HTML encoding.
        (mv-let (col rchars)
          (vl-html-encode-string-aux x 0 (length x) col (vl-ps->tabsize) rchars)
          (vl-ps-seq (vl-ps-update-rchars rchars)
                     (vl-ps-update-col col)))
      ;; Else, nothing to encode
      (vl-ps-seq (vl-ps-update-rchars (cons x rchars))
                 (vl-ps-update-col (vl-col-after-printing-string col x))))))

(define vl-print-charlist-main ((x character-listp) &key (ps 'ps))
  :parents (vl-print)
  (let ((rchars  (vl-ps->rchars))
        (col     (vl-ps->col)))
    (if (vl-ps->htmlp)
        (mv-let (col rchars)
          (vl-html-encode-chars-aux x col (vl-ps->tabsize) rchars)
          (vl-ps-seq (vl-ps-update-rchars rchars)
                     (vl-ps-update-col col)))
      (vl-ps-seq (vl-ps-update-rchars (revappend x rchars))
                 (vl-ps-update-col (vl-col-after-printing-chars col x))))))


(define vl-print-natchars-aux ((n natp)
                               (acc)
                               (col natp))
  (declare (type (integer 0 *) n col))
  :parents (vl-print-nat)
  :short "Optimized base-10 natural number printing into @(see ps)."
  :verify-guards nil
  :returns (mv (acc)
               (new-col natp :rule-classes :type-prescription))

  :prepwork
  ((local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
   (local (in-theory (enable acl2-count)))

   (local (defthm crock
            (implies (posp n)
                     (< (acl2-count (floor n 10))
                        (acl2-count n)))
            :rule-classes ((:rewrite) (:linear)))))


  (if (mbe :logic (zp n)
           :exec (eql (the integer n) 0))
      (mv acc (lnfix col))
    (mv-let (acc col)
      (vl-print-natchars-aux (the integer (truncate (the integer n) 10)) acc col)
      (mv (cons (the character (code-char
                                (the (unsigned-byte 8)
                                  (+ (the (unsigned-byte 8) 48)
                                     (the (unsigned-byte 8)
                                       (rem (the integer n) 10))))))
                acc)
          (the (integer 0 *) (+ 1 col)))))
  ///
  (defthm acc-of-vl-print-natchars-aux
    (equal (mv-nth 0 (vl-print-natchars-aux n acc col))
           (str::revappend-natchars-aux n acc))
    :hints(("Goal" :in-theory (e/d (str::revappend-natchars-aux)
                                   (str::revappend-natchars-aux-redef)))))
  (verify-guards vl-print-natchars-aux))

(define vl-print-nat-main ((n natp) &key (ps 'ps))
  :parents (vl-print-nat)
  (declare (type (integer 0 *) n))
  (if (zp n)
      (vl-ps-seq (vl-ps-update-rchars (cons #\0 (vl-ps->rchars)))
                 (vl-ps-update-col (+ 1 (vl-ps->col))))
    (mv-let (rchars col)
      (vl-print-natchars-aux n (vl-ps->rchars) (vl-ps->col))
      (vl-ps-seq
       (vl-ps-update-rchars rchars)
       (vl-ps-update-col col)))))


(defsection vl-print-nat
  :parents (basic-printing)
  :short "@(call vl-print-nat) is an optimized version of @(see vl-print) for
natural numbers."

  :long "<p>We make a few optimizations.</p>

<ul>

<li>We identify numeric literals (like 5) at compile time and turn them into
strings, so they can be printed at runtime without any coercion.</li>

<li>Numbers don't have to be encoded, so there's no need to consider whether
we're in HTML mode.</li>

<li>We essentially use str::revappend-natchars instead of calling natstr or
similar.  This does the minimum amount of consing and doesn't build a
string.</li>

<li>We manually inline the executable definition of str::revappend-natchars to
avoid doing the loop.</li>

</ul>"

  (defmacro vl-print-nat (x)
    (cond ((natp x)
           (let ((str (natstr x)))
             `(vl-print-raw-fast ,str ,(length str))))
          (t
           `(vl-print-nat-main ,x)))))


(define vl-print-non-string ((x (and (vl-printable-p x)
                                     (not (stringp x))))
                             &key (ps 'ps))
  :parents (vl-print)
  :short "Wrapper that makes it more reasonable to inline vl-print-main."
  (cond ((consp x)
         ;; Hence a character list.
         (vl-print-charlist-main x))
        ((characterp x)
         ;; Fast to check.
         (vl-print-charlist-main (list x)))
        ((natp x)
         (vl-print-nat-main x))
        (t
         ;; Else some other kind of number
         (vl-print-charlist-main
          (explode-atom x 10)))))

(define vl-print-main ((x vl-printable-p) &key (ps 'ps))
  :parents (vl-print)
  :inline t
  (if (stringp x)
      (vl-print-str-main x)
    (vl-print-non-string x)))

(define vl-print-raw-fast ((x stringp) (len natp) &key (ps 'ps))
  :parents (vl-print)
  :short "Fancy hack for printing string literals."
  :long "<p>See for instance @(see vl-print-str) for details.</p>"
  (declare (type (integer 0 *) len)
           (type string x))
  (vl-ps-seq (vl-ps-update-rchars (cons x (vl-ps->rchars)))
             (vl-ps-update-col (+ len (vl-ps->col)))))

(defsection vl-print-str
  :parents (vl-print)
  :short "@('(vl-print-str x)') is an optimized version of @(see vl-print) for
strings."
  :long "@(def vl-print-str)"

  (defmacro vl-print-str (x &key (ps 'ps))
    ;; Note that this is a macro, so these are static, compile-time checks
    ;; about what X is.  If we see a string literal that is simple enough, we
    ;; know that we don't have to do any encoding, etc.
    (cond ((equal x "")
           ps)
          ((and (stringp x)
                (not (vl-string-needs-html-encoding-p x 0 (length x))))
           `(vl-print-raw-fast ,x ,(length x) :ps ,ps))
          (t
           `(vl-print-str-main ,x :ps ,ps)))))


(defsection vl-print
  :parents (basic-printing)
  :short "@(call vl-print) prints text with automatic encoding."
  :long "<p>@('x') may be any @(see vl-printable-p) object, and we print it to
@(see ps).  In text mode, the characters for the printed representation of
@('x') are printed verbatim.  In HTML mode, we automatically encode characters
like @('&') into @('&amp;').  See also @(see vl-print-markup) and @(see
vl-print-url) for alternatives that perform different kinds of encoding.</p>

<p>Note: this function ignores @(see ps)'s print-base and always prints in base
10!</p>

@(def vl-print)"

  (defmacro vl-print (x)
    (cond ((equal x "")
           'ps)
          ((stringp x)
           (if (vl-string-needs-html-encoding-p x 0 (length x))
               `(vl-print-str ,x)
             `(vl-print-raw-fast ,x ,(length x))))
          ((natp x)
           `(vl-print-nat ,x))
          (t
           `(vl-print-main ,x)))))


;; (define vl-remove-leading-spaces (x)
;;   :parents (basic-printing)
;;   :short "@(call vl-remove-leading-spaces) removes any @('#\Space') characters
;; from the front of the list @('x')."
;;   ;; BOZO this doesn't exactly work for printedlists though?  It only
;;   ;; removes spaces that are literally characters, doesn't deal with
;;   ;; strings...
;;   (cond ((atom x)
;;          x)
;;         ((eql (car x) #\Space)
;;          (vl-remove-leading-spaces (cdr x)))
;;         (t
;;          x))
;;   ///
;;   (defthm vl-printedlist-p-of-vl-remove-leading-spaces
;;     (implies (force (vl-printedlist-p x))
;;              (vl-printedlist-p (vl-remove-leading-spaces x)))))


(define vl-println-main ((x vl-printable-p) &key (ps 'ps))
  :parents (vl-println)
  (let* ((rchars (vl-ps->rchars))
         (col    (vl-ps->col))
         (htmlp  (vl-ps->htmlp))
         ;; Coerce X into either a string or character list.
         (x      (cond ((stringp x) x)
                       ((atom x)    (explode-atom x 10))
                       (t           x))))
    (declare (type (integer 0 *) col))
    (if htmlp
        ;; Need to do HTML encoding.
        (b* ((tabsize       (vl-ps->tabsize))
             ((mv & rchars) (if (stringp x)
                                (vl-html-encode-string-aux x 0 (length x) col tabsize rchars)
                              (vl-html-encode-chars-aux x col tabsize rchars))))
          (vl-ps-seq (vl-ps-update-rchars (revappend *vl-html-newline* rchars))
                     (vl-ps-update-col 0)))
      ;; Plain-text, no encoding necessary.
      ;; We used to remove any trailing whitespace before printing the newline,
      ;; but now for simplicity and performance we don't bother.
      (if (stringp x)
          (vl-ps-seq (vl-ps-update-rchars
                      (cons #\Newline
                            ;; the following used to be:
                            ;; (vl-remove-leading-spaces
                            ;;   (str::revappend-chars x rchars)
                            (cons x rchars)))
                     (vl-ps-update-col 0))
        (vl-ps-seq (vl-ps-update-rchars
                    (cons #\Newline
                          ;; the following used to be:
                          ;; (vl-remove-leading-spaces
                          ;;   (revappend x rchars))
                          (revappend x rchars)))
                   (vl-ps-update-col 0))))))

(define vl-println-raw-fast1 (&key (ps 'ps))
  :parents (vl-println)
  :short "Optimized version for the special case when the string to print is
empty."
  :inline t
  (vl-ps-seq
   (vl-ps-update-rchars (cons (if (vl-ps->htmlp) "<br/>
" #\Newline) (vl-ps->rchars)))
   (vl-ps-update-col 0)))

(define vl-println-raw-fast2 ((str stringp) &key (ps 'ps))
  :parents (vl-println)
  :short "Optimized version for string literals that need no encoding."
  :inline t
  (vl-ps-seq
   (vl-ps-update-rchars (cons (if (vl-ps->htmlp) "<br/>
" #\Newline) (cons str (vl-ps->rchars))))
   (vl-ps-update-col 0)))

(defsection vl-println
  :parents (basic-printing)
  :short "@(call vl-println) prints text with automatic encoding, and always
adds a newline."
  :long "<p>This function is like @(see vl-print), except that a newline is
printed after @('x').  When we are in HTML mode, a @('<br/>') tag and a newline
are printed.</p>"

  (defmacro vl-println (x)
    (cond ((equal x "")
           `(vl-println-raw-fast1))
          ((and (stringp x)
                (not (vl-string-needs-html-encoding-p x 0 (length x))))
           `(vl-println-raw-fast2 ,x))
          (t
           `(vl-println-main ,x)))))

(define vl-println? ((x vl-printable-p) &key (ps 'ps))
  :parents (basic-printing)
  :short "@(call vl-println?) prints text with automatic encoding, and may also
inserts a newline if we have gone past the @('autowrap-col')."

  :long "<p>This function is like @(see vl-print), except that after @('x') is
printed, we check to see whether the current @('col') exceeds the
@('autowrap-col') for @(see ps).  If so, we insert a newline (and, in HTML
mode, a @('<br/>') tag) as in @(see vl-println), and indent the next line to
the column specified by the @(see ps)'s @('autowrap-ind').</p>

<p>When writing pretty-printers, it is useful to call this function in places
that would be acceptable line-break points, so that very long lines will be
split up at reasonably good places.</p>"

  (let* ((rchars       (vl-ps->rchars))
         (col          (vl-ps->col))
         (htmlp        (vl-ps->htmlp))
         (autowrap-col (vl-ps->autowrap-col))
         ;; Coerce X into either a string or character list
         (x            (cond ((stringp x) x)
                             ((atom x)    (explode-atom x 10))
                             (t           x))))
    (if htmlp
        ;; Need to do HTML encoding.
        (b* ((tabsize         (vl-ps->tabsize))
             ((mv col rchars) (if (stringp x)
                                  (vl-html-encode-string-aux x 0 (length x) col tabsize rchars)
                                (vl-html-encode-chars-aux x col tabsize rchars)))
             ((when (< col autowrap-col))
              ;; No autowrapping.
              (vl-ps-seq (vl-ps-update-rchars rchars)
                         (vl-ps-update-col col)))
             ;; Otherwise, autowrap.
             (indent (vl-ps->autowrap-ind))
             (rchars (revappend *vl-html-newline* rchars))
             (rchars (repeated-revappend indent *vl-html-&nbsp* rchars)))
          (vl-ps-seq (vl-ps-update-rchars rchars)
                     (vl-ps-update-col indent)))

      ;; Otherwise, plain text, nothing to encode.
      (b* ((col      (if (stringp x)
                         (vl-col-after-printing-string col x)
                       (vl-col-after-printing-chars col x)))
           (rchars   (if (stringp x)
                         (cons x rchars)
                       (revappend x rchars)))
           ((when (< col autowrap-col))
            ;; No autowrapping necessary
            (vl-ps-seq (vl-ps-update-rchars rchars)
                       (vl-ps-update-col col)))
           ;; Otherwise autowrap
           (indent (vl-ps->autowrap-ind))
           ;; We previously removed leading whitespace from rchars
           (rchars (cons #\Newline rchars))
           (rchars (make-list-ac indent #\Space rchars)))
        (vl-ps-seq (vl-ps-update-rchars rchars)
                   (vl-ps-update-col indent))))))




(define vl-print-markup-main ((x vl-printable-p) &key (ps 'ps))
  :parents (vl-print-markup)
  :short "General case."
  (let ((rchars  (vl-ps->rchars)))
    (cond ((stringp x)
           (vl-ps-update-rchars (cons x rchars)))
          ((atom x)
           (vl-ps-update-rchars (revappend (explode-atom x 10) rchars)))
          (t
           (vl-ps-update-rchars (revappend x rchars))))))

(define vl-print-markup-raw-fast ((x stringp) &key (ps 'ps))
  :parents (vl-print-markup)
  :short "Optimized, inline version for string literals."
  :inline t
  (vl-ps-update-rchars (cons x (vl-ps->rchars))))


(defsection vl-print-markup
  :parents (basic-printing)
  :short "@(call vl-print-markup) prints verbatim text with no encoding."

  :long "<p>@('x') is any object that satisfies @(see vl-printable-p).  We
print the characters for @('x') directly to @(see ps) without any automatic
encoding, no matter what mode we are in.  This function is generally intended
for the printing of HTML tags.</p>"

  (defmacro vl-print-markup (x)
    (if (stringp x)
        `(vl-print-markup-raw-fast ,x)
      `(vl-print-markup-main ,x))))


(define vl-println-markup ((x vl-printable-p) &key (ps 'ps))
  :parents (basic-printing)
  :short "@(call vl-println-markup) prints verbatim text with no encoding, then
prints a newline."

  :long "<p>This is identical to @(see vl-print-markup) except for the newline.
Unlike @(see vl-println), no @('<br/>') tag is printed in HTML mode.  The goal
is only to provide a convenient way to insert line breaks in the middle of a
lot of markup.</p>"

  (let ((rchars  (vl-ps->rchars)))
    (cond ((stringp x)
           (vl-ps-seq
            (vl-ps-update-rchars (cons #\Newline (cons x rchars)))
            (vl-ps-update-col 0)))
          ((atom x)
           (vl-ps-seq
            (vl-ps-update-rchars (cons #\Newline (revappend (explode-atom x 10) rchars)))
            (vl-ps-update-col 0)))
          (t
           (vl-ps-seq
            (vl-ps-update-rchars (cons #\Newline (revappend x rchars)))
            (vl-ps-update-col 0))))))


(define vl-print-url ((x vl-printable-p) &key (ps 'ps))
  :parents (basic-printing)
  :short "@(call vl-print-url) prints text with automatic URL encoding."
  :long "<p>This function simply prints the URL-encoding of @('x') to @(see
ps), regardless of the output mode.  It is useful for printing parts of URLs
with the proper encoding.</p>"
  (let ((rchars (vl-ps->rchars)))
    (cond ((stringp x)
           (vl-ps-update-rchars (vl-url-encode-string-aux x 0 (length x) rchars)))
          ((atom x)
           (vl-ps-update-rchars (vl-url-encode-chars-aux (explode-atom x 10) rchars)))
          (t
           (vl-ps-update-rchars (vl-url-encode-chars-aux x rchars))))))

(define vl-print-strings-with-commas-aux ((x string-listp) &key (ps 'ps))
  :parents (vl-print-strings-with-commas)
  (cond ((atom x)
         ps)
        ((atom (cdr x))
         (vl-print (car x)))
        (t
         (vl-ps-seq (vl-print (car x))
                    (vl-println? ", ")
                    (vl-print-strings-with-commas-aux (cdr x))))))

(define vl-print-strings-with-commas ((x string-listp)
                                      (indent natp)
                                      &key (ps 'ps))
  :parents (basic-printing)
  :short "@(call vl-print-strings-with-commas) prints the elements of @('x'), a
string list, separated by commas."
  :long "<p>The output is automatically encoded and word wrapped, and each line
is indented to column @('indent').</p>"
  (let ((orig-indent (vl-ps->autowrap-ind)))
    (vl-ps-seq
     (vl-ps-update-autowrap-ind indent)
     (vl-indent indent)
     (vl-print-strings-with-commas-aux x)
     (vl-ps-update-autowrap-ind orig-indent))))

(define vl-print-strings-as-lines ((x string-listp) &key (ps 'ps))
  :parents (basic-printing)
  :short "@(call vl-print-strings-as-lines) prints the elements of @('x'), a
string list, on separate lines."
  :long "<p>The output is automatically encoded, and @('<br/>') tags are added
to separate the lines when we are in the HTML output mode.  Each string is
printed on its own line, with no indenting and no automatic word wrapping.</p>"
  (if (atom x)
      ps
    (vl-ps-seq (vl-println (car x))
               (vl-print-strings-as-lines (cdr x)))))


(defsection formatted-printing
  :parents (printer)
  :short "Higher-level routines for printing objects with a @('fmt')- or
@('cw')-like feel."

  :long "<p>We implement limited versions of @('fmt') and @('cw').  The
following ACL2-style directives are supported and behave similarly as those
described in \"@(':doc fmt').\"</p>

<ul>

<li>@('~~'), prints a tilde</li>
<li>@('~%'), prints a newline</li>
<li>@('~|'), prints a newline if we are not already on column 0</li>
<li>@('~[space]'), prints a space</li>
<li>@('~\[newline]'), skips subsequent whitespace</li>

<li>@('~xi'), pretty-print an object.</li>

<li>@('~si'), prints a string verbatim, or acts like @('~xi') when given any
non-string object.</li>

<li>@('~&i'), print a list, separated by commas, with the word \"and\"
preceeding the final element.</li>

</ul>

<p>Note: our pretty-printer is currently very lousy.  Its output is not nearly
as nice as ACL2's ordinary @('~x') directives.</p>

<p>Note: although other ACL2-style directives are not yet supported, we may
eventually extend the printer to allow them.</p>")

(define vl-ppr-escape-slashes
  ((x          stringp)
   (n          natp)
   (xl         natp)
   (slash-char characterp)
   (col        natp)
   acc)
  :guard (and (<= n xl)
              (= xl (length x)))
  :returns (mv (col-prime natp :rule-classes :type-prescription)
               (acc-prime))
  :parents (vl-stupid-ppr1)
  :short "This is basically like acl2::prin1-with-slashes, but we put the
characters into the accumulator in reverse order instead of printing them."
  :measure (nfix (- (nfix xl) (nfix n)))
  (if (mbe :logic (zp (- (nfix xl) (nfix n)))
           :exec (eql n xl))
      (mv (lnfix col) acc)
    (let ((char (char x n)))
      (vl-ppr-escape-slashes x (+ 1 (lnfix n)) xl
                             slash-char
                             (if (eql char #\Newline)
                                 0
                               (+ 1 col))
                             (if (or (eql char #\\)
                                     (eql char slash-char))
                                 (list* char #\\ acc)
                               (cons char acc)))))
  ///
  (defthm character-listp-of-vl-ppr-escape-slashes
    (implies (and (character-listp acc)
                  (force (stringp x))
                  (force (natp n))
                  (force (natp xl))
                  (force (natp col))
                  (force (<= n xl))
                  (force (= xl (length x))))
             (character-listp
              (mv-nth 1 (vl-ppr-escape-slashes x n xl slash-char col acc)))))

  (defthm vl-printedlist-p-of-vl-ppr-escape-slashes
    (implies (and (vl-printedlist-p acc)
                  (force (stringp x))
                  (force (natp n))
                  (force (natp xl))
                  (force (natp col))
                  (force (<= n xl))
                  (force (= xl (length x))))
             (vl-printedlist-p
              (mv-nth 1 (vl-ppr-escape-slashes x n xl slash-char col acc))))))


(defsection vl-ppr-explode-symbol-aux

  (local (in-theory (disable acl2::may-need-slashes-fn)))

  (defund vl-ppr-explode-symbol-aux (name col acc)
    "Returns (MV COL-PRIME ACC-PRIME)"
    (declare (xargs :guard (and (stringp name)
                                (natp col))))

; Name is the name of a symbol or a package, and acc is the accumulator we
; are writing into in reverse order.  Write the characters of name into acc,
; escaping them and adding bars if necessary.  I.e., |foo|, |Foo\|bar|, etc.

    (if (acl2::may-need-slashes-fn name 10)
        (mv-let (col acc)
                (vl-ppr-escape-slashes name 0 (length name) #\| (+ 1 col) (cons #\| acc))
                (mv (+ 1 col) (cons #\| acc)))
      (mv (+ (lnfix col) (length name))
          (str::revappend-chars name acc))))

  (local (in-theory (enable vl-ppr-explode-symbol-aux)))

  (defthm natp-of-vl-ppr-explode-symbol-aux
    (natp (mv-nth 0 (vl-ppr-explode-symbol-aux name col acc)))
    :rule-classes :type-prescription)

  (defthm character-listp-of-vl-ppr-explode-symbol-aux
    (implies (and (character-listp acc)
                  (force (stringp name))
                  (force (natp col)))
             (character-listp (mv-nth 1 (vl-ppr-explode-symbol-aux name col acc)))))

  (defthm vl-printedlist-p-of-vl-ppr-explode-symbol-aux
    (implies (and (vl-printedlist-p acc)
                  (force (stringp name))
                  (force (natp col)))
             (vl-printedlist-p (mv-nth 1 (vl-ppr-explode-symbol-aux name col acc))))))




(defsection vl-ppr-explode-symbol

  (defund vl-ppr-explode-symbol (x pkg col acc)
    "Returns (MV COL-PRIME ACC-PRIME)"
    (declare (xargs :guard (and (symbolp x)
                                (symbolp pkg)
                                (natp col))))

; X is the symbol we want to explode.  Pkg is a symbol in the current package
; we are printing from.  Acc is a list of characters where we are to write the
; symbol's name in reverse order.

    (let ((xname (symbol-name x))
          (xpkg  (symbol-package-name x)))
      (cond ((or (equal xpkg xname)
                 (equal (intern-in-package-of-symbol xname pkg) x))
             (vl-ppr-explode-symbol-aux xname col acc))
            ((equal xpkg "KEYWORD")
             (vl-ppr-explode-symbol-aux xname (+ 1 col) (cons #\: acc)))
            (t
             (b* (((mv col acc) (vl-ppr-explode-symbol-aux xpkg col acc))
                  (col          (+ 2 col))
                  (acc          (list* #\: #\: acc)))
                 (vl-ppr-explode-symbol-aux xname col acc))))))

  (local (in-theory (enable vl-ppr-explode-symbol)))

  (defthm natp-of-vl-ppr-explode-symbol
    (natp (mv-nth 0 (vl-ppr-explode-symbol name pkg col acc)))
    :rule-classes :type-prescription)

  (defthm character-listp-of-vl-ppr-explode-symbol
    (implies (and (character-listp acc)
                  (force (symbolp x))
                  (force (symbolp pkg))
                  (force (natp col)))
             (character-listp
              (mv-nth 1 (vl-ppr-explode-symbol x pkg col acc)))))

  (defthm vl-printedlist-p-of-vl-ppr-explode-symbol
    (implies (and (vl-printedlist-p acc)
                  (force (symbolp x))
                  (force (symbolp pkg))
                  (force (natp col)))
             (vl-printedlist-p
              (mv-nth 1 (vl-ppr-explode-symbol x pkg col acc))))))



(defsection vl-ppr-explode-string

  (defund vl-ppr-explode-string (x col acc)
    "Returns (MV COL-PRIME ACC-PRIME)"
    (declare (xargs :guard (and (stringp x)
                                (natp col)))
             (type string x))
    (mv-let (col acc)
            (vl-ppr-escape-slashes x 0 (length x) #\" (+ 1 col) (cons #\" acc))
            (mv (+ 1 col) (cons #\" acc))))

  (local (in-theory (enable vl-ppr-explode-string)))

  (defthm natp-of-vl-ppr-explode-string
    (natp (mv-nth 0 (vl-ppr-explode-string x col acc)))
    :rule-classes :type-prescription)

  (defthm character-listp-of-vl-ppr-explode-string
    (implies (and (character-listp acc)
                  (force (stringp x))
                  (force (natp col)))
             (character-listp
              (mv-nth 1 (vl-ppr-explode-string x col acc)))))

  (defthm vl-printedlist-p-of-vl-ppr-explode-string
    (implies (and (vl-printedlist-p acc)
                  (force (stringp x))
                  (force (natp col)))
             (vl-printedlist-p
              (mv-nth 1 (vl-ppr-explode-string x col acc))))))



(defsection vl-ppr-explode-atom

  (defund vl-ppr-explode-atom (x pkg base col acc)
    "Returns (MV COL-PRIME ACC-PRIME)"
    (declare (xargs :guard (and (atom x)
                                (symbolp pkg)
                                (acl2::print-base-p base)
                                (natp col))))
    (cond ((symbolp x)
           (vl-ppr-explode-symbol x pkg col acc))
          ((stringp x)
           (vl-ppr-explode-string x col acc))
          ((acl2-numberp x)
           (let* ((explode (explode-atom x base))
                  (len     (len explode)))
             (mv (+ (lnfix col) len) (revappend explode acc))))
          ((characterp x)
           (case x
             (#\Space   (mv (+ (lnfix col) 7) (str::revappend-chars "#\\Space" acc)))
             (#\Newline (mv (+ (lnfix col) 9) (str::revappend-chars "#\\Newline" acc)))
             (#\Tab     (mv (+ (lnfix col) 5) (str::revappend-chars "#\\Tab" acc)))
             (#\Rubout  (mv (+ (lnfix col) 8) (str::revappend-chars "#\\Rubout" acc)))
             (#\Page    (mv (+ (lnfix col) 6) (str::revappend-chars "#\\Page" acc)))
             (otherwise (mv (+ (lnfix col) 3) (list* x #\\ #\# acc)))))
          (t
           (prog2$ (er hard? 'vl-ppr-explode-atom "Bad atom: ~x0." x)
                   (mv (+ (nfix col) 10) (str::revappend-chars "<bad atom>" acc))))))

  (local (in-theory (enable vl-ppr-explode-atom)))

  (defthm natp-of-vl-ppr-explode-atom
    (natp (mv-nth 0 (vl-ppr-explode-atom x pkg base col acc)))
    :rule-classes :type-prescription)

  (defthm character-listp-of-vl-ppr-explode-atom
    (implies (and (character-listp acc)
                  (force (atom x))
                  (force (symbolp pkg))
                  (force (acl2::print-base-p base))
                  (force (natp col)))
             (character-listp
              (mv-nth 1 (vl-ppr-explode-atom x pkg base col acc)))))

  (defthm vl-printedlist-p-of-vl-ppr-explode-atom
    (implies (and (vl-printedlist-p acc)
                  (force (atom x))
                  (force (symbolp pkg))
                  (force (acl2::print-base-p base))
                  (force (natp col)))
             (vl-printedlist-p
              (mv-nth 1 (vl-ppr-explode-atom x pkg base col acc))))))




(defsection vl-stupid-ppr1

  (defund vl-stupid-ppr1 (x pkg base rmargin in-listp col acc)
    "Returns (MV COL-PRIME ACC-PRIME)"
    (declare (xargs :guard (and (symbolp pkg)
                                (acl2::print-base-p base)
                                (natp rmargin)
                                (natp col))
                    :verify-guards nil))
    (if (atom x)
        (vl-ppr-explode-atom x pkg base col acc)

      (b* (((mv col acc)
            (if in-listp
                (vl-stupid-ppr1 (car x) pkg base rmargin nil col acc)
              (vl-stupid-ppr1 (car x) pkg base rmargin nil (+ 1 col) (cons #\( acc))))

           ((when (not (cdr x)))
            (mv (+ 1 (lnfix col)) (if in-listp acc (cons #\) acc))))

           ;; "Maybe break"
           ((mv col acc) (if (< col rmargin)
                             (mv col acc)
                           (mv 0 (cons #\Newline acc)))))

          (if (consp (cdr x))
              ;; Successive elements of a list, no dots.
              (b* (((mv col acc)
                    (vl-stupid-ppr1 (cdr x) pkg base rmargin t (+ 1 col) (cons #\Space acc))))

                  (mv (+ 1 (lnfix col))
                      (if in-listp acc (cons #\) acc))))

            ;; End element, need a dot.
            (b* ((col (+ 3 col))
                 (acc (list* #\Space #\. #\Space acc))

                 ;; "Maybe break"
                 ((mv col acc) (if (< col rmargin)
                                   (mv col acc)
                                 (mv 0 (cons #\Newline acc))))

                 ((mv col acc)
                  (vl-stupid-ppr1 (cdr x) pkg base rmargin t col acc)))

                (mv (+ 1 (lnfix col))
                    (if in-listp acc (cons #\) acc))))))))

  (local (in-theory (enable vl-stupid-ppr1)))

  (defthm natp-of-vl-stupid-ppr1
    (natp (mv-nth 0 (vl-stupid-ppr1 x pkg base rmargin in-listp col acc)))
    :rule-classes :type-prescription)

  (defthm character-listp-of-vl-stupid-ppr1
    (implies (and (character-listp acc)
                  (force (symbolp pkg))
                  (force (acl2::print-base-p base))
                  (force (natp rmargin))
                  (force (natp col)))
             (character-listp
              (mv-nth 1 (vl-stupid-ppr1 x pkg base rmargin in-listp col acc)))))

  (defthm vl-printedlist-p-of-vl-stupid-ppr1
    (implies (and (vl-printedlist-p acc)
                  (force (symbolp pkg))
                  (force (acl2::print-base-p base))
                  (force (natp rmargin))
                  (force (natp col)))
             (vl-printedlist-p
              (mv-nth 1 (vl-stupid-ppr1 x pkg base rmargin in-listp col acc)))))

  (verify-guards vl-stupid-ppr1))



(defsection vl-skip-ws

; X is the string we are parsing and XL is its length.  N is our current
; position.  We return the index of the first non-whitespace character at or
; after N.

  (defund vl-skip-ws (x n xl)
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (= xl (length x))
                                (<= n xl))
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (= n xl))
        (lnfix n)
      (let ((char (char x n)))
        (if (or (eql char #\Space)
                (eql char #\Newline)
                (eql char #\Tab)
                (eql char #\Page))
            (vl-skip-ws x (+ 1 (lnfix n)) xl)
          (lnfix n)))))

  (local (in-theory (enable vl-skip-ws)))

  (defthm upper-bound-of-vl-skip-ws
    (implies (and (<= (nfix n) xl)
                  (natp xl))
             (<= (vl-skip-ws x n xl) xl))
    :rule-classes ((:rewrite) (:linear)))

  (defthm lower-bound-of-vl-skip-ws
    (implies (natp n)
             (<= n (vl-skip-ws x n xl)))
    :rule-classes ((:rewrite) (:linear))))




(defsection vl-basic-fmt-parse-tilde

  (local (in-theory (enable len)))

  (defund vl-basic-fmt-parse-tilde (x n xl)
    "Returns (MV TYPE VAL N-PRIME)"

; Valid types:
;   :SKIP means do not print anything, just skip until N-PRIME
;   :NORMAL means print VAL as normal text
;   :CBREAK means print a conditional break
;
; For any other directive, we assume the directive has the form
;   ~[char2][char3]
;
; For instance, ~x0 would have char2 = #\x and char3 = #\0.  For these
; directives, we return char2 as TYPE and char3 as VAL.

    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (= xl (length x))
                                (< n xl))))
    (b* ((n  (lnfix n))
         (xl (lnfix xl))
         (char1 (char x n))
         ((when (not (eql char1 #\~)))
          (mv :normal char1 (+ n 1)))

         ;; Every tilde must have an argument.
         ((when (= (+ n 1) xl))
          (prog2$ (er hard? 'vl-basic-fmt-parse-tilde
                      "The format string ~x0 ends with a lone tilde." x)
                  (mv :normal char1 (+ n 1))))

         ;; In a few special cases, there are no other arguments.
         (char2 (char x (+ n 1)))
         ((when (eql char2 #\~))
          (mv :normal #\~ (+ n 2)))
         ((when (eql char2 #\%))
          (mv :normal #\Newline (+ n 2)))
         ((when (eql char2 #\Space))
          (mv :hard-space #\Space (+ n 2)))
         ((when (eql char2 #\|))
          (mv :cbreak #\Newline (+ n 2)))
         ((when (eql char2 #\Newline))
          (mv :skip #\Space (vl-skip-ws x (+ n 2) xl)))

         ;; Otherwise the directive must have an argument.
         ((when (= (+ n 2) xl))
          (prog2$ (er hard? 'vl-basic-fmt-parse-tilde
                      "The format string ~x0 ends with ~x1, but this directive needs argument."
                      x
                      (coerce (list char1 char2) 'string))
                  (mv :normal char1 (+ n 1))))

         (char3 (char x (+ n 2))))
        (mv char2 char3 (+ n 3))))

  (local (in-theory (enable vl-basic-fmt-parse-tilde)))

  (defthm characterp-of-vl-basic-fmt-parse-tilde-val
    (implies (and (force (stringp x))
                  (force (natp n))
                  (force (natp xl))
                  (force (= xl (length x)))
                  (force (< n xl)))
             (characterp (mv-nth 1 (vl-basic-fmt-parse-tilde x n xl)))))

  (defthm natp-of-vl-basic-fmt-parse-tilde-nprime
    (natp (mv-nth 2 (vl-basic-fmt-parse-tilde x n xl)))
    :rule-classes :type-prescription)

  (defthm upper-bound-of-vl-basic-fmt-parse-tilde-nprime
    (implies (and (< (nfix n) (nfix xl)))
             (<= (mv-nth 2 (vl-basic-fmt-parse-tilde x n xl))
                 (nfix xl)))
    :rule-classes ((:rewrite) (:linear)))

  (defthm lower-bound-of-vl-basic-fmt-parse-tilde-nprime
    (< (nfix n) (mv-nth 2 (vl-basic-fmt-parse-tilde x n xl)))
    :rule-classes ((:rewrite) (:linear))))


(local (defthm true-listp-when-character-listp-rewrite-expensive
         (implies (character-listp x)
                  (true-listp x))))

(define vl-fmt-tilde-x (x &key (ps 'ps))
  (b* ((rchars  (vl-ps->rchars))
       (col     (vl-ps->col))
       (pkg     (vl-ps->package))
       (base    (vl-ps->base))
       (htmlp   (vl-ps->htmlp))
       (tabsize (vl-ps->tabsize))
       (rmargin (vl-ps->autowrap-col))
       ((unless htmlp)
        (mv-let (col rchars)
                (vl-stupid-ppr1 x pkg base rmargin nil col rchars)
                (vl-ps-seq
                 (vl-ps-update-col col)
                 (vl-ps-update-rchars rchars))))
       ;; Else, we need to HTML-encode the printing of X.  Rather than
       ;; complicate all the ppr functions with htmlp, we just do the normal
       ;; printing then HTML-encode the resulting character list.  This is kind
       ;; of horrifyingly inefficient.  On the other hand, it's still linear
       ;; and shouldn't be THAT bad...
       (temp         nil)
       ((mv & temp)  (vl-stupid-ppr1 x pkg base rmargin nil col temp))
       (temp         (reverse temp))
       ((mv col rchars) (vl-html-encode-chars-aux temp col tabsize rchars)))
      (vl-ps-seq
       (vl-ps-update-col col)
       (vl-ps-update-rchars rchars))))

(define vl-fmt-tilde-s (x &key (ps 'ps))
  (cond ((stringp x)
         (vl-print x))
        (t
         (vl-fmt-tilde-x x))))

(define vl-fmt-tilde-& (x &key (ps 'ps))
  (if (atom x)
      ps
    (vl-ps-seq
     (vl-fmt-tilde-s (car x))
     (if (atom (cdr x))
         ;; Last one.  We're all done.
         ps
       (vl-ps-seq
        ;; Separate elements with a comma and a space, unless we're down to the
        ;; last two elements in which case we only use a space.
        (vl-print (if (consp (cddr x)) ", " " "))
        ;; Maybe-break.  We'll let the browser's word wrapping deal with things
        ;; if we're in HTML mode, so only break in text mode.
        (if (vl-ps->htmlp) ps (vl-println? ""))
        (if (consp (cddr x))
            ;; No "and" yet.
            (vl-fmt-tilde-& (cdr x))
          (vl-ps-seq
           (vl-print "and ")
           (if (vl-ps->htmlp) ps (vl-println? "")) ;; Another maybe-break.
           (vl-fmt-tilde-& (cdr x)))))))))


(local
 (encapsulate
  ()
  (defun test-vl-fmt-tilde-& (x) (with-local-ps (vl-fmt-tilde-& x)))
  (assert! (equal (test-vl-fmt-tilde-& '(a)) "A"))
  (assert! (equal (test-vl-fmt-tilde-& '(a b)) "A and B"))
  (assert! (equal (test-vl-fmt-tilde-& '(a b c)) "A, B and C"))
  (assert! (equal (test-vl-fmt-tilde-& '(a b c d)) "A, B, C and D"))))




(define vl-fmt-print-space (&key (ps 'ps))
  ;; Prints spaces encountered in the format string itself, maybe word-wrapping
  ;; if necessary.
  (if (vl-ps->htmlp)
      ;; In HTML mode, fmt will just print ordinary spaces instead of trying
      ;; to do automatic word wrapping.
      (vl-print " ")
    (b* ((rchars (vl-ps->rchars))
         (col    (vl-ps->col))
         (autowrap-col (vl-ps->autowrap-col))
         ((when (< col autowrap-col))
          ;; No autowrapping
          (vl-ps-seq (vl-ps-update-rchars (cons #\Space rchars))
                     (vl-ps-update-col (+ 1 col))))
         (indent (vl-ps->autowrap-ind))
         (rchars (cons #\Newline rchars))
         (rchars (make-list-ac indent #\Space rchars)))
        (vl-ps-seq
         (vl-ps-update-rchars rchars)
         (vl-ps-update-col indent)))))

(define vl-fmt-print-normal ((x :type character) &key (ps 'ps))
  (cond ((eql x #\-)
         (vl-println? x))
        ((eql x #\Space)
         (vl-fmt-print-space))
        (t
         (vl-print x))))

(defsection vl-basic-fmt-aux-fn

  (defmacro vl-basic-fmt-aux (x n xl alist)
    `(vl-basic-fmt-aux-fn ,x ,n ,xl ,alist ps))

  (defund vl-basic-fmt-aux-fn (x n xl alist ps)
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (<= n xl)
                                (= xl (length x))
                                (alistp alist))
                    :guard-debug t
                    :stobjs ps
                    :measure (nfix (- (nfix xl) (nfix n)))))
    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (eql xl n))
        ps
      (b* (((mv type val n)
            (vl-basic-fmt-parse-tilde x n xl))
           (ps (case type
                 (:skip   ps)
                 (:normal (vl-fmt-print-normal val))
                 (:hard-space (vl-print #\Space))
                 (:cbreak (if (zp (vl-ps->col))
                              ps
                            (vl-println "")))
                 (otherwise
                  (b* ((lookup (assoc val alist))
                       ((unless lookup)
                        (prog2$ (er hard? 'vl-basic-fmt-aux-fn
                                    "alist does not bind ~x0; fmt-string is ~x1."
                                    val x)
                                ps)))
                      (case type
                        (#\s (vl-fmt-tilde-s (cdr lookup)))
                        (#\& (vl-fmt-tilde-& (cdr lookup)))
                        (#\x (vl-fmt-tilde-x (cdr lookup)))
                        (otherwise
                         (prog2$ (er hard? 'vl-basic-fmt-aux-fn
                                     "Unsupported directive: ~~~x0.~%" type)
                                 ps))))))))
          (vl-basic-fmt-aux x n xl alist)))))



(define vl-basic-fmt ((x stringp) (alist alistp) &key (ps 'ps))
  :parents (formatted-printing)
  :short "Basic @('fmt')-like printing function for @(see ps)."

  :long "<p>@(call vl-basic-fmt) takes as inputs @('x'), a format string as
described in @(see formatted-printing), and an alist that should map characters
to objects, which provides the arguments to the format string, as in ordinary
fmt-style ACL2 printing.</p>"

  (vl-basic-fmt-aux x 0 (length x) alist))



(defsection vl-basic-cw
  :parents (formatted-printing)
  :short "Basic @('cw')-like printing function for @(see ps)."

  :long "<p>This is a simple wrapper for @(see vl-basic-fmt).  See also @(see
vl-basic-cw-obj).</p>"

  (defmacro vl-basic-cw (x &rest args)
    `(vl-basic-fmt ,x (pairlis$
                       '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                       (list ,@args)))))


(define vl-basic-cw-obj ((msg stringp) args &key (ps 'ps))
  :parents (formatted-printing)
  :short "Like @(see vl-basic-cw), but reads its format string from an object."

  :long "<p>Ordinariy, @('vl-basic-cw') requires you to provide its arguments
explicitly in the macro call.  That is, you might write something like
this:</p>

@({
 (vl-basic-cw \"foo is ~x0 and bar is ~x1.~%\" foo bar)
})

<p>With @('vl-basic-cw-obj'), the arguments are instead expected to be a list,
and this list is deconstructed to produce the alist to be given to @(see
vl-basic-fmt).  For instance, to print the same text as above, we might
write:</p>

@({
 (vl-basic-cw-obj \"foo is ~x0 and bar is ~x1~%\" (list foo bar))
})

<p>This is particularly useful for, e.g., @(see warnings) or other cases where
you want to cons up a structure that can be printed, but not necessarily print
it right away.</p>"

  (cond ((<= (len args) 10)
         (vl-basic-fmt msg (pairlis$
                            '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                            (redundant-list-fix args))))
        (t
         (prog2$ (er hard? 'vl-basic-cw-obj
                     "vl-basic-cw-obj is limited to 10 arguments.")
                 ps))))


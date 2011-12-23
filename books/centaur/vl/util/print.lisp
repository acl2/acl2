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
(local (include-book "make-event/assert" :dir :system))
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


;; These rules force too aggressively since we're often doing things to
;; printedlist's instead of string or character lists here.
(local (in-theory (disable string-listp-of-append
                           string-listp-of-rev)))


(defsection vl-printed-p
  :parents (printer)
  :short "A printed object (string or character)."

  (defund vl-printed-p (x)
    (declare (xargs :guard t))
    (or (characterp x)
        (stringp x)))

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
  :parents (printer))

(defthm vl-printedlist-p-when-character-listp
  (implies (character-listp x)
           (vl-printedlist-p x))
  :hints(("Goal" :induct (len x))))

(defthm vl-printedlist-p-when-string-listp
  (implies (string-listp x)
           (vl-printedlist-p x))
  :hints(("Goal" :induct (len x))))

(defthm vl-printedlist-p-of-repeated-revappend
  (implies (and (vl-printedlist-p x)
                (force (vl-printedlist-p y)))
           (vl-printedlist-p (repeated-revappend n x y)))
  :hints(("Goal" :in-theory (e/d (repeated-revappend)
                                 ((force))))))

(defthm vl-printedlist-p-of-make-list-ac
  (implies (and (vl-printed-p x)
                (force (vl-printedlist-p y)))
           (vl-printedlist-p (make-list-ac n x y)))
  :hints(("Goal" :in-theory (e/d (repeated-revappend)
                                 ((force))))))


(defund vl-printedlist-length (x acc)
  (declare (xargs :guard (and (vl-printedlist-p x)
                              (natp acc))))
    (if (atom x)
        acc
      (vl-printedlist-length (cdr x)
                             (+ (if (characterp (car x))
                                    1
                                  (length (car x)))
                                acc))))


(defund vl-printedlist-peek (x)
  ;; Get the very last character that was printed.
  (declare (xargs :guard (vl-printedlist-p x)
                  :guard-debug t))
  (and (consp x)
       (if (characterp (car x))
           (car x)
         (let ((len (length (car x))))
           (if (= len 0)
               ;; Degenerate case where we printed an empty string, look
               ;; further.
               (vl-printedlist-peek (cdr x))
             (char (car x) (1- len)))))))

(defthm vl-printedlist-p-of-vl-html-encode-chars-aux
  (implies (and (character-listp x)
                (natp col)
                (vl-printedlist-p acc))
           (vl-printedlist-p (mv-nth 1 (vl-html-encode-chars-aux x col tabsize acc))))
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
           (vl-printedlist-p (mv-nth 1 (vl-html-encode-string-aux x n xl col tabsize acc))))
  :hints(("Goal" :in-theory (enable vl-html-encode-string-aux))))


(defthm vl-printedlist-p-of-vl-url-encode-chars-aux
  (implies (vl-printedlist-p acc)
           (vl-printedlist-p (vl-url-encode-chars-aux x acc)))
  :hints(("Goal"
          :induct (vl-url-encode-chars-aux x acc)
          :in-theory (e/d (vl-url-encode-chars-aux) (aref1)))
         (and acl2::stable-under-simplificationp
              '(:in-theory (enable aref1)))))


(defthm vl-printedlist-p-of-vl-url-encode-string-aux
  (implies (and (stringp x)
                (vl-printedlist-p acc)
                (natp n)
                (natp xl)
                (<= n xl)
                (= xl (length x)))
           (vl-printedlist-p (vl-url-encode-string-aux x n xl acc)))
  :hints(("Goal"
          :induct (vl-url-encode-string-aux x n xl acc)
          :in-theory (e/d (vl-url-encode-string-aux)
                          (aref1)))
         (and acl2::stable-under-simplificationp
              '(:in-theory (enable aref1)))))



(defsection ps
  :parents (printer)
  :short "The <b>p</b>rinter <b>s</b>tate stobj."

  :long "<p>Our printer's state is a represented as the stobj <tt>ps</tt>, whose
definition is as follows.</p>

@(def ps)

<p>The main fields are:</p>

<ul>

<li><tt>rchars</tt> -- holds the printed elements (characters and strings) in
reverse order.  The is badly named because originally it only held characters,
but we later extended it to strings to make string-printing more
efficient.</li>

<li><tt>col</tt> -- records the current column number.</li>

</ul>

<p>These fields are typically altered by every printing function.</p>

<p>The printer also includes some configuration fields which allow you to
influence the behavior of certain printing functions.  These fields are
typically not changed by printing functions.  They can also be easily loaded
and saved into a @(see vl-psconfig-p) object.</p>

<ul>

<li><tt>autowrap-col</tt>, a column number for autowrapping,</li>

<li><tt>autowrap-ind</tt>, number of spaces to indent after autowrapping,</li>

<li><tt>htmlp</tt>, a flag indicating whether we are printing html,</li>

<li><tt>tabsize</tt>, the tab size to use for &amp;nbsp; expansion in html mode,</li>

<li><tt>package</tt>, a symbol which specifies the \"home\" package for
    printing symbols (e.g., <tt>ACL2::foo</tt> vs. <tt>VL::foo</tt>.</li>

<li><tt>base</tt>, an <tt>acl2::print-base-p</tt> for base 10, 16, etc.</li>

</ul>

<p>Finally, the printer includes a <tt>misc</tt> field which must be an alist,
and which can be used to pass along any custom parameters that your own
printing functions would like to inspect.</p>

<p>I once considered changing the way <tt>ps</tt> works, so that we would use
an array of characters and write into the array, instead of consing characters.
This is appealing because we might be able to avoid consing during printing at
the cost of having to allocate a buffer at the beginning.  But, preliminary
tests suggested that there is not much of a speed improvement, and while it
might have some nice memory characteristics, the current solution is
particularly nice in that it makes @(see with-local-ps) very cheap, etc.</p>

<h3>Macro wrappers</h3>

<p>We generally hide the existence of <tt>ps</tt> by introducing
<tt>ps</tt>-free wrapper macros.  We provide such macros for the primitive
field accessors:</p>

 @(def vl-ps->rchars)
 @(def vl-ps->col)
 @(def vl-ps->autowrap-col)
 @(def vl-ps->autowrap-ind)
 @(def vl-ps->htmlp)
 @(def vl-ps->tabsize)
 @(def vl-ps->package)
 @(def vl-ps->base)
 @(def vl-ps->misc)

<p>And also for the primitive field mutators:</p>

 @(def vl-ps-update-rchars)
 @(def vl-ps-update-col)
 @(def vl-ps-update-autowrap-col)
 @(def vl-ps-update-autowrap-ind)
 @(def vl-ps-update-htmlp)
 @(def vl-ps-update-tabsize)
 @(def vl-ps-update-package)
 @(def vl-ps-update-base)
 @(def vl-ps-update-misc)"

  (defund print-base-p (x)
    (declare (xargs :guard t))
    (if (acl2::print-base-p x)
        t
      nil))

  (defttag vl-optimize)
  (progn!
   (set-raw-mode t)
   (declaim (inline vl-ps->rchars-fn
                    vl-ps->col-fn
                    vl-ps->autowrap-col-fn
                    vl-ps->autowrap-ind-fn
                    vl-ps->htmlp-fn
                    vl-ps->tabsize-fn
                    vl-ps->package-fn
                    vl-ps->base-fn
                    vl-ps->misc-fn
                    vl-ps-update-rchars-fn
                    vl-ps-update-col-fn
                    vl-ps-update-autowrap-col-fn
                    vl-ps-update-autowrap-ind-fn
                    vl-ps-update-htmlp-fn
                    vl-ps-update-tabsize-fn
                    vl-ps-update-package-fn
                    vl-ps-update-base-fn
                    vl-ps-update-misc-fn)))
  (defttag nil)

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
    (htmlp        :initially nil)

    ;; What is the desired tab size?  This is only used in HTML mode to decide
    ;; how many &nbsp; characters to insert.
    (tabsize      :initially 8 :type (integer 1 *))

    (pkg          :initially VL::a-symbol-that-is-not-imported :type symbol)
    (base         :initially 10 :type (satisfies print-base-p))

    (misc         :initially nil :type (satisfies alistp))

    :inline t

    :renaming ((psp                 vl-pstate-p)
               (rchars              vl-ps->rchars-fn)
               (col                 vl-ps->col-fn)
               (autowrap-col        vl-ps->autowrap-col-fn)
               (autowrap-ind        vl-ps->autowrap-ind-fn)
               (htmlp               vl-ps->htmlp-fn)
               (tabsize             vl-ps->tabsize-fn)
               (pkg                 vl-ps->package-fn)
               (base                vl-ps->base-fn)
               (misc                vl-ps->misc-fn)
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

  (defmacro vl-ps->rchars ()
    `(vl-ps->rchars-fn ps))

  (defmacro vl-ps->col ()
    `(vl-ps->col-fn ps))

  (defmacro vl-ps->autowrap-col ()
    `(vl-ps->autowrap-col-fn ps))

  (defmacro vl-ps->autowrap-ind ()
    `(vl-ps->autowrap-ind-fn ps))

  (defmacro vl-ps->htmlp ()
    `(vl-ps->htmlp-fn ps))

  (defmacro vl-ps->tabsize ()
    `(vl-ps->tabsize-fn ps))

  (defmacro vl-ps->package ()
    `(vl-ps->package-fn ps))

  (defmacro vl-ps->base ()
    `(vl-ps->base-fn ps))

  (defmacro vl-ps->misc ()
    `(vl-ps->misc-fn ps))

  (add-macro-alias vl-ps->rchars             vl-ps->rchars-fn)
  (add-macro-alias vl-ps->col                vl-ps->col-fn)
  (add-macro-alias vl-ps->autowrap-col       vl-ps->autowrap-col-fn)
  (add-macro-alias vl-ps->autowrap-ind       vl-ps->autowrap-ind-fn)
  (add-macro-alias vl-ps->htmlp              vl-ps->htmlp-fn)
  (add-macro-alias vl-ps->tabsize            vl-ps->tabsize-fn)
  (add-macro-alias vl-ps->package            vl-ps->package-fn)
  (add-macro-alias vl-ps->base               vl-ps->base-fn)
  (add-macro-alias vl-ps->misc               vl-ps->misc-fn)


  (defmacro vl-ps-update-rchars (rchars)
    `(vl-ps-update-rchars-fn ,rchars ps))

  (defmacro vl-ps-update-col (col)
    `(vl-ps-update-col-fn ,col ps))

  (defmacro vl-ps-update-autowrap-col (autowrap-col)
    `(vl-ps-update-autowrap-col-fn ,autowrap-col ps))

  (defmacro vl-ps-update-autowrap-ind (autowrap-ind)
    `(vl-ps-update-autowrap-ind-fn ,autowrap-ind ps))

  (defmacro vl-ps-update-htmlp (htmlp)
    `(vl-ps-update-htmlp-fn ,htmlp ps))

  (defmacro vl-ps-update-tabsize (tabsize)
    `(vl-ps-update-tabsize-fn ,tabsize ps))

  (defmacro vl-ps-update-package (package)
    `(vl-ps-update-package-fn ,package ps))

  (defmacro vl-ps-update-base (base)
    `(vl-ps-update-base-fn ,base ps))

  (defmacro vl-ps-update-misc (misc)
    `(vl-ps-update-misc-fn ,misc ps))

  (add-macro-alias vl-ps-update-rchars       vl-ps-update-rchars-fn)
  (add-macro-alias vl-ps-update-col          vl-ps-update-col-fn)
  (add-macro-alias vl-ps-update-autowrap-col vl-ps-update-autowrap-col-fn)
  (add-macro-alias vl-ps-update-autowrap-ind vl-ps-update-autowrap-ind-fn)
  (add-macro-alias vl-ps-update-htmlp        vl-ps-update-htmlp-fn)
  (add-macro-alias vl-ps-update-tabsize      vl-ps-update-tabsize-fn)
  (add-macro-alias vl-ps-update-package      vl-ps-update-package-fn)
  (add-macro-alias vl-ps-update-base         vl-ps-update-base-fn)
  (add-macro-alias vl-ps-update-misc         vl-ps-update-misc-fn)



  (defthm vl-printedlist-p-of-vl-ps->rchars
    (implies (force (vl-pstate-p ps))
             (vl-printedlist-p (vl-ps->rchars))))

  (defthm natp-of-vl-ps->col
    (implies (force (vl-pstate-p ps))
             (natp (vl-ps->col)))
    :rule-classes :type-prescription)

  (defthm natp-of-vl-ps->autowrap-col
    (implies (force (vl-pstate-p ps))
             (natp (vl-ps->autowrap-col)))
    :rule-classes :type-prescription)

  (defthm natp-of-vl-ps->autowrap-ind
    (implies (force (vl-pstate-p ps))
             (natp (vl-ps->autowrap-ind)))
    :rule-classes :type-prescription)

  (defthm posp-of-vl-ps->tabsize
    (implies (force (vl-pstate-p ps))
             (posp (vl-ps->tabsize)))
    :rule-classes :type-prescription)

  (defthm symbolp-of-vl-ps->package
    (implies (force (vl-pstate-p ps))
             (symbolp (vl-ps->package)))
    :rule-classes :type-prescription)

  (defthm print-base-p-of-vl-ps->base
    (implies (force (vl-pstate-p ps))
             (print-base-p (vl-ps->base))))

  (defthm acl2-print-base-p-of-vl-ps->base
    (implies (force (vl-pstate-p ps))
             (acl2::print-base-p (vl-ps->base)))
    :hints(("Goal"
            :use ((:instance print-base-p-of-vl-ps->base))
            :in-theory (e/d (print-base-p)
                            (print-base-p-of-vl-ps->base)))))

  (defthm alistp-of-vl-ps->misc
    (implies (force (vl-pstate-p ps))
             (alistp (vl-ps->misc))))



  (defthm vl-pstate-p-of-vl-ps-update-rchars
    (implies (and (force (vl-printedlist-p x))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-ps-update-rchars x))))

  (defthm vl-pstate-p-of-vl-ps-update-col
    (implies (and (force (natp col))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-ps-update-col col))))

  (defthm vl-pstate-p-of-vl-ps-update-autowrap-col
    (implies (and (force (natp col))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-ps-update-autowrap-col col))))

  (defthm vl-pstate-p-of-vl-ps-update-autowrap-ind
    (implies (and (force (natp col))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-ps-update-autowrap-ind col))))

  (defthm vl-pstate-p-of-vl-ps-update-htmlp
    (implies (force (vl-pstate-p ps))
             (vl-pstate-p (vl-ps-update-htmlp htmlp))))

  (defthm vl-pstate-p-of-vl-ps-update-tabsize
    (implies (and (force (posp tabsize))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-ps-update-tabsize tabsize))))

  (defthm vl-pstate-p-of-vl-ps-update-package
    (implies (and (force (symbolp package))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-ps-update-package package))))

  (defthm vl-pstate-p-of-vl-ps-update-base
    (implies (and (force (print-base-p base))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-ps-update-base base))))

  (defthm vl-pstate-p-of-vl-ps-update-misc
    (implies (and (force (alistp misc))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-ps-update-misc misc))))

  (in-theory (disable vl-pstate-p
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
                      vl-ps-update-misc)))



(defsection defpp
  :parents (printer)
  :short "Macro for introducing user-defined printing functions."

  :long "<p>The macro <tt>defpp</tt> (\"define pretty printer\") helps to
automate the introduction of @(see ps)-based printing functions.</p>

<p>Generally, to carry out your guard proofs, you need to show that every
printing function you introduce will produce a valid <tt>vl-pstate-p</tt> when
given a valid <tt>vl-pstate-p</tt> as input.  This macro automatically tries to
prove this property for you.</p>

<p>See <tt>vl/util/print.lisp</tt> and also <tt>vl/writer.lisp</tt> for many
examples of its use.</p>"

  (defmacro defpp (name formals &key body (guard 't) guard-hints guard-debug parents short long inlinep)
    (let* ((mksym-package-symbol name)
           (fn (mksym name '-fn)))
      `(defsection ,name
         :parents ,parents
         :short ,short
         :long ,long

         (defmacro ,name (,@formals)
           (list ',fn ,@formals 'ps))

         (,(if inlinep 'definlined 'defund) ,fn (,@formals ps)
           (declare (xargs :guard (and ,guard
                                       (vl-pstate-p ps))
                           :stobjs ps
                           :guard-debug ,guard-debug
                           :guard-hints ,guard-hints))
           ,body)

         (add-macro-alias ,name ,fn)

         (local (in-theory (enable ,name)))
         (defthm ,(mksym 'vl-pstate-p-of- name)
           (implies (and (force ,guard)
                         (force (vl-pstate-p ps)))
                    (vl-pstate-p (,name ,@formals)))
           :hints ,guard-hints)))))



(defsection vl-ps-seq
  :parents (basic-printing)
  :short "Macro for issuing a sequence of printer commands."

  :long "<p>The macro <tt>(vl-ps-seq ...)</tt> can be used to combine printing
commands.  For instance,</p>

<code>
 (vl-ps-seq
   (vl-print \"foo\")
   (vl-println \"bar\")
   ...)
</code>

<p>Is short for:</p>

<code>
 (let* ((ps (vl-print \"foo\"))
        (ps (vl-println \"bar\"))
        ...)
   ps)
</code>"

  (defun vl-ps-seq-pairs (x)
    (if (consp x)
        (cons `(ps ,(car x))
              (vl-ps-seq-pairs (cdr x)))
      nil))

  (defmacro vl-ps-seq (&rest args)
    (list 'let* (vl-ps-seq-pairs args) 'ps)))



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
wrapped in a <tt>&lt;span&gt;</tt> tag of the given class."

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
might directly access the <tt>rchars</tt> field of @(see ps), using, e.g.,
@(call vl-ps->rchars), but it is a weird @(see vl-printedlist-p) structure, is
in reverse order, and is generally not very convenient to work with.  So, it
is typically more convenient to use these alternatives.</p>")


(defsection vl-ps->chars
  :parents (accessing-printed-output)
  :short "<tt>(vl-ps-&gt;chars)</tt> returns what was printed as a character
list."

  :long "<p>Building up a big character list can be somewhat expensive, so see
also @(see vl-ps->string).</p>"

  (defund vl-rchars-to-chars (x acc)
    (declare (xargs :guard (vl-printedlist-p x)))
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

  (defthm character-listp-of-vl-rchars-to-chars
    (implies (and (vl-printedlist-p x)
                  (character-listp acc))
             (character-listp (vl-rchars-to-chars x acc)))
    :hints(("Goal" :in-theory (enable vl-rchars-to-chars))))

  (defund vl-ps->chars-fn (ps)
    (declare (xargs :guard (vl-pstate-p ps) :stobjs ps))
    (vl-rchars-to-chars (vl-ps->rchars) nil))

  (defmacro vl-ps->chars ()
    `(vl-ps->chars-fn ps))

  (add-macro-alias vl-ps->chars vl-ps->chars-fn)

  (defthm character-listp-of-vl-ps->chars
    (implies (force (vl-pstate-p ps))
             (character-listp (vl-ps->chars)))
    :hints(("Goal" :in-theory (enable vl-ps->chars)))))



(defsection vl-ps->string
  :parents (accessing-printed-output)
  :short "<tt>(vl-ps-&gt;string)</tt> returns the printed characters as a
string, in the order in which they were printed."

  :long "<p>This is logically just <tt>(coerce (vl-ps-&gt;chars) 'string)</tt>,
but we install a more efficient definition under the hood in raw Lisp.</p>"

  (defund vl-ps->string-fn (ps)
    (declare (xargs :guard (vl-pstate-p ps)
                    :stobjs ps))
    (coerce (vl-ps->chars) 'string))

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

       ;; Since the elems are in reverse order, we'll work backwards from the
       ;; end of the array.
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

  (defttag nil)

  (defmacro vl-ps->string ()
    `(vl-ps->string-fn ps))

  (add-macro-alias vl-ps->string vl-ps->string-fn)

  (defthm stringp-of-vl-ps->string
    (stringp (vl-ps->string))
    :rule-classes :type-prescription
    :hints(("Goal" :in-theory (enable vl-ps->string)))))



(defsection vl-print-to-file
  :parents (accessing-printed-output)
  :short "(program mode) Write the printed characters to a file."

  :long "<p><tt>(vl-print-to-file filename)</tt> writes the printed characters
to the indicated file.</p>"

  (defun vl-print-to-file-fn (filename ps state)
    (declare (xargs :mode :program
                    :guard (stringp filename)
                    :stobjs (ps state)))
    (b* (((mv channel state) (open-output-channel filename :character state))
         (state              (princ$ (vl-ps->string) channel state)))
        (close-output-channel channel state)))

  (defmacro vl-print-to-file (filename)
    `(vl-print-to-file-fn ,filename ps state)))


(defsection with-ps-file
  :parents (accessing-printed-output)
  :short "(program mode) Convenient wrapper for @(see vl-print-to-file)."
  :long "@(def with-ps-file)"

  (defmacro with-ps-file (filename &rest forms)
    `(acl2::with-local-stobj ps
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
<tt>with-local-stobj</tt> to give you a temporary <tt>ps</tt> to work with.</p>

<p>An alternative, which we do not often use, is to explicitly manage saving
and restoring of the printer's state.  To support this, we provide some
routines for saving and restoring configurations, and for resetting the
printer's fields.</p>")

(defsection with-local-ps
  :parents (printing-locally)
  :short "Print using a local instance of @(see ps)."

  :long "<p>The convenient (but trivial) macro <tt>with-local-ps</tt> allows
you to print using a local copy of @(see ps), and returns the result of
printing as a string.</p>

<p>Unfortunately, <tt>with-local-stobj</tt> cannot be used at the top level
loop, and hence <tt>with-local-ps</tt> cannot be used at the top level.
However, it can still be used in functions, and you can call those functions
from the loop.  For instance,</p>

<code>
 (defun f (foo bar)
   (declare (xargs :guard (and (integerp foo) (integerp bar))))
   (with-local-ps
    (vl-print \"; foo = \")
    (vl-print foo)
    (vl-print \", bar = \")
    (vl-print bar)))

 (f 3 6) ;; returns \"; foo = 3, bar = 6\"
</code>

<p>Note that in this example, <tt>f</tt> prints using the default
configuration.  Other configurations can be easily saved and loaded; see the
discussion in @(see vl-psconfig-p) for details.</p>"

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
  :long "<p><tt>(vl-cw-ps-seq ...)</tt> expands to <tt>(cw-unformatted (@(see
with-local-ps) ...))</tt>.  Due to the use of <tt>with-local-ps</tt>, this
macro can only be used within functions, and cannot be called from the top
level.</p>"

  (defmacro vl-cw-ps-seq (&rest args)
    `(cw-unformatted (with-local-ps ,@args))))



(defpp vl-ps-full-reset ()
  :parents (printing-locally)
  :short "Erase all contents and reset @(see ps) to its default configuration."

  :long "<p><tt>(vl-ps-full-reset)</tt> restores @(see ps) to its initial
state.  This erases any text that has been printed, sets the column number to
0, and also sets all of the config variables to their defaults (text mode, 80
column autowrap with 5 space autoindent, and a tab size of 8.)  See also @(see
vl-ps-text-reset) for an alternative that does not alter the configuration.</p>"

  :body (vl-ps-seq
         (vl-ps-update-rchars nil)
         (vl-ps-update-col 0)
         (vl-ps-update-autowrap-col 80)
         (vl-ps-update-autowrap-ind 5)
         (vl-ps-update-htmlp nil)
         (vl-ps-update-tabsize 8)
         (vl-ps-update-package 'VL::a-symbol-that-is-not-imported)
         (vl-ps-update-base 10)))


(defpp vl-ps-text-reset ()
  :parents (printing-locally)
  :short "Erase the contents of @(see ps) without altering its configuration."

  :long "<p><tt>(vl-ps-text-reset)</tt> erases any text in @(see ps) and sets
the column number to 0.  It does not alter any of the configuration variables.
See also @(see vl-ps-full-reset) for a way to completely restore @(see ps) to
its default state.</p>"

  :body (vl-ps-seq
         (vl-ps-update-rchars nil)
         (vl-ps-update-col 0)))



(defaggregate vl-psconfig
  (autowrap-col autowrap-ind htmlp tabsize package base)
  :tag :vl-psconfig
  :require ((natp-of-vl-psconfig->autowrap-col (natp autowrap-col))
            (natp-of-vl-psconfig->autowrap-ind (natp autowrap-ind))
            (booleanp-of-vl-psconfig->htmlp    (booleanp htmlp))
            (posp-of-vl-psconfig->tabsize      (posp tabsize))
            (symbolp-of-vl-psconfig->package   (symbolp package))
            (print-base-p-of-vl-psconfig->base (print-base-p base)))
  :parents (printing-locally)
  :short "Configuration object for saving and loading printer state."
  :long "See @(see vl-ps-load-config) and @(see vl-ps-save-config).")

(defthm vl-psconfig->tabsize-type
  (implies (force (vl-psconfig-p config))
           (posp (vl-psconfig->tabsize config)))
  :rule-classes :type-prescription)


(defpp vl-ps-load-config (config)
  :parents (printing-locally)
  :short "Load configuration settings from a @(see vl-psconfig-p) object into
@(see ps)."

  :long "<p>Note that this does not change the currently-printed text or update
the column number; it only changes the configuration settings.</p>"

  :guard (vl-psconfig-p config)
  :body (let ((autowrap-col (vl-psconfig->autowrap-col config))
              (autowrap-ind (vl-psconfig->autowrap-ind config))
              (htmlp        (vl-psconfig->htmlp config))
              (tabsize      (vl-psconfig->tabsize config))
              (package      (vl-psconfig->package config))
              (base         (vl-psconfig->base config)))
          (vl-ps-seq (vl-ps-update-autowrap-col autowrap-col)
                     (vl-ps-update-autowrap-ind autowrap-ind)
                     (vl-ps-update-htmlp htmlp)
                     (vl-ps-update-tabsize tabsize)
                     (vl-ps-update-package package)
                     (vl-ps-update-base base))))


(defsection vl-ps-save-config
  :parents (printing-locally)
  :short "Save the current configuration of @(see ps) into a @(see
vl-psconfig-p) object."

  :long "<p>Note that this does not save the currently-printed text and column
number; only the configuration settings are saved.</p>"

  (defund vl-ps-save-config-fn (ps)
    (declare (xargs :guard (vl-pstate-p ps)
                    :stobjs ps))
    (make-vl-psconfig :autowrap-col (vl-ps->autowrap-col)
                      :autowrap-ind (vl-ps->autowrap-ind)
                      :htmlp        (if (vl-ps->htmlp) t nil)
                      :tabsize      (vl-ps->tabsize)
                      :package      (vl-ps->package)
                      :base         (vl-ps->base)
                      ))

  (defmacro vl-ps-save-config ()
    `(vl-ps-save-config-fn ps))

  (add-macro-alias vl-ps-save-config vl-ps-save-config-fn)

  (defthm vl-psconfig-p-of-vl-ps-save-config
    (implies (force (vl-pstate-p ps))
             (vl-psconfig-p (vl-ps-save-config)))
    :hints(("Goal" :in-theory (enable vl-ps-save-config)))))





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

(defund vl-col-after-printing-chars (col chars)
  ;; Chars are some characters to print, which are not yet reversed.  Col is
  ;; our current cursor column number.  We figure out what the new column is
  ;; going to be after we print chars.
  (declare (xargs :guard (and (natp col)
                              (character-listp chars)))
           (type integer col))

; BOZO can this possibly be right?  What about tabs?

  (cond ((atom chars)
         (mbe :logic (nfix col)
              :exec col))
        ((eql (car chars) #\Newline)
         (vl-col-after-printing-chars 0 (cdr chars)))
        (t
         (vl-col-after-printing-chars (+ 1 col) (cdr chars)))))

(defthm natp-of-vl-col-after-printing-chars
  (natp (vl-col-after-printing-chars col chars))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-col-after-printing-chars))))

(defund vl-col-after-printing-string-aux (col x n xl)
  (declare (xargs :guard (and (natp col)
                              (stringp x)
                              (natp n)
                              (natp xl)
                              (<= n xl)
                              (= xl (length x)))
                  :measure (nfix (- (nfix xl) (nfix n))))
           (type integer col n xl)
           (type string x))
  (cond ((mbe :logic (zp (- (nfix xl) (nfix n)))
              :exec (= n xl))
         (mbe :logic (nfix col)
              :exec col))
        ((eql (char x n) #\Newline)
         (vl-col-after-printing-string-aux 0 x
                                           (mbe :logic (+ 1 (nfix n)) :exec (+ 1 n))
                                           xl))
        (t
         (vl-col-after-printing-string-aux (+ 1 col)
                                           x
                                           (mbe :logic (+ 1 (nfix n)) :exec (+ 1 n))
                                           xl))))

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
                             vl-col-after-printing-chars))))

(definlined vl-col-after-printing-string (col string)
  (declare (xargs :guard (and (natp col)
                              (stringp string)))
           (type integer col)
           (type string string))
  (mbe :logic (vl-col-after-printing-chars col (coerce string 'list))
       :exec (vl-col-after-printing-string-aux col string 0 (length string))))

(defthm natp-of-vl-col-after-printing-string
  (natp (vl-col-after-printing-string col string))
  :rule-classes :type-prescription
  :hints(("Goal" :in-theory (enable vl-col-after-printing-string))))



(defpp vl-indent (n)
  :guard (natp n)
  :parents (basic-printing)
  :short "@(call vl-indent) indents to column <tt>n</tt>."

  :long "<p>In text mode we indent by printing spaces; in HTML mode we instead
print <tt>&amp;nbsp;</tt> characters.  Note that this function has no effect if
we are already past column <tt>n</tt>.</p>"

  :body
  (let ((rchars (vl-ps->rchars))
        (col    (vl-ps->col))
        (htmlp  (vl-ps->htmlp)))
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






(defsection vl-printable-p
  :parents (basic-printing)
  :short "@(call vl-printable-p) recognizes strings, character lists, numbers, and
ordinary characters."
  :long "<p>We use this function as the guard for functions such as @(see
vl-print), @(see vl-println), etc.  We do not allow <tt>x</tt> to be a symbol
because of the potential confusion between the symbol <tt>nil</tt> and
character lists.</p>"

  (defund vl-printable-p (x)
    (declare (xargs :guard t))
    (or (stringp x)
        (character-listp x)
        (acl2-numberp x)
        (characterp x)))

  (local (in-theory (enable vl-printable-p)))

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



(defund vl-string-needs-html-encoding-p (x n xl)
  (declare (type string x)
           (type integer n xl)
           (xargs :guard (and (stringp x)
                              (natp n)
                              (natp xl)
                              (<= n xl)
                              (= xl (length x)))
                  :measure (nfix (- (nfix xl) (nfix n)))))
  (if (mbe :logic (zp (- (nfix xl) (nfix n)))
           :exec (= xl n))
      nil
    (let ((char (char x n)))
      (or (eql char #\Space)
          (eql char #\Newline)
          (eql char #\<)
          (eql char #\>)
          (eql char #\&)
          (eql char #\")
          (eql char #\Tab)
          (vl-string-needs-html-encoding-p x
                                           (+ (mbe :logic (nfix n) :exec n) 1)
                                           xl)))))



(defsection vl-print
  :parents (basic-printing)
  :short "@(call vl-print) prints text with automatic encoding."

  :long "<p><tt>x</tt> may be any @(see vl-printable-p) object, and we print it
to @(see ps).  In text mode, the characters for the printed representation of
<tt>x</tt> are printed verbatim.  In HTML mode, we automatically encode
characters like <tt>&amp;</tt> into <tt>&amp;amp;</tt>.  See also @(see
vl-print-markup) and @(see vl-print-url) for alternatives that perform
different kinds of encoding.</p>"

  (defpp vl-print-str-main (x)
    :guard (stringp x)
    :body
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

  (defpp vl-print-charlist-main (x)
    :guard (character-listp x)
    :body
    (let ((rchars  (vl-ps->rchars))
          (col     (vl-ps->col)))
      (if (vl-ps->htmlp)
          (mv-let (col rchars)
            (vl-html-encode-chars-aux x col (vl-ps->tabsize) rchars)
            (vl-ps-seq (vl-ps-update-rchars rchars)
                       (vl-ps-update-col col)))
        (vl-ps-seq (vl-ps-update-rchars (revappend x rchars))
                   (vl-ps-update-col (vl-col-after-printing-chars col x))))))

  (defpp vl-print-main (x)
    :guard (vl-printable-p x)
    :guard-debug t
    :inlinep t
    :body
    (if (stringp x)
        (vl-print-str-main x)
      (vl-print-charlist-main (if (atom x) (explode-atom x 10) x))))

  (defpp vl-print-raw-fast (x len)
    :guard (and (stringp x)
                (natp len))
    :body
    (vl-ps-seq (vl-ps-update-rchars (cons x (vl-ps->rchars)))
               (vl-ps-update-col (+ len (vl-ps->col)))))

  (defmacro vl-print-str (x)
    ;; Same as (vl-print x), but requires (stringp x) instead of
    ;; (vl-printable-p x), and may be somewhat faster as a result.
    (cond ((equal x "")
           'ps)
          ((and (stringp x)
                (not (vl-string-needs-html-encoding-p x 0 (length x))))
           `(vl-print-raw-fast ,x ,(length x)))
          (t
           `(vl-print-str-main ,x))))

  (defmacro vl-print (x)
    (cond ((equal x "")
           'ps)
          ((stringp x)
           (if (vl-string-needs-html-encoding-p x 0 (length x))
               `(vl-print-str ,x)
             `(vl-print-raw-fast ,x ,(length x))))
          (t
           `(vl-print-main ,x)))))


(defsection vl-print-nat
  :parents (basic-printing)
  :short "@(call vl-print-nat) is an optimized version of @(see vl-print) for
natural numbers."

  ;; We make a few optimizations.
  ;;
  ;; 1. Numbers don't have to be encoded, so there's no need to consider
  ;;    whether we're in HTML mode.
  ;;
  ;; 2. We essentially use str::revappend-natchars instead of calling
  ;;    str::natstr or similar.  This does the minimum amount of consing and
  ;;    doesn't build a string.
  ;;
  ;; 3. We manually inline the executable definition of str::revappend-natchars
  ;;    to avoid doing the loop.

; How many characters are printed?  If 0-9, we need one digit.  10-99 we need 2 digits.
; etc.  We're asking for the minimum power of ten that is less than the number.
; This is hrmn.

  (local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))
  (local (in-theory (enable acl2-count)))

  (local (defthm crock
           (implies (posp n)
                    (< (acl2-count (floor n 10))
                       (acl2-count n)))
           :rule-classes ((:rewrite) (:linear))))

  (defund vl-print-natchars-aux (n acc col)
    (declare (type integer n col)
             (xargs :guard (and (natp n)
                                (natp col))
                    :verify-guards nil))
    (if (mbe :logic (zp n)
             :exec (= (the integer n) 0))
        (mv acc col)
      (mv-let (acc col)
        (vl-print-natchars-aux (the integer (truncate (the integer n) 10)) acc col)
        (mv (cons (the character (code-char
                                  (the (unsigned-byte 8)
                                    (+ (the (unsigned-byte 8) 48)
                                       (the (unsigned-byte 8)
                                         (rem (the integer n) 10))))))
                  acc)
            (+ 1 col)))))

  (local (in-theory (enable vl-print-natchars-aux)))

  (defthm natp-of-vl-print-natchars-aux-1
    (implies (natp col)
             (natp (mv-nth 1 (vl-print-natchars-aux n acc col))))
    :rule-classes :type-prescription)

  (defthm acc-of-vl-print-natchars-aux
    (equal (mv-nth 0 (vl-print-natchars-aux n acc col))
           (str::revappend-natchars-aux n acc))
    :hints(("Goal" :in-theory (e/d (str::revappend-natchars-aux)
                                   (str::revappend-natchars-aux-redef)))))

  (verify-guards vl-print-natchars-aux)

  (defpp vl-print-nat-main (n)
    :guard (natp n)
    :body
    (if (equal n 0)
        (vl-ps-seq (vl-ps-update-rchars (cons #\0 (vl-ps->rchars)))
                   (vl-ps-update-col (+ 1 (vl-ps->col))))
      (mv-let (rchars col)
        (vl-print-natchars-aux n (vl-ps->rchars) (vl-ps->col))
        (vl-ps-seq
         (vl-ps-update-rchars rchars)
         (vl-ps-update-col col)))))

  (defmacro vl-print-nat (x)
    (cond ((natp x)
           (let ((str (str::natstr x)))
             `(vl-print-raw-fast ,str ,(length str))))
          (t
           `(vl-print-nat-main ,x)))))



(defund vl-remove-leading-spaces (x)
  (declare (xargs :guard t))
  (cond ((atom x)
         x)
        ((eql (car x) #\Space)
         (vl-remove-leading-spaces (cdr x)))
        (t
         x)))

(defthm vl-printedlist-p-of-vl-remove-leading-spaces
  (implies (force (vl-printedlist-p x))
           (vl-printedlist-p (vl-remove-leading-spaces x)))
  :hints(("Goal" :in-theory (enable vl-remove-leading-spaces))))



(defsection vl-println
  :parents (basic-printing)
  :short "@(call vl-println) prints text with automatic encoding, and always
adds a newline."
  :long "<p>This function is like @(see vl-print), except that a newline is
printed after <tt>x</tt>.  When we are in HTML mode, a <tt>&lt;br/&gt;</tt>
tag and a newline are printed.</p>"

  (defpp vl-println-main (x)
    :guard (vl-printable-p x)
    :body
    (let* ((rchars (vl-ps->rchars))
           (col    (vl-ps->col))
           (htmlp  (vl-ps->htmlp))
           ;; Coerce X into either a string or character list.
           (x      (cond ((stringp x) x)
                         ((atom x)    (explode-atom x 10))
                         (t           x))))
      (if htmlp
          ;; Need to do HTML encoding.
          (b* ((tabsize       (vl-ps->tabsize))
               ((mv & rchars) (if (stringp x)
                                  (vl-html-encode-string-aux x 0 (length x) col tabsize rchars)
                                (vl-html-encode-chars-aux x col tabsize rchars))))
            (vl-ps-seq (vl-ps-update-rchars (revappend *vl-html-newline* rchars))
                       (vl-ps-update-col 0)))
        ;; Plain-text, no encoding necessary.

; We used to remove any trailing whitespace before printing the newline, but
; now for simplicity and performance we don't bother.

        (if (stringp x)
            (vl-ps-seq (vl-ps-update-rchars
                        (cons #\Newline
                              ;; the following used to be: (vl-remove-leading-spaces (str::revappend-chars x rchars)
                              (cons x rchars)))
                       (vl-ps-update-col 0))
          (vl-ps-seq (vl-ps-update-rchars
                      (cons #\Newline
                            ;; the following used to be: (vl-remove-leading-spaces (revappend x rchars))
                            (revappend x rchars)))
                     (vl-ps-update-col 0))))))

  (defpp vl-println-raw-fast1 ()
    :inlinep t
    :body
    (vl-ps-seq
     (vl-ps-update-rchars (cons (if (vl-ps->htmlp) "<br/>
" #\Newline) (vl-ps->rchars)))
     (vl-ps-update-col 0)))

  (defpp vl-println-raw-fast2 (str)
    :guard (stringp str)
    :inlinep t
    :body
    (vl-ps-seq
     (vl-ps-update-rchars (cons (if (vl-ps->htmlp) "<br/>
" #\Newline) (cons str (vl-ps->rchars))))
     (vl-ps-update-col 0)))

  (defmacro vl-println (x)
    (cond ((equal x "")
           `(vl-println-raw-fast1))
          ((and (stringp x)
                (not (vl-string-needs-html-encoding-p x 0 (length x))))
           `(vl-println-raw-fast2 ,x))
          (t
           `(vl-println-main ,x)))))



(defpp vl-println? (x)
  :guard (vl-printable-p x)
  :parents (basic-printing)
  :short "@(call vl-println?) prints text with automatic encoding, and may also
inserts a newline if we have gone past the <tt>autowrap-col</tt>."

  :long "<p>This function is like @(see vl-print), except that after <tt>x</tt>
is printed, we check to see whether the current <tt>col</tt> exceeds the
<tt>autowrap-col</tt> for @(see ps).  If so, we insert a newline (and, in HTML
mode, a <tt>&lt;br/&gt;</tt> tag) as in @(see vl-println), and indent the next
line to the column specified by the @(see ps)'s <tt>autowrap-ind</tt>.</p>

<p>When writing pretty-printers, it is useful to call this function in places
that would be acceptable line-break points, so that very long lines will be
split up at reasonably good places.</p>"

  :body
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


(defsection vl-print-markup
  :parents (basic-printing)
  :short "@(call vl-print-markup) prints verbatim text with no encoding."
  :long "<p><tt>x</tt> is any object that satisfies @(see vl-printable-p).  We
print the characters for <tt>x</tt> directly to @(see ps) without any automatic
encoding, no matter what mode we are in.  This function is generally intended
for the printing of HTML tags.</p>"

  (defpp vl-print-markup-main (x)
    :guard (vl-printable-p x)
    :body (let ((rchars  (vl-ps->rchars)))
            (cond ((stringp x)
                   (vl-ps-update-rchars (cons x rchars)))
                  ((atom x)
                   (vl-ps-update-rchars (revappend (explode-atom x 10) rchars)))
                  (t
                   (vl-ps-update-rchars (revappend x rchars))))))

  (defpp vl-print-markup-raw-fast (x)
    :guard (stringp x)
    :inlinep t
    :body
    (vl-ps-update-rchars (cons x (vl-ps->rchars))))

  (defmacro vl-print-markup (x)
    (if (stringp x)
        `(vl-print-markup-raw-fast ,x)
      `(vl-print-markup-main ,x))))



(defpp vl-println-markup (x)
  :guard (vl-printable-p x)
  :parents (basic-printing)
  :short "@(call vl-println-markup) prints verbatim text with no encoding, then
prints a newline."
  :long "<p>This is identical to @(see vl-print-markup) except for the newline.
Unlike @(see vl-println), no <tt>&lt;br/&gt;</tt> tag is printed in HTML mode.
The goal is only to provide a convenient way to insert line breaks in the
middle of a lot of markup.</p>"
  :body
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


(defpp vl-print-url (x)
  :guard (vl-printable-p x)
  :parents (basic-printing)
  :short "@(call vl-print-url) prints text with automatic URL encoding."
  :long "<p>This function simply prints the URL-encoding of <tt>x</tt> to @(see
ps), regardless of the output mode.  It is useful for printing parts of URLs
with the proper encoding.</p>"
  :body
  (let ((rchars (vl-ps->rchars)))
    (cond ((stringp x)
           (vl-ps-update-rchars (vl-url-encode-string-aux x 0 (length x) rchars)))
          ((atom x)
           (vl-ps-update-rchars (vl-url-encode-chars-aux (explode-atom x 10) rchars)))
          (t
           (vl-ps-update-rchars (vl-url-encode-chars-aux x rchars))))))



(defpp vl-print-strings-with-commas-aux (x)
  :guard (string-listp x)
  :body (cond ((atom x)
               ps)
              ((atom (cdr x))
               (vl-print (car x)))
              (t
               (vl-ps-seq (vl-print (car x))
                          (vl-println? ", ")
                          (vl-print-strings-with-commas-aux (cdr x))))))

(defpp vl-print-strings-with-commas (x indent)
  :guard (and (string-listp x)
              (natp indent))
  :parents (basic-printing)
  :short "@(call vl-print-strings-with-commas) prints the elements of
<tt>x</tt>, a string list, separated by commas."
  :long "<p>The output is automatically encoded and word wrapped, and each line
is indented to column <tt>indent</tt>.</p>"
  :body (let ((orig-indent (vl-ps->autowrap-ind)))
          (vl-ps-seq
           (vl-ps-update-autowrap-ind indent)
           (vl-indent indent)
           (vl-print-strings-with-commas-aux x)
           (vl-ps-update-autowrap-ind orig-indent))))


(defpp vl-print-strings-as-lines (x)
  :guard (string-listp x)
  :parents (basic-printing)
  :short "@(call vl-print-strings-as-lines) prints the elements of <tt>x</tt>,
a string list, on separate lines."
  :long "<p>The output is automatically encoded, and <tt>&lt;br/&gt;</tt> tags are
added to separate the lines when we are in the HTML output mode.  Each string is
printed on its own line, with no indenting and no automatic word wrapping.</p>"
  :body (if (atom x)
            ps
          (vl-ps-seq
           (vl-println (car x))
           (vl-print-strings-as-lines (cdr x)))))



(defsection formatted-printing
  :parents (printer)
  :short "Higher-level routines for printing objects with a <tt>fmt</tt>- or
<tt>cw</tt>-like feel."

  :long "<p>We implement limited versions of <tt>fmt</tt> and <tt>cw</tt>.  The
following ACL2-style directives are supported and behave similarly as those
described in \"<tt>:doc fmt</tt>.\"</p>

<ul>

<li><tt>~~</tt>, prints a tilde</li>
<li><tt>~%</tt>, prints a newline</li>
<li><tt>~|</tt>, prints a newline if we are not already on column 0</li>
<li><tt>~[space]</tt>, prints a space</li>
<li><tt>~\[newline]</tt>, skips subsequent whitespace</li>

<li><tt>~xi</tt>, pretty-print an object.</li>

<li><tt>~si</tt>, prints a string verbatim, or acts like <tt>~xi</tt> when
given any non-string object.</li>

<li><tt>~&amp;i</tt>, print a list, separated by commas, with the word \"and\"
preceeding the final element.</li>

</ul>

<p>Note: our pretty-printer is currently very lousy.  Its output is not
nearly as nice as ACL2's ordinary <tt>~x</tt> directives.</p>

<p>Note: although other ACL2-style directives are not yet supported, we
may eventually extend the printer to allow them.</p>")


(defsection vl-ppr-escape-slashes

  (defund vl-ppr-escape-slashes (x n xl slash-char col acc)
    "Returns (MV COL-PRIME ACC-PRIME)"
    (declare (xargs :guard (and (stringp x)
                                (natp n)
                                (natp xl)
                                (natp col)
                                (<= n xl)
                                (= xl (length x)))
                    :measure (nfix (- (nfix xl) (nfix n)))))

; This is basically like acl2::prin1-with-slashes, but we put the characters
; into the accumulator in reverse order instead of printing them.

    (if (mbe :logic (zp (- (nfix xl) (nfix n)))
             :exec (= n xl))
        (mv (mbe :logic (nfix col) :exec col)
            acc)
      (let ((char (char x n)))
        (vl-ppr-escape-slashes x
                               (mbe :logic (+ 1 (nfix n)) :exec (+ 1 n))
                               xl
                               slash-char
                               (if (eql char #\Newline)
                                   0
                                 (+ 1 col))
                               (if (or (eql char #\\)
                                       (eql char slash-char))
                                   (list* char #\\ acc)
                                 (cons char acc))))))

  (local (in-theory (enable vl-ppr-escape-slashes)))

  (defthm natp-of-vl-ppr-escape-slashes
    (natp (mv-nth 0 (vl-ppr-escape-slashes x n xl slash-char col acc)))
    :rule-classes :type-prescription)

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
      (mv (+ (mbe :logic (nfix col) :exec col)
             (length name))
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
             (mv (+ (mbe :logic (nfix col) :exec col) len) (revappend explode acc))))
          ((characterp x)
           (case x
             (#\Space   (mv (+ (mbe :logic (nfix col) :exec col) 7)
                            (str::revappend-chars "#\\Space" acc)))
             (#\Newline (mv (+ (mbe :logic (nfix col) :exec col) 9)
                            (str::revappend-chars "#\\Newline" acc)))
             (#\Tab     (mv (+ (mbe :logic (nfix col) :exec col) 5)
                            (str::revappend-chars "#\\Tab" acc)))
             (#\Rubout  (mv (+ (mbe :logic (nfix col) :exec col) 8)
                            (str::revappend-chars "#\\Rubout" acc)))
             (#\Page    (mv (+ (mbe :logic (nfix col) :exec col) 6)
                            (str::revappend-chars "#\\Page" acc)))
             (otherwise (mv (+ (mbe :logic (nfix col) :exec col) 3)
                            (list* x #\\ #\# acc)))))
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
            (mv (+ 1 (mbe :logic (nfix col) :exec col))
                (if in-listp acc (cons #\) acc))))

           ;; "Maybe break"
           ((mv col acc) (if (< col rmargin)
                             (mv col acc)
                           (mv 0 (cons #\Newline acc)))))

          (if (consp (cdr x))
              ;; Successive elements of a list, no dots.
              (b* (((mv col acc)
                    (vl-stupid-ppr1 (cdr x) pkg base rmargin t (+ 1 col) (cons #\Space acc))))

                  (mv (mbe :logic (+ 1 (nfix col))
                           :exec (+ 1 col))
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

                (mv (mbe :logic (+ 1 (nfix col))
                         :exec (+ 1 col))
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
        (mbe :logic (nfix n)
             :exec n)
      (let ((char (char x n)))
        (if (or (eql char #\Space)
                (eql char #\Newline)
                (eql char #\Tab)
                (eql char #\Page))
            (vl-skip-ws x
                        (+ (mbe :logic (nfix n) :exec n) 1)
                        xl)
          (mbe :logic (nfix n)
               :exec n)))))

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
    (b* ((n  (mbe :logic (nfix n) :exec n))
         (xl (mbe :logic (nfix xl) :exec xl))
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



(defpp vl-fmt-tilde-x (x)
  :guard t
  :body
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

(defpp vl-fmt-tilde-s (x)
  :guard t
  :body
  (cond ((stringp x)
         (vl-print x))
        (t
         (vl-fmt-tilde-x x))))

(defpp vl-fmt-tilde-& (x)
  :guard t
  :body
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




(defpp vl-fmt-print-space ()
  ;; Prints spaces encountered in the format string itself, maybe word-wrapping
  ;; if necessary.
  :body
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

(defpp vl-fmt-print-normal (x)
  :guard (characterp x)
  :body
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
             :exec (= xl n))
        ps
      (b* (((mv type val n)
            (vl-basic-fmt-parse-tilde x n xl))
           (ps (case type
                 (:skip   ps)
                 (:normal (vl-fmt-print-normal val))
                 (:hard-space (vl-print #\Space))
                 (:cbreak (if (= (vl-ps->col) 0) ps (vl-println "")))
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
          (vl-basic-fmt-aux x n xl alist))))

  (local (in-theory (enable vl-basic-fmt-aux-fn)))

  (defthm vl-pstate-p-of-vl-basic-fmt-aux
    (implies (and (force (stringp x))
                  (force (natp n))
                  (force (natp xl))
                  (force (<= n xl))
                  (force (= xl (length x)))
                  (force (alistp alist))
                  (force (vl-pstate-p ps)))
             (vl-pstate-p (vl-basic-fmt-aux x n xl alist)))))


(defpp vl-basic-fmt (x alist)
  :guard (and (stringp x)
              (alistp alist))
  :parents (formatted-printing)
  :short "Basic <tt>fmt</tt>-like printing function for @(see ps)."
  :long "<p>@(call vl-basic-fmt) takes as inputs <tt>x</tt>, a format string as
described in @(see formatted-printing), and an alist that should map characters
to objects, which provides the arguments to the format string, as in ordinary
fmt-style ACL2 printing.</p>"
  :body (vl-basic-fmt-aux x 0 (length x) alist))



(defsection vl-basic-cw
  :parents (formatted-printing)
  :short "Basic <tt>cw</tt>-like printing function for @(see ps)."
  :long "<p>This is a simple wrapper for @(see vl-basic-fmt).  See also @(see
vl-basic-cw-obj).</p>"

  (defmacro vl-basic-cw (x &rest args)
    `(vl-basic-fmt ,x (pairlis$
                       '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                       (list ,@args)))))


(defpp vl-basic-cw-obj (msg args)
  :guard (stringp msg)
  :parents (formatted-printing)
  :short "Like @(see vl-basic-cw), but reads its format string from an object."

  :long "<p>Ordinariy, <tt>vl-basic-cw</tt> requires you to provide its
arguments explicitly in the macro call.  That is, you might write something
like this:</p>

<code>
 (vl-basic-cw \"foo is ~x0 and bar is ~x1.~%\" foo bar)
</code>

<p>With <tt>vl-basic-cw-obj</tt>, the arguments are instead expected to be a
list, and this list is deconstructed to produce the alist to be given to @(see
vl-basic-fmt).  For instance, to print the same text as above, we might
write:</p>

<code>
 (vl-basic-cw-obj \"foo is ~x0 and bar is ~x1~%\" (list foo bar))
</code>

<p>This is particularly useful for, e.g., @(see warnings) or other cases where
you want to cons up a structure that can be printed, but not necessarily print
it right away.</p>"

  :body (cond ((<= (len args) 10)
               (vl-basic-fmt msg (pairlis$
                                  '(#\0 #\1 #\2 #\3 #\4 #\5 #\6 #\7 #\8 #\9)
                                  (redundant-list-fix args))))
              (t
               (prog2$ (er hard? 'vl-basic-cw-obj
                           "vl-basic-cw-obj is limited to 10 arguments.")
                       ps))))

